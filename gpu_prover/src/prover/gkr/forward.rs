use std::collections::BTreeMap;
use std::mem::ManuallyDrop;
use std::ops::DerefMut;
use std::ptr::null;
use std::sync::Arc;

use cs::definitions::{
    gkr::{AddressSpaceType, RamWordRepresentation, DECODER_LOOKUP_FORMAL_SET_INDEX},
    GKRAddress, VirtualSetupPoly, PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
};
use cs::gkr_compiler::{
    CompiledAddressSpaceRelationStrict, CompiledAddressStrict, CompiledMemoryTimestamp,
    GKRCircuitArtifact, GKRLayerDescription, InitsOrTeardownsTimestampAndValue,
    NoFieldGKRCacheRelation, NoFieldGKRRelation, OutputType,
};
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::memory::memory_copy_async;
use era_cudart::paste::paste;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use field::{Field, FieldExtension, PrimeField};
use prover::gkr::high_bits_offset_for_inits_and_teardowns;
use prover::gkr::prover::dimension_reduction::forward::DimensionReducingInputOutput;
use prover::gkr::prover::GKRExternalChallenges;

use super::backward::GpuGKRDimensionReducingBackwardState;
use super::setup::{bootstrap_storage_from_trace_holders, GpuGKRForwardSetup};
use super::stage1::GpuGKRStage1Output;
use super::transform::normalize_compiled_circuit_for_gpu;
use super::{
    GpuBaseFieldPoly, GpuBaseFieldSourceKind, GpuExtensionFieldPoly, GpuGKRLayerSource,
    GpuGKRStorage,
};
use crate::allocator::tracker::AllocationPlacement;
use crate::ops::simple::{
    add_into_y, mul, mul_into_y, set_by_ref, set_by_val, sub_into_x, Add, BinaryOp, Mul, SetByRef,
    SetByVal, Sub,
};
use crate::primitives::context::{DeviceAllocation, HostAllocation, ProverContext, UnsafeAccessor};
use crate::primitives::device_structures::{DeviceMatrixChunkMutImpl, DeviceVectorChunk};
use crate::primitives::device_tracing::Range;
use crate::primitives::field::{BF, E4};
use crate::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};

pub(crate) struct GpuGKRForwardOutput<B, E> {
    tracing_ranges: Vec<Range>,
    pub(crate) storage: GpuGKRStorage<B, E>,
    pub(crate) initial_layer_for_sumcheck: usize,
    pub(crate) dimension_reducing_inputs:
        BTreeMap<usize, BTreeMap<OutputType, DimensionReducingInputOutput>>,
}

pub(crate) struct GpuGKRTranscriptHandoff<E> {
    _tracing_ranges: Vec<Range>,
    explicit_evaluations: BTreeMap<OutputType, [HostAllocation<[E]>; 2]>,
    /// Backing for the packed flat evaluations buffer: the consolidated
    /// per-`AddressClass` Arc populated by the forward dim-reduction pass.
    /// All reduced-output polys for the initial sumcheck layer share this
    /// Arc with `poly_idx == BTreeMap iteration index`, so the first
    /// `flat_total_len` elements form the same contiguous packing the
    /// transcript and initial-claim kernels consume.
    flat_evaluations_backing: Arc<DeviceAllocation<E>>,
    /// Number of valid `E` elements at the start of `flat_evaluations_backing`
    /// — `num_polys * poly_len`, equal to `backing.len()` in the production
    /// path but sized explicitly to keep the contract local.
    flat_total_len: usize,
}

pub(crate) struct ForwardOutputSlabTarget<E> {
    pub(crate) backing: Arc<DeviceAllocation<E>>,
    pub(crate) len: usize,
}

impl<E: Copy> GpuGKRTranscriptHandoff<E> {
    pub(crate) fn explicit_evaluation_accessors(
        &self,
    ) -> BTreeMap<OutputType, [UnsafeAccessor<[E]>; 2]> {
        self.explicit_evaluations
            .iter()
            .map(|(output_type, evals)| {
                (
                    *output_type,
                    [evals[0].get_accessor(), evals[1].get_accessor()],
                )
            })
            .collect()
    }

    /// View over the packed flat evaluations buffer (the prefix of the
    /// shared backing Arc that holds all reduced-output polys for the
    /// initial sumcheck layer in BTreeMap iteration order).
    pub(crate) fn device_flat_evaluations(&self) -> &DeviceSlice<E> {
        &self.flat_evaluations_backing[..self.flat_total_len]
    }

    pub(crate) fn into_explicit_evaluations(
        self,
    ) -> BTreeMap<OutputType, [HostAllocation<[E]>; 2]> {
        self.explicit_evaluations
    }

    pub(crate) fn final_explicit_evaluations(&self) -> BTreeMap<OutputType, [Vec<E>; 2]> {
        self.explicit_evaluations
            .iter()
            .map(|(output_type, evals)| {
                let copied =
                    std::array::from_fn(|idx| unsafe { evals[idx].get_accessor().get() }.to_vec());
                (*output_type, copied)
            })
            .collect()
    }

    pub(crate) fn flattened_transcript_evaluations(&self) -> Vec<E> {
        let capacity = self
            .explicit_evaluations
            .values()
            .map(|evals| {
                evals
                    .iter()
                    .map(|poly| unsafe { poly.get_accessor().get() }.len())
                    .sum::<usize>()
            })
            .sum();
        let mut flattened = Vec::with_capacity(capacity);
        for evals in self.explicit_evaluations.values() {
            for poly in evals.iter() {
                flattened.extend_from_slice(unsafe { poly.get_accessor().get() });
            }
        }

        flattened
    }
}

impl<B, E: Copy> GpuGKRForwardOutput<B, E> {
    /// Capture the consolidated backing Arc that holds every reduced-output
    /// poly at the initial sumcheck layer in BTreeMap iteration order, and
    /// optionally schedule a contiguous D2D into the proof slab plus per-poly
    /// D2H readbacks for tests.
    ///
    /// The reduced-output polys are written by the last forward dim-reduction
    /// round into a single per-`AddressClass` Arc
    /// (`storage.layers[output_layer].ext_class_backings[ThisLayerInnerLayerWrite]`)
    /// where `poly_idx == BTreeMap iteration index`. The first
    /// `num_polys * poly_len` elements of that Arc form the contiguous flat
    /// evaluations the post-forward transcript-commit and on-device
    /// initial-claim kernels read; they're exposed via
    /// `device_flat_evaluations()` without a per-poly pack.
    ///
    /// `with_host_readback`: when `true`, schedule per-poly D2Hs into pinned
    /// host slots so `final_explicit_evaluations()` /
    /// `flattened_transcript_evaluations()` produce the host-side mirror used
    /// by tests. Production passes `false` — `prove()`'s assembly callback
    /// reads `final_explicit_evaluations` from the slab mirror via
    /// `ProofLayout::parse_final_explicit_evaluations`. In the proof path, the
    /// final forward dim-reduction writes this backing directly into the slab's
    /// `output_evaluations` prefix.
    pub(crate) fn schedule_transcript_handoff(
        &self,
        with_host_readback: bool,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRTranscriptHandoff<E>> {
        let tracing_ranges = Vec::new();
        let reduced_outputs = self
            .dimension_reducing_inputs
            .get(&self.initial_layer_for_sumcheck)
            .expect("reduced outputs for initial sumcheck layer must exist");

        let output_layer = self.initial_layer_for_sumcheck + 1;
        let class = super::gkr_address_audit::AddressClass::ThisLayerInnerLayerWrite;
        let flat_evaluations_backing: Arc<DeviceAllocation<E>> = Arc::clone(
            self.storage
                .layers
                .get(output_layer)
                .and_then(|layer| layer.ext_class_backings.get(&class))
                .expect(
                    "consolidated backing Arc for reduced-output polys must exist after the \
                     forward dim-reduction pass",
                ),
        );

        let mut explicit_evaluations = BTreeMap::new();
        let mut flat_total_len = 0usize;
        for (output_type, reduced_io) in reduced_outputs.iter() {
            let [first_addr, second_addr]: [GKRAddress; 2] = reduced_io
                .output
                .clone()
                .try_into()
                .expect("transcript handoff expects exactly two reduced outputs per type");
            for addr in [first_addr, second_addr] {
                let poly = self
                    .storage
                    .try_get_ext_poly(addr)
                    .unwrap_or_else(|| panic!("missing reduced extension poly for {:?}", addr));
                flat_total_len += poly.len();
            }
            if with_host_readback {
                let first = schedule_ext_poly_readback(&self.storage, first_addr, context)?;
                let second = schedule_ext_poly_readback(&self.storage, second_addr, context)?;
                explicit_evaluations.insert(*output_type, [first, second]);
            }
        }
        debug_assert!(
            flat_total_len <= flat_evaluations_backing.len(),
            "consolidated backing must contain the reduced-output poly prefix"
        );

        Ok(GpuGKRTranscriptHandoff {
            _tracing_ranges: tracing_ranges,
            explicit_evaluations,
            flat_evaluations_backing,
            flat_total_len,
        })
    }
}

impl<B, E> GpuGKRForwardOutput<B, E> {
    pub(crate) fn into_dimension_reducing_backward_state(
        self,
    ) -> GpuGKRDimensionReducingBackwardState<B, E> {
        GpuGKRDimensionReducingBackwardState::new(
            self.tracing_ranges,
            self.storage,
            self.initial_layer_for_sumcheck,
            self.dimension_reducing_inputs,
        )
    }
}

pub(super) use super::forward_kernels::*;

pub(crate) fn schedule_forward_pass<E>(
    setup_trace_holder: Option<&crate::prover::trace_holder::TraceHolder<BF>>,
    synthetic_setup_trace_holder: Option<&crate::prover::trace_holder::TraceHolder<BF>>,
    stage1: &mut GpuGKRStage1Output,
    forward_setup: &mut GpuGKRForwardSetup<E>,
    compiled_circuit: &GKRCircuitArtifact<BF>,
    external_challenges: &GKRExternalChallenges<BF, E>,
    final_trace_size_log_2: usize,
    output_evaluations_slab: Option<ForwardOutputSlabTarget<E>>,
    context: &ProverContext,
) -> CudaResult<GpuGKRForwardOutput<BF, E>>
where
    E: FieldExtension<BF>
        + Field
        + SetByRef
        + SetByVal
        + GpuGKRForwardCacheKernelSet
        + GpuGKRVirtualBaseAccumKernelSet
        + GpuGKRDimensionReducingForwardTowerKernelSet
        + super::forward_kernels::GpuGKRFlatForwardKernelSet,
    Add: BinaryOp<E, E, E>,
    Add: BinaryOp<BF, E, E>,
    Add: BinaryOp<E, BF, E>,
    Add: BinaryOp<BF, BF, BF>,
    Mul: BinaryOp<E, E, E>,
    Mul: BinaryOp<BF, E, E>,
    Mul: BinaryOp<E, BF, E>,
    Mul: BinaryOp<BF, BF, BF>,
    Sub: BinaryOp<E, E, E>,
    Sub: BinaryOp<E, BF, E>,
    Sub: BinaryOp<BF, BF, BF>,
{
    let compiled_circuit = normalize_compiled_circuit_for_gpu(compiled_circuit.clone());
    let trace_len = compiled_circuit.trace_len;
    let stream = context.get_exec_stream();
    let mut tracing_ranges = Vec::new();
    let forward_range = Range::new("gkr.forward.schedule")?;
    forward_range.start(stream)?;
    let usage = analyze_forward_lookup_usage(&compiled_circuit);
    let decoder_predicate_address = compiled_circuit
        .memory_layout
        .machine_state
        .as_ref()
        .map(|machine_state| GKRAddress::BaseLayerMemory(machine_state.execute));
    let setup_trace_holder = setup_trace_holder
        .or(synthetic_setup_trace_holder)
        .expect("forward pass requires either uploaded or synthetic setup trace holder");
    let mut storage = bootstrap_storage_from_trace_holders::<E>(
        Some(setup_trace_holder),
        setup_trace_holder.columns_count,
        setup_trace_holder.log_domain_size,
        setup_trace_holder.log_lde_factor,
        setup_trace_holder.log_rows_per_leaf,
        setup_trace_holder.log_tree_cap_size,
        &stage1.memory_trace_holder,
        &stage1.witness_trace_holder,
        context,
    )?;
    let storage_layout = std::sync::Arc::new(
        crate::prover::gkr::storage_layout::GpuGKRStorageLayout::from_artifact_with_tower(
            &compiled_circuit,
            final_trace_size_log_2,
        ),
    );
    storage.set_layout(storage_layout);

    if usage.last_generic_mapping_layer.is_none() {
        stage1.lookup_mappings.release_generic_family();
    }
    if usage.last_range_mapping_layer.is_none() {
        stage1.lookup_mappings.release_range_check_16();
    }
    if usage.last_timestamp_mapping_layer.is_none() {
        stage1.lookup_mappings.release_timestamp();
    }
    if usage.last_generic_lookup_layer.is_none() {
        forward_setup.release_generic_lookup();
    }

    for (layer_idx, layer) in compiled_circuit.layers.iter().enumerate() {
        let layer_range = Range::new(format!("gkr.forward.layer.{layer_idx}"))?;
        layer_range.start(stream)?;
        schedule_layer(
            layer_idx,
            compiled_circuit.layers.len(),
            layer,
            &compiled_circuit,
            &mut tracing_ranges,
            &mut storage,
            stage1,
            forward_setup,
            external_challenges,
            decoder_predicate_address,
            trace_len,
            context,
        )?;
        layer_range.end(stream)?;
        tracing_ranges.push(layer_range);
        release_forward_lookup_resources_after_layer(layer_idx, &usage, stage1, forward_setup);
    }

    for (output_type, addresses) in compiled_circuit.global_output_map.iter() {
        for address in addresses.iter().copied() {
            assert!(
                storage.try_get_ext_poly(address).is_some(),
                "missing GPU forward output for {:?} at {:?}",
                output_type,
                address,
            );
        }
    }

    let dimension_reduction_range = Range::new("gkr.forward.dimension_reduction")?;
    dimension_reduction_range.start(stream)?;
    let (initial_layer_for_sumcheck, dimension_reducing_inputs) =
        schedule_dimension_reduction_forward(
            &mut storage,
            compiled_circuit.layers.len(),
            compiled_circuit.global_output_map.clone(),
            trace_len.trailing_zeros() as usize,
            final_trace_size_log_2,
            output_evaluations_slab,
            &mut tracing_ranges,
            context,
        )?;
    dimension_reduction_range.end(stream)?;
    tracing_ranges.push(dimension_reduction_range);
    forward_range.end(stream)?;
    tracing_ranges.push(forward_range);

    Ok(GpuGKRForwardOutput {
        tracing_ranges,
        storage,
        initial_layer_for_sumcheck,
        dimension_reducing_inputs,
    })
}

pub(super) fn schedule_ext_poly_readback<B, E: Copy>(
    storage: &GpuGKRStorage<B, E>,
    address: GKRAddress,
    context: &ProverContext,
) -> CudaResult<HostAllocation<[E]>> {
    let poly = storage
        .try_get_ext_poly(address)
        .unwrap_or_else(|| panic!("missing reduced extension poly for {:?}", address));
    let mut host = unsafe { context.alloc_host_uninit_slice(poly.len()) };
    memory_copy_async(&mut host, poly.as_device_slice(), context.get_exec_stream())?;
    Ok(host)
}

fn schedule_layer<E>(
    layer_idx: usize,
    total_layers: usize,
    layer: &GKRLayerDescription,
    compiled_circuit: &GKRCircuitArtifact<BF>,
    tracing_ranges: &mut Vec<Range>,
    storage: &mut GpuGKRStorage<BF, E>,
    stage1: &GpuGKRStage1Output,
    forward_setup: &GpuGKRForwardSetup<E>,
    external_challenges: &GKRExternalChallenges<BF, E>,
    decoder_predicate_address: Option<GKRAddress>,
    trace_len: usize,
    context: &ProverContext,
) -> CudaResult<()>
where
    E: FieldExtension<BF>
        + Field
        + SetByRef
        + SetByVal
        + GpuGKRForwardCacheKernelSet
        + GpuGKRVirtualBaseAccumKernelSet
        + super::forward_kernels::GpuGKRFlatForwardKernelSet,
    Add: BinaryOp<E, E, E>,
    Add: BinaryOp<BF, E, E>,
    Add: BinaryOp<E, BF, E>,
    Mul: BinaryOp<E, E, E>,
    Mul: BinaryOp<BF, E, E>,
    Mul: BinaryOp<E, BF, E>,
    Sub: BinaryOp<E, E, E>,
    Sub: BinaryOp<E, BF, E>,
    Sub: BinaryOp<BF, BF, BF>,
{
    let stream = context.get_exec_stream();
    hydrate_scratch_space_layer(layer_idx, compiled_circuit, stage1, storage);
    // Phase 3.2: decompose InitialGrandProductWithoutCaches and
    // MaterializeGrandProductTermExpression gates into MemoryTuple cache
    // relations plus lightweight follow-ups (InitialGrandProductFromCaches /
    // Copy). The synthesized cache relations merge into this layer's cache
    // batch; the lowered gate list replaces layer.gates / _with_external_connections
    // for the rest of the scheduler.
    let grand_product_plan =
        super::lowering::LayerNoCacheLoweringPlan::grand_product_only(layer_idx, layer);
    let merged_cached_relations = if grand_product_plan.internal_helper_relations.is_empty() {
        None
    } else {
        let mut merged = layer.cached_relations.clone();
        for (address, relation) in &grand_product_plan.internal_helper_relations {
            let previous = merged.insert(*address, relation.clone());
            assert!(
                previous.is_none(),
                "grand-product helper address {:?} collides with existing cache relation",
                address
            );
        }
        Some(merged)
    };
    let cached_relations_ref = merged_cached_relations
        .as_ref()
        .unwrap_or(&layer.cached_relations);
    if cached_relations_ref.is_empty() {
        schedule_cache_relations(
            layer_idx,
            cached_relations_ref,
            storage,
            stage1,
            forward_setup,
            external_challenges,
            decoder_predicate_address,
            trace_len,
            context,
        )?;
    } else {
        let cache_range = Range::new(format!("gkr.forward.layer.{layer_idx}.cache"))?;
        cache_range.start(stream)?;
        schedule_cache_relations(
            layer_idx,
            cached_relations_ref,
            storage,
            stage1,
            forward_setup,
            external_challenges,
            decoder_predicate_address,
            trace_len,
            context,
        )?;
        cache_range.end(stream)?;
        tracing_ranges.push(cache_range);
    }

    let gates_range = Range::new(format!("gkr.forward.layer.{layer_idx}.gates"))?;
    gates_range.start(stream)?;
    assert_forward_layer_invariants(layer_idx, total_layers, layer);
    assert_forward_no_cache_layer_invariants(layer, decoder_predicate_address);
    let expected_output_layer = layer_idx + 1;
    schedule_materialized_vector_lookup_inputs(
        expected_output_layer,
        layer,
        storage,
        stage1,
        forward_setup,
        decoder_predicate_address,
        trace_len,
        context,
    )?;
    schedule_materialized_single_lookup_inputs(
        expected_output_layer,
        layer,
        storage,
        trace_len,
        context,
    )?;
    let plan = build_flat_forward_plan(
        layer_idx,
        &grand_product_plan.lowered_gates,
        &grand_product_plan.lowered_gates_with_external_connections,
        &compiled_circuit.scratch_space_mapping,
        storage,
        external_challenges,
        forward_setup.lookup_additive_part_device().as_ptr(),
        trace_len,
        context,
    )?;
    if super::forward_kernels::flat_desc_has_work(&plan.desc) {
        super::forward_kernels::launch_flat_forward_layer(&plan.desc, trace_len, context)?;
    }
    commit_flat_forward_plan(expected_output_layer, storage, plan);
    gates_range.end(stream)?;
    tracing_ranges.push(gates_range);

    Ok(())
}

fn assert_forward_no_cache_layer_invariants(
    layer: &GKRLayerDescription,
    decoder_predicate_address: Option<GKRAddress>,
) {
    for gate in layer
        .gates
        .iter()
        .chain(layer.gates_with_external_connections.iter())
    {
        if let NoFieldGKRRelation::LookupWithDensAndSetupExpressions { input, .. } =
            &gate.enforced_relation
        {
            assert_eq!(
                Some(input.0),
                decoder_predicate_address,
                "GPU no-cache decoder lowering expects the decoder predicate input"
            );
        }
    }
}

fn schedule_materialized_vector_lookup_inputs<E>(
    expected_output_layer: usize,
    layer: &GKRLayerDescription,
    storage: &mut GpuGKRStorage<BF, E>,
    stage1: &GpuGKRStage1Output,
    forward_setup: &GpuGKRForwardSetup<E>,
    decoder_predicate_address: Option<GKRAddress>,
    trace_len: usize,
    context: &ProverContext,
) -> CudaResult<()>
where
    E: FieldExtension<BF> + Field + SetByRef + SetByVal + GpuGKRForwardCacheKernelSet,
{
    let generic_lookup = if forward_setup.generic_lookup_len() > 0 {
        forward_setup.generic_lookup().as_ptr()
    } else {
        null()
    };
    let mut pending = layer
        .gates
        .iter()
        .chain(layer.gates_with_external_connections.iter())
        .filter_map(|gate| match &gate.enforced_relation {
            NoFieldGKRRelation::MaterializedVectorLookupInput { input, output } => {
                assert_eq!(gate.output_layer, expected_output_layer);
                Some((input, output))
            }
            _ => None,
        })
        .peekable();

    while pending.peek().is_some() {
        let mut batch = GpuGKRForwardCacheBatch::default();
        let mut outputs = Vec::with_capacity(MAX_CACHE_RELATIONS_PER_LAYER);
        for descriptor in batch.descriptors.iter_mut() {
            let Some((input, output)) = pending.next() else {
                break;
            };
            let is_decoder_lookup = input.lookup_set_index == DECODER_LOOKUP_FORMAL_SET_INDEX;
            let mapping = if input.lookup_set_index != DECODER_LOOKUP_FORMAL_SET_INDEX {
                stage1
                    .lookup_mappings
                    .generic_mapping(input.lookup_set_index)
            } else {
                stage1
                    .lookup_mappings
                    .decoder_mapping()
                    .expect("decoder mapping must be present for decoder lookup relation")
            };
            // Allocate via the consolidated layout-driven path so the
            // resulting view shares its backing with sibling
            // `MaterializedVectorLookupInput` outputs at this layer. The
            // mutable borrow must complete before we read back from storage
            // for the decoder-mask lookup below.
            let dst_view = storage.allocate_ext_view(expected_output_layer, *output, context)?;
            let ext_output = dst_view.as_mut_ptr();
            let decoder_mask = if is_decoder_lookup {
                storage
                    .get_base_layer(
                        decoder_predicate_address
                            .expect("decoder lookup requires a decoder predicate column"),
                    )
                    .as_ptr()
            } else {
                null()
            };
            outputs.push((*output, dst_view));
            *descriptor = GpuGKRForwardCacheDescriptor {
                kind: GpuGKRForwardCacheKind::VectorizedLookup,
                mapping: mapping.as_ptr(),
                generic_lookup,
                decoder_mask,
                decoder_fill_value: if is_decoder_lookup {
                    forward_setup.decoder_lookup_fill_value_device().as_ptr()
                } else {
                    null()
                },
                ext_output,
                ..GpuGKRForwardCacheDescriptor::default()
            };
            batch.count += 1;
        }
        for (address, poly) in outputs {
            storage.insert_extension_at_layer(expected_output_layer, address, poly);
        }
        launch_forward_cache(batch, trace_len, context)?;
    }

    Ok(())
}

fn schedule_materialized_single_lookup_inputs<E>(
    expected_output_layer: usize,
    layer: &GKRLayerDescription,
    storage: &mut GpuGKRStorage<BF, E>,
    trace_len: usize,
    context: &ProverContext,
) -> CudaResult<()>
where
    Add: BinaryOp<BF, BF, BF>,
    Mul: BinaryOp<BF, BF, BF>,
{
    for gate in layer
        .gates
        .iter()
        .chain(layer.gates_with_external_connections.iter())
    {
        let (input, output) = match &gate.enforced_relation {
            NoFieldGKRRelation::MaterializeSingleLookupInput { input, output, .. } => {
                (&input.input, output)
            }
            NoFieldGKRRelation::LinearBaseFieldRelation { input, output } => (input, output),
            _ => continue,
        };
        assert_eq!(gate.output_layer, expected_output_layer);
        let dst_view = storage.allocate_base_view(expected_output_layer, *output, context)?;
        assert_eq!(dst_view.len(), trace_len);
        // SAFETY: dst_view was just allocated for this gate's output slot;
        // no other clone of this view is scheduled to write before this loop's
        // ops (set_by_val + scale_and_add) complete.
        let mut dst_chunk = unsafe { dst_view.as_mut_chunk_unchecked() };
        set_by_val(
            BF::from_u32_unchecked(input.constant),
            &mut dst_chunk,
            context.get_exec_stream(),
        )?;
        for (coeff, address) in input.linear_terms.iter() {
            scale_and_add_base_column_in_place(
                &mut dst_chunk,
                storage.get_base_layer(*address),
                BF::from_u32_unchecked(*coeff),
                context,
            )?;
        }
        drop(dst_chunk);
        storage.insert_base_field_at_layer(expected_output_layer, *output, dst_view);
    }

    Ok(())
}

fn hydrate_scratch_space_layer<E>(
    layer_idx: usize,
    compiled_circuit: &GKRCircuitArtifact<BF>,
    stage1: &GpuGKRStage1Output,
    storage: &mut GpuGKRStorage<BF, E>,
) {
    let Some(scratch_space_trace) = stage1.scratch_space_trace.as_ref() else {
        return;
    };
    let trace_len = compiled_circuit.trace_len;
    for (scratch_idx, address) in compiled_circuit.scratch_space_mapping_rev.iter() {
        let GKRAddress::InnerLayer { layer, .. } = *address else {
            continue;
        };
        if layer != layer_idx || storage.try_get_base_poly(*address).is_some() {
            continue;
        }
        let offset = scratch_idx * trace_len;
        storage.insert_base_field_at_layer(
            layer_idx,
            *address,
            GpuBaseFieldPoly::from_arc(Arc::clone(scratch_space_trace), offset, trace_len),
        );
    }
}

fn assert_forward_layer_invariants(
    layer_idx: usize,
    total_layers: usize,
    layer: &GKRLayerDescription,
) {
    assert!(
        layer.gates.is_empty() ^ layer.gates_with_external_connections.is_empty(),
        "layer {layer_idx} must use exactly one gate collection"
    );
    if layer_idx + 1 != total_layers {
        assert!(
            layer.gates_with_external_connections.is_empty(),
            "non-final layer {layer_idx} must not use external gate connections"
        );
    } else {
        assert!(
            layer.gates.is_empty(),
            "final layer {layer_idx} must use external gate connections only"
        );
    }
}

fn vector_lookup_mapping_ptr(
    stage1: &GpuGKRStage1Output,
    relation: &cs::definitions::gkr::NoFieldVectorLookupRelation,
) -> *const u32 {
    if relation.lookup_set_index == DECODER_LOOKUP_FORMAL_SET_INDEX {
        stage1
            .lookup_mappings
            .decoder_mapping()
            .expect("decoder mapping must be present for decoder lookup relation")
            .as_ptr()
    } else {
        stage1
            .lookup_mappings
            .generic_mapping(relation.lookup_set_index)
            .as_ptr()
    }
}

fn single_column_lookup_mapping_ptr(
    stage1: &GpuGKRStage1Output,
    relation: &cs::definitions::gkr::NoFieldSingleColumnLookupRelation,
    range_check_width: u32,
) -> *const u32 {
    if range_check_width == 16 {
        stage1
            .lookup_mappings
            .range_check_mapping(relation.lookup_set_index)
            .as_ptr()
    } else {
        stage1
            .lookup_mappings
            .timestamp_mapping(relation.lookup_set_index)
            .as_ptr()
    }
}

struct FlatBuilder<'a, E> {
    desc: &'a mut GpuFlatForwardStaticDesc<E>,
    src_map: std::collections::HashMap<usize, u16>,
}

impl<E> FlatBuilder<'_, E> {
    fn add_src(&mut self, ptr: *const u8) -> u16 {
        let key = ptr as usize;
        if let Some(&idx) = self.src_map.get(&key) {
            return idx;
        }
        let idx = self.desc.num_sources;
        assert!(
            (idx as usize) < FLAT_FWD_MAX_SOURCES,
            "flat forward: source table overflow ({idx} >= {FLAT_FWD_MAX_SOURCES})"
        );
        self.desc.sources[idx as usize] = ptr;
        self.desc.num_sources = idx + 1;
        let idx = idx as u16;
        self.src_map.insert(key, idx);
        idx
    }
}

/// Low-3-bits-tagged null pointer encoding for virtual base sources; mirrors
/// `flat_fwd_load_bf` in native/prover/gkr/flat_forward.cuh.
fn encode_virtual_source(kind: GpuBaseFieldSourceKind) -> *const u8 {
    (kind as usize) as *const u8
}

fn build_flat_forward_plan<E>(
    layer_idx: usize,
    lowered_gates: &[cs::gkr_compiler::GateArtifacts],
    lowered_gates_with_external_connections: &[cs::gkr_compiler::GateArtifacts],
    scratch_space_mapping: &BTreeMap<GKRAddress, usize>,
    storage: &mut GpuGKRStorage<BF, E>,
    external_challenges: &GKRExternalChallenges<BF, E>,
    lookup_additive_challenge: *const E,
    trace_len: usize,
    context: &ProverContext,
) -> CudaResult<FlatForwardPlan<E>>
where
    E: Field + FieldExtension<BF> + GpuGKRVirtualBaseAccumKernelSet + SetByVal,
    Add: BinaryOp<E, E, E>,
    Mul: BinaryOp<BF, E, E>,
    Mul: BinaryOp<E, E, E>,
{
    let expected_output_layer = layer_idx + 1;

    let mut desc: Box<GpuFlatForwardStaticDesc<E>> = Box::new(GpuFlatForwardStaticDesc::default());
    desc.gamma = lookup_additive_challenge;
    let mut builder = FlatBuilder {
        desc: &mut desc,
        src_map: std::collections::HashMap::new(),
    };

    let mut computed_extension_outputs = Vec::new();
    let mut aliased_base_outputs = Vec::new();
    let mut aliased_extension_outputs = Vec::new();

    for gate in lowered_gates
        .iter()
        .chain(lowered_gates_with_external_connections.iter())
    {
        assert_eq!(gate.output_layer, expected_output_layer);
        match &gate.enforced_relation {
            NoFieldGKRRelation::CopyInBaseField { input, output }
            | NoFieldGKRRelation::CopyInExtensionField { input, output } => {
                if let Some(source) = storage.try_get_base_poly(*input) {
                    aliased_base_outputs.push((*output, source.clone_shared()));
                } else {
                    aliased_extension_outputs
                        .push((*output, storage.get_ext_poly(*input).clone_shared()));
                }
            }
            NoFieldGKRRelation::InitialGrandProductFromCaches { input, output }
            | NoFieldGKRRelation::TrivialProduct { input, output } => {
                let lhs = storage.get_ext_poly(input[0]).as_ptr();
                let rhs = storage.get_ext_poly(input[1]).as_ptr();
                let dst_view =
                    storage.allocate_ext_view(expected_output_layer, *output, context)?;
                let dst_ptr = dst_view.as_mut_ptr();
                computed_extension_outputs.push((*output, dst_view));
                let src_a = builder.add_src(lhs as *const u8);
                let src_b = builder.add_src(rhs as *const u8);
                let i = builder.desc.num_products as usize;
                assert!(
                    i < FLAT_FWD_MAX_PER_CATEGORY,
                    "flat forward: products overflow"
                );
                builder.desc.products[i] = GpuFlatFwdProductEntry {
                    src_a,
                    src_b,
                    dst: dst_ptr,
                };
                builder.desc.num_products = (i + 1) as u32;
            }
            NoFieldGKRRelation::MaskIntoIdentityProduct {
                input,
                mask,
                output,
            } => {
                let input_ptr = storage.get_ext_poly(*input).as_ptr();
                let mask_ptr = storage.get_base_layer(*mask).as_ptr();
                let dst_view =
                    storage.allocate_ext_view(expected_output_layer, *output, context)?;
                let dst_ptr = dst_view.as_mut_ptr();
                computed_extension_outputs.push((*output, dst_view));
                let src_mask = builder.add_src(mask_ptr as *const u8);
                let src_input = builder.add_src(input_ptr as *const u8);
                let i = builder.desc.num_masks as usize;
                assert!(
                    i < FLAT_FWD_MAX_PER_CATEGORY,
                    "flat forward: masks overflow"
                );
                builder.desc.masks[i] = GpuFlatFwdMaskEntry {
                    src_mask,
                    src_input,
                    dst: dst_ptr,
                };
                builder.desc.num_masks = (i + 1) as u32;
            }
            NoFieldGKRRelation::AggregateLookupRationalPair { input, output } => {
                let [a, b] = input[0].map(|addr| storage.get_ext_poly(addr).as_ptr());
                let [c, d] = input[1].map(|addr| storage.get_ext_poly(addr).as_ptr());
                let num_view =
                    storage.allocate_ext_view(expected_output_layer, output[0], context)?;
                let den_view =
                    storage.allocate_ext_view(expected_output_layer, output[1], context)?;
                let num_ptr = num_view.as_mut_ptr();
                let den_ptr = den_view.as_mut_ptr();
                computed_extension_outputs.push((output[0], num_view));
                computed_extension_outputs.push((output[1], den_view));
                let src_a = builder.add_src(a as *const u8);
                let src_b = builder.add_src(b as *const u8);
                let src_c = builder.add_src(c as *const u8);
                let src_d = builder.add_src(d as *const u8);
                let i = builder.desc.num_lookup4s as usize;
                assert!(
                    i < FLAT_FWD_MAX_PER_CATEGORY,
                    "flat forward: lookup4s overflow"
                );
                builder.desc.lookup4s[i] = GpuFlatFwdLookup4Entry {
                    src_a,
                    src_b,
                    src_c,
                    src_d,
                    num: num_ptr,
                    den: den_ptr,
                };
                builder.desc.num_lookup4s = (i + 1) as u32;
            }
            NoFieldGKRRelation::LookupWithCachedDensAndSetup {
                input,
                setup,
                output,
            } => {
                let a = storage.get_base_layer(input[0]).as_ptr();
                let b = storage.get_ext_poly(input[1]).as_ptr();
                let c = storage.get_base_layer(setup[0]).as_ptr();
                let d = storage.get_ext_poly(setup[1]).as_ptr();
                let num_view =
                    storage.allocate_ext_view(expected_output_layer, output[0], context)?;
                let den_view =
                    storage.allocate_ext_view(expected_output_layer, output[1], context)?;
                let num_ptr = num_view.as_mut_ptr();
                let den_ptr = den_view.as_mut_ptr();
                computed_extension_outputs.push((output[0], num_view));
                computed_extension_outputs.push((output[1], den_view));
                let src_a = builder.add_src(a as *const u8);
                let src_b = builder.add_src(b as *const u8);
                let src_c = builder.add_src(c as *const u8);
                let src_d = builder.add_src(d as *const u8);
                let i = builder.desc.num_cached_denses as usize;
                assert!(
                    i < FLAT_FWD_MAX_PER_CATEGORY,
                    "flat forward: cached_denses overflow"
                );
                builder.desc.cached_denses[i] = GpuFlatFwdCachedDensEntry {
                    src_a,
                    src_b,
                    src_c,
                    src_d,
                    num: num_ptr,
                    den: den_ptr,
                };
                builder.desc.num_cached_denses = (i + 1) as u32;
            }
            NoFieldGKRRelation::LookupPairFromMaterializedBaseInputs { input, output } => {
                let lhs = storage.get_base_layer(input[0]).as_ptr();
                let rhs = storage.get_base_layer(input[1]).as_ptr();
                let num_view =
                    storage.allocate_ext_view(expected_output_layer, output[0], context)?;
                let den_view =
                    storage.allocate_ext_view(expected_output_layer, output[1], context)?;
                let num_ptr = num_view.as_mut_ptr();
                let den_ptr = den_view.as_mut_ptr();
                computed_extension_outputs.push((output[0], num_view));
                computed_extension_outputs.push((output[1], den_view));
                let src_b = builder.add_src(lhs as *const u8);
                let src_d = builder.add_src(rhs as *const u8);
                let i = builder.desc.num_bf_pairs as usize;
                assert!(
                    i < FLAT_FWD_MAX_PER_CATEGORY,
                    "flat forward: bf_pairs overflow"
                );
                builder.desc.bf_pairs[i] = GpuFlatFwdBfPairEntry {
                    src_b,
                    src_d,
                    num: num_ptr,
                    den: den_ptr,
                };
                builder.desc.num_bf_pairs = (i + 1) as u32;
            }
            NoFieldGKRRelation::LookupPairFromMaterializedVectorInputs { input, output }
            | NoFieldGKRRelation::LookupPairFromCachedVectorInputs { input, output } => {
                let lhs = storage.get_ext_poly(input[0]).as_ptr();
                let rhs = storage.get_ext_poly(input[1]).as_ptr();
                let num_view =
                    storage.allocate_ext_view(expected_output_layer, output[0], context)?;
                let den_view =
                    storage.allocate_ext_view(expected_output_layer, output[1], context)?;
                let num_ptr = num_view.as_mut_ptr();
                let den_ptr = den_view.as_mut_ptr();
                computed_extension_outputs.push((output[0], num_view));
                computed_extension_outputs.push((output[1], den_view));
                let src_b = builder.add_src(lhs as *const u8);
                let src_d = builder.add_src(rhs as *const u8);
                let i = builder.desc.num_e4_pairs as usize;
                assert!(
                    i < FLAT_FWD_MAX_PER_CATEGORY,
                    "flat forward: e4_pairs overflow"
                );
                builder.desc.e4_pairs[i] = GpuFlatFwdE4PairEntry {
                    src_b,
                    src_d,
                    num: num_ptr,
                    den: den_ptr,
                };
                builder.desc.num_e4_pairs = (i + 1) as u32;
            }
            NoFieldGKRRelation::LookupFromMaterializedBaseInputWithSetup {
                input,
                setup,
                output,
            } => {
                let b = storage.get_base_layer(*input).as_ptr();
                let c = storage.get_base_layer(setup[0]).as_ptr();
                let d_ptr: *const u8 =
                    if let Some(kind) = GpuBaseFieldSourceKind::from_address(setup[1]) {
                        encode_virtual_source(kind)
                    } else {
                        storage.get_base_layer(setup[1]).as_ptr() as *const u8
                    };
                let num_view =
                    storage.allocate_ext_view(expected_output_layer, output[0], context)?;
                let den_view =
                    storage.allocate_ext_view(expected_output_layer, output[1], context)?;
                let num_ptr = num_view.as_mut_ptr();
                let den_ptr = den_view.as_mut_ptr();
                computed_extension_outputs.push((output[0], num_view));
                computed_extension_outputs.push((output[1], den_view));
                let src_b = builder.add_src(b as *const u8);
                let src_c = builder.add_src(c as *const u8);
                let src_d = builder.add_src(d_ptr);
                let i = builder.desc.num_bf_minus_mults as usize;
                assert!(
                    i < FLAT_FWD_MAX_PER_CATEGORY,
                    "flat forward: bf_minus_mults overflow"
                );
                builder.desc.bf_minus_mults[i] = GpuFlatFwdBfMinusMultEntry {
                    src_b,
                    src_c,
                    src_d,
                    _pad: 0,
                    num: num_ptr,
                    den: den_ptr,
                };
                builder.desc.num_bf_minus_mults = (i + 1) as u32;
            }
            NoFieldGKRRelation::LookupFromMaterializedVectorInputWithSetup {
                input,
                setup,
                output,
            } => {
                let b = storage.get_ext_poly(*input).as_ptr();
                let c = storage.get_base_layer(setup[0]).as_ptr();
                let d = storage.get_ext_poly(setup[1]).as_ptr();
                let num_view =
                    storage.allocate_ext_view(expected_output_layer, output[0], context)?;
                let den_view =
                    storage.allocate_ext_view(expected_output_layer, output[1], context)?;
                let num_ptr = num_view.as_mut_ptr();
                let den_ptr = den_view.as_mut_ptr();
                computed_extension_outputs.push((output[0], num_view));
                computed_extension_outputs.push((output[1], den_view));
                let src_b = builder.add_src(b as *const u8);
                let src_c = builder.add_src(c as *const u8);
                let src_d = builder.add_src(d as *const u8);
                let i = builder.desc.num_e4_minus_mults as usize;
                assert!(
                    i < FLAT_FWD_MAX_PER_CATEGORY,
                    "flat forward: e4_minus_mults overflow"
                );
                builder.desc.e4_minus_mults[i] = GpuFlatFwdE4MinusMultEntry {
                    src_b,
                    src_c,
                    src_d,
                    _pad: 0,
                    num: num_ptr,
                    den: den_ptr,
                };
                builder.desc.num_e4_minus_mults = (i + 1) as u32;
            }
            NoFieldGKRRelation::LookupUnbalancedPairWithMaterializedBaseInputs {
                input,
                remainder,
                output,
            } => {
                let [a, b] = input.map(|addr| storage.get_ext_poly(addr).as_ptr());
                let remainder = storage.get_base_layer(*remainder).as_ptr();
                let num_view =
                    storage.allocate_ext_view(expected_output_layer, output[0], context)?;
                let den_view =
                    storage.allocate_ext_view(expected_output_layer, output[1], context)?;
                let num_ptr = num_view.as_mut_ptr();
                let den_ptr = den_view.as_mut_ptr();
                computed_extension_outputs.push((output[0], num_view));
                computed_extension_outputs.push((output[1], den_view));
                let src_a = builder.add_src(a as *const u8);
                let src_b = builder.add_src(b as *const u8);
                let src_d = builder.add_src(remainder as *const u8);
                let i = builder.desc.num_bf_unbalanceds as usize;
                assert!(
                    i < FLAT_FWD_MAX_PER_CATEGORY,
                    "flat forward: bf_unbalanceds overflow"
                );
                builder.desc.bf_unbalanceds[i] = GpuFlatFwdBfUnbalancedEntry {
                    src_a,
                    src_b,
                    src_d,
                    _pad: 0,
                    num: num_ptr,
                    den: den_ptr,
                };
                builder.desc.num_bf_unbalanceds = (i + 1) as u32;
            }
            NoFieldGKRRelation::LookupUnbalancedPairWithMaterializedVectorInputs {
                input,
                remainder,
                output,
            } => {
                let [a, b] = input.map(|addr| storage.get_ext_poly(addr).as_ptr());
                let remainder = storage.get_ext_poly(*remainder).as_ptr();
                let num_view =
                    storage.allocate_ext_view(expected_output_layer, output[0], context)?;
                let den_view =
                    storage.allocate_ext_view(expected_output_layer, output[1], context)?;
                let num_ptr = num_view.as_mut_ptr();
                let den_ptr = den_view.as_mut_ptr();
                computed_extension_outputs.push((output[0], num_view));
                computed_extension_outputs.push((output[1], den_view));
                let src_a = builder.add_src(a as *const u8);
                let src_b = builder.add_src(b as *const u8);
                let src_d = builder.add_src(remainder as *const u8);
                let i = builder.desc.num_e4_unbalanceds as usize;
                assert!(
                    i < FLAT_FWD_MAX_PER_CATEGORY,
                    "flat forward: e4_unbalanceds overflow"
                );
                builder.desc.e4_unbalanceds[i] = GpuFlatFwdE4UnbalancedEntry {
                    src_a,
                    src_b,
                    src_d,
                    _pad: 0,
                    num: num_ptr,
                    den: den_ptr,
                };
                builder.desc.num_e4_unbalanceds = (i + 1) as u32;
            }
            NoFieldGKRRelation::EnforceConstraintsMaxQuadratic { .. } => {}
            NoFieldGKRRelation::MaterializedVectorLookupInput { output, .. } => {
                assert!(
                    storage.try_get_ext_poly(*output).is_some(),
                    "materialized vector lookup output {:?} must be precomputed before gate lowering",
                    output
                );
            }
            NoFieldGKRRelation::MaterializeSingleLookupInput { output, .. } => {
                assert!(
                    storage.try_get_base_poly(*output).is_some(),
                    "materialized single lookup output {:?} must be precomputed before gate lowering",
                    output
                );
            }
            NoFieldGKRRelation::LinearBaseFieldRelation { output, .. } => {
                assert!(
                    storage.try_get_base_poly(*output).is_some(),
                    "materialized linear base output {:?} must be precomputed before gate lowering",
                    output
                );
            }
            NoFieldGKRRelation::MaxQuadratic { output, .. }
                if scratch_space_mapping.contains_key(output)
                    || storage.try_get_base_poly(*output).is_some() => {}
            NoFieldGKRRelation::EnforceSingleMaxQuadraticConstraint { .. } => {}
            NoFieldGKRRelation::LookupPairFromBaseInputs { .. }
            | NoFieldGKRRelation::LookupWithDensAndSetupExpressions { .. }
            | NoFieldGKRRelation::LookupPairFromVectorInputs { .. }
            | NoFieldGKRRelation::LookupFromVectorInputWithSetup { .. }
            | NoFieldGKRRelation::LookupUnbalancedPairWithVectorInputs { .. } => {
                // Mapping-based lookup relations only appear in uncached GKR
                // layouts (`*_no_caches_gkr.json`); gpu_prover exclusively
                // consumes cached layouts, where these are pre-materialized
                // into the direct-source categories above.
                unreachable!(
                    "mapping-based GKR relation unexpected in cached layout: {:?}",
                    gate.enforced_relation
                )
            }
            NoFieldGKRRelation::InitsOrTeardownsInitialPair {
                timestamp_and_value,
                setup,
                output,
                set_idxes,
            } => {
                let dst_view =
                    storage.allocate_ext_view(expected_output_layer, *output, context)?;
                materialize_inits_and_teardowns_initial_pair_into(
                    storage,
                    &dst_view,
                    timestamp_and_value,
                    *setup,
                    set_idxes.map(|idx| idx as u32),
                    high_bits_offset_for_inits_and_teardowns::<2>(trace_len),
                    external_challenges,
                    trace_len,
                    context,
                )?;
                computed_extension_outputs.push((*output, dst_view));
            }
            NoFieldGKRRelation::InitialGrandProductWithoutCaches { .. }
            | NoFieldGKRRelation::MaterializeGrandProductTermExpression { .. } => {
                unreachable!(
                    "grand-product gates must be decomposed by \
                     LayerNoCacheLoweringPlan::grand_product_only before lowering"
                )
            }
            NoFieldGKRRelation::MaxQuadratic { .. }
            | NoFieldGKRRelation::UnbalancedGrandProductWithCache { .. } => {
                unimplemented!(
                    "unsupported GPU forward relation: {:?}",
                    gate.enforced_relation
                )
            }
        }
    }

    Ok(FlatForwardPlan {
        desc,
        computed_extension_outputs,
        aliased_base_outputs,
        aliased_extension_outputs,
    })
}

fn commit_flat_forward_plan<E>(
    expected_output_layer: usize,
    storage: &mut GpuGKRStorage<BF, E>,
    plan: FlatForwardPlan<E>,
) {
    let FlatForwardPlan {
        desc: _,
        computed_extension_outputs,
        aliased_base_outputs,
        aliased_extension_outputs,
    } = plan;

    for (address, poly) in computed_extension_outputs {
        storage.insert_extension_at_layer(expected_output_layer, address, poly);
    }
    for (address, poly) in aliased_base_outputs {
        storage.insert_base_field_at_layer(expected_output_layer, address, poly);
    }
    for (address, poly) in aliased_extension_outputs {
        storage.insert_extension_at_layer(expected_output_layer, address, poly);
    }
}

fn analyze_forward_lookup_usage(compiled_circuit: &GKRCircuitArtifact<BF>) -> ForwardLookupUsage {
    let mut usage = ForwardLookupUsage::default();
    for (layer_idx, layer) in compiled_circuit.layers.iter().enumerate() {
        for relation in layer.cached_relations.values() {
            match relation {
                NoFieldGKRCacheRelation::SingleColumnLookup {
                    range_check_width, ..
                } => {
                    if *range_check_width == 16 {
                        usage.last_range_mapping_layer = Some(layer_idx);
                    } else {
                        usage.last_timestamp_mapping_layer = Some(layer_idx);
                    }
                }
                NoFieldGKRCacheRelation::VectorizedLookup(_) => {
                    usage.last_generic_mapping_layer = Some(layer_idx);
                    usage.last_generic_lookup_layer = Some(layer_idx);
                }
                NoFieldGKRCacheRelation::VectorizedLookupSetup(_) => {
                    usage.last_generic_lookup_layer = Some(layer_idx);
                }
                NoFieldGKRCacheRelation::MemoryTuple(_) => {}
            }
        }
        for gate in layer
            .gates
            .iter()
            .chain(layer.gates_with_external_connections.iter())
        {
            match &gate.enforced_relation {
                NoFieldGKRRelation::MaterializedVectorLookupInput { .. }
                | NoFieldGKRRelation::LookupWithDensAndSetupExpressions { .. }
                | NoFieldGKRRelation::LookupPairFromVectorInputs { .. }
                | NoFieldGKRRelation::LookupFromVectorInputWithSetup { .. }
                | NoFieldGKRRelation::LookupUnbalancedPairWithVectorInputs { .. } => {
                    usage.last_generic_mapping_layer = Some(layer_idx);
                    usage.last_generic_lookup_layer = Some(layer_idx);
                }
                NoFieldGKRRelation::LookupPairFromBaseInputs {
                    range_check_width, ..
                } => {
                    if *range_check_width == 16 {
                        usage.last_range_mapping_layer = Some(layer_idx);
                    } else {
                        usage.last_timestamp_mapping_layer = Some(layer_idx);
                    }
                }
                _ => {}
            }
        }
    }
    usage
}

fn release_forward_lookup_resources_after_layer<E>(
    layer_idx: usize,
    usage: &ForwardLookupUsage,
    stage1: &mut GpuGKRStage1Output,
    forward_setup: &mut GpuGKRForwardSetup<E>,
) {
    if usage.last_generic_mapping_layer == Some(layer_idx) {
        stage1.lookup_mappings.release_generic_family();
    }
    if usage.last_range_mapping_layer == Some(layer_idx) {
        stage1.lookup_mappings.release_range_check_16();
    }
    if usage.last_timestamp_mapping_layer == Some(layer_idx) {
        stage1.lookup_mappings.release_timestamp();
    }
    if usage.last_generic_lookup_layer == Some(layer_idx) {
        forward_setup.release_generic_lookup();
    }
}

fn cache_relation_layer(layer_idx: usize, address: GKRAddress) -> usize {
    let GKRAddress::Cached { layer, .. } = address else {
        panic!(
            "forward cache scheduler expects cached address, got {:?}",
            address
        );
    };
    assert_eq!(
        layer, layer_idx,
        "cached relation address {:?} does not belong to scheduled layer {}",
        address, layer_idx
    );
    layer
}

fn add_memory_tuple_linear_term<E: Field>(
    descriptor: &mut GpuGKRForwardCacheDescriptor<E>,
    term_idx: usize,
    input: *const BF,
    challenge: E,
) {
    descriptor.linear_inputs[term_idx] = input;
    descriptor.linear_challenges[term_idx] = challenge;
}

fn push_memory_tuple_linear_term<E: Field>(
    descriptor: &mut GpuGKRForwardCacheDescriptor<E>,
    input: *const BF,
    challenge: E,
) {
    let term_idx = descriptor
        .linear_inputs
        .iter()
        .position(|ptr| ptr.is_null())
        .expect("GPU memory tuple linear terms exceeded fixed descriptor capacity");
    add_memory_tuple_linear_term(descriptor, term_idx, input, challenge);
}

enum LoweredCacheRelationOutput<E> {
    Base(GpuBaseFieldPoly<BF>),
    Ext(GpuExtensionFieldPoly<E>),
}

fn lower_cache_relation<E>(
    layer_idx: usize,
    address: GKRAddress,
    relation: &NoFieldGKRCacheRelation,
    storage: &mut GpuGKRStorage<BF, E>,
    stage1: &GpuGKRStage1Output,
    forward_setup: &GpuGKRForwardSetup<E>,
    external_challenges: &GKRExternalChallenges<BF, E>,
    decoder_predicate_address: Option<GKRAddress>,
    trace_len: usize,
    context: &ProverContext,
) -> CudaResult<(
    GpuGKRForwardCacheDescriptor<E>,
    LoweredCacheRelationOutput<E>,
)>
where
    E: FieldExtension<BF> + Field + SetByRef + SetByVal,
    Add: BinaryOp<E, E, E>,
    Add: BinaryOp<BF, E, E>,
    Add: BinaryOp<E, BF, E>,
    Mul: BinaryOp<E, E, E>,
    Mul: BinaryOp<BF, E, E>,
    Mul: BinaryOp<E, BF, E>,
    Sub: BinaryOp<E, E, E>,
    Sub: BinaryOp<E, BF, E>,
    Sub: BinaryOp<BF, BF, BF>,
{
    cache_relation_layer(layer_idx, address);
    let generic_lookup = if forward_setup.generic_lookup_len() > 0 {
        forward_setup.generic_lookup().as_ptr()
    } else {
        null()
    };

    match relation {
        NoFieldGKRCacheRelation::SingleColumnLookup {
            relation,
            range_check_width,
        } => {
            let mapping = if *range_check_width == 16 {
                stage1
                    .lookup_mappings
                    .range_check_mapping(relation.lookup_set_index)
            } else {
                stage1
                    .lookup_mappings
                    .timestamp_mapping(relation.lookup_set_index)
            };
            let setup_address = if *range_check_width == 16 {
                GKRAddress::VirtualSetup(VirtualSetupPoly::RangeCheck16Bits)
            } else {
                GKRAddress::VirtualSetup(VirtualSetupPoly::RangeCheckTimestamp)
            };
            let setup_source_kind = GpuBaseFieldSourceKind::from_address(setup_address)
                .expect("single-column lookup setup must be virtual");
            let dst_view = storage.allocate_base_view(layer_idx, address, context)?;
            let base_output = dst_view.as_mut_ptr();
            Ok((
                GpuGKRForwardCacheDescriptor {
                    kind: GpuGKRForwardCacheKind::SingleColumnLookup,
                    mapping: mapping.as_ptr(),
                    setup_values: null(),
                    setup_source_kind,
                    base_output,
                    ..GpuGKRForwardCacheDescriptor::default()
                },
                LoweredCacheRelationOutput::Base(dst_view),
            ))
        }
        NoFieldGKRCacheRelation::VectorizedLookup(rel) => {
            let is_decoder_lookup = rel.lookup_set_index == DECODER_LOOKUP_FORMAL_SET_INDEX;
            let mapping = if rel.lookup_set_index != DECODER_LOOKUP_FORMAL_SET_INDEX {
                stage1.lookup_mappings.generic_mapping(rel.lookup_set_index)
            } else {
                stage1
                    .lookup_mappings
                    .decoder_mapping()
                    .expect("decoder mapping must be present for decoder lookup relation")
            };
            let dst_view = storage.allocate_ext_view(layer_idx, address, context)?;
            let ext_output = dst_view.as_mut_ptr();
            let decoder_mask = if is_decoder_lookup {
                storage
                    .get_base_layer(
                        decoder_predicate_address
                            .expect("decoder lookup requires a decoder predicate column"),
                    )
                    .as_ptr()
            } else {
                null()
            };
            Ok((
                GpuGKRForwardCacheDescriptor {
                    kind: GpuGKRForwardCacheKind::VectorizedLookup,
                    mapping: mapping.as_ptr(),
                    generic_lookup,
                    decoder_mask,
                    decoder_fill_value: if is_decoder_lookup {
                        forward_setup.decoder_lookup_fill_value_device().as_ptr()
                    } else {
                        null()
                    },
                    ext_output,
                    ..GpuGKRForwardCacheDescriptor::default()
                },
                LoweredCacheRelationOutput::Ext(dst_view),
            ))
        }
        NoFieldGKRCacheRelation::VectorizedLookupSetup(_) => {
            let dst_view = storage.allocate_ext_view(layer_idx, address, context)?;
            let ext_output = dst_view.as_mut_ptr();
            Ok((
                GpuGKRForwardCacheDescriptor {
                    kind: GpuGKRForwardCacheKind::VectorizedLookupSetup,
                    generic_lookup,
                    ext_output,
                    generic_lookup_len: forward_setup.generic_lookup_len() as u32,
                    ..GpuGKRForwardCacheDescriptor::default()
                },
                LoweredCacheRelationOutput::Ext(dst_view),
            ))
        }
        NoFieldGKRCacheRelation::MemoryTuple(rel) => {
            let dst_view = storage.allocate_ext_view(layer_idx, address, context)?;
            let ext_output = dst_view.as_mut_ptr();
            let mut descriptor = GpuGKRForwardCacheDescriptor {
                kind: GpuGKRForwardCacheKind::MemoryTuple,
                ext_output,
                constant_term: external_challenges.permutation_argument_additive_part,
                ..GpuGKRForwardCacheDescriptor::default()
            };
            let mut deferred_low_dynamic_term: Option<(*const BF, E)> = None;
            match rel.address_space {
                CompiledAddressSpaceRelationStrict::Constant(c) => {
                    descriptor.address_space_kind = GpuGKRForwardCacheAddressSpaceKind::Constant;
                    descriptor.address_space_constant = BF::from_u32_unchecked(c);
                }
                CompiledAddressSpaceRelationStrict::IsRegister(offset) => {
                    descriptor.address_space_kind = GpuGKRForwardCacheAddressSpaceKind::Not;
                    descriptor.address_space_ptr = storage
                        .get_base_layer(GKRAddress::BaseLayerMemory(offset))
                        .as_ptr();
                }
                CompiledAddressSpaceRelationStrict::IsRam(offset) => {
                    descriptor.address_space_kind = GpuGKRForwardCacheAddressSpaceKind::Is;
                    descriptor.address_space_ptr = storage
                        .get_base_layer(GKRAddress::BaseLayerMemory(offset))
                        .as_ptr();
                }
            }

            match &rel.address {
                CompiledAddressStrict::ConstantU16(c) => {
                    let mut contribution = external_challenges
                        .permutation_argument_linearization_challenges
                        [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                    contribution.mul_assign_by_base(&BF::from_u32_unchecked(*c as u32));
                    descriptor.constant_term.add_assign(&contribution);
                }
                CompiledAddressStrict::Constant(c) => {
                    let mut contribution = external_challenges
                        .permutation_argument_linearization_challenges
                        [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                    contribution.mul_assign_by_base(&BF::from_u32_unchecked(*c));
                    descriptor.constant_term.add_assign(&contribution);
                }
                CompiledAddressStrict::U16Space(offset) => {
                    add_memory_tuple_linear_term(
                        &mut descriptor,
                        MEMORY_TUPLE_ADDRESS_LOW_TERM,
                        storage
                            .get_base_layer(GKRAddress::BaseLayerMemory(*offset))
                            .as_ptr(),
                        external_challenges.permutation_argument_linearization_challenges
                            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX],
                    );
                }
                CompiledAddressStrict::U32Space([low, high]) => {
                    add_memory_tuple_linear_term(
                        &mut descriptor,
                        MEMORY_TUPLE_ADDRESS_LOW_TERM,
                        storage
                            .get_base_layer(GKRAddress::BaseLayerMemory(*low))
                            .as_ptr(),
                        external_challenges.permutation_argument_linearization_challenges
                            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX],
                    );
                    add_memory_tuple_linear_term(
                        &mut descriptor,
                        MEMORY_TUPLE_ADDRESS_HIGH_TERM,
                        storage
                            .get_base_layer(GKRAddress::BaseLayerMemory(*high))
                            .as_ptr(),
                        external_challenges.permutation_argument_linearization_challenges
                            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX],
                    );
                }
                CompiledAddressStrict::U32SpaceSpecialIndirect {
                    low_base,
                    low_dynamic_offset,
                    low_offset,
                    high,
                } => {
                    let low_challenge = external_challenges
                        .permutation_argument_linearization_challenges
                        [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                    let high_challenge = external_challenges
                        .permutation_argument_linearization_challenges
                        [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
                    if *low_offset != 0 {
                        let mut contribution = low_challenge;
                        contribution.mul_assign_by_base(&BF::from_u32_unchecked(*low_offset));
                        descriptor.constant_term.add_assign(&contribution);
                    }
                    add_memory_tuple_linear_term(
                        &mut descriptor,
                        MEMORY_TUPLE_ADDRESS_LOW_TERM,
                        storage
                            .get_base_layer(GKRAddress::BaseLayerMemory(*low_base))
                            .as_ptr(),
                        low_challenge,
                    );
                    if let Some((multiplier, dynamic_offset)) = *low_dynamic_offset {
                        let mut challenge = low_challenge;
                        challenge.mul_assign_by_base(&BF::from_u32_unchecked(multiplier as u32));
                        deferred_low_dynamic_term = Some((
                            storage
                                .get_base_layer(GKRAddress::BaseLayerMemory(dynamic_offset))
                                .as_ptr(),
                            challenge,
                        ));
                    }
                    add_memory_tuple_linear_term(
                        &mut descriptor,
                        MEMORY_TUPLE_ADDRESS_HIGH_TERM,
                        storage
                            .get_base_layer(GKRAddress::BaseLayerMemory(*high))
                            .as_ptr(),
                        high_challenge,
                    );
                }
                CompiledAddressStrict::U32SpaceGeneric(..) => {
                    unimplemented!(
                        "unsupported GPU memory tuple address relation: {:?}",
                        rel.address
                    )
                }
            }

            match &rel.timestamp {
                CompiledMemoryTimestamp::Zero => {}
                CompiledMemoryTimestamp::Normal(timestamp) => {
                    add_memory_tuple_linear_term(
                        &mut descriptor,
                        MEMORY_TUPLE_TIMESTAMP_LOW_TERM,
                        storage
                            .get_base_layer(GKRAddress::BaseLayerMemory(timestamp[0]))
                            .as_ptr(),
                        external_challenges.permutation_argument_linearization_challenges
                            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX],
                    );
                    if rel.timestamp_offset != 0 {
                        let mut contribution = external_challenges
                            .permutation_argument_linearization_challenges
                            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                        contribution
                            .mul_assign_by_base(&BF::from_u32_unchecked(rel.timestamp_offset));
                        descriptor.constant_term.add_assign(&contribution);
                    }
                    add_memory_tuple_linear_term(
                        &mut descriptor,
                        MEMORY_TUPLE_TIMESTAMP_HIGH_TERM,
                        storage
                            .get_base_layer(GKRAddress::BaseLayerMemory(timestamp[1]))
                            .as_ptr(),
                        external_challenges.permutation_argument_linearization_challenges
                            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX],
                    );
                }
            }

            match rel.value {
                RamWordRepresentation::Zero => {}
                RamWordRepresentation::U16Limbs(read_value) => {
                    add_memory_tuple_linear_term(
                        &mut descriptor,
                        MEMORY_TUPLE_VALUE_LOW_TERM,
                        storage
                            .get_base_layer(GKRAddress::BaseLayerMemory(read_value[0]))
                            .as_ptr(),
                        external_challenges.permutation_argument_linearization_challenges
                            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX],
                    );
                    add_memory_tuple_linear_term(
                        &mut descriptor,
                        MEMORY_TUPLE_VALUE_HIGH_TERM,
                        storage
                            .get_base_layer(GKRAddress::BaseLayerMemory(read_value[1]))
                            .as_ptr(),
                        external_challenges.permutation_argument_linearization_challenges
                            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX],
                    );
                }
                RamWordRepresentation::U8Limbs(read_value_bytes) => {
                    let byte_shift = BF::from_u32_unchecked(1 << 8);
                    for (challenge_idx, low_term_idx, high_term_idx, low_offset, high_offset) in [
                        (
                            PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
                            MEMORY_TUPLE_VALUE_LOW_TERM,
                            MEMORY_TUPLE_VALUE_LOW_EXTRA_TERM,
                            read_value_bytes[0],
                            read_value_bytes[1],
                        ),
                        (
                            PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
                            MEMORY_TUPLE_VALUE_HIGH_TERM,
                            MEMORY_TUPLE_VALUE_HIGH_EXTRA_TERM,
                            read_value_bytes[2],
                            read_value_bytes[3],
                        ),
                    ] {
                        let challenge = external_challenges
                            .permutation_argument_linearization_challenges[challenge_idx];
                        add_memory_tuple_linear_term(
                            &mut descriptor,
                            low_term_idx,
                            storage
                                .get_base_layer(GKRAddress::BaseLayerMemory(low_offset))
                                .as_ptr(),
                            challenge,
                        );
                        let mut shifted_challenge = challenge;
                        shifted_challenge.mul_assign_by_base(&byte_shift);
                        add_memory_tuple_linear_term(
                            &mut descriptor,
                            high_term_idx,
                            storage
                                .get_base_layer(GKRAddress::BaseLayerMemory(high_offset))
                                .as_ptr(),
                            shifted_challenge,
                        );
                    }
                }
            }

            if let Some((input, challenge)) = deferred_low_dynamic_term {
                push_memory_tuple_linear_term(&mut descriptor, input, challenge);
            }

            Ok((descriptor, LoweredCacheRelationOutput::Ext(dst_view)))
        }
    }
}

fn schedule_cache_relations<E>(
    layer_idx: usize,
    relations: &BTreeMap<GKRAddress, NoFieldGKRCacheRelation>,
    storage: &mut GpuGKRStorage<BF, E>,
    stage1: &GpuGKRStage1Output,
    forward_setup: &GpuGKRForwardSetup<E>,
    external_challenges: &GKRExternalChallenges<BF, E>,
    decoder_predicate_address: Option<GKRAddress>,
    trace_len: usize,
    context: &ProverContext,
) -> CudaResult<()>
where
    E: FieldExtension<BF> + Field + SetByRef + SetByVal + GpuGKRForwardCacheKernelSet,
    Add: BinaryOp<E, E, E>,
    Add: BinaryOp<BF, E, E>,
    Add: BinaryOp<E, BF, E>,
    Mul: BinaryOp<E, E, E>,
    Mul: BinaryOp<BF, E, E>,
    Mul: BinaryOp<E, BF, E>,
    Sub: BinaryOp<E, E, E>,
    Sub: BinaryOp<E, BF, E>,
    Sub: BinaryOp<BF, BF, BF>,
{
    if relations.is_empty() {
        return Ok(());
    }
    assert!(
        forward_setup.generic_lookup_len() <= u32::MAX as usize,
        "generic lookup runtime too large for fused forward cache kernel"
    );

    let mut pending_relations = relations.iter();
    loop {
        let mut batch = GpuGKRForwardCacheBatch::default();
        for descriptor in batch.descriptors.iter_mut() {
            let Some((address, relation)) = pending_relations.next() else {
                break;
            };
            let (lowered, output) = lower_cache_relation(
                layer_idx,
                *address,
                relation,
                storage,
                stage1,
                forward_setup,
                external_challenges,
                decoder_predicate_address,
                trace_len,
                context,
            )?;
            *descriptor = lowered;
            let output_layer = cache_relation_layer(layer_idx, *address);
            match output {
                LoweredCacheRelationOutput::Base(poly) => {
                    storage.insert_base_field_at_layer(output_layer, *address, poly);
                }
                LoweredCacheRelationOutput::Ext(poly) => {
                    storage.insert_extension_at_layer(output_layer, *address, poly);
                }
            }
            batch.count += 1;
        }
        if batch.count == 0 {
            break;
        }
        launch_forward_cache(batch, trace_len, context)?;
    }
    Ok(())
}

/// Per-slot initial input pointers handed to the first tower launch of each chunk.
#[derive(Clone, Copy)]
pub(super) enum LoweredSlotInitialInput<E> {
    PairwiseProduct { input: *const E },
    LookupPair { num: *const E, den: *const E },
}

/// Per-slot output pointers for a single reduction round.
#[derive(Clone, Copy)]
pub(super) enum LoweredSlotOutput<E> {
    PairwiseProduct {
        output: *mut E,
    },
    LookupPair {
        output_num: *mut E,
        output_den: *mut E,
    },
}

pub(super) struct LoweredDimReducingForwardRound<E> {
    pub(super) slot_initial_inputs: Vec<LoweredSlotInitialInput<E>>,
    pub(super) slot_output_types: Vec<OutputType>,
    pub(super) slot_outputs: Vec<LoweredSlotOutput<E>>,
    pub(super) layer_description: BTreeMap<OutputType, DimensionReducingInputOutput>,
    pub(super) computed_extension_outputs: Vec<(GKRAddress, GpuExtensionFieldPoly<E>)>,
}

pub(super) fn schedule_dimension_reduction_forward<E>(
    storage: &mut GpuGKRStorage<BF, E>,
    initial_layer_idx: usize,
    initial_output_map: BTreeMap<OutputType, Vec<GKRAddress>>,
    initial_trace_log_2: usize,
    final_trace_log_2: usize,
    output_evaluations_slab: Option<ForwardOutputSlabTarget<E>>,
    tracing_ranges: &mut Vec<Range>,
    context: &ProverContext,
) -> CudaResult<(
    usize,
    BTreeMap<usize, BTreeMap<OutputType, DimensionReducingInputOutput>>,
)>
where
    E: FieldExtension<BF> + Field + SetByRef + SetByVal,
    E: GpuGKRDimensionReducingForwardTowerKernelSet,
    Add: BinaryOp<E, E, E>,
    Add: BinaryOp<BF, E, E>,
    Add: BinaryOp<E, BF, E>,
    Mul: BinaryOp<E, E, E>,
    Mul: BinaryOp<BF, E, E>,
    Mul: BinaryOp<E, BF, E>,
    Sub: BinaryOp<E, E, E>,
    Sub: BinaryOp<E, BF, E>,
    Sub: BinaryOp<BF, BF, BF>,
{
    let mut dimension_reduction_description = BTreeMap::new();
    let mut current_layer_idx = initial_layer_idx;
    let stream = context.get_exec_stream();
    let total_rounds = initial_trace_log_2.saturating_sub(final_trace_log_2);
    if total_rounds == 0 {
        return Ok((current_layer_idx, dimension_reduction_description));
    }

    // Phase 1: lower + commit every round sequentially so subsequent rounds can resolve inputs
    // from storage. Collect per-round per-slot output pointers for the later tower assembly.
    let mut per_round_slot_outputs: Vec<Vec<LoweredSlotOutput<E>>> =
        Vec::with_capacity(total_rounds);
    let mut slot_initial_inputs: Option<Vec<LoweredSlotInitialInput<E>>> = None;
    let mut slot_output_types: Option<Vec<OutputType>> = None;

    for round_idx in 0..total_rounds {
        let input_size_log_2 = initial_trace_log_2 - round_idx;
        let output_trace_len = 1usize << (input_size_log_2 - 1);
        let is_final_round = round_idx + 1 == total_rounds;

        let layer_inputs = if current_layer_idx != initial_layer_idx {
            let previous: &BTreeMap<OutputType, DimensionReducingInputOutput> =
                dimension_reduction_description
                    .get(&(current_layer_idx - 1))
                    .expect("dimension reduction input layer must exist");
            BTreeMap::from_iter(previous.iter().map(|(k, v)| (*k, v.output.clone())))
        } else {
            initial_output_map.clone()
        };

        let lowered = lower_dimension_reducing_forward_round(
            &layer_inputs,
            current_layer_idx,
            output_trace_len,
            storage,
            if is_final_round {
                output_evaluations_slab.as_ref()
            } else {
                None
            },
            context,
        )?;

        if round_idx == 0 {
            slot_initial_inputs = Some(lowered.slot_initial_inputs.clone());
            slot_output_types = Some(lowered.slot_output_types.clone());
        }
        per_round_slot_outputs.push(lowered.slot_outputs.clone());

        for (address, poly) in lowered.computed_extension_outputs {
            storage.insert_extension_at_layer(current_layer_idx + 1, address, poly);
        }
        dimension_reduction_description.insert(current_layer_idx, lowered.layer_description);
        current_layer_idx += 1;
    }

    // Phase 2: slot-major dispatch, all launches on exec_stream. Each slot's full reduction
    // chain (every tower chunk) runs contiguously before the next slot starts. One NVTX range
    // per OutputType wraps all slots belonging to that type — PermutationProduct covers both
    // read_set and write_set chains; each lookup type covers its single (num, den) chain.
    let slot_initial_inputs =
        slot_initial_inputs.expect("non-zero rounds implies we captured initial inputs");
    let slot_output_types =
        slot_output_types.expect("non-zero rounds implies we captured slot output types");
    let slot_count = slot_initial_inputs.len();
    let log_block = GKR_DIM_REDUCING_FORWARD_TOWER_LOG_BLOCK as usize;

    let mut slot_idx = 0usize;
    while slot_idx < slot_count {
        let range_type = slot_output_types[slot_idx];
        let range_end = slot_output_types[slot_idx..]
            .iter()
            .position(|t| *t != range_type)
            .map(|offset| slot_idx + offset)
            .unwrap_or(slot_count);

        let range = Range::new(format!(
            "gkr.forward.dimension_reduction.tower.{:?}",
            range_type
        ))?;
        range.start(stream)?;

        for s in slot_idx..range_end {
            let mut cur_input = slot_initial_inputs[s];
            let mut cur_input_log_2 = initial_trace_log_2;
            let mut r = 0usize;
            while r < total_rounds {
                let remaining = total_rounds - r;
                let chunk_rounds = remaining.min(log_block);
                let chunk_input_len = 1u32 << cur_input_log_2;
                dispatch_tower_slot_launch(
                    cur_input,
                    s,
                    r,
                    chunk_rounds,
                    chunk_input_len,
                    &per_round_slot_outputs,
                    stream,
                )?;
                r += chunk_rounds;
                cur_input_log_2 -= chunk_rounds;
                if r < total_rounds {
                    let last_round = r - 1;
                    cur_input = match per_round_slot_outputs[last_round][s] {
                        LoweredSlotOutput::PairwiseProduct { output } => {
                            LoweredSlotInitialInput::PairwiseProduct {
                                input: output as *const E,
                            }
                        }
                        LoweredSlotOutput::LookupPair {
                            output_num,
                            output_den,
                        } => LoweredSlotInitialInput::LookupPair {
                            num: output_num as *const E,
                            den: output_den as *const E,
                        },
                    };
                }
            }
        }

        range.end(stream)?;
        tracing_ranges.push(range);

        slot_idx = range_end;
    }

    Ok((current_layer_idx - 1, dimension_reduction_description))
}

fn dispatch_tower_slot_launch<E>(
    slot_input: LoweredSlotInitialInput<E>,
    slot_idx: usize,
    chunk_start_round: usize,
    chunk_rounds: usize,
    chunk_input_len: u32,
    per_round_slot_outputs: &[Vec<LoweredSlotOutput<E>>],
    stream: &era_cudart::stream::CudaStream,
) -> CudaResult<()>
where
    E: GpuGKRDimensionReducingForwardTowerKernelSet,
{
    match slot_input {
        LoweredSlotInitialInput::PairwiseProduct { input } => {
            let mut batch = GpuGKRDimensionReducingForwardTowerPairwiseBatch::<E>::default();
            batch.input = input;
            batch.input_len = chunk_input_len;
            batch.round_count = chunk_rounds as u32;
            for local_r in 0..chunk_rounds {
                let round_idx = chunk_start_round + local_r;
                match per_round_slot_outputs[round_idx][slot_idx] {
                    LoweredSlotOutput::PairwiseProduct { output } => {
                        batch.round_outputs[local_r] = output;
                    }
                    LoweredSlotOutput::LookupPair { .. } => panic!(
                        "tower slot {} changed kind between round 0 and round {}",
                        slot_idx, round_idx
                    ),
                }
            }
            launch_dimension_reducing_forward_tower_pairwise(&batch, stream)
        }
        LoweredSlotInitialInput::LookupPair { num, den } => {
            let mut batch = GpuGKRDimensionReducingForwardTowerLookupBatch::<E>::default();
            batch.input_num = num;
            batch.input_den = den;
            batch.input_len = chunk_input_len;
            batch.round_count = chunk_rounds as u32;
            for local_r in 0..chunk_rounds {
                let round_idx = chunk_start_round + local_r;
                match per_round_slot_outputs[round_idx][slot_idx] {
                    LoweredSlotOutput::LookupPair {
                        output_num,
                        output_den,
                    } => {
                        batch.round_outputs_num[local_r] = output_num;
                        batch.round_outputs_den[local_r] = output_den;
                    }
                    LoweredSlotOutput::PairwiseProduct { .. } => panic!(
                        "tower slot {} changed kind between round 0 and round {}",
                        slot_idx, round_idx
                    ),
                }
            }
            launch_dimension_reducing_forward_tower_lookup(&batch, stream)
        }
    }
}

// Tower outputs are routed through the consolidated per-(tower-layer, class)
// backings populated by `GpuGKRStorageLayout::from_artifact_with_tower`. Each
// view returned by `storage.allocate_ext_view` is sized to the round's
// `output_trace_len` (the layout's per-layer `log2_stride` halves each round).
fn lower_dimension_reducing_forward_round<E>(
    layer_inputs: &BTreeMap<OutputType, Vec<GKRAddress>>,
    current_layer_idx: usize,
    output_trace_len: usize,
    storage: &mut GpuGKRStorage<BF, E>,
    output_evaluations_slab: Option<&ForwardOutputSlabTarget<E>>,
    context: &ProverContext,
) -> CudaResult<LoweredDimReducingForwardRound<E>>
where
    E: FieldExtension<BF> + Field,
    E: 'static,
{
    let output_layer = current_layer_idx + 1;
    if let Some(target) = output_evaluations_slab {
        let output_polys: usize = layer_inputs.values().map(Vec::len).sum();
        assert_eq!(
            target.len,
            output_polys * output_trace_len,
            "slab output_evaluations length must match final forward reduction outputs",
        );
        assert!(
            target.backing.len() >= target.len,
            "proof slab backing must contain the output_evaluations prefix",
        );
        if output_layer >= storage.layers.len() {
            storage
                .layers
                .resize_with(output_layer + 1, GpuGKRLayerSource::default);
        }
        let previous = storage.layers[output_layer].ext_class_backings.insert(
            super::gkr_address_audit::AddressClass::ThisLayerInnerLayerWrite,
            Arc::clone(&target.backing),
        );
        assert!(
            previous.is_none(),
            "final forward output slab backing must be bound before any output allocation",
        );
    }
    let mut output_idx = 0usize;
    let mut layer_description = BTreeMap::new();
    let mut slot_initial_inputs = Vec::new();
    let mut slot_output_types = Vec::new();
    let mut slot_outputs = Vec::new();
    let mut computed_extension_outputs = Vec::new();

    for (arg_type, inputs) in layer_inputs.iter() {
        let inputs: [GKRAddress; 2] = inputs
            .clone()
            .try_into()
            .expect("dimension reduction forward inputs must have arity 2");
        match *arg_type {
            OutputType::PermutationProduct => {
                let mut outputs = [GKRAddress::placeholder(); 2];
                for (idx, input) in inputs.into_iter().enumerate() {
                    let input_start_ptr = storage
                        .try_get_ext_poly(input)
                        .unwrap_or_else(|| {
                            panic!("missing dimension reduction input poly for {:?}", input)
                        })
                        .as_ptr();
                    let output = GKRAddress::InnerLayer {
                        layer: output_layer,
                        offset: output_idx,
                    };
                    output_idx += 1;
                    let reduced = storage.allocate_ext_view(output_layer, output, context)?;
                    assert_eq!(
                        reduced.len(),
                        output_trace_len,
                        "tower layer {output_layer} layout stride implies len {} but round expects {}",
                        reduced.len(),
                        output_trace_len,
                    );
                    let output_ptr = reduced.as_mut_ptr();
                    slot_initial_inputs.push(LoweredSlotInitialInput::PairwiseProduct {
                        input: input_start_ptr,
                    });
                    slot_output_types.push(*arg_type);
                    slot_outputs.push(LoweredSlotOutput::PairwiseProduct { output: output_ptr });
                    computed_extension_outputs.push((output, reduced));
                    outputs[idx] = output;
                }
                layer_description.insert(
                    *arg_type,
                    DimensionReducingInputOutput {
                        inputs: inputs.to_vec(),
                        output: outputs.to_vec(),
                    },
                );
            }
            OutputType::Lookup16Bits | OutputType::LookupTimestamps | OutputType::GenericLookup => {
                let num_ptr = storage
                    .try_get_ext_poly(inputs[0])
                    .unwrap_or_else(|| {
                        panic!(
                            "missing lookup reduction numerator poly for {:?}",
                            inputs[0]
                        )
                    })
                    .as_ptr();
                let den_ptr = storage
                    .try_get_ext_poly(inputs[1])
                    .unwrap_or_else(|| {
                        panic!(
                            "missing lookup reduction denominator poly for {:?}",
                            inputs[1]
                        )
                    })
                    .as_ptr();
                let new_num = GKRAddress::InnerLayer {
                    layer: output_layer,
                    offset: output_idx,
                };
                output_idx += 1;
                let new_den = GKRAddress::InnerLayer {
                    layer: output_layer,
                    offset: output_idx,
                };
                output_idx += 1;
                let reduced_num = storage.allocate_ext_view(output_layer, new_num, context)?;
                let reduced_den = storage.allocate_ext_view(output_layer, new_den, context)?;
                assert_eq!(reduced_num.len(), output_trace_len);
                assert_eq!(reduced_den.len(), output_trace_len);
                let out_num_ptr = reduced_num.as_mut_ptr();
                let out_den_ptr = reduced_den.as_mut_ptr();
                slot_initial_inputs.push(LoweredSlotInitialInput::LookupPair {
                    num: num_ptr,
                    den: den_ptr,
                });
                slot_output_types.push(*arg_type);
                slot_outputs.push(LoweredSlotOutput::LookupPair {
                    output_num: out_num_ptr,
                    output_den: out_den_ptr,
                });
                computed_extension_outputs.push((new_num, reduced_num));
                computed_extension_outputs.push((new_den, reduced_den));
                layer_description.insert(
                    *arg_type,
                    DimensionReducingInputOutput {
                        inputs: inputs.to_vec(),
                        output: [new_num, new_den].to_vec(),
                    },
                );
            }
        }
    }
    Ok(LoweredDimReducingForwardRound {
        slot_initial_inputs,
        slot_output_types,
        slot_outputs,
        layer_description,
        computed_extension_outputs,
    })
}

fn alloc_base(len: usize, context: &ProverContext) -> CudaResult<DeviceAllocation<BF>> {
    context.alloc(len, AllocationPlacement::Top)
}

fn alloc_ext<E>(len: usize, context: &ProverContext) -> CudaResult<DeviceAllocation<E>> {
    context.alloc(len, AllocationPlacement::Top)
}

fn add_ext_scalar_in_place<E>(
    dst: &mut DeviceAllocation<E>,
    scalar: E,
    context: &ProverContext,
) -> CudaResult<()>
where
    E: Field + SetByVal,
    Add: BinaryOp<E, E, E>,
{
    let mut scalar_device = context.alloc(1, AllocationPlacement::BestFit)?;
    set_by_val(scalar, scalar_device.deref_mut(), context.get_exec_stream())?;
    add_into_y(
        &DeviceVectorChunk::new(&scalar_device, 0, 1),
        dst.deref_mut(),
        context.get_exec_stream(),
    )
}

fn add_ext_device_scalar_in_place<E>(
    dst: &mut DeviceAllocation<E>,
    scalar_device: &DeviceAllocation<E>,
    context: &ProverContext,
) -> CudaResult<()>
where
    E: Field,
    Add: BinaryOp<E, E, E>,
{
    add_into_y(
        &DeviceVectorChunk::new(scalar_device, 0, 1),
        dst.deref_mut(),
        context.get_exec_stream(),
    )
}

fn sub_ext_scalar_in_place<E>(
    dst: &mut DeviceAllocation<E>,
    scalar: E,
    context: &ProverContext,
) -> CudaResult<()>
where
    E: Field + SetByVal,
    Sub: BinaryOp<E, E, E>,
{
    let mut scalar_device = context.alloc(1, AllocationPlacement::BestFit)?;
    set_by_val(scalar, scalar_device.deref_mut(), context.get_exec_stream())?;
    sub_into_x(
        dst.deref_mut(),
        &DeviceVectorChunk::new(&scalar_device, 0, 1),
        context.get_exec_stream(),
    )
}

fn flatten_inits_or_teardowns_linear_combination<E: Field + FieldExtension<BF>>(
    timestamps_and_values: Option<([usize; 2], [usize; 2])>,
    setup: [GKRAddress; 2],
    address_high_bits: u32,
    address_high_bits_shift: u32,
    external_challenges: &GKRExternalChallenges<BF, E>,
) -> (BTreeMap<GKRAddress, E>, E) {
    let mut result = BTreeMap::new();
    let mut constant_term = external_challenges.permutation_argument_additive_part;
    constant_term.add_assign_base(&BF::from_u32_unchecked(AddressSpaceType::RAM as u32));

    {
        let challenge = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
        assert!(result.insert(setup[0], challenge).is_none());
    }
    {
        let mut challenge = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
        assert!(result.insert(setup[1], challenge).is_none());
        challenge.mul_assign_by_base(&BF::from_u32_unchecked(
            address_high_bits << address_high_bits_shift,
        ));
        constant_term.add_assign(&challenge);
    }

    if let Some((timestamps, values)) = timestamps_and_values {
        for (idx, address) in [
            (
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX,
                GKRAddress::BaseLayerMemory(timestamps[0]),
            ),
            (
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX,
                GKRAddress::BaseLayerMemory(timestamps[1]),
            ),
            (
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
                GKRAddress::BaseLayerMemory(values[0]),
            ),
            (
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
                GKRAddress::BaseLayerMemory(values[1]),
            ),
        ] {
            let challenge = external_challenges.permutation_argument_linearization_challenges[idx];
            assert!(result.insert(address, challenge).is_none());
        }
    }

    (result, constant_term)
}

fn materialize_linear_base_combination<E>(
    storage: &GpuGKRStorage<BF, E>,
    terms: &BTreeMap<GKRAddress, E>,
    constant_term: E,
    trace_len: usize,
    context: &ProverContext,
) -> CudaResult<DeviceAllocation<E>>
where
    E: Field + FieldExtension<BF> + GpuGKRVirtualBaseAccumKernelSet + SetByVal,
    Add: BinaryOp<E, E, E>,
    Mul: BinaryOp<BF, E, E>,
{
    let mut dst = context.alloc(trace_len, AllocationPlacement::BestFit)?;
    set_by_val(constant_term, dst.deref_mut(), context.get_exec_stream())?;
    for (&address, &challenge) in terms.iter() {
        if let Some(source) = storage.try_get_base_poly(address) {
            scale_and_add_base_column(&mut dst, source, challenge, context)?;
        } else if let Some(source_kind) = GpuBaseFieldSourceKind::from_address(address) {
            launch_virtual_base_accum(
                source_kind,
                challenge,
                dst.as_mut_ptr(),
                trace_len,
                context,
            )?;
        } else {
            panic!(
                "base linear combination expects real or virtual base source, got {:?}",
                address
            );
        }
    }
    Ok(dst)
}

fn materialize_inits_and_teardowns_initial_pair_into<E>(
    storage: &GpuGKRStorage<BF, E>,
    dst: &GpuExtensionFieldPoly<E>,
    timestamp_and_value: &InitsOrTeardownsTimestampAndValue,
    setup: [GKRAddress; 2],
    address_high_bits: [u32; 2],
    address_high_bits_shift: u32,
    external_challenges: &GKRExternalChallenges<BF, E>,
    trace_len: usize,
    context: &ProverContext,
) -> CudaResult<()>
where
    E: Field + FieldExtension<BF> + GpuGKRVirtualBaseAccumKernelSet + SetByVal,
    Add: BinaryOp<E, E, E>,
    Mul: BinaryOp<BF, E, E>,
    Mul: BinaryOp<E, E, E>,
{
    assert_eq!(
        dst.len(),
        trace_len,
        "InitsOrTeardownsInitialPair destination view must span trace_len"
    );
    let lhs_timestamps_and_values = match timestamp_and_value {
        InitsOrTeardownsTimestampAndValue::Init => None,
        InitsOrTeardownsTimestampAndValue::Teardown {
            lhs_timestamp,
            lhs_value,
            ..
        } => Some((*lhs_timestamp, *lhs_value)),
    };
    let rhs_timestamps_and_values = match timestamp_and_value {
        InitsOrTeardownsTimestampAndValue::Init => None,
        InitsOrTeardownsTimestampAndValue::Teardown {
            rhs_timestamp,
            rhs_value,
            ..
        } => Some((*rhs_timestamp, *rhs_value)),
    };

    let (lhs_terms, lhs_constant) = flatten_inits_or_teardowns_linear_combination(
        lhs_timestamps_and_values,
        setup,
        address_high_bits[0],
        address_high_bits_shift,
        external_challenges,
    );
    let (rhs_terms, rhs_constant) = flatten_inits_or_teardowns_linear_combination(
        rhs_timestamps_and_values,
        setup,
        address_high_bits[1],
        address_high_bits_shift,
        external_challenges,
    );
    let lhs =
        materialize_linear_base_combination(storage, &lhs_terms, lhs_constant, trace_len, context)?;
    let rhs =
        materialize_linear_base_combination(storage, &rhs_terms, rhs_constant, trace_len, context)?;
    // SAFETY: `dst` was just allocated for this consumer; no other clone of
    // this view is scheduled to write before the mul completes.
    let mut dst_chunk = unsafe { dst.as_mut_chunk_unchecked() };
    mul(
        &DeviceVectorChunk::new(&lhs, 0, trace_len),
        &DeviceVectorChunk::new(&rhs, 0, trace_len),
        &mut dst_chunk,
        context.get_exec_stream(),
    )
}

fn scale_and_add_base_column<E>(
    dst: &mut DeviceAllocation<E>,
    source: &GpuBaseFieldPoly<BF>,
    scalar: E,
    context: &ProverContext,
) -> CudaResult<()>
where
    E: FieldExtension<BF> + Field + SetByVal,
    Add: BinaryOp<E, E, E>,
    Mul: BinaryOp<BF, E, E>,
{
    let mut weighted = context.alloc(source.len(), AllocationPlacement::BestFit)?;
    set_by_val(scalar, weighted.deref_mut(), context.get_exec_stream())?;
    mul_into_y(
        &source.as_device_chunk(),
        weighted.deref_mut(),
        context.get_exec_stream(),
    )?;
    add_into_y(
        &DeviceVectorChunk::new(&weighted, 0, source.len()),
        dst.deref_mut(),
        context.get_exec_stream(),
    )
}

fn scale_and_add_base_column_in_place<D>(
    dst: &mut D,
    source: &GpuBaseFieldPoly<BF>,
    scalar: BF,
    context: &ProverContext,
) -> CudaResult<()>
where
    D: DeviceMatrixChunkMutImpl<BF> + ?Sized,
    Add: BinaryOp<BF, BF, BF>,
    Mul: BinaryOp<BF, BF, BF>,
{
    let mut weighted = context.alloc(source.len(), AllocationPlacement::BestFit)?;
    set_by_val(scalar, weighted.deref_mut(), context.get_exec_stream())?;
    mul_into_y(
        &source.as_device_chunk(),
        weighted.deref_mut(),
        context.get_exec_stream(),
    )?;
    add_into_y(
        &DeviceVectorChunk::new(&weighted, 0, source.len()),
        dst,
        context.get_exec_stream(),
    )
}

fn shifted_base_to_ext<E>(
    source: &GpuBaseFieldPoly<BF>,
    additive_part: &DeviceAllocation<E>,
    context: &ProverContext,
) -> CudaResult<DeviceAllocation<E>>
where
    E: Field + SetByRef,
    Add: BinaryOp<E, E, E>,
    Add: BinaryOp<BF, E, E>,
{
    let mut dst = alloc_ext(source.len(), context)?;
    set_by_ref(
        &DeviceVectorChunk::new(additive_part, 0, 1),
        dst.deref_mut(),
        context.get_exec_stream(),
    )?;
    add_into_y(
        &source.as_device_chunk(),
        dst.deref_mut(),
        context.get_exec_stream(),
    )?;
    Ok(dst)
}

fn ext_from_base<E>(value: BF) -> E
where
    E: FieldExtension<BF> + Field,
{
    let mut result = E::ZERO;
    result.add_assign_base(&value);
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::allocator::tracker::AllocationPlacement;
    use crate::ops::simple::set_by_val;
    use crate::primitives::field::E4;
    use crate::prover::test_utils::make_test_context;
    use cs::gkr_compiler::{GateArtifacts, NoFieldMaxQuadraticConstraintsGKRRelation};
    use era_cudart::memory::memory_copy_async;
    use prover::gkr::virtual_polys::init_and_teardown_base::materialize_virtual_inits_and_teardowns_base_address_setup_poly;
    use serial_test::serial;
    use std::alloc::Global;
    use worker::Worker;

    fn sample_ext(seed: u32) -> E4 {
        E4::from_array_of_base([
            BF::new(seed),
            BF::new(seed + 1),
            BF::new(seed + 2),
            BF::new(seed + 3),
        ])
    }

    fn sample_external_challenges(seed: u32) -> GKRExternalChallenges<BF, E4> {
        GKRExternalChallenges {
            permutation_argument_linearization_challenges: std::array::from_fn(|idx| {
                sample_ext(seed + 10 + idx as u32)
            }),
            permutation_argument_additive_part: sample_ext(seed),
            _marker: std::marker::PhantomData,
        }
    }

    fn upload_base_poly(values: &[BF], context: &ProverContext) -> GpuBaseFieldPoly<BF> {
        let mut device = context
            .alloc(values.len(), AllocationPlacement::Top)
            .unwrap();
        memory_copy_async(&mut device, values, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        GpuBaseFieldPoly::new(device)
    }

    fn upload_ext_poly(values: &[E4], context: &ProverContext) -> GpuExtensionFieldPoly<E4> {
        let mut device = context
            .alloc(values.len(), AllocationPlacement::Top)
            .unwrap();
        memory_copy_async(&mut device, values, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        GpuExtensionFieldPoly::new(device)
    }

    fn read_ext_poly(poly: &GpuExtensionFieldPoly<E4>, context: &ProverContext) -> Vec<E4> {
        let mut host = vec![E4::ZERO; poly.len()];
        memory_copy_async(&mut host, poly.as_device_slice(), context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        host
    }

    fn read_base_allocation(values: &DeviceAllocation<BF>, context: &ProverContext) -> Vec<BF> {
        let mut host = vec![BF::ZERO; values.len()];
        memory_copy_async(&mut host, values, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        host
    }

    fn empty_constraints() -> NoFieldMaxQuadraticConstraintsGKRRelation {
        NoFieldMaxQuadraticConstraintsGKRRelation {
            quadratic_terms: Vec::new().into_boxed_slice(),
            linear_terms: Vec::new().into_boxed_slice(),
            constants: Vec::new().into_boxed_slice(),
        }
    }

    fn make_empty_forward_setup(
        trace_len: usize,
        lookup_additive_challenge: E4,
        context: &ProverContext,
    ) -> GpuGKRForwardSetup<E4> {
        let mut d_lookup_challenges: crate::primitives::context::DeviceAllocation<E4> = context
            .alloc(3, crate::allocator::tracker::AllocationPlacement::BestFit)
            .unwrap();
        era_cudart::memory::memory_copy_async(
            &mut d_lookup_challenges,
            &[E4::ONE, lookup_additive_challenge, E4::ZERO][..],
            context.get_exec_stream(),
        )
        .unwrap();
        crate::prover::gkr::setup::schedule_forward_setup_for_shape::<E4>(
            None,
            trace_len,
            0,
            0,
            false,
            d_lookup_challenges,
            context,
        )
        .unwrap()
    }

    fn expected_pairwise_reduction(values: &[E4]) -> Vec<E4> {
        values
            .chunks_exact(2)
            .map(|chunk| {
                let mut value = chunk[0];
                value.mul_assign(&chunk[1]);
                value
            })
            .collect()
    }

    fn expected_lookup_pair_reduction(num: &[E4], den: &[E4]) -> (Vec<E4>, Vec<E4>) {
        let mut reduced_num = Vec::with_capacity(num.len() / 2);
        let mut reduced_den = Vec::with_capacity(den.len() / 2);

        for (num_pair, den_pair) in num.chunks_exact(2).zip(den.chunks_exact(2)) {
            let mut left_term = num_pair[0];
            left_term.mul_assign(&den_pair[1]);
            let mut right_term = num_pair[1];
            right_term.mul_assign(&den_pair[0]);
            left_term.add_assign(&right_term);
            reduced_num.push(left_term);

            let mut den_value = den_pair[0];
            den_value.mul_assign(&den_pair[1]);
            reduced_den.push(den_value);
        }

        (reduced_num, reduced_den)
    }

    fn expected_init_value(
        row: usize,
        address_high_bits: u32,
        high_bits_shift: u32,
        address_low: &[BF],
        address_high: &[BF],
        external_challenges: &GKRExternalChallenges<BF, E4>,
    ) -> E4 {
        let mut result = external_challenges.permutation_argument_additive_part;
        result.add_assign_base(&BF::from_u32_unchecked(AddressSpaceType::RAM as u32));

        let mut address_low_term = external_challenges
            .permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
        address_low_term.mul_assign_by_base(&address_low[row]);
        result.add_assign(&address_low_term);

        let mut address_high_value = address_high[row];
        address_high_value.add_assign(&BF::from_u32_unchecked(
            address_high_bits << high_bits_shift,
        ));
        let mut address_high_term = external_challenges
            .permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
        address_high_term.mul_assign_by_base(&address_high_value);
        result.add_assign(&address_high_term);

        result
    }

    fn expected_teardown_value(
        row: usize,
        address_high_bits: u32,
        high_bits_shift: u32,
        timestamp_offsets: [usize; 2],
        value_offsets: [usize; 2],
        base_layer_memory_sources: [&[BF]; 4],
        address_low: &[BF],
        address_high: &[BF],
        external_challenges: &GKRExternalChallenges<BF, E4>,
    ) -> E4 {
        let mut result = expected_init_value(
            row,
            address_high_bits,
            high_bits_shift,
            address_low,
            address_high,
            external_challenges,
        );

        for (idx, offset) in [
            (
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX,
                timestamp_offsets[0],
            ),
            (
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX,
                timestamp_offsets[1],
            ),
            (
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
                value_offsets[0],
            ),
            (
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
                value_offsets[1],
            ),
        ] {
            let mut term = external_challenges.permutation_argument_linearization_challenges[idx];
            term.mul_assign_by_base(&base_layer_memory_sources[offset][row]);
            result.add_assign(&term);
        }

        result
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn forward_cache_single_column_lookup_synthesizes_virtual_setup_values() {
        let context = make_test_context(256, 32);
        let mappings_range16 = [0u32, 1, 65_535, 65_536, 70_000, 42, 7, 2];
        let mappings_timestamp = [0u32, 1, (1 << 19) - 1, 1 << 19, (1 << 19) + 1, 42, 7, 2];
        let trace_len = mappings_range16.len();

        let mut range16_dev = context.alloc(trace_len, AllocationPlacement::Top).unwrap();
        memory_copy_async(
            &mut range16_dev,
            &mappings_range16,
            context.get_exec_stream(),
        )
        .unwrap();
        let mut timestamp_dev = context.alloc(trace_len, AllocationPlacement::Top).unwrap();
        memory_copy_async(
            &mut timestamp_dev,
            &mappings_timestamp,
            context.get_exec_stream(),
        )
        .unwrap();
        let mut out_range16 = context.alloc(trace_len, AllocationPlacement::Top).unwrap();
        let mut out_timestamp = context.alloc(trace_len, AllocationPlacement::Top).unwrap();

        let mut batch: GpuGKRForwardCacheBatch<E4> = GpuGKRForwardCacheBatch::default();
        batch.count = 2;
        batch.descriptors[0] = GpuGKRForwardCacheDescriptor {
            kind: GpuGKRForwardCacheKind::SingleColumnLookup,
            mapping: range16_dev.as_ptr(),
            setup_source_kind: GpuBaseFieldSourceKind::VirtualRangeCheck16Bits,
            base_output: out_range16.as_mut_ptr(),
            ..GpuGKRForwardCacheDescriptor::default()
        };
        batch.descriptors[1] = GpuGKRForwardCacheDescriptor {
            kind: GpuGKRForwardCacheKind::SingleColumnLookup,
            mapping: timestamp_dev.as_ptr(),
            setup_source_kind: GpuBaseFieldSourceKind::VirtualRangeCheckTimestamp,
            base_output: out_timestamp.as_mut_ptr(),
            ..GpuGKRForwardCacheDescriptor::default()
        };

        launch_forward_cache(batch, trace_len, &context).unwrap();

        let expected_range16 = mappings_range16
            .iter()
            .map(|&value| {
                if value < (1 << 16) {
                    BF::new(value)
                } else {
                    BF::ZERO
                }
            })
            .collect::<Vec<_>>();
        let expected_timestamp = mappings_timestamp
            .iter()
            .map(|&value| {
                if value < (1 << 19) {
                    BF::new(value)
                } else {
                    BF::ZERO
                }
            })
            .collect::<Vec<_>>();

        assert_eq!(
            read_base_allocation(&out_range16, &context),
            expected_range16
        );
        assert_eq!(
            read_base_allocation(&out_timestamp, &context),
            expected_timestamp
        );
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn materialize_inits_and_teardowns_initial_pair_matches_cpu_for_init_and_teardown() {
        let context = make_test_context(256, 32);
        let trace_len = 1usize << 14;
        let worker = Worker::new();
        let address_high_bits = [1u32, 5u32];
        let high_bits_shift = high_bits_offset_for_inits_and_teardowns::<2>(trace_len);
        let external_challenges = sample_external_challenges(300);
        let setup = [
            GKRAddress::VirtualSetup(VirtualSetupPoly::InitsAndTeardownsLow),
            GKRAddress::VirtualSetup(VirtualSetupPoly::InitsAndTeardownsHigh),
        ];

        let (address_low, address_high) =
            materialize_virtual_inits_and_teardowns_base_address_setup_poly::<BF, Global, 2>(
                trace_len.trailing_zeros(),
                &worker,
            );
        let timestamp_low = (0..trace_len)
            .map(|idx| BF::new((100 + idx) as u32))
            .collect::<Vec<_>>();
        let timestamp_high = (0..trace_len)
            .map(|idx| BF::new((200 + idx) as u32))
            .collect::<Vec<_>>();
        let value_low = (0..trace_len)
            .map(|idx| BF::new((300 + idx) as u32))
            .collect::<Vec<_>>();
        let value_high = (0..trace_len)
            .map(|idx| BF::new((400 + idx) as u32))
            .collect::<Vec<_>>();

        let mut storage = GpuGKRStorage::<BF, E4>::default();
        storage.insert_base_field_at_layer(
            0,
            GKRAddress::BaseLayerMemory(0),
            upload_base_poly(&timestamp_low, &context),
        );
        storage.insert_base_field_at_layer(
            0,
            GKRAddress::BaseLayerMemory(1),
            upload_base_poly(&timestamp_high, &context),
        );
        storage.insert_base_field_at_layer(
            0,
            GKRAddress::BaseLayerMemory(2),
            upload_base_poly(&value_low, &context),
        );
        storage.insert_base_field_at_layer(
            0,
            GKRAddress::BaseLayerMemory(3),
            upload_base_poly(&value_high, &context),
        );

        let init_output = GpuExtensionFieldPoly::<E4>::new(
            context
                .alloc(trace_len, AllocationPlacement::BestFit)
                .unwrap(),
        );
        materialize_inits_and_teardowns_initial_pair_into(
            &storage,
            &init_output,
            &InitsOrTeardownsTimestampAndValue::Init,
            setup,
            address_high_bits,
            high_bits_shift,
            &external_challenges,
            trace_len,
            &context,
        )
        .unwrap();
        let teardown_output = GpuExtensionFieldPoly::<E4>::new(
            context
                .alloc(trace_len, AllocationPlacement::BestFit)
                .unwrap(),
        );
        materialize_inits_and_teardowns_initial_pair_into(
            &storage,
            &teardown_output,
            &InitsOrTeardownsTimestampAndValue::Teardown {
                lhs_timestamp: [0, 1],
                lhs_value: [2, 3],
                rhs_timestamp: [1, 0],
                rhs_value: [3, 2],
            },
            setup,
            address_high_bits,
            high_bits_shift,
            &external_challenges,
            trace_len,
            &context,
        )
        .unwrap();

        let expected_init = (0..trace_len)
            .map(|row| {
                let lhs = expected_init_value(
                    row,
                    address_high_bits[0],
                    high_bits_shift,
                    address_low.as_ref(),
                    address_high.as_ref(),
                    &external_challenges,
                );
                let rhs = expected_init_value(
                    row,
                    address_high_bits[1],
                    high_bits_shift,
                    address_low.as_ref(),
                    address_high.as_ref(),
                    &external_challenges,
                );
                let mut value = lhs;
                value.mul_assign(&rhs);
                value
            })
            .collect::<Vec<_>>();
        let base_layer_memory_sources = [
            timestamp_low.as_slice(),
            timestamp_high.as_slice(),
            value_low.as_slice(),
            value_high.as_slice(),
        ];
        let expected_teardown = (0..trace_len)
            .map(|row| {
                let lhs = expected_teardown_value(
                    row,
                    address_high_bits[0],
                    high_bits_shift,
                    [0, 1],
                    [2, 3],
                    base_layer_memory_sources,
                    address_low.as_ref(),
                    address_high.as_ref(),
                    &external_challenges,
                );
                let rhs = expected_teardown_value(
                    row,
                    address_high_bits[1],
                    high_bits_shift,
                    [1, 0],
                    [3, 2],
                    base_layer_memory_sources,
                    address_low.as_ref(),
                    address_high.as_ref(),
                    &external_challenges,
                );
                let mut value = lhs;
                value.mul_assign(&rhs);
                value
            })
            .collect::<Vec<_>>();

        assert_eq!(read_ext_poly(&init_output, &context), expected_init);
        assert_eq!(read_ext_poly(&teardown_output, &context), expected_teardown);
    }

    #[test]
    #[serial]
    fn forward_layer_lowering_and_launch_match_expected_outputs() {
        let context = make_test_context(256, 32);
        let trace_len = 8;
        let copy_input = GKRAddress::BaseLayerMemory(0);
        let lookup_lhs = GKRAddress::BaseLayerMemory(1);
        let lookup_rhs = GKRAddress::BaseLayerWitness(0);
        let product_lhs = GKRAddress::InnerLayer {
            layer: 0,
            offset: 0,
        };
        let product_rhs = GKRAddress::InnerLayer {
            layer: 0,
            offset: 1,
        };
        let copy_output = GKRAddress::InnerLayer {
            layer: 1,
            offset: 0,
        };
        let product_output = GKRAddress::InnerLayer {
            layer: 1,
            offset: 1,
        };
        let lookup_num_output = GKRAddress::InnerLayer {
            layer: 1,
            offset: 2,
        };
        let lookup_den_output = GKRAddress::InnerLayer {
            layer: 1,
            offset: 3,
        };

        let copy_values = (0..trace_len)
            .map(|idx| BF::new((idx + 1) as u32))
            .collect::<Vec<_>>();
        let lookup_lhs_values = [2u32, 3, 5, 7, 11, 13, 17, 19].map(BF::new);
        let lookup_rhs_values = [23u32, 29, 31, 37, 41, 43, 47, 53].map(BF::new);
        let product_lhs_values = (0..trace_len)
            .map(|idx| sample_ext(10 + idx as u32))
            .collect::<Vec<_>>();
        let product_rhs_values = (0..trace_len)
            .map(|idx| sample_ext(30 + idx as u32))
            .collect::<Vec<_>>();
        let lookup_additive_challenge = sample_ext(90);

        let mut storage = GpuGKRStorage::<BF, E4>::default();
        storage.insert_base_field_at_layer(0, copy_input, upload_base_poly(&copy_values, &context));
        storage.insert_base_field_at_layer(
            0,
            lookup_lhs,
            upload_base_poly(&lookup_lhs_values, &context),
        );
        storage.insert_base_field_at_layer(
            0,
            lookup_rhs,
            upload_base_poly(&lookup_rhs_values, &context),
        );
        storage.insert_extension_at_layer(
            0,
            product_lhs,
            upload_ext_poly(&product_lhs_values, &context),
        );
        storage.insert_extension_at_layer(
            0,
            product_rhs,
            upload_ext_poly(&product_rhs_values, &context),
        );

        let mut lookup_additive_device = context.alloc(1, AllocationPlacement::BestFit).unwrap();
        set_by_val(
            lookup_additive_challenge,
            lookup_additive_device.deref_mut(),
            context.get_exec_stream(),
        )
        .unwrap();
        context.get_exec_stream().synchronize().unwrap();

        let layer = GKRLayerDescription {
            layer: 0,
            gates_with_external_connections: Vec::new(),
            cached_relations: BTreeMap::new(),
            intermediate_layer_width: None,
            gates: vec![
                GateArtifacts {
                    output_layer: 1,
                    enforced_relation: NoFieldGKRRelation::CopyInExtensionField {
                        input: copy_input,
                        output: copy_output,
                    },
                },
                GateArtifacts {
                    output_layer: 1,
                    enforced_relation: NoFieldGKRRelation::TrivialProduct {
                        input: [product_lhs, product_rhs],
                        output: product_output,
                    },
                },
                GateArtifacts {
                    output_layer: 1,
                    enforced_relation: NoFieldGKRRelation::LookupPairFromMaterializedBaseInputs {
                        input: [lookup_lhs, lookup_rhs],
                        output: [lookup_num_output, lookup_den_output],
                    },
                },
                GateArtifacts {
                    output_layer: 1,
                    enforced_relation: NoFieldGKRRelation::EnforceConstraintsMaxQuadratic {
                        input: empty_constraints(),
                    },
                },
            ],
        };
        let external_challenges = sample_external_challenges(200);
        let stage1 = GpuGKRStage1Output::empty_for_tests(&context).unwrap();
        let forward_setup =
            make_empty_forward_setup(trace_len, lookup_additive_challenge, &context);

        assert_forward_layer_invariants(0, 2, &layer);
        let plan = build_flat_forward_plan::<E4>(
            0,
            &layer.gates,
            &layer.gates_with_external_connections,
            &BTreeMap::new(),
            &mut storage,
            &external_challenges,
            forward_setup.lookup_additive_part_device().as_ptr(),
            trace_len,
            &context,
        )
        .unwrap();
        super::super::forward_kernels::launch_flat_forward_layer::<E4>(
            &plan.desc, trace_len, &context,
        )
        .unwrap();
        commit_flat_forward_plan(1, &mut storage, plan);
        context.get_exec_stream().synchronize().unwrap();

        let copied = storage
            .try_get_base_poly(copy_output)
            .expect("copy output must remain in base storage");
        assert!(storage
            .get_base_layer(copy_input)
            .shares_backing_with(copied));

        let expected_product = product_lhs_values
            .iter()
            .zip(product_rhs_values.iter())
            .map(|(lhs, rhs)| {
                let mut value = *lhs;
                value.mul_assign(rhs);
                value
            })
            .collect::<Vec<_>>();
        assert_eq!(
            read_ext_poly(storage.get_ext_poly(product_output), &context),
            expected_product
        );

        let mut expected_lookup_num = Vec::with_capacity(trace_len);
        let mut expected_lookup_den = Vec::with_capacity(trace_len);
        for (&lhs, &rhs) in lookup_lhs_values.iter().zip(lookup_rhs_values.iter()) {
            let mut shifted_lhs = ext_from_base::<E4>(lhs);
            shifted_lhs.add_assign(&lookup_additive_challenge);
            let mut shifted_rhs = ext_from_base::<E4>(rhs);
            shifted_rhs.add_assign(&lookup_additive_challenge);

            let mut num = shifted_lhs;
            num.add_assign(&shifted_rhs);
            let mut den = shifted_lhs;
            den.mul_assign(&shifted_rhs);

            expected_lookup_num.push(num);
            expected_lookup_den.push(den);
        }

        assert_eq!(
            read_ext_poly(storage.get_ext_poly(lookup_num_output), &context),
            expected_lookup_num
        );
        assert_eq!(
            read_ext_poly(storage.get_ext_poly(lookup_den_output), &context),
            expected_lookup_den
        );
    }

    #[test]
    #[serial]
    fn dimension_reducing_forward_tower_matches_reference() {
        let context = make_test_context(1024, 32);
        // initial_trace_log_2 = 11, final_trace_log_2 = 0 → 11 rounds total.
        // With log_block = 8: one 8-round body launch (grid 2^3 = 8) + one 3-round tail launch
        // (grid 1, parallel streams). Exercises both body and tail code paths.
        let initial_trace_log_2 = 11usize;
        let final_trace_log_2 = 0usize;
        let initial_trace_len = 1usize << initial_trace_log_2;
        let current_layer_idx = 3usize;

        let read_set = GKRAddress::InnerLayer {
            layer: current_layer_idx,
            offset: 0,
        };
        let write_set = GKRAddress::InnerLayer {
            layer: current_layer_idx,
            offset: 1,
        };
        let lookup16_num = GKRAddress::InnerLayer {
            layer: current_layer_idx,
            offset: 2,
        };
        let lookup16_den = GKRAddress::InnerLayer {
            layer: current_layer_idx,
            offset: 3,
        };
        let timestamp_num = GKRAddress::InnerLayer {
            layer: current_layer_idx,
            offset: 4,
        };
        let timestamp_den = GKRAddress::InnerLayer {
            layer: current_layer_idx,
            offset: 5,
        };
        let generic_num = GKRAddress::InnerLayer {
            layer: current_layer_idx,
            offset: 6,
        };
        let generic_den = GKRAddress::InnerLayer {
            layer: current_layer_idx,
            offset: 7,
        };

        let read_values = (0..initial_trace_len)
            .map(|idx| sample_ext(100 + idx as u32))
            .collect::<Vec<_>>();
        let write_values = (0..initial_trace_len)
            .map(|idx| sample_ext(200 + idx as u32))
            .collect::<Vec<_>>();
        let lookup16_num_values = (0..initial_trace_len)
            .map(|idx| sample_ext(300 + idx as u32))
            .collect::<Vec<_>>();
        let lookup16_den_values = (0..initial_trace_len)
            .map(|idx| sample_ext(400 + idx as u32))
            .collect::<Vec<_>>();
        let timestamp_num_values = (0..initial_trace_len)
            .map(|idx| sample_ext(500 + idx as u32))
            .collect::<Vec<_>>();
        let timestamp_den_values = (0..initial_trace_len)
            .map(|idx| sample_ext(600 + idx as u32))
            .collect::<Vec<_>>();
        let generic_num_values = (0..initial_trace_len)
            .map(|idx| sample_ext(700 + idx as u32))
            .collect::<Vec<_>>();
        let generic_den_values = (0..initial_trace_len)
            .map(|idx| sample_ext(800 + idx as u32))
            .collect::<Vec<_>>();

        let mut storage = GpuGKRStorage::<BF, E4>::default();
        for (address, values) in [
            (read_set, &read_values),
            (write_set, &write_values),
            (lookup16_num, &lookup16_num_values),
            (lookup16_den, &lookup16_den_values),
            (timestamp_num, &timestamp_num_values),
            (timestamp_den, &timestamp_den_values),
            (generic_num, &generic_num_values),
            (generic_den, &generic_den_values),
        ] {
            storage.insert_extension_at_layer(
                current_layer_idx,
                address,
                upload_ext_poly(values, &context),
            );
        }

        let initial_output_map = BTreeMap::from([
            (OutputType::PermutationProduct, vec![read_set, write_set]),
            (OutputType::Lookup16Bits, vec![lookup16_num, lookup16_den]),
            (
                OutputType::LookupTimestamps,
                vec![timestamp_num, timestamp_den],
            ),
            (OutputType::GenericLookup, vec![generic_num, generic_den]),
        ]);

        let mut tracing_ranges = Vec::new();
        let (final_layer_idx, dim_reducing_inputs) = schedule_dimension_reduction_forward::<E4>(
            &mut storage,
            current_layer_idx,
            initial_output_map,
            initial_trace_log_2,
            final_trace_log_2,
            None,
            &mut tracing_ranges,
            &context,
        )
        .unwrap();
        context.get_exec_stream().synchronize().unwrap();

        let total_rounds = initial_trace_log_2 - final_trace_log_2;
        assert_eq!(final_layer_idx, current_layer_idx + total_rounds - 1);

        // Walk every intermediate layer and compare against a fresh CPU reduction.
        let mut expected_read = read_values.clone();
        let mut expected_write = write_values.clone();
        let mut expected_lookup16 = (lookup16_num_values.clone(), lookup16_den_values.clone());
        let mut expected_timestamp = (timestamp_num_values.clone(), timestamp_den_values.clone());
        let mut expected_generic = (generic_num_values.clone(), generic_den_values.clone());

        for round_idx in 0..total_rounds {
            expected_read = expected_pairwise_reduction(&expected_read);
            expected_write = expected_pairwise_reduction(&expected_write);
            expected_lookup16 =
                expected_lookup_pair_reduction(&expected_lookup16.0, &expected_lookup16.1);
            expected_timestamp =
                expected_lookup_pair_reduction(&expected_timestamp.0, &expected_timestamp.1);
            expected_generic =
                expected_lookup_pair_reduction(&expected_generic.0, &expected_generic.1);

            let layer_description = dim_reducing_inputs
                .get(&(current_layer_idx + round_idx))
                .expect("dim reducing description present for round");

            let permutation_outputs = &layer_description[&OutputType::PermutationProduct].output;
            assert_eq!(
                read_ext_poly(storage.get_ext_poly(permutation_outputs[0]), &context),
                expected_read,
                "read chain mismatch at round {}",
                round_idx
            );
            assert_eq!(
                read_ext_poly(storage.get_ext_poly(permutation_outputs[1]), &context),
                expected_write,
                "write chain mismatch at round {}",
                round_idx
            );

            for (arg, expected) in [
                (OutputType::Lookup16Bits, &expected_lookup16),
                (OutputType::LookupTimestamps, &expected_timestamp),
                (OutputType::GenericLookup, &expected_generic),
            ] {
                let lookup_outputs = &layer_description[&arg].output;
                assert_eq!(
                    read_ext_poly(storage.get_ext_poly(lookup_outputs[0]), &context),
                    expected.0,
                    "{:?} num chain mismatch at round {}",
                    arg,
                    round_idx
                );
                assert_eq!(
                    read_ext_poly(storage.get_ext_poly(lookup_outputs[1]), &context),
                    expected.1,
                    "{:?} den chain mismatch at round {}",
                    arg,
                    round_idx
                );
            }
        }
    }
}
