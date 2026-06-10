use std::collections::BTreeMap;
use std::ops::DerefMut;
use std::ptr::null;
use std::sync::Arc;

use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;

use super::backward::GpuGKRDimensionReducingBackwardState;
use super::gkr_address_audit::AddressClass;
use super::setup::{bootstrap_storage_from_trace_holders, GpuGKRForwardSetup};
use super::stage1::GpuGKRStage1Output;
use super::transform::normalize_compiled_circuit_for_gpu;
use super::{
    GpuBaseFieldPoly, GpuBaseFieldSourceKind, GpuExtensionFieldPoly, GpuGKRLayerSource,
    GpuGKRStorage,
};
use crate::allocator::tracker::AllocationPlacement;
use crate::ops::simple::{
    add_into_y, mul, mul_into_y, set_by_val, Add, BinaryOp, Mul, SetByRef, SetByVal, Sub,
};
use crate::primitives::context::{DeviceAllocation, HostAllocation};
use crate::primitives::device_structures::{DeviceMatrixChunkMutImpl, DeviceVectorChunk};
use crate::primitives::device_tracing::Range;
use crate::primitives::field::BF;
use crate::prover::ProverContext;

pub(crate) struct GpuGKRForwardOutput<B, E> {
    tracing_ranges: Vec<Range>,
    pub(crate) storage: GpuGKRStorage<B, E>,
    pub(crate) initial_layer_for_sumcheck: usize,
    pub(crate) dimension_reducing_inputs:
        BTreeMap<usize, BTreeMap<OutputType, DimensionReducingInputOutput>>,
}

#[allow(dead_code)]
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
    /// View over the packed flat evaluations buffer (the prefix of the
    /// shared backing Arc that holds all reduced-output polys for the
    /// initial sumcheck layer in BTreeMap iteration order).
    pub(crate) fn device_flat_evaluations(&self) -> &DeviceSlice<E> {
        &self.flat_evaluations_backing[..self.flat_total_len]
    }

    #[cfg(test)]
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

    #[cfg(test)]
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

pub(crate) mod kernels;
pub(super) use kernels::*;

mod cache_relation;
mod dimension_reducing;
mod flat_plan;
pub(crate) mod generated_layer0;
mod materialize_helpers;

use cache_relation::{lower_cache_relation, LoweredCacheRelationOutput};

#[cfg(test)]
use crate::upstream::{
    high_bits_offset_for_inits_and_teardowns, CompiledAddressSpaceRelationStrict,
    CompiledAddressStrict, CompiledMemoryTimestamp, NoFieldSpecialMemoryContributionRelation,
    RamWordRepresentation, VirtualSetupPoly,
};
use crate::upstream::{
    AddressSpaceType, DimensionReducingInputOutput, Field, FieldExtension, GKRAddress,
    GKRCircuitArtifact, GKRExternalChallenges, GKRLayerDescription,
    InitsOrTeardownsTimestampAndValue, NoFieldGKRCacheRelation, NoFieldGKRRelation, OutputType,
    PrimeField, DECODER_LOOKUP_FORMAL_SET_INDEX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
};
use dimension_reducing::schedule_dimension_reduction_forward;
use materialize_helpers::{
    materialize_inits_and_teardowns_initial_pair_into, scale_and_add_base_column_in_place,
};

use flat_plan::{
    analyze_forward_lookup_usage, build_flat_forward_plan, cache_relation_layer,
    commit_flat_forward_plan, release_forward_lookup_resources_after_layer,
};

#[allow(clippy::too_many_arguments)]
pub(crate) fn schedule_forward_pass<E>(
    setup_trace_holder: Option<&crate::prover::trace::holder::TraceHolder<BF>>,
    synthetic_setup_trace_holder: Option<&crate::prover::trace::holder::TraceHolder<BF>>,
    stage1: &mut GpuGKRStage1Output,
    forward_setup: &mut GpuGKRForwardSetup<E>,
    compiled_circuit: &GKRCircuitArtifact<BF>,
    external_challenges: &GKRExternalChallenges<BF, E>,
    final_trace_size_log_2: usize,
    output_evaluations_slab: Option<ForwardOutputSlabTarget<E>>,
    is_add_sub: bool,
    context: &ProverContext,
) -> CudaResult<GpuGKRForwardOutput<BF, E>>
where
    E: FieldExtension<BF> + Field + SetByRef + SetByVal + crate::prover::gkr::ForwardKernels,
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
    bind_scratch_space_into_storage(&compiled_circuit, stage1, &mut storage);

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

    E::schedule_lookup_gamma_consts_prelude(
        forward_setup.lookup_additive_part_device().as_ptr(),
        context,
    )?;

    // Resolve the layer-0 A/B switch once. The generated fused kernel is
    // specific to the add_sub_lui_auipc_mop circuit with a cached layout; if the
    // env is set for any other circuit we must panic loudly rather than emit a
    // wrong proof.
    let use_generated_layer0 = generated_layer0::generated_layer0_enabled();
    let is_add_sub_cached =
        generated_layer0::is_add_sub_cached_layout(is_add_sub, &compiled_circuit);
    if use_generated_layer0 && !is_add_sub_cached {
        panic!(
            "{} is enabled but the circuit is not add_sub_lui_auipc_mop with a cached layout \
             (is_add_sub={is_add_sub}, has_decoder_lookup={}); the generated layer-0 kernel is \
             add_sub-cached-specific",
            generated_layer0::AB_GKR_FWD_GENERATED_LAYER0_ENV,
            compiled_circuit.has_decoder_lookup,
        );
    }
    let generated_layer0_active = use_generated_layer0 && is_add_sub_cached;

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
            generated_layer0_active,
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

#[allow(clippy::too_many_arguments)]
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
    generated_layer0_active: bool,
    context: &ProverContext,
) -> CudaResult<()>
where
    E: FieldExtension<BF> + Field + SetByRef + SetByVal + crate::prover::gkr::ForwardKernels,
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

    // A/B switch: for layer 0 of the add_sub-cached circuit, the pre-generated
    // fused kernel produces the COMPLETE layer-0 output (all caches + all inner
    // gate outputs) in one launch, replacing the normal cache-relation /
    // materialized-lookup-input / flat-forward-plan scheduling below.
    if generated_layer0_active && layer_idx == 0 {
        let generated_range = Range::new("gkr.forward.layer.0.generated")?;
        generated_range.start(stream)?;
        assert_forward_layer_invariants(layer_idx, total_layers, layer);
        generated_layer0::schedule_generated_layer0(
            layer,
            storage,
            forward_setup,
            external_challenges,
            trace_len,
            context,
        )?;
        generated_range.end(stream)?;
        tracing_ranges.push(generated_range);
        return Ok(());
    }

    let cached_relations_ref = &layer.cached_relations;
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
        &layer.gates,
        &layer.gates_with_external_connections,
        stage1,
        forward_setup,
        decoder_predicate_address,
        &compiled_circuit.scratch_space_mapping,
        storage,
        external_challenges,
        trace_len,
        context,
    )?;
    for desc in plan.descs.iter() {
        if kernels::flat_desc_has_work(desc) {
            kernels::launch_flat_forward_layer(desc, trace_len, context)?;
        }
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
                "GPU no-cache decoder dispatch expects the decoder predicate input"
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
    E: FieldExtension<BF> + Field + SetByRef + SetByVal + crate::prover::gkr::ForwardKernels,
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

/// Register `stage1.scratch_space_trace` as the consolidated `AddressClass::ScratchSpace`
/// backing at layer 0, plus per-`ScratchSpace` poly views. Mirrors the trace-holder
/// pattern in `bind_trace_holder_columns_into_storage`: scratch is a first-class
/// trace-aligned class (poly_idx == scratch_idx), so the layout-driven backward
/// path (`build_backing_ranges`, `register_flat_base_folding_for_layer`,
/// `allocate_base_view`) picks it up uniformly with witness/memory.
///
/// Called once by `schedule_forward_pass` after the storage layout is bound and
/// before per-layer scheduling begins.
fn bind_scratch_space_into_storage<E>(
    compiled_circuit: &GKRCircuitArtifact<BF>,
    stage1: &GpuGKRStage1Output,
    storage: &mut GpuGKRStorage<BF, E>,
) {
    let Some(scratch_space_trace) = stage1.scratch_space_trace.as_ref() else {
        return;
    };
    if compiled_circuit.scratch_space_size == 0 {
        return;
    }
    let trace_len = compiled_circuit.trace_len;
    let scratch_space_size = compiled_circuit.scratch_space_size;
    for scratch_idx in 0..scratch_space_size {
        let address = GKRAddress::ScratchSpace(scratch_idx);
        if storage.try_get_base_poly(address).is_some() {
            continue;
        }
        let offset = scratch_idx * trace_len;
        storage.insert_base_field_at_layer(
            0,
            address,
            GpuBaseFieldPoly::from_arc(Arc::clone(scratch_space_trace), offset, trace_len),
        );
    }
    if storage.layers.is_empty() {
        storage
            .layers
            .resize_with(1, crate::prover::gkr::GpuGKRLayerSource::default);
    }
    let prev = storage.layers[0]
        .base_class_backings
        .insert(AddressClass::ScratchSpace, Arc::clone(scratch_space_trace));
    assert!(
        prev.is_none(),
        "scratch_space backing already registered for layer 0 AddressClass::ScratchSpace"
    );
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

pub(super) fn vector_lookup_mapping_ptr(
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

pub(super) fn single_column_lookup_mapping_ptr(
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
    E: FieldExtension<BF> + Field + SetByRef + SetByVal + crate::prover::gkr::ForwardKernels,
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

#[cfg(test)]
mod tests;
