use std::collections::BTreeMap;
use std::mem::ManuallyDrop;
use std::ops::DerefMut;
use std::ptr::null;
use std::sync::Arc;

use cs::definitions::{
    gkr::{AddressSpaceType, RamWordRepresentation, DECODER_LOOKUP_FORMAL_SET_INDEX},
    GKRAddress, VirtualSetupPoly, MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX,
    MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
    MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX,
    MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX, MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
    MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
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
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use field::{Field, FieldExtension, PrimeField};
use prover::gkr::high_bits_offset_for_inits_and_teardowns;
use prover::gkr::prover::dimension_reduction::forward::DimensionReducingInputOutput;
use prover::gkr::prover::GKRExternalChallenges;

use super::backward::GpuGKRDimensionReducingBackwardState;
use super::setup::{bootstrap_storage_from_trace_holders, GpuGKRForwardSetup};
use super::stage1::GpuGKRStage1Output;
use super::transform::normalize_compiled_circuit_for_gpu;
use super::{GpuBaseFieldPoly, GpuBaseFieldSourceKind, GpuExtensionFieldPoly, GpuGKRStorage};
use crate::allocator::tracker::AllocationPlacement;
use crate::ops::simple::{
    add_into_y, mul_into_y, set_by_ref, set_by_val, sub_into_x, Add, BinaryOp, Mul, SetByRef,
    SetByVal, Sub,
};
use crate::primitives::context::{DeviceAllocation, HostAllocation, ProverContext, UnsafeAccessor};
use crate::primitives::device_structures::DeviceVectorChunk;
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
    pub(crate) fn schedule_transcript_handoff(
        &self,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRTranscriptHandoff<E>> {
        let stream = context.get_exec_stream();
        let mut tracing_ranges = Vec::new();
        let handoff_range = Range::new("gkr.forward.transcript_handoff.schedule")?;
        handoff_range.start(stream)?;
        let reduced_outputs = self
            .dimension_reducing_inputs
            .get(&self.initial_layer_for_sumcheck)
            .expect("reduced outputs for initial sumcheck layer must exist");
        let mut explicit_evaluations = BTreeMap::new();
        for (output_type, reduced_io) in reduced_outputs.iter() {
            let [first_addr, second_addr]: [GKRAddress; 2] = reduced_io
                .output
                .clone()
                .try_into()
                .expect("transcript handoff expects exactly two reduced outputs per type");
            let first = schedule_ext_poly_readback(&self.storage, first_addr, context)?;
            let second = schedule_ext_poly_readback(&self.storage, second_addr, context)?;
            explicit_evaluations.insert(*output_type, [first, second]);
        }
        handoff_range.end(stream)?;
        tracing_ranges.push(handoff_range);

        Ok(GpuGKRTranscriptHandoff {
            _tracing_ranges: tracing_ranges,
            explicit_evaluations,
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
    context: &ProverContext,
) -> CudaResult<GpuGKRForwardOutput<BF, E>>
where
    E: FieldExtension<BF>
        + Field
        + SetByRef
        + SetByVal
        + GpuGKRForwardKernelSet
        + GpuGKRForwardCacheKernelSet
        + GpuGKRVirtualBaseAccumKernelSet
        + GpuGKRDimensionReducingForwardKernelSet,
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
            &compiled_circuit,
            trace_len.trailing_zeros() as usize,
            final_trace_size_log_2,
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
        + GpuGKRForwardKernelSet
        + GpuGKRForwardCacheKernelSet
        + GpuGKRVirtualBaseAccumKernelSet,
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
    let cache_range = Range::new(format!("gkr.forward.layer.{layer_idx}.cache"))?;
    cache_range.start(stream)?;
    schedule_cache_relations(
        layer_idx,
        &layer.cached_relations,
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
    let lowered = lower_forward_layer(
        layer_idx,
        &layer.gates,
        &layer.gates_with_external_connections,
        &compiled_circuit.scratch_space_mapping,
        storage,
        stage1,
        forward_setup,
        external_challenges,
        decoder_predicate_address,
        forward_setup.lookup_additive_part_device().as_ptr(),
        trace_len,
        context,
    )?;
    for batch in &lowered.batches {
        launch_forward_layer(batch, trace_len, context)?;
    }
    commit_lowered_forward_layer(expected_output_layer, storage, lowered);
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
            let mut dst = alloc_ext(trace_len, context)?;
            let ext_output = dst.as_mut_ptr();
            outputs.push((*output, GpuExtensionFieldPoly::new(dst)));
            *descriptor = GpuGKRForwardCacheDescriptor {
                kind: GpuGKRForwardCacheKind::VectorizedLookup,
                mapping: mapping.as_ptr(),
                generic_lookup,
                decoder_mask: if is_decoder_lookup {
                    storage
                        .get_base_layer(
                            decoder_predicate_address
                                .expect("decoder lookup requires a decoder predicate column"),
                        )
                        .as_ptr()
                } else {
                    null()
                },
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
        let mut dst = alloc_base(trace_len, context)?;
        set_by_val(
            BF::from_u32_unchecked(input.constant),
            dst.deref_mut(),
            context.get_exec_stream(),
        )?;
        for (coeff, address) in input.linear_terms.iter() {
            scale_and_add_base_column_in_place(
                &mut dst,
                storage.get_base_layer(*address),
                BF::from_u32_unchecked(*coeff),
                context,
            )?;
        }
        storage.insert_base_field_at_layer(
            expected_output_layer,
            *output,
            GpuBaseFieldPoly::new(dst),
        );
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

fn build_forward_memory_tuple_expression_descriptor<E: FieldExtension<BF> + Field>(
    relation: &cs::gkr_compiler::NoFieldSpecialMemoryContributionRelation,
    storage: &GpuGKRStorage<BF, E>,
    external_challenges: &GKRExternalChallenges<BF, E>,
) -> GpuGKRForwardMemoryTupleExpressionDescriptor<E> {
    let mut descriptor = GpuGKRForwardMemoryTupleExpressionDescriptor {
        address_space_kind: GpuGKRForwardCacheAddressSpaceKind::Empty,
        address_space_ptr: null(),
        address_space_constant: BF::ZERO,
        constant_term: external_challenges.permutation_argument_additive_part,
        linear_inputs: [null(); MEMORY_TUPLE_LINEAR_TERMS],
        linear_challenges: [E::ZERO; MEMORY_TUPLE_LINEAR_TERMS],
    };
    let mut deferred_low_dynamic_term: Option<(*const BF, E)> = None;
    match relation.address_space {
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

    match &relation.address {
        CompiledAddressStrict::ConstantU16(c) => {
            let mut contribution = external_challenges
                .permutation_argument_linearization_challenges
                [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
            contribution.mul_assign_by_base(&BF::from_u32_unchecked(*c as u32));
            descriptor.constant_term.add_assign(&contribution);
        }
        CompiledAddressStrict::Constant(c) => {
            let mut contribution = external_challenges
                .permutation_argument_linearization_challenges
                [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
            contribution.mul_assign_by_base(&BF::from_u32_unchecked(*c));
            descriptor.constant_term.add_assign(&contribution);
        }
        CompiledAddressStrict::U16Space(offset) => {
            add_memory_tuple_linear_term(
                &mut GpuGKRForwardCacheDescriptor {
                    linear_inputs: descriptor.linear_inputs,
                    linear_challenges: descriptor.linear_challenges,
                    ..GpuGKRForwardCacheDescriptor::default()
                },
                MEMORY_TUPLE_ADDRESS_LOW_TERM,
                storage
                    .get_base_layer(GKRAddress::BaseLayerMemory(*offset))
                    .as_ptr(),
                external_challenges.permutation_argument_linearization_challenges
                    [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX],
            );
            descriptor.linear_inputs[MEMORY_TUPLE_ADDRESS_LOW_TERM] = storage
                .get_base_layer(GKRAddress::BaseLayerMemory(*offset))
                .as_ptr();
            descriptor.linear_challenges[MEMORY_TUPLE_ADDRESS_LOW_TERM] = external_challenges
                .permutation_argument_linearization_challenges
                [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
        }
        CompiledAddressStrict::U32Space([low, high]) => {
            descriptor.linear_inputs[MEMORY_TUPLE_ADDRESS_LOW_TERM] = storage
                .get_base_layer(GKRAddress::BaseLayerMemory(*low))
                .as_ptr();
            descriptor.linear_challenges[MEMORY_TUPLE_ADDRESS_LOW_TERM] = external_challenges
                .permutation_argument_linearization_challenges
                [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
            descriptor.linear_inputs[MEMORY_TUPLE_ADDRESS_HIGH_TERM] = storage
                .get_base_layer(GKRAddress::BaseLayerMemory(*high))
                .as_ptr();
            descriptor.linear_challenges[MEMORY_TUPLE_ADDRESS_HIGH_TERM] = external_challenges
                .permutation_argument_linearization_challenges
                [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
        }
        CompiledAddressStrict::U32SpaceSpecialIndirect {
            low_base,
            low_dynamic_offset,
            low_offset,
            high,
        } => {
            let low_challenge = external_challenges.permutation_argument_linearization_challenges
                [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
            let high_challenge = external_challenges.permutation_argument_linearization_challenges
                [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
            if *low_offset != 0 {
                let mut contribution = low_challenge;
                contribution.mul_assign_by_base(&BF::from_u32_unchecked(*low_offset));
                descriptor.constant_term.add_assign(&contribution);
            }
            descriptor.linear_inputs[MEMORY_TUPLE_ADDRESS_LOW_TERM] = storage
                .get_base_layer(GKRAddress::BaseLayerMemory(*low_base))
                .as_ptr();
            descriptor.linear_challenges[MEMORY_TUPLE_ADDRESS_LOW_TERM] = low_challenge;
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
            descriptor.linear_inputs[MEMORY_TUPLE_ADDRESS_HIGH_TERM] = storage
                .get_base_layer(GKRAddress::BaseLayerMemory(*high))
                .as_ptr();
            descriptor.linear_challenges[MEMORY_TUPLE_ADDRESS_HIGH_TERM] = high_challenge;
        }
        CompiledAddressStrict::U32SpaceGeneric(..) => {
            unimplemented!(
                "unsupported GPU memory tuple address relation: {:?}",
                relation.address
            )
        }
    }

    match &relation.timestamp {
        CompiledMemoryTimestamp::Zero => {}
        CompiledMemoryTimestamp::Normal(timestamp) => {
            descriptor.linear_inputs[MEMORY_TUPLE_TIMESTAMP_LOW_TERM] = storage
                .get_base_layer(GKRAddress::BaseLayerMemory(timestamp[0]))
                .as_ptr();
            descriptor.linear_challenges[MEMORY_TUPLE_TIMESTAMP_LOW_TERM] = external_challenges
                .permutation_argument_linearization_challenges
                [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
            if relation.timestamp_offset != 0 {
                let mut contribution = external_challenges
                    .permutation_argument_linearization_challenges
                    [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                contribution.mul_assign_by_base(&BF::from_u32_unchecked(relation.timestamp_offset));
                descriptor.constant_term.add_assign(&contribution);
            }
            descriptor.linear_inputs[MEMORY_TUPLE_TIMESTAMP_HIGH_TERM] = storage
                .get_base_layer(GKRAddress::BaseLayerMemory(timestamp[1]))
                .as_ptr();
            descriptor.linear_challenges[MEMORY_TUPLE_TIMESTAMP_HIGH_TERM] = external_challenges
                .permutation_argument_linearization_challenges
                [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX];
        }
    }

    match relation.value {
        RamWordRepresentation::Zero => {}
        RamWordRepresentation::U16Limbs(read_value) => {
            descriptor.linear_inputs[MEMORY_TUPLE_VALUE_LOW_TERM] = storage
                .get_base_layer(GKRAddress::BaseLayerMemory(read_value[0]))
                .as_ptr();
            descriptor.linear_challenges[MEMORY_TUPLE_VALUE_LOW_TERM] = external_challenges
                .permutation_argument_linearization_challenges
                [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX];
            descriptor.linear_inputs[MEMORY_TUPLE_VALUE_HIGH_TERM] = storage
                .get_base_layer(GKRAddress::BaseLayerMemory(read_value[1]))
                .as_ptr();
            descriptor.linear_challenges[MEMORY_TUPLE_VALUE_HIGH_TERM] = external_challenges
                .permutation_argument_linearization_challenges
                [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX];
        }
        RamWordRepresentation::U8Limbs(read_value_bytes) => {
            let byte_shift = BF::from_u32_unchecked(1 << 8);
            for (challenge_idx, low_term_idx, high_term_idx, low_offset, high_offset) in [
                (
                    MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
                    MEMORY_TUPLE_VALUE_LOW_TERM,
                    MEMORY_TUPLE_VALUE_LOW_EXTRA_TERM,
                    read_value_bytes[0],
                    read_value_bytes[1],
                ),
                (
                    MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
                    MEMORY_TUPLE_VALUE_HIGH_TERM,
                    MEMORY_TUPLE_VALUE_HIGH_EXTRA_TERM,
                    read_value_bytes[2],
                    read_value_bytes[3],
                ),
            ] {
                let challenge = external_challenges.permutation_argument_linearization_challenges
                    [challenge_idx];
                descriptor.linear_inputs[low_term_idx] = storage
                    .get_base_layer(GKRAddress::BaseLayerMemory(low_offset))
                    .as_ptr();
                descriptor.linear_challenges[low_term_idx] = challenge;
                let mut shifted = challenge;
                shifted.mul_assign_by_base(&byte_shift);
                descriptor.linear_inputs[high_term_idx] = storage
                    .get_base_layer(GKRAddress::BaseLayerMemory(high_offset))
                    .as_ptr();
                descriptor.linear_challenges[high_term_idx] = shifted;
            }
        }
    }

    if let Some((input, challenge)) = deferred_low_dynamic_term {
        let term_idx = descriptor
            .linear_inputs
            .iter()
            .position(|ptr| ptr.is_null())
            .expect("GPU memory tuple linear terms exceeded fixed descriptor capacity");
        descriptor.linear_inputs[term_idx] = input;
        descriptor.linear_challenges[term_idx] = challenge;
    }

    descriptor
}

fn forward_generic_lookup_ptr<E>(forward_setup: &GpuGKRForwardSetup<E>) -> *const E {
    if forward_setup.generic_lookup_len() > 0 {
        forward_setup.generic_lookup().as_ptr()
    } else {
        null()
    }
}

fn lower_forward_layer<E>(
    layer_idx: usize,
    lowered_gates: &[cs::gkr_compiler::GateArtifacts],
    lowered_gates_with_external_connections: &[cs::gkr_compiler::GateArtifacts],
    scratch_space_mapping: &BTreeMap<GKRAddress, usize>,
    storage: &GpuGKRStorage<BF, E>,
    stage1: &GpuGKRStage1Output,
    forward_setup: &GpuGKRForwardSetup<E>,
    external_challenges: &GKRExternalChallenges<BF, E>,
    decoder_predicate_address: Option<GKRAddress>,
    lookup_additive_challenge: *const E,
    trace_len: usize,
    context: &ProverContext,
) -> CudaResult<LoweredGpuGKRForwardLayer<E>>
where
    E: Field + FieldExtension<BF> + GpuGKRVirtualBaseAccumKernelSet + SetByVal,
    Add: BinaryOp<E, E, E>,
    Mul: BinaryOp<BF, E, E>,
    Mul: BinaryOp<E, E, E>,
{
    let expected_output_layer = layer_idx + 1;
    let total_gates = lowered_gates.len() + lowered_gates_with_external_connections.len();
    let mut batches = Vec::with_capacity(total_gates.div_ceil(GKR_FORWARD_MAX_GATES_PER_LAYER));
    let mut batch = GpuGKRForwardLayerBatch::new(lookup_additive_challenge);
    let mut batch_gate_idx = 0usize;

    let mut computed_extension_outputs = Vec::new();
    let mut aliased_base_outputs = Vec::new();
    let mut aliased_extension_outputs = Vec::new();
    assert!(
        forward_setup.generic_lookup_len() <= u32::MAX as usize,
        "generic lookup runtime too large for fused forward kernel"
    );
    let generic_lookup = forward_generic_lookup_ptr(forward_setup);
    let generic_lookup_len = forward_setup.generic_lookup_len() as u32;

    for gate in lowered_gates
        .iter()
        .chain(lowered_gates_with_external_connections.iter())
    {
        if batch_gate_idx == GKR_FORWARD_MAX_GATES_PER_LAYER {
            batch.gate_count = batch_gate_idx as u32;
            batches.push(batch);
            batch = GpuGKRForwardLayerBatch::new(lookup_additive_challenge);
            batch_gate_idx = 0;
        }
        assert_eq!(gate.output_layer, expected_output_layer);
        batch.descriptors[batch_gate_idx] = match &gate.enforced_relation {
            NoFieldGKRRelation::Copy { input, output } => {
                if let Some(source) = storage.try_get_base_poly(*input) {
                    aliased_base_outputs.push((*output, source.clone_shared()));
                } else {
                    aliased_extension_outputs
                        .push((*output, storage.get_ext_poly(*input).clone_shared()));
                }
                GpuGKRForwardGateDescriptor::no_op()
            }
            NoFieldGKRRelation::InitialGrandProductFromCaches { input, output }
            | NoFieldGKRRelation::TrivialProduct { input, output } => {
                let lhs = storage.get_ext_poly(input[0]);
                let rhs = storage.get_ext_poly(input[1]);
                let mut dst = alloc_ext(trace_len, context)?;
                let dst_ptr = dst.as_mut_ptr();
                computed_extension_outputs.push((*output, GpuExtensionFieldPoly::new(dst)));
                GpuGKRForwardGateDescriptor::with_product(lhs.as_ptr(), rhs.as_ptr(), dst_ptr)
            }
            NoFieldGKRRelation::MaskIntoIdentityProduct {
                input,
                mask,
                output,
            } => {
                let input = storage.get_ext_poly(*input);
                let mask = storage.get_base_layer(*mask);
                let mut dst = alloc_ext(trace_len, context)?;
                let dst_ptr = dst.as_mut_ptr();
                computed_extension_outputs.push((*output, GpuExtensionFieldPoly::new(dst)));
                GpuGKRForwardGateDescriptor::with_mask_identity(
                    input.as_ptr(),
                    mask.as_ptr(),
                    dst_ptr,
                )
            }
            NoFieldGKRRelation::AggregateLookupRationalPair { input, output } => {
                let [a, b] = input[0].map(|addr| storage.get_ext_poly(addr));
                let [c, d] = input[1].map(|addr| storage.get_ext_poly(addr));
                let mut num = alloc_ext(trace_len, context)?;
                let mut den = alloc_ext(trace_len, context)?;
                let num_ptr = num.as_mut_ptr();
                let den_ptr = den.as_mut_ptr();
                computed_extension_outputs.push((output[0], GpuExtensionFieldPoly::new(num)));
                computed_extension_outputs.push((output[1], GpuExtensionFieldPoly::new(den)));
                GpuGKRForwardGateDescriptor::with_lookup_pair(
                    a.as_ptr(),
                    b.as_ptr(),
                    c.as_ptr(),
                    d.as_ptr(),
                    num_ptr,
                    den_ptr,
                )
            }
            NoFieldGKRRelation::LookupWithCachedDensAndSetup {
                input,
                setup,
                output,
            } => {
                let a = storage.get_base_layer(input[0]);
                let b = storage.get_ext_poly(input[1]);
                let c = storage.get_base_layer(setup[0]);
                let d = storage.get_ext_poly(setup[1]);
                let mut num = alloc_ext(trace_len, context)?;
                let mut den = alloc_ext(trace_len, context)?;
                let num_ptr = num.as_mut_ptr();
                let den_ptr = den.as_mut_ptr();
                computed_extension_outputs.push((output[0], GpuExtensionFieldPoly::new(num)));
                computed_extension_outputs.push((output[1], GpuExtensionFieldPoly::new(den)));
                GpuGKRForwardGateDescriptor::with_lookup_cached_dens_and_setup(
                    a.as_ptr(),
                    b.as_ptr(),
                    c.as_ptr(),
                    d.as_ptr(),
                    num_ptr,
                    den_ptr,
                )
            }
            NoFieldGKRRelation::LookupPairFromMaterializedBaseInputs { input, output } => {
                let lhs = storage.get_base_layer(input[0]);
                let rhs = storage.get_base_layer(input[1]);
                let mut num = alloc_ext(trace_len, context)?;
                let mut den = alloc_ext(trace_len, context)?;
                let num_ptr = num.as_mut_ptr();
                let den_ptr = den.as_mut_ptr();
                computed_extension_outputs.push((output[0], GpuExtensionFieldPoly::new(num)));
                computed_extension_outputs.push((output[1], GpuExtensionFieldPoly::new(den)));
                GpuGKRForwardGateDescriptor::with_lookup_base_pair(
                    lhs.as_ptr(),
                    rhs.as_ptr(),
                    num_ptr,
                    den_ptr,
                )
            }
            NoFieldGKRRelation::LookupPairFromMaterializedVectorInputs { input, output }
            | NoFieldGKRRelation::LookupPairFromCachedVectorInputs { input, output } => {
                let lhs = storage.get_ext_poly(input[0]);
                let rhs = storage.get_ext_poly(input[1]);
                let mut num = alloc_ext(trace_len, context)?;
                let mut den = alloc_ext(trace_len, context)?;
                let num_ptr = num.as_mut_ptr();
                let den_ptr = den.as_mut_ptr();
                computed_extension_outputs.push((output[0], GpuExtensionFieldPoly::new(num)));
                computed_extension_outputs.push((output[1], GpuExtensionFieldPoly::new(den)));
                GpuGKRForwardGateDescriptor::with_lookup_ext_pair(
                    lhs.as_ptr(),
                    rhs.as_ptr(),
                    num_ptr,
                    den_ptr,
                )
            }
            NoFieldGKRRelation::LookupFromMaterializedBaseInputWithSetup {
                input,
                setup,
                output,
            } => {
                let b = storage.get_base_layer(*input);
                let c = storage.get_base_layer(setup[0]);
                let (d, d_source_kind) =
                    if let Some(source_kind) = GpuBaseFieldSourceKind::from_address(setup[1]) {
                        (null(), source_kind)
                    } else {
                        (
                            storage.get_base_layer(setup[1]).as_ptr(),
                            GpuBaseFieldSourceKind::Real,
                        )
                    };
                let mut num = alloc_ext(trace_len, context)?;
                let mut den = alloc_ext(trace_len, context)?;
                let num_ptr = num.as_mut_ptr();
                let den_ptr = den.as_mut_ptr();
                computed_extension_outputs.push((output[0], GpuExtensionFieldPoly::new(num)));
                computed_extension_outputs.push((output[1], GpuExtensionFieldPoly::new(den)));
                GpuGKRForwardGateDescriptor::with_lookup_base_minus_multiplicity_by_base(
                    b.as_ptr(),
                    c.as_ptr(),
                    d,
                    d_source_kind,
                    num_ptr,
                    den_ptr,
                )
            }
            NoFieldGKRRelation::LookupFromMaterializedVectorInputWithSetup {
                input,
                setup,
                output,
            } => {
                let b = storage.get_ext_poly(*input);
                let c = storage.get_base_layer(setup[0]);
                let d = storage.get_ext_poly(setup[1]);
                let mut num = alloc_ext(trace_len, context)?;
                let mut den = alloc_ext(trace_len, context)?;
                let num_ptr = num.as_mut_ptr();
                let den_ptr = den.as_mut_ptr();
                computed_extension_outputs.push((output[0], GpuExtensionFieldPoly::new(num)));
                computed_extension_outputs.push((output[1], GpuExtensionFieldPoly::new(den)));
                GpuGKRForwardGateDescriptor::with_lookup_ext_minus_multiplicity_by_ext(
                    b.as_ptr(),
                    c.as_ptr(),
                    d.as_ptr(),
                    num_ptr,
                    den_ptr,
                )
            }
            NoFieldGKRRelation::LookupUnbalancedPairWithMaterializedBaseInputs {
                input,
                remainder,
                output,
            } => {
                let [a, b] = input.map(|addr| storage.get_ext_poly(addr));
                let remainder = storage.get_base_layer(*remainder);
                let mut num = alloc_ext(trace_len, context)?;
                let mut den = alloc_ext(trace_len, context)?;
                let num_ptr = num.as_mut_ptr();
                let den_ptr = den.as_mut_ptr();
                computed_extension_outputs.push((output[0], GpuExtensionFieldPoly::new(num)));
                computed_extension_outputs.push((output[1], GpuExtensionFieldPoly::new(den)));
                GpuGKRForwardGateDescriptor::with_lookup_unbalanced_base(
                    a.as_ptr(),
                    b.as_ptr(),
                    remainder.as_ptr(),
                    num_ptr,
                    den_ptr,
                )
            }
            NoFieldGKRRelation::LookupUnbalancedPairWithMaterializedVectorInputs {
                input,
                remainder,
                output,
            } => {
                let [a, b] = input.map(|addr| storage.get_ext_poly(addr));
                let remainder = storage.get_ext_poly(*remainder);
                let mut num = alloc_ext(trace_len, context)?;
                let mut den = alloc_ext(trace_len, context)?;
                let num_ptr = num.as_mut_ptr();
                let den_ptr = den.as_mut_ptr();
                computed_extension_outputs.push((output[0], GpuExtensionFieldPoly::new(num)));
                computed_extension_outputs.push((output[1], GpuExtensionFieldPoly::new(den)));
                GpuGKRForwardGateDescriptor::with_lookup_unbalanced_extension(
                    a.as_ptr(),
                    b.as_ptr(),
                    remainder.as_ptr(),
                    num_ptr,
                    den_ptr,
                )
            }
            NoFieldGKRRelation::EnforceConstraintsMaxQuadratic { .. } => {
                GpuGKRForwardGateDescriptor::no_op()
            }
            NoFieldGKRRelation::MaterializedVectorLookupInput { output, .. } => {
                assert!(
                    storage.try_get_ext_poly(*output).is_some(),
                    "materialized vector lookup output {:?} must be precomputed before gate lowering",
                    output
                );
                GpuGKRForwardGateDescriptor::no_op()
            }
            NoFieldGKRRelation::MaterializeSingleLookupInput { output, .. } => {
                assert!(
                    storage.try_get_base_poly(*output).is_some(),
                    "materialized single lookup output {:?} must be precomputed before gate lowering",
                    output
                );
                GpuGKRForwardGateDescriptor::no_op()
            }
            NoFieldGKRRelation::LinearBaseFieldRelation { output, .. } => {
                assert!(
                    storage.try_get_base_poly(*output).is_some(),
                    "materialized linear base output {:?} must be precomputed before gate lowering",
                    output
                );
                GpuGKRForwardGateDescriptor::no_op()
            }
            NoFieldGKRRelation::MaxQuadratic { output, .. }
                if scratch_space_mapping.contains_key(output)
                    || storage.try_get_base_poly(*output).is_some() =>
            {
                GpuGKRForwardGateDescriptor::no_op()
            }
            NoFieldGKRRelation::EnforceSingleMaxQuadraticConstraint { .. } => {
                GpuGKRForwardGateDescriptor::no_op()
            }
            NoFieldGKRRelation::InitialGrandProductWithoutCaches { input, output } => {
                let lhs = build_forward_memory_tuple_expression_descriptor(
                    &input[0],
                    storage,
                    external_challenges,
                );
                let rhs = build_forward_memory_tuple_expression_descriptor(
                    &input[1],
                    storage,
                    external_challenges,
                );
                let mut dst = alloc_ext(trace_len, context)?;
                let dst_ptr = dst.as_mut_ptr();
                computed_extension_outputs.push((*output, GpuExtensionFieldPoly::new(dst)));
                GpuGKRForwardGateDescriptor::with_initial_grand_product_without_caches(
                    lhs, rhs, dst_ptr,
                )
            }
            NoFieldGKRRelation::MaterializeGrandProductTermExpression { input, output } => {
                let input = build_forward_memory_tuple_expression_descriptor(
                    input,
                    storage,
                    external_challenges,
                );
                let mut dst = alloc_ext(trace_len, context)?;
                let dst_ptr = dst.as_mut_ptr();
                computed_extension_outputs.push((*output, GpuExtensionFieldPoly::new(dst)));
                GpuGKRForwardGateDescriptor::with_materialize_grand_product_term_expression(
                    input, dst_ptr,
                )
            }
            NoFieldGKRRelation::LookupPairFromBaseInputs {
                input,
                output,
                range_check_width,
            } => {
                let lhs_mapping =
                    single_column_lookup_mapping_ptr(stage1, &input[0], *range_check_width);
                let rhs_mapping =
                    single_column_lookup_mapping_ptr(stage1, &input[1], *range_check_width);
                let mut num = alloc_ext(trace_len, context)?;
                let mut den = alloc_ext(trace_len, context)?;
                let num_ptr = num.as_mut_ptr();
                let den_ptr = den.as_mut_ptr();
                computed_extension_outputs.push((output[0], GpuExtensionFieldPoly::new(num)));
                computed_extension_outputs.push((output[1], GpuExtensionFieldPoly::new(den)));
                GpuGKRForwardGateDescriptor::with_lookup_pair_from_base_inputs(
                    lhs_mapping,
                    rhs_mapping,
                    num_ptr,
                    den_ptr,
                )
            }
            NoFieldGKRRelation::LookupWithDensAndSetupExpressions {
                input,
                setup,
                output,
            } => {
                let decoder_predicate = storage
                    .get_base_layer(
                        decoder_predicate_address
                            .expect("decoder lookup requires a decoder predicate column"),
                    )
                    .as_ptr();
                let input_mapping = vector_lookup_mapping_ptr(stage1, &input.1);
                let multiplicity = storage.get_base_layer(setup.0).as_ptr();
                let mut num = alloc_ext(trace_len, context)?;
                let mut den = alloc_ext(trace_len, context)?;
                let num_ptr = num.as_mut_ptr();
                let den_ptr = den.as_mut_ptr();
                computed_extension_outputs.push((output[0], GpuExtensionFieldPoly::new(num)));
                computed_extension_outputs.push((output[1], GpuExtensionFieldPoly::new(den)));
                GpuGKRForwardGateDescriptor::with_lookup_with_dens_and_setup_expressions(
                    decoder_predicate,
                    input_mapping,
                    multiplicity,
                    generic_lookup,
                    forward_setup.decoder_lookup_fill_value_device().as_ptr(),
                    generic_lookup_len,
                    num_ptr,
                    den_ptr,
                )
            }
            NoFieldGKRRelation::LookupPairFromVectorInputs { input, output } => {
                let lhs_mapping = vector_lookup_mapping_ptr(stage1, &input[0]);
                let rhs_mapping = vector_lookup_mapping_ptr(stage1, &input[1]);
                let mut num = alloc_ext(trace_len, context)?;
                let mut den = alloc_ext(trace_len, context)?;
                let num_ptr = num.as_mut_ptr();
                let den_ptr = den.as_mut_ptr();
                computed_extension_outputs.push((output[0], GpuExtensionFieldPoly::new(num)));
                computed_extension_outputs.push((output[1], GpuExtensionFieldPoly::new(den)));
                GpuGKRForwardGateDescriptor::with_lookup_pair_from_vector_inputs(
                    lhs_mapping,
                    rhs_mapping,
                    generic_lookup,
                    num_ptr,
                    den_ptr,
                )
            }
            NoFieldGKRRelation::LookupFromVectorInputWithSetup {
                input,
                setup,
                output,
            } => {
                let input_mapping = vector_lookup_mapping_ptr(stage1, input);
                let multiplicity = storage.get_base_layer(setup.0).as_ptr();
                let mut num = alloc_ext(trace_len, context)?;
                let mut den = alloc_ext(trace_len, context)?;
                let num_ptr = num.as_mut_ptr();
                let den_ptr = den.as_mut_ptr();
                computed_extension_outputs.push((output[0], GpuExtensionFieldPoly::new(num)));
                computed_extension_outputs.push((output[1], GpuExtensionFieldPoly::new(den)));
                GpuGKRForwardGateDescriptor::with_lookup_from_vector_input_with_setup(
                    input_mapping,
                    multiplicity,
                    generic_lookup,
                    generic_lookup_len,
                    num_ptr,
                    den_ptr,
                )
            }
            NoFieldGKRRelation::LookupUnbalancedPairWithVectorInputs {
                input,
                remainder,
                output,
            } => {
                let [a, b] = input.map(|addr| storage.get_ext_poly(addr));
                let remainder_mapping = vector_lookup_mapping_ptr(stage1, remainder);
                let mut num = alloc_ext(trace_len, context)?;
                let mut den = alloc_ext(trace_len, context)?;
                let num_ptr = num.as_mut_ptr();
                let den_ptr = den.as_mut_ptr();
                computed_extension_outputs.push((output[0], GpuExtensionFieldPoly::new(num)));
                computed_extension_outputs.push((output[1], GpuExtensionFieldPoly::new(den)));
                GpuGKRForwardGateDescriptor::with_lookup_unbalanced_pair_with_vector_inputs(
                    a.as_ptr(),
                    b.as_ptr(),
                    remainder_mapping,
                    generic_lookup,
                    num_ptr,
                    den_ptr,
                )
            }
            NoFieldGKRRelation::InitsOrTeardownsInitialPair {
                timestamp_and_value,
                setup,
                output,
                set_idxes,
            } => {
                let dst = materialize_inits_and_teardowns_initial_pair(
                    storage,
                    timestamp_and_value,
                    *setup,
                    set_idxes.map(|idx| idx as u32),
                    high_bits_offset_for_inits_and_teardowns::<2>(trace_len),
                    external_challenges,
                    trace_len,
                    context,
                )?;
                computed_extension_outputs.push((*output, GpuExtensionFieldPoly::new(dst)));
                GpuGKRForwardGateDescriptor::no_op()
            }
            NoFieldGKRRelation::MaxQuadratic { .. }
            | NoFieldGKRRelation::UnbalancedGrandProductWithCache { .. } => {
                unimplemented!(
                    "unsupported GPU forward relation: {:?}",
                    gate.enforced_relation
                )
            }
        };
        batch_gate_idx += 1;
    }

    if batch_gate_idx > 0 {
        batch.gate_count = batch_gate_idx as u32;
        batches.push(batch);
    }

    Ok(LoweredGpuGKRForwardLayer {
        batches,
        computed_extension_outputs,
        aliased_base_outputs,
        aliased_extension_outputs,
    })
}

fn commit_lowered_forward_layer<E>(
    expected_output_layer: usize,
    storage: &mut GpuGKRStorage<BF, E>,
    lowered: LoweredGpuGKRForwardLayer<E>,
) {
    let LoweredGpuGKRForwardLayer {
        batches: _,
        computed_extension_outputs,
        aliased_base_outputs,
        aliased_extension_outputs,
    } = lowered;

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
            let mut dst = alloc_base(trace_len, context)?;
            let base_output = dst.as_mut_ptr();
            Ok((
                GpuGKRForwardCacheDescriptor {
                    kind: GpuGKRForwardCacheKind::SingleColumnLookup,
                    mapping: mapping.as_ptr(),
                    setup_values: null(),
                    setup_source_kind,
                    base_output,
                    ..GpuGKRForwardCacheDescriptor::default()
                },
                LoweredCacheRelationOutput::Base(GpuBaseFieldPoly::new(dst)),
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
            let mut dst = alloc_ext(trace_len, context)?;
            let ext_output = dst.as_mut_ptr();
            Ok((
                GpuGKRForwardCacheDescriptor {
                    kind: GpuGKRForwardCacheKind::VectorizedLookup,
                    mapping: mapping.as_ptr(),
                    generic_lookup,
                    decoder_mask: if is_decoder_lookup {
                        storage
                            .get_base_layer(
                                decoder_predicate_address
                                    .expect("decoder lookup requires a decoder predicate column"),
                            )
                            .as_ptr()
                    } else {
                        null()
                    },
                    decoder_fill_value: if is_decoder_lookup {
                        forward_setup.decoder_lookup_fill_value_device().as_ptr()
                    } else {
                        null()
                    },
                    ext_output,
                    ..GpuGKRForwardCacheDescriptor::default()
                },
                LoweredCacheRelationOutput::Ext(GpuExtensionFieldPoly::new(dst)),
            ))
        }
        NoFieldGKRCacheRelation::VectorizedLookupSetup(_) => {
            let mut dst = alloc_ext(trace_len, context)?;
            let ext_output = dst.as_mut_ptr();
            Ok((
                GpuGKRForwardCacheDescriptor {
                    kind: GpuGKRForwardCacheKind::VectorizedLookupSetup,
                    generic_lookup,
                    ext_output,
                    generic_lookup_len: forward_setup.generic_lookup_len() as u32,
                    ..GpuGKRForwardCacheDescriptor::default()
                },
                LoweredCacheRelationOutput::Ext(GpuExtensionFieldPoly::new(dst)),
            ))
        }
        NoFieldGKRCacheRelation::MemoryTuple(rel) => {
            let mut dst = alloc_ext(trace_len, context)?;
            let ext_output = dst.as_mut_ptr();
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
                        [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                    contribution.mul_assign_by_base(&BF::from_u32_unchecked(*c as u32));
                    descriptor.constant_term.add_assign(&contribution);
                }
                CompiledAddressStrict::Constant(c) => {
                    let mut contribution = external_challenges
                        .permutation_argument_linearization_challenges
                        [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
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
                            [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX],
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
                            [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX],
                    );
                    add_memory_tuple_linear_term(
                        &mut descriptor,
                        MEMORY_TUPLE_ADDRESS_HIGH_TERM,
                        storage
                            .get_base_layer(GKRAddress::BaseLayerMemory(*high))
                            .as_ptr(),
                        external_challenges.permutation_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX],
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
                        [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                    let high_challenge = external_challenges
                        .permutation_argument_linearization_challenges
                        [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
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
                            [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX],
                    );
                    if rel.timestamp_offset != 0 {
                        let mut contribution = external_challenges
                            .permutation_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
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
                            [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX],
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
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX],
                    );
                    add_memory_tuple_linear_term(
                        &mut descriptor,
                        MEMORY_TUPLE_VALUE_HIGH_TERM,
                        storage
                            .get_base_layer(GKRAddress::BaseLayerMemory(read_value[1]))
                            .as_ptr(),
                        external_challenges.permutation_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX],
                    );
                }
                RamWordRepresentation::U8Limbs(read_value_bytes) => {
                    let byte_shift = BF::from_u32_unchecked(1 << 8);
                    for (challenge_idx, low_term_idx, high_term_idx, low_offset, high_offset) in [
                        (
                            MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
                            MEMORY_TUPLE_VALUE_LOW_TERM,
                            MEMORY_TUPLE_VALUE_LOW_EXTRA_TERM,
                            read_value_bytes[0],
                            read_value_bytes[1],
                        ),
                        (
                            MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
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

            Ok((
                descriptor,
                LoweredCacheRelationOutput::Ext(GpuExtensionFieldPoly::new(dst)),
            ))
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

fn schedule_dimension_reduction_forward<E>(
    storage: &mut GpuGKRStorage<BF, E>,
    compiled_circuit: &GKRCircuitArtifact<BF>,
    initial_trace_log_2: usize,
    final_trace_log_2: usize,
    tracing_ranges: &mut Vec<Range>,
    context: &ProverContext,
) -> CudaResult<(
    usize,
    BTreeMap<usize, BTreeMap<OutputType, DimensionReducingInputOutput>>,
)>
where
    E: FieldExtension<BF> + Field + SetByRef + SetByVal,
    E: GpuGKRDimensionReducingForwardKernelSet,
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
    let layer_idx = compiled_circuit.layers.len();
    let mut current_layer_idx = layer_idx;
    let stream = context.get_exec_stream();

    for input_size_log_2 in ((final_trace_log_2 + 1)..=initial_trace_log_2).rev() {
        let round_range = Range::new(format!(
            "gkr.forward.dimension_reduction.round.2pow{}_to_2pow{}",
            input_size_log_2,
            input_size_log_2 - 1
        ))?;
        round_range.start(stream)?;
        let layer_inputs = if current_layer_idx != layer_idx {
            let previous: &BTreeMap<OutputType, DimensionReducingInputOutput> =
                dimension_reduction_description
                    .get(&(current_layer_idx - 1))
                    .expect("dimension reduction input layer must exist");
            BTreeMap::from_iter(previous.iter().map(|(k, v)| (*k, v.output.clone())))
        } else {
            compiled_circuit.global_output_map.clone()
        };

        let input_trace_len = 1 << input_size_log_2;
        let output_trace_len = input_trace_len / 2;
        let lowered = lower_dimension_reducing_forward_round(
            &layer_inputs,
            current_layer_idx,
            output_trace_len,
            storage,
            context,
        )?;
        launch_dimension_reducing_forward(&lowered.batch, output_trace_len, context)?;
        let layer_description = commit_lowered_dimension_reducing_forward_round(
            current_layer_idx + 1,
            storage,
            lowered,
        );
        dimension_reduction_description.insert(current_layer_idx, layer_description);
        current_layer_idx += 1;
        round_range.end(stream)?;
        tracing_ranges.push(round_range);
    }

    Ok((current_layer_idx - 1, dimension_reduction_description))
}

fn lower_dimension_reducing_forward_round<E>(
    layer_inputs: &BTreeMap<OutputType, Vec<GKRAddress>>,
    current_layer_idx: usize,
    output_trace_len: usize,
    storage: &GpuGKRStorage<BF, E>,
    context: &ProverContext,
) -> CudaResult<LoweredGpuGKRDimensionReducingForwardRound<E>>
where
    E: FieldExtension<BF> + Field,
{
    let output_layer = current_layer_idx + 1;
    let mut output_idx = 0usize;
    let mut layer_description = BTreeMap::new();
    let mut lowered_inputs = Vec::new();
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
                    let source = storage.try_get_ext_poly(input).unwrap_or_else(|| {
                        panic!("missing dimension reduction input poly for {:?}", input)
                    });
                    let output = GKRAddress::InnerLayer {
                        layer: output_layer,
                        offset: output_idx,
                    };
                    output_idx += 1;
                    let mut reduced = alloc_ext(output_trace_len, context)?;
                    lowered_inputs.push(
                        LoweredGpuGKRDimensionReducingForwardInput::PairwiseProduct {
                            input: source.as_ptr(),
                            output: reduced.as_mut_ptr(),
                        },
                    );
                    computed_extension_outputs.push((output, GpuExtensionFieldPoly::new(reduced)));
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
                let num = storage.try_get_ext_poly(inputs[0]).unwrap_or_else(|| {
                    panic!(
                        "missing lookup reduction numerator poly for {:?}",
                        inputs[0]
                    )
                });
                let den = storage.try_get_ext_poly(inputs[1]).unwrap_or_else(|| {
                    panic!(
                        "missing lookup reduction denominator poly for {:?}",
                        inputs[1]
                    )
                });
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
                let mut reduced_num = alloc_ext(output_trace_len, context)?;
                let mut reduced_den = alloc_ext(output_trace_len, context)?;
                lowered_inputs.push(LoweredGpuGKRDimensionReducingForwardInput::LookupPair {
                    num: num.as_ptr(),
                    den: den.as_ptr(),
                    output_num: reduced_num.as_mut_ptr(),
                    output_den: reduced_den.as_mut_ptr(),
                });
                computed_extension_outputs.push((new_num, GpuExtensionFieldPoly::new(reduced_num)));
                computed_extension_outputs.push((new_den, GpuExtensionFieldPoly::new(reduced_den)));
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

    Ok(LoweredGpuGKRDimensionReducingForwardRound {
        batch: pack_dimension_reducing_forward_batch(&lowered_inputs),
        layer_description,
        computed_extension_outputs,
    })
}

fn commit_lowered_dimension_reducing_forward_round<E>(
    output_layer: usize,
    storage: &mut GpuGKRStorage<BF, E>,
    lowered: LoweredGpuGKRDimensionReducingForwardRound<E>,
) -> BTreeMap<OutputType, DimensionReducingInputOutput> {
    let LoweredGpuGKRDimensionReducingForwardRound {
        batch: _,
        layer_description,
        computed_extension_outputs,
    } = lowered;

    for (address, poly) in computed_extension_outputs {
        storage.insert_extension_at_layer(output_layer, address, poly);
    }

    layer_description
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
            [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
        assert!(result.insert(setup[0], challenge).is_none());
    }
    {
        let mut challenge = external_challenges.permutation_argument_linearization_challenges
            [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
        assert!(result.insert(setup[1], challenge).is_none());
        challenge.mul_assign_by_base(&BF::from_u32_unchecked(
            address_high_bits << address_high_bits_shift,
        ));
        constant_term.add_assign(&challenge);
    }

    if let Some((timestamps, values)) = timestamps_and_values {
        for (idx, address) in [
            (
                MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX,
                GKRAddress::BaseLayerMemory(timestamps[0]),
            ),
            (
                MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX,
                GKRAddress::BaseLayerMemory(timestamps[1]),
            ),
            (
                MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
                GKRAddress::BaseLayerMemory(values[0]),
            ),
            (
                MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
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

fn materialize_inits_and_teardowns_initial_pair<E>(
    storage: &GpuGKRStorage<BF, E>,
    timestamp_and_value: &InitsOrTeardownsTimestampAndValue,
    setup: [GKRAddress; 2],
    address_high_bits: [u32; 2],
    address_high_bits_shift: u32,
    external_challenges: &GKRExternalChallenges<BF, E>,
    trace_len: usize,
    context: &ProverContext,
) -> CudaResult<DeviceAllocation<E>>
where
    E: Field + FieldExtension<BF> + GpuGKRVirtualBaseAccumKernelSet + SetByVal,
    Add: BinaryOp<E, E, E>,
    Mul: BinaryOp<BF, E, E>,
    Mul: BinaryOp<E, E, E>,
{
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
    let mut rhs =
        materialize_linear_base_combination(storage, &rhs_terms, rhs_constant, trace_len, context)?;
    mul_into_y(
        &DeviceVectorChunk::new(&lhs, 0, trace_len),
        rhs.deref_mut(),
        context.get_exec_stream(),
    )?;
    Ok(rhs)
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

fn scale_and_add_base_column_in_place(
    dst: &mut DeviceAllocation<BF>,
    source: &GpuBaseFieldPoly<BF>,
    scalar: BF,
    context: &ProverContext,
) -> CudaResult<()>
where
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
        dst.deref_mut(),
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
        let mut lookup_challenges_host = unsafe { context.alloc_host_uninit_slice(3) };
        unsafe {
            lookup_challenges_host
                .get_mut_accessor()
                .get_mut()
                .copy_from_slice(&[E4::ONE, lookup_additive_challenge, E4::ZERO]);
        }
        crate::prover::gkr::setup::schedule_forward_setup_for_shape::<E4>(
            None,
            trace_len,
            0,
            0,
            false,
            &lookup_challenges_host,
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
            [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
        address_low_term.mul_assign_by_base(&address_low[row]);
        result.add_assign(&address_low_term);

        let mut address_high_value = address_high[row];
        address_high_value.add_assign(&BF::from_u32_unchecked(
            address_high_bits << high_bits_shift,
        ));
        let mut address_high_term = external_challenges
            .permutation_argument_linearization_challenges
            [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
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
                MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX,
                timestamp_offsets[0],
            ),
            (
                MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX,
                timestamp_offsets[1],
            ),
            (
                MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
                value_offsets[0],
            ),
            (
                MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
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

        let init_output = materialize_inits_and_teardowns_initial_pair(
            &storage,
            &InitsOrTeardownsTimestampAndValue::Init,
            setup,
            address_high_bits,
            high_bits_shift,
            &external_challenges,
            trace_len,
            &context,
        )
        .unwrap();
        let teardown_output = materialize_inits_and_teardowns_initial_pair(
            &storage,
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

        let init_output = GpuExtensionFieldPoly::new(init_output);
        let teardown_output = GpuExtensionFieldPoly::new(teardown_output);
        assert_eq!(read_ext_poly(&init_output, &context), expected_init);
        assert_eq!(read_ext_poly(&teardown_output, &context), expected_teardown);
    }

    #[test]
    #[should_panic(expected = "exceeding the fused forward cap")]
    fn forward_layer_panics_when_gate_count_exceeds_cap() {
        let context = make_test_context(64, 8);
        let trace_len = 8;
        let mut storage = GpuGKRStorage::<BF, E4>::default();
        let input = GKRAddress::BaseLayerMemory(0);
        storage.insert_base_field_at_layer(
            0,
            input,
            upload_base_poly(&vec![BF::new(1); trace_len], &context),
        );

        let layer = GKRLayerDescription {
            layer: 0,
            gates_with_external_connections: Vec::new(),
            cached_relations: BTreeMap::new(),
            gates: (0..(GKR_FORWARD_MAX_GATES_PER_LAYER + 1))
                .map(|offset| GateArtifacts {
                    output_layer: 1,
                    enforced_relation: NoFieldGKRRelation::Copy {
                        input,
                        output: GKRAddress::InnerLayer { layer: 1, offset },
                    },
                })
                .collect(),
        };
        let external_challenges = sample_external_challenges(100);
        let stage1 = GpuGKRStage1Output::empty_for_tests(&context).unwrap();
        let forward_setup = make_empty_forward_setup(trace_len, sample_ext(101), &context);

        let _ = lower_forward_layer(
            0,
            &layer.gates,
            &layer.gates_with_external_connections,
            &BTreeMap::new(),
            &storage,
            &stage1,
            &forward_setup,
            &external_challenges,
            None,
            forward_setup.lookup_additive_part_device().as_ptr(),
            trace_len,
            &context,
        );
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
            gates: vec![
                GateArtifacts {
                    output_layer: 1,
                    enforced_relation: NoFieldGKRRelation::Copy {
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
        let lowered = lower_forward_layer(
            0,
            &layer.gates,
            &layer.gates_with_external_connections,
            &BTreeMap::new(),
            &storage,
            &stage1,
            &forward_setup,
            &external_challenges,
            None,
            forward_setup.lookup_additive_part_device().as_ptr(),
            trace_len,
            &context,
        )
        .unwrap();
        assert_eq!(lowered.batches.len(), 1);
        assert_eq!(lowered.batches[0].gate_count, layer.gates.len() as u32);

        launch_forward_layer::<E4>(&lowered.batches[0], trace_len, &context).unwrap();
        commit_lowered_forward_layer(1, &mut storage, lowered);
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
    fn dimension_reducing_forward_round_lowering_and_launch_match_expected_outputs() {
        let context = make_test_context(256, 32);
        let input_trace_len = 8;
        let output_trace_len = input_trace_len / 2;
        let current_layer_idx = 7;

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

        let read_values = (0..input_trace_len)
            .map(|idx| sample_ext(10 + idx as u32))
            .collect::<Vec<_>>();
        let write_values = (0..input_trace_len)
            .map(|idx| sample_ext(30 + idx as u32))
            .collect::<Vec<_>>();
        let lookup16_num_values = (0..input_trace_len)
            .map(|idx| sample_ext(50 + idx as u32))
            .collect::<Vec<_>>();
        let lookup16_den_values = (0..input_trace_len)
            .map(|idx| sample_ext(70 + idx as u32))
            .collect::<Vec<_>>();
        let timestamp_num_values = (0..input_trace_len)
            .map(|idx| sample_ext(90 + idx as u32))
            .collect::<Vec<_>>();
        let timestamp_den_values = (0..input_trace_len)
            .map(|idx| sample_ext(110 + idx as u32))
            .collect::<Vec<_>>();
        let generic_num_values = (0..input_trace_len)
            .map(|idx| sample_ext(130 + idx as u32))
            .collect::<Vec<_>>();
        let generic_den_values = (0..input_trace_len)
            .map(|idx| sample_ext(150 + idx as u32))
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

        let layer_inputs = BTreeMap::from([
            (OutputType::PermutationProduct, vec![read_set, write_set]),
            (OutputType::Lookup16Bits, vec![lookup16_num, lookup16_den]),
            (
                OutputType::LookupTimestamps,
                vec![timestamp_num, timestamp_den],
            ),
            (OutputType::GenericLookup, vec![generic_num, generic_den]),
        ]);

        let lowered = lower_dimension_reducing_forward_round(
            &layer_inputs,
            current_layer_idx,
            output_trace_len,
            &storage,
            &context,
        )
        .unwrap();
        assert_eq!(lowered.batch.input_count, 5);

        let expected_description = BTreeMap::from([
            (
                OutputType::PermutationProduct,
                DimensionReducingInputOutput {
                    inputs: vec![read_set, write_set],
                    output: vec![
                        GKRAddress::InnerLayer {
                            layer: current_layer_idx + 1,
                            offset: 0,
                        },
                        GKRAddress::InnerLayer {
                            layer: current_layer_idx + 1,
                            offset: 1,
                        },
                    ],
                },
            ),
            (
                OutputType::Lookup16Bits,
                DimensionReducingInputOutput {
                    inputs: vec![lookup16_num, lookup16_den],
                    output: vec![
                        GKRAddress::InnerLayer {
                            layer: current_layer_idx + 1,
                            offset: 2,
                        },
                        GKRAddress::InnerLayer {
                            layer: current_layer_idx + 1,
                            offset: 3,
                        },
                    ],
                },
            ),
            (
                OutputType::LookupTimestamps,
                DimensionReducingInputOutput {
                    inputs: vec![timestamp_num, timestamp_den],
                    output: vec![
                        GKRAddress::InnerLayer {
                            layer: current_layer_idx + 1,
                            offset: 4,
                        },
                        GKRAddress::InnerLayer {
                            layer: current_layer_idx + 1,
                            offset: 5,
                        },
                    ],
                },
            ),
            (
                OutputType::GenericLookup,
                DimensionReducingInputOutput {
                    inputs: vec![generic_num, generic_den],
                    output: vec![
                        GKRAddress::InnerLayer {
                            layer: current_layer_idx + 1,
                            offset: 6,
                        },
                        GKRAddress::InnerLayer {
                            layer: current_layer_idx + 1,
                            offset: 7,
                        },
                    ],
                },
            ),
        ]);
        assert_eq!(lowered.layer_description, expected_description);

        launch_dimension_reducing_forward::<E4>(&lowered.batch, output_trace_len, &context)
            .unwrap();
        let layer_description = commit_lowered_dimension_reducing_forward_round(
            current_layer_idx + 1,
            &mut storage,
            lowered,
        );
        context.get_exec_stream().synchronize().unwrap();

        assert_eq!(layer_description, expected_description);

        let expected_read = expected_pairwise_reduction(&read_values);
        let expected_write = expected_pairwise_reduction(&write_values);
        let (expected_lookup16_num, expected_lookup16_den) =
            expected_lookup_pair_reduction(&lookup16_num_values, &lookup16_den_values);
        let (expected_timestamp_num, expected_timestamp_den) =
            expected_lookup_pair_reduction(&timestamp_num_values, &timestamp_den_values);
        let (expected_generic_num, expected_generic_den) =
            expected_lookup_pair_reduction(&generic_num_values, &generic_den_values);

        assert_eq!(
            read_ext_poly(
                storage
                    .get_ext_poly(expected_description[&OutputType::PermutationProduct].output[0]),
                &context,
            ),
            expected_read
        );
        assert_eq!(
            read_ext_poly(
                storage
                    .get_ext_poly(expected_description[&OutputType::PermutationProduct].output[1]),
                &context,
            ),
            expected_write
        );
        assert_eq!(
            read_ext_poly(
                storage.get_ext_poly(expected_description[&OutputType::Lookup16Bits].output[0]),
                &context,
            ),
            expected_lookup16_num
        );
        assert_eq!(
            read_ext_poly(
                storage.get_ext_poly(expected_description[&OutputType::Lookup16Bits].output[1]),
                &context,
            ),
            expected_lookup16_den
        );
        assert_eq!(
            read_ext_poly(
                storage.get_ext_poly(expected_description[&OutputType::LookupTimestamps].output[0]),
                &context,
            ),
            expected_timestamp_num
        );
        assert_eq!(
            read_ext_poly(
                storage.get_ext_poly(expected_description[&OutputType::LookupTimestamps].output[1]),
                &context,
            ),
            expected_timestamp_den
        );
        assert_eq!(
            read_ext_poly(
                storage.get_ext_poly(expected_description[&OutputType::GenericLookup].output[0]),
                &context,
            ),
            expected_generic_num
        );
        assert_eq!(
            read_ext_poly(
                storage.get_ext_poly(expected_description[&OutputType::GenericLookup].output[1]),
                &context,
            ),
            expected_generic_den
        );
    }

    #[test]
    #[serial]
    fn dimension_reducing_forward_round_launch_respects_sparse_input_count() {
        let context = make_test_context(256, 32);
        let input_trace_len = 8;
        let output_trace_len = input_trace_len / 2;
        let current_layer_idx = 3;

        let num = GKRAddress::InnerLayer {
            layer: current_layer_idx,
            offset: 0,
        };
        let den = GKRAddress::InnerLayer {
            layer: current_layer_idx,
            offset: 1,
        };
        let num_values = (0..input_trace_len)
            .map(|idx| sample_ext(200 + idx as u32))
            .collect::<Vec<_>>();
        let den_values = (0..input_trace_len)
            .map(|idx| sample_ext(220 + idx as u32))
            .collect::<Vec<_>>();

        let mut storage = GpuGKRStorage::<BF, E4>::default();
        storage.insert_extension_at_layer(
            current_layer_idx,
            num,
            upload_ext_poly(&num_values, &context),
        );
        storage.insert_extension_at_layer(
            current_layer_idx,
            den,
            upload_ext_poly(&den_values, &context),
        );

        let layer_inputs = BTreeMap::from([(OutputType::GenericLookup, vec![num, den])]);

        let lowered = lower_dimension_reducing_forward_round(
            &layer_inputs,
            current_layer_idx,
            output_trace_len,
            &storage,
            &context,
        )
        .unwrap();
        assert_eq!(lowered.batch.input_count, 1);

        launch_dimension_reducing_forward::<E4>(&lowered.batch, output_trace_len, &context)
            .unwrap();
        let layer_description = commit_lowered_dimension_reducing_forward_round(
            current_layer_idx + 1,
            &mut storage,
            lowered,
        );
        context.get_exec_stream().synchronize().unwrap();

        let expected_description = BTreeMap::from([(
            OutputType::GenericLookup,
            DimensionReducingInputOutput {
                inputs: vec![num, den],
                output: vec![
                    GKRAddress::InnerLayer {
                        layer: current_layer_idx + 1,
                        offset: 0,
                    },
                    GKRAddress::InnerLayer {
                        layer: current_layer_idx + 1,
                        offset: 1,
                    },
                ],
            },
        )]);
        assert_eq!(layer_description, expected_description);

        let (expected_num, expected_den) = expected_lookup_pair_reduction(&num_values, &den_values);
        assert_eq!(
            read_ext_poly(
                storage.get_ext_poly(expected_description[&OutputType::GenericLookup].output[0]),
                &context,
            ),
            expected_num
        );
        assert_eq!(
            read_ext_poly(
                storage.get_ext_poly(expected_description[&OutputType::GenericLookup].output[1]),
                &context,
            ),
            expected_den
        );
    }

    #[test]
    #[should_panic(expected = "exceeding the fused forward cap")]
    fn dimension_reducing_forward_batch_panics_when_input_count_exceeds_cap() {
        let input = LoweredGpuGKRDimensionReducingForwardInput::<E4>::PairwiseProduct {
            input: null(),
            output: null::<E4>().cast_mut(),
        };
        let lowered_inputs = vec![input; GKR_DIM_REDUCING_FORWARD_MAX_INPUTS + 1];
        let _ = pack_dimension_reducing_forward_batch(&lowered_inputs);
    }
}
