use std::collections::BTreeMap;
use std::mem::ManuallyDrop;
use std::ops::DerefMut;
use std::ptr::null;
use std::sync::Arc;

use cs::definitions::{
    gkr::{RamWordRepresentation, DECODER_LOOKUP_FORMAL_SET_INDEX},
    GKRAddress, VirtualSetupPoly, MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX,
    MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
    MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX,
    MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX, MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
    MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
};
use cs::gkr_compiler::{
    CompiledAddressSpaceRelationStrict, CompiledAddressStrict, CompiledMemoryTimestamp,
    GKRCircuitArtifact, GKRLayerDescription, NoFieldGKRCacheRelation, NoFieldGKRRelation,
    OutputType,
};
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::memory::memory_copy_async;
use era_cudart::paste::paste;
use era_cudart::result::CudaResult;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use field::{Field, FieldExtension, PrimeField};
use prover::gkr::prover::dimension_reduction::forward::DimensionReducingInputOutput;
use prover::gkr::prover::GKRExternalChallenges;

use super::backward::GpuGKRDimensionReducingBackwardState;
use super::setup::{GpuGKRForwardSetup, GpuGKRSetupTransfer};
use super::stage1::GpuGKRStage1Output;
use super::transform::normalize_compiled_circuit_for_gpu;
use super::{GpuBaseFieldPoly, GpuExtensionFieldPoly, GpuGKRStorage};
use crate::allocator::tracker::AllocationPlacement;
use crate::ops::batch_inv::BatchInv;
use crate::ops::simple::{
    add_into_y, mul_into_y, set_by_ref, set_by_val, sub_into_x, Add, BinaryOp, Mul, SetByRef,
    SetByVal, Sub,
};
use crate::primitives::context::{DeviceAllocation, HostAllocation, ProverContext, UnsafeAccessor};
use crate::primitives::device_structures::DeviceVectorChunk;
use crate::primitives::device_tracing::Range;
use crate::primitives::field::{BF, E2, E4, E6};
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
    setup: &GpuGKRSetupTransfer<'_>,
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
        + BatchInv
        + GpuGKRForwardKernelSet
        + GpuGKRForwardCacheKernelSet
        + GpuGKRDimensionReducingForwardKernelSet,
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
    setup.ensure_transferred(context)?;
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
    let mut storage = setup.bootstrap_storage_from_stage1::<E>(stage1, context)?;

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
        + BatchInv
        + GpuGKRForwardKernelSet
        + GpuGKRForwardCacheKernelSet,
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
    let expected_output_layer = layer_idx + 1;
    let lowered = lower_forward_layer(
        layer_idx,
        layer,
        &compiled_circuit.scratch_space_mapping,
        storage,
        forward_setup.lookup_additive_part_device().as_ptr(),
        trace_len,
        context,
    )?;
    launch_forward_layer(&lowered.batch, trace_len, context)?;
    commit_lowered_forward_layer(expected_output_layer, storage, lowered);
    gates_range.end(stream)?;
    tracing_ranges.push(gates_range);

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

fn lower_forward_layer<E>(
    layer_idx: usize,
    layer: &GKRLayerDescription,
    scratch_space_mapping: &BTreeMap<GKRAddress, usize>,
    storage: &GpuGKRStorage<BF, E>,
    lookup_additive_challenge: *const E,
    trace_len: usize,
    context: &ProverContext,
) -> CudaResult<LoweredGpuGKRForwardLayer<E>> {
    let expected_output_layer = layer_idx + 1;
    let total_gates = layer.gates.len() + layer.gates_with_external_connections.len();
    assert!(
        total_gates <= GKR_FORWARD_MAX_GATES_PER_LAYER,
        "layer {layer_idx} has {total_gates} gates, exceeding the fused forward cap of {}",
        GKR_FORWARD_MAX_GATES_PER_LAYER
    );

    let mut batch = GpuGKRForwardLayerBatch::new(lookup_additive_challenge);
    batch.gate_count = total_gates as u32;

    let mut computed_extension_outputs = Vec::new();
    let mut aliased_base_outputs = Vec::new();
    let mut aliased_extension_outputs = Vec::new();

    for (gate_idx, gate) in layer
        .gates
        .iter()
        .chain(layer.gates_with_external_connections.iter())
        .enumerate()
    {
        assert_eq!(gate.output_layer, expected_output_layer);
        batch.descriptors[gate_idx] = match &gate.enforced_relation {
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
                let d = storage.get_base_layer(setup[1]);
                let mut num = alloc_ext(trace_len, context)?;
                let mut den = alloc_ext(trace_len, context)?;
                let num_ptr = num.as_mut_ptr();
                let den_ptr = den.as_mut_ptr();
                computed_extension_outputs.push((output[0], GpuExtensionFieldPoly::new(num)));
                computed_extension_outputs.push((output[1], GpuExtensionFieldPoly::new(den)));
                GpuGKRForwardGateDescriptor::with_lookup_base_minus_multiplicity_by_base(
                    b.as_ptr(),
                    c.as_ptr(),
                    d.as_ptr(),
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
            NoFieldGKRRelation::MaxQuadratic { output, .. }
                if scratch_space_mapping.contains_key(output)
                    || storage.try_get_base_poly(*output).is_some() =>
            {
                GpuGKRForwardGateDescriptor::no_op()
            }
            NoFieldGKRRelation::LinearBaseFieldRelation { .. }
            | NoFieldGKRRelation::MaxQuadratic { .. }
            | NoFieldGKRRelation::LookupPairFromVectorInputs { .. }
            | NoFieldGKRRelation::LookupPairFromBaseInputs { .. }
            | NoFieldGKRRelation::MaterializeSingleLookupInput { .. }
            | NoFieldGKRRelation::MaterializedVectorLookupInput { .. }
            | NoFieldGKRRelation::UnbalancedGrandProductWithCache { .. } => {
                unimplemented!(
                    "unsupported GPU forward relation: {:?}",
                    gate.enforced_relation
                )
            }
        };
    }

    Ok(LoweredGpuGKRForwardLayer {
        batch,
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
        batch: _,
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
) -> CudaResult<GpuGKRForwardCacheDescriptor<E>>
where
    E: FieldExtension<BF> + Field + SetByRef + SetByVal + BatchInv,
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
    let cache_layer = cache_relation_layer(layer_idx, address);
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
            let setup_values = storage.get_base_layer(setup_address).as_ptr();
            let mut dst = alloc_base(trace_len, context)?;
            let base_output = dst.as_mut_ptr();
            storage.insert_base_field_at_layer(cache_layer, address, GpuBaseFieldPoly::new(dst));
            Ok(GpuGKRForwardCacheDescriptor {
                kind: GpuGKRForwardCacheKind::SingleColumnLookup,
                mapping: mapping.as_ptr(),
                setup_values,
                base_output,
                ..GpuGKRForwardCacheDescriptor::default()
            })
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
            storage.insert_extension_at_layer(
                cache_layer,
                address,
                GpuExtensionFieldPoly::new(dst),
            );
            Ok(GpuGKRForwardCacheDescriptor {
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
            })
        }
        NoFieldGKRCacheRelation::VectorizedLookupSetup(_) => {
            let mut dst = alloc_ext(trace_len, context)?;
            let ext_output = dst.as_mut_ptr();
            storage.insert_extension_at_layer(
                cache_layer,
                address,
                GpuExtensionFieldPoly::new(dst),
            );
            Ok(GpuGKRForwardCacheDescriptor {
                kind: GpuGKRForwardCacheKind::VectorizedLookupSetup,
                generic_lookup,
                ext_output,
                generic_lookup_len: forward_setup.generic_lookup_len() as u32,
                ..GpuGKRForwardCacheDescriptor::default()
            })
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
            match rel.address_space {
                CompiledAddressSpaceRelationStrict::Constant(c) => {
                    descriptor.address_space_kind = GpuGKRForwardCacheAddressSpaceKind::Constant;
                    descriptor.address_space_constant = BF::from_u32_unchecked(c);
                }
                CompiledAddressSpaceRelationStrict::Is(offset) => {
                    descriptor.address_space_kind = GpuGKRForwardCacheAddressSpaceKind::Is;
                    descriptor.address_space_ptr = storage
                        .get_base_layer(GKRAddress::BaseLayerMemory(offset))
                        .as_ptr();
                }
                CompiledAddressSpaceRelationStrict::Not(offset) => {
                    descriptor.address_space_kind = GpuGKRForwardCacheAddressSpaceKind::Not;
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
                        push_memory_tuple_linear_term(
                            &mut descriptor,
                            storage
                                .get_base_layer(GKRAddress::BaseLayerMemory(dynamic_offset))
                                .as_ptr(),
                            challenge,
                        );
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

            storage.insert_extension_at_layer(
                cache_layer,
                address,
                GpuExtensionFieldPoly::new(dst),
            );
            Ok(descriptor)
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
    E: FieldExtension<BF> + Field + SetByRef + SetByVal + BatchInv + GpuGKRForwardCacheKernelSet,
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
        relations.len() <= MAX_CACHE_RELATIONS_PER_LAYER,
        "layer {} has {} cache relations, exceeds hard limit {}",
        layer_idx,
        relations.len(),
        MAX_CACHE_RELATIONS_PER_LAYER
    );
    assert!(
        forward_setup.generic_lookup_len() <= u32::MAX as usize,
        "generic lookup runtime too large for fused forward cache kernel"
    );

    let mut batch = GpuGKRForwardCacheBatch::default();
    for ((address, relation), descriptor) in relations.iter().zip(batch.descriptors.iter_mut()) {
        *descriptor = lower_cache_relation(
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
        batch.count += 1;
    }

    launch_forward_cache(batch, trace_len, context)
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
    E: FieldExtension<BF> + Field + SetByRef + SetByVal + BatchInv,
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
    use serial_test::serial;

    fn sample_ext(seed: u32) -> E4 {
        E4::from_array_of_base([
            BF::new(seed),
            BF::new(seed + 1),
            BF::new(seed + 2),
            BF::new(seed + 3),
        ])
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

    fn empty_constraints() -> NoFieldMaxQuadraticConstraintsGKRRelation {
        NoFieldMaxQuadraticConstraintsGKRRelation {
            quadratic_terms: Vec::new().into_boxed_slice(),
            linear_terms: Vec::new().into_boxed_slice(),
            constants: Vec::new().into_boxed_slice(),
        }
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
            additional_base_layer_openings: Vec::new(),
        };

        let _ = lower_forward_layer(
            0,
            &layer,
            &BTreeMap::new(),
            &storage,
            null(),
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
            additional_base_layer_openings: Vec::new(),
        };

        assert_forward_layer_invariants(0, 2, &layer);
        let lowered = lower_forward_layer(
            0,
            &layer,
            &BTreeMap::new(),
            &storage,
            lookup_additive_device.as_ptr(),
            trace_len,
            &context,
        )
        .unwrap();
        assert_eq!(lowered.batch.gate_count, layer.gates.len() as u32);

        launch_forward_layer::<E4>(&lowered.batch, trace_len, &context).unwrap();
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
