use std::collections::BTreeMap;
use std::mem::{align_of, size_of};
use std::ops::DerefMut;

use cs::definitions::{
    gkr::{DECODER_LOOKUP_FORMAL_SET_INDEX, RamWordRepresentation},
    GKRAddress,
    MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX, MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
    MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX,
    MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX, MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
    MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
};
use cs::gkr_compiler::{
    CompiledAddressSpaceRelationStrict, CompiledAddressStrict, GKRCircuitArtifact,
    GKRLayerDescription, NoFieldGKRCacheRelation, NoFieldGKRRelation, OutputType,
};
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use field::{Field, FieldExtension, PrimeField};
use prover::gkr::prover::dimension_reduction::forward::DimensionReducingInputOutput;
use prover::gkr::prover::GKRExternalChallenges;

use super::backward::GpuGKRDimensionReducingBackwardState;
use super::setup::{GpuGKRForwardSetup, GpuGKRSetupTransfer};
use super::stage1::GpuGKRStage1Output;
use super::{GpuBaseFieldPoly, GpuExtensionFieldPoly, GpuGKRStorage};
use crate::allocator::tracker::AllocationPlacement;
use crate::ops::blake2s::gather_rows;
use crate::ops::complex::BatchInv;
use crate::ops::simple::{
    add_into_y, mul, mul_into_x, mul_into_y, set_arithmetic_sequence, set_by_ref, set_by_val,
    sub_into_x, Add, BinaryOp, Mul, SetByRef, SetByVal, Sub,
};
use crate::primitives::context::{DeviceAllocation, HostAllocation, ProverContext, UnsafeAccessor};
use crate::primitives::device_structures::{
    DeviceMatrix, DeviceMatrixMut, DeviceVectorChunk, DeviceVectorChunkMut,
};
use crate::primitives::device_tracing::Range;
use crate::primitives::field::BF;

pub(crate) struct GpuGKRForwardOutput<B, E> {
    #[allow(dead_code)] // Keeps queued NVTX host callbacks alive until the stream consumes them.
    tracing_ranges: Vec<Range>,
    #[allow(dead_code)] // Keeps async reduction index uploads alive until queued work completes.
    forward_scratch: GpuGKRForwardScratch,
    pub(crate) storage: GpuGKRStorage<B, E>,
    pub(crate) initial_layer_for_sumcheck: usize,
    pub(crate) dimension_reducing_inputs:
        BTreeMap<usize, BTreeMap<OutputType, DimensionReducingInputOutput>>,
}

pub(crate) struct GpuGKRTranscriptHandoff<E> {
    #[allow(dead_code)] // Keeps queued NVTX host callbacks alive until the stream consumes them.
    tracing_ranges: Vec<Range>,
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
            tracing_ranges,
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
            self.forward_scratch,
            self.storage,
            self.initial_layer_for_sumcheck,
            self.dimension_reducing_inputs,
        )
    }
}

pub(super) struct GpuGKRForwardScratch {
    even_indexes_device: DeviceAllocation<u32>,
    odd_indexes_device: DeviceAllocation<u32>,
}

impl GpuGKRForwardScratch {
    fn new(max_output_trace_len: usize, context: &ProverContext) -> CudaResult<Self> {
        assert!(max_output_trace_len <= (u32::MAX as usize / 2));
        let mut even_indexes_device =
            context.alloc(max_output_trace_len, AllocationPlacement::BestFit)?;
        let mut odd_indexes_device =
            context.alloc(max_output_trace_len, AllocationPlacement::BestFit)?;
        set_arithmetic_sequence(
            0,
            2,
            even_indexes_device.deref_mut(),
            context.get_exec_stream(),
        )?;
        set_arithmetic_sequence(
            1,
            2,
            odd_indexes_device.deref_mut(),
            context.get_exec_stream(),
        )?;
        Ok(Self {
            even_indexes_device,
            odd_indexes_device,
        })
    }

    fn even_indexes(&self, len: usize) -> &DeviceSlice<u32> {
        &self.even_indexes_device[..len]
    }

    fn odd_indexes(&self, len: usize) -> &DeviceSlice<u32> {
        &self.odd_indexes_device[..len]
    }
}

#[derive(Clone, Copy, Default)]
struct ForwardLookupUsage {
    last_generic_mapping_layer: Option<usize>,
    last_range_mapping_layer: Option<usize>,
    last_timestamp_mapping_layer: Option<usize>,
    last_generic_lookup_layer: Option<usize>,
}

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
    setup.ensure_transferred(context)?;
    let trace_len = compiled_circuit.trace_len;
    let stream = context.get_exec_stream();
    let mut tracing_ranges = Vec::new();
    let forward_range = Range::new("gkr.forward.schedule")?;
    forward_range.start(stream)?;
    let usage = analyze_forward_lookup_usage(compiled_circuit);
    let mut storage = setup.bootstrap_storage_from_stage1::<E>(stage1);
    let scratch_range = Range::new("gkr.forward.allocate_reduction_scratch")?;
    scratch_range.start(stream)?;
    let forward_scratch = GpuGKRForwardScratch::new(trace_len / 2, context)?;
    scratch_range.end(stream)?;
    tracing_ranges.push(scratch_range);

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
            layer,
            &mut tracing_ranges,
            &mut storage,
            stage1,
            forward_setup,
            external_challenges,
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
            compiled_circuit,
            trace_len.trailing_zeros() as usize,
            final_trace_size_log_2,
            &forward_scratch,
            &mut tracing_ranges,
            context,
        )?;
    dimension_reduction_range.end(stream)?;
    tracing_ranges.push(dimension_reduction_range);
    forward_range.end(stream)?;
    tracing_ranges.push(forward_range);

    Ok(GpuGKRForwardOutput {
        tracing_ranges,
        forward_scratch,
        storage,
        initial_layer_for_sumcheck,
        dimension_reducing_inputs,
    })
}

fn schedule_ext_poly_readback<B, E: Copy>(
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
    layer: &GKRLayerDescription,
    tracing_ranges: &mut Vec<Range>,
    storage: &mut GpuGKRStorage<BF, E>,
    stage1: &GpuGKRStage1Output,
    forward_setup: &GpuGKRForwardSetup<E>,
    external_challenges: &GKRExternalChallenges<BF, E>,
    trace_len: usize,
    context: &ProverContext,
) -> CudaResult<()>
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
    let stream = context.get_exec_stream();
    let cache_range = Range::new(format!("gkr.forward.layer.{layer_idx}.cache"))?;
    cache_range.start(stream)?;
    for (address, cache_relation) in layer.cached_relations.iter() {
        schedule_cache_relation(
            layer_idx,
            *address,
            cache_relation,
            storage,
            stage1,
            forward_setup,
            external_challenges,
            trace_len,
            context,
        )?;
    }
    cache_range.end(stream)?;
    tracing_ranges.push(cache_range);

    let gates_range = Range::new(format!("gkr.forward.layer.{layer_idx}.gates"))?;
    gates_range.start(stream)?;

    let expected_output_layer = layer_idx + 1;
    let gates = layer
        .gates
        .iter()
        .chain(layer.gates_with_external_connections.iter());
    for gate in gates {
        match &gate.enforced_relation {
            NoFieldGKRRelation::Copy { input, output } => {
                if let Some(source) = storage
                    .try_get_base_poly(*input)
                    .map(|poly| poly.clone_shared())
                {
                    storage.insert_base_field_at_layer(expected_output_layer, *output, source);
                } else {
                    let source = storage.get_ext_poly(*input).clone_shared();
                    storage.insert_extension_at_layer(expected_output_layer, *output, source);
                }
            }
            NoFieldGKRRelation::InitialGrandProductFromCaches { input, output }
            | NoFieldGKRRelation::TrivialProduct { input, output } => {
                let lhs = storage.get_ext_poly(input[0]).clone_shared();
                let rhs = storage.get_ext_poly(input[1]).clone_shared();
                let mut dst = alloc_ext(trace_len, context)?;
                mul(
                    &lhs.as_device_chunk(),
                    &rhs.as_device_chunk(),
                    dst.deref_mut(),
                    context.get_exec_stream(),
                )?;
                storage.insert_extension_at_layer(
                    expected_output_layer,
                    *output,
                    GpuExtensionFieldPoly::new(dst),
                );
            }
            NoFieldGKRRelation::MaskIntoIdentityProduct {
                input,
                mask,
                output,
            } => {
                let input = storage.get_ext_poly(*input).clone_shared();
                let mask = storage.get_base_layer(*mask).clone_shared();
                let mut dst = alloc_ext(trace_len, context)?;
                set_by_ref(
                    &input.as_device_chunk(),
                    dst.deref_mut(),
                    context.get_exec_stream(),
                )?;
                sub_ext_scalar_in_place(&mut dst, E::ONE, context)?;
                mul_into_x(
                    dst.deref_mut(),
                    &mask.as_device_chunk(),
                    context.get_exec_stream(),
                )?;
                add_ext_scalar_in_place(&mut dst, E::ONE, context)?;
                storage.insert_extension_at_layer(
                    expected_output_layer,
                    *output,
                    GpuExtensionFieldPoly::new(dst),
                );
            }
            NoFieldGKRRelation::AggregateLookupRationalPair { input, output } => {
                let [a, b] = input[0].map(|addr| storage.get_ext_poly(addr).clone_shared());
                let [c, d] = input[1].map(|addr| storage.get_ext_poly(addr).clone_shared());
                let mut num = alloc_ext(trace_len, context)?;
                let mut den = alloc_ext(trace_len, context)?;
                let mut temp = alloc_ext(trace_len, context)?;
                mul(
                    &b.as_device_chunk(),
                    &d.as_device_chunk(),
                    den.deref_mut(),
                    context.get_exec_stream(),
                )?;
                mul(
                    &a.as_device_chunk(),
                    &d.as_device_chunk(),
                    num.deref_mut(),
                    context.get_exec_stream(),
                )?;
                mul(
                    &c.as_device_chunk(),
                    &b.as_device_chunk(),
                    temp.deref_mut(),
                    context.get_exec_stream(),
                )?;
                add_into_y(
                    &DeviceVectorChunk::new(&temp, 0, trace_len),
                    num.deref_mut(),
                    context.get_exec_stream(),
                )?;
                storage.insert_extension_at_layer(
                    expected_output_layer,
                    output[0],
                    GpuExtensionFieldPoly::new(num),
                );
                storage.insert_extension_at_layer(
                    expected_output_layer,
                    output[1],
                    GpuExtensionFieldPoly::new(den),
                );
            }
            NoFieldGKRRelation::LookupWithCachedDensAndSetup {
                input,
                setup,
                output,
            } => {
                let a = storage.get_base_layer(input[0]).clone_shared();
                let b = storage.get_ext_poly(input[1]).clone_shared();
                let c = storage.get_base_layer(setup[0]).clone_shared();
                let d = storage.get_ext_poly(setup[1]).clone_shared();
                let mut shifted_b = alloc_ext(trace_len, context)?;
                let mut shifted_d = alloc_ext(trace_len, context)?;
                let mut num = alloc_ext(trace_len, context)?;
                let mut den = alloc_ext(trace_len, context)?;
                let mut temp = alloc_ext(trace_len, context)?;
                set_by_ref(
                    &b.as_device_chunk(),
                    shifted_b.deref_mut(),
                    context.get_exec_stream(),
                )?;
                add_ext_device_scalar_in_place(
                    &mut shifted_b,
                    forward_setup.lookup_additive_part_device(),
                    context,
                )?;
                set_by_ref(
                    &d.as_device_chunk(),
                    shifted_d.deref_mut(),
                    context.get_exec_stream(),
                )?;
                add_ext_device_scalar_in_place(
                    &mut shifted_d,
                    forward_setup.lookup_additive_part_device(),
                    context,
                )?;
                mul(
                    &DeviceVectorChunk::new(&shifted_b, 0, trace_len),
                    &DeviceVectorChunk::new(&shifted_d, 0, trace_len),
                    den.deref_mut(),
                    context.get_exec_stream(),
                )?;
                mul(
                    &a.as_device_chunk(),
                    &DeviceVectorChunk::new(&shifted_d, 0, trace_len),
                    temp.deref_mut(),
                    context.get_exec_stream(),
                )?;
                mul(
                    &c.as_device_chunk(),
                    &DeviceVectorChunk::new(&shifted_b, 0, trace_len),
                    num.deref_mut(),
                    context.get_exec_stream(),
                )?;
                sub_into_x(
                    temp.deref_mut(),
                    &DeviceVectorChunk::new(&num, 0, trace_len),
                    context.get_exec_stream(),
                )?;
                storage.insert_extension_at_layer(
                    expected_output_layer,
                    output[0],
                    GpuExtensionFieldPoly::new(temp),
                );
                storage.insert_extension_at_layer(
                    expected_output_layer,
                    output[1],
                    GpuExtensionFieldPoly::new(den),
                );
            }
            NoFieldGKRRelation::LookupPairFromMaterializedBaseInputs { input, output } => {
                let lhs = storage.get_base_layer(input[0]).clone_shared();
                let rhs = storage.get_base_layer(input[1]).clone_shared();
                let mut num = shifted_base_to_ext(
                    &lhs,
                    forward_setup.lookup_additive_part_device(),
                    context,
                )?;
                let tmp = shifted_base_to_ext(
                    &rhs,
                    forward_setup.lookup_additive_part_device(),
                    context,
                )?;
                let mut den = alloc_ext(trace_len, context)?;
                mul(
                    &DeviceVectorChunk::new(&num, 0, trace_len),
                    &DeviceVectorChunk::new(&tmp, 0, trace_len),
                    den.deref_mut(),
                    context.get_exec_stream(),
                )?;
                add_into_y(
                    &DeviceVectorChunk::new(&tmp, 0, trace_len),
                    num.deref_mut(),
                    context.get_exec_stream(),
                )?;
                storage.insert_extension_at_layer(
                    expected_output_layer,
                    output[0],
                    GpuExtensionFieldPoly::new(num),
                );
                storage.insert_extension_at_layer(
                    expected_output_layer,
                    output[1],
                    GpuExtensionFieldPoly::new(den),
                );
            }
            NoFieldGKRRelation::LookupFromMaterializedBaseInputWithSetup {
                input,
                setup,
                output,
            } => {
                let base_input = storage.get_base_layer(*input).clone_shared();
                let c = storage.get_base_layer(setup[0]).clone_shared();
                let d = storage.get_base_layer(setup[1]).clone_shared();
                let shifted = shifted_base_to_ext(
                    &base_input,
                    forward_setup.lookup_additive_part_device(),
                    context,
                )?;
                let shifted_d =
                    shifted_base_to_ext(&d, forward_setup.lookup_additive_part_device(), context)?;
                let mut num = alloc_ext(trace_len, context)?;
                let mut den = alloc_ext(trace_len, context)?;
                let mut temp = alloc_ext(trace_len, context)?;
                mul(
                    &DeviceVectorChunk::new(&shifted, 0, trace_len),
                    &DeviceVectorChunk::new(&shifted_d, 0, trace_len),
                    den.deref_mut(),
                    context.get_exec_stream(),
                )?;
                mul(
                    &DeviceVectorChunk::new(&shifted, 0, trace_len),
                    &c.as_device_chunk(),
                    temp.deref_mut(),
                    context.get_exec_stream(),
                )?;
                set_by_ref(
                    &DeviceVectorChunk::new(&shifted_d, 0, trace_len),
                    num.deref_mut(),
                    context.get_exec_stream(),
                )?;
                sub_into_x(
                    num.deref_mut(),
                    &DeviceVectorChunk::new(&temp, 0, trace_len),
                    context.get_exec_stream(),
                )?;
                storage.insert_extension_at_layer(
                    expected_output_layer,
                    output[0],
                    GpuExtensionFieldPoly::new(num),
                );
                storage.insert_extension_at_layer(
                    expected_output_layer,
                    output[1],
                    GpuExtensionFieldPoly::new(den),
                );
            }
            NoFieldGKRRelation::LookupUnbalancedPairWithMaterializedBaseInputs {
                input,
                remainder,
                output,
            } => {
                let [a, b] = input.map(|addr| storage.get_ext_poly(addr).clone_shared());
                let remainder = storage.get_base_layer(*remainder).clone_shared();
                let shifted = shifted_base_to_ext(
                    &remainder,
                    forward_setup.lookup_additive_part_device(),
                    context,
                )?;
                let mut num = alloc_ext(trace_len, context)?;
                let mut den = alloc_ext(trace_len, context)?;
                mul(
                    &b.as_device_chunk(),
                    &DeviceVectorChunk::new(&shifted, 0, trace_len),
                    den.deref_mut(),
                    context.get_exec_stream(),
                )?;
                mul(
                    &a.as_device_chunk(),
                    &DeviceVectorChunk::new(&shifted, 0, trace_len),
                    num.deref_mut(),
                    context.get_exec_stream(),
                )?;
                add_into_y(
                    &b.as_device_chunk(),
                    num.deref_mut(),
                    context.get_exec_stream(),
                )?;
                storage.insert_extension_at_layer(
                    expected_output_layer,
                    output[0],
                    GpuExtensionFieldPoly::new(num),
                );
                storage.insert_extension_at_layer(
                    expected_output_layer,
                    output[1],
                    GpuExtensionFieldPoly::new(den),
                );
            }
            NoFieldGKRRelation::LookupUnbalancedPairWithMaterializedVectorInputs {
                input,
                remainder,
                output,
            } => {
                let [a, b] = input.map(|addr| storage.get_ext_poly(addr).clone_shared());
                let shifted_remainder = storage.get_ext_poly(*remainder).clone_shared();
                let mut den = alloc_ext(trace_len, context)?;
                let mut num = alloc_ext(trace_len, context)?;
                mul(
                    &b.as_device_chunk(),
                    &shifted_remainder.as_device_chunk(),
                    den.deref_mut(),
                    context.get_exec_stream(),
                )?;
                mul(
                    &a.as_device_chunk(),
                    &shifted_remainder.as_device_chunk(),
                    num.deref_mut(),
                    context.get_exec_stream(),
                )?;
                add_into_y(
                    &b.as_device_chunk(),
                    num.deref_mut(),
                    context.get_exec_stream(),
                )?;
                storage.insert_extension_at_layer(
                    expected_output_layer,
                    output[0],
                    GpuExtensionFieldPoly::new(num),
                );
                storage.insert_extension_at_layer(
                    expected_output_layer,
                    output[1],
                    GpuExtensionFieldPoly::new(den),
                );
            }
            NoFieldGKRRelation::EnforceConstraintsMaxQuadratic { .. } => {}
            NoFieldGKRRelation::LinearBaseFieldRelation { .. }
            | NoFieldGKRRelation::MaxQuadratic { .. }
            | NoFieldGKRRelation::LookupPairFromVectorInputs { .. }
            | NoFieldGKRRelation::LookupPairFromBaseInputs { .. }
            | NoFieldGKRRelation::LookupPairFromMaterializedVectorInputs { .. }
            | NoFieldGKRRelation::LookupPairFromCachedVectorInputs { .. }
            | NoFieldGKRRelation::MaterializeSingleLookupInput { .. }
            | NoFieldGKRRelation::MaterializedVectorLookupInput { .. }
            | NoFieldGKRRelation::UnbalancedGrandProductWithCache { .. } => {
                unimplemented!(
                    "unsupported GPU forward relation: {:?}",
                    gate.enforced_relation
                )
            }
        }
    }
    gates_range.end(stream)?;
    tracing_ranges.push(gates_range);

    Ok(())
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
                NoFieldGKRCacheRelation::MemoryTuple(_) | NoFieldGKRCacheRelation::LongLinear => {}
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

fn schedule_cache_relation<E>(
    layer_idx: usize,
    address: GKRAddress,
    relation: &NoFieldGKRCacheRelation,
    storage: &mut GpuGKRStorage<BF, E>,
    stage1: &GpuGKRStage1Output,
    forward_setup: &GpuGKRForwardSetup<E>,
    external_challenges: &GKRExternalChallenges<BF, E>,
    trace_len: usize,
    context: &ProverContext,
) -> CudaResult<()>
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
            let setup_column = if *range_check_width == 16 { 0 } else { 1 };
            let setup_values = storage
                .get_base_layer(GKRAddress::Setup(setup_column))
                .clone_shared();
            let mut dst = alloc_base(trace_len, context)?;
            gather_rows(
                mapping,
                false,
                0,
                &setup_values.as_device_chunk(),
                dst.deref_mut(),
                context.get_exec_stream(),
            )?;
            assert_eq!(layer_idx, 0);
            storage.insert_base_field_at_layer(0, address, GpuBaseFieldPoly::new(dst));
        }
        NoFieldGKRCacheRelation::VectorizedLookup(rel) => {
            let mapping = if rel.lookup_set_index != DECODER_LOOKUP_FORMAL_SET_INDEX {
                stage1.lookup_mappings.generic_mapping(rel.lookup_set_index)
            } else {
                stage1
                    .lookup_mappings
                    .decoder_mapping()
                    .expect("decoder mapping must be present for decoder lookup relation")
            };
            let mut dst = alloc_ext(trace_len, context)?;
            gather_ext_rows_into_ext(
                mapping,
                forward_setup.generic_lookup(),
                0,
                forward_setup.generic_lookup_len(),
                &mut dst,
                context,
            )?;
            storage.insert_extension_at_layer(0, address, GpuExtensionFieldPoly::new(dst));
        }
        NoFieldGKRCacheRelation::VectorizedLookupSetup(_) => {
            let mut dst = alloc_ext(trace_len, context)?;
            set_by_val(E::ZERO, dst.deref_mut(), context.get_exec_stream())?;
            if forward_setup.generic_lookup_len() > 0 {
                let src = DeviceVectorChunk::new(
                    forward_setup.generic_lookup(),
                    0,
                    forward_setup.generic_lookup_len(),
                );
                let mut prefix =
                    DeviceVectorChunkMut::new(&mut dst, 0, forward_setup.generic_lookup_len());
                set_by_ref(&src, &mut prefix, context.get_exec_stream())?;
            }
            storage.insert_extension_at_layer(0, address, GpuExtensionFieldPoly::new(dst));
        }
        NoFieldGKRCacheRelation::MemoryTuple(rel) => {
            let mut dst = alloc_ext(trace_len, context)?;
            set_by_val(
                external_challenges.permutation_argument_additive_part,
                dst.deref_mut(),
                context.get_exec_stream(),
            )?;
            match rel.address_space {
                CompiledAddressSpaceRelationStrict::Constant(c) => {
                    add_ext_scalar_in_place(
                        &mut dst,
                        ext_from_base(BF::from_u32_unchecked(c)),
                        context,
                    )?;
                }
                CompiledAddressSpaceRelationStrict::Is(offset) => {
                    let source = storage
                        .get_base_layer(GKRAddress::BaseLayerMemory(offset))
                        .clone_shared();
                    add_into_y(
                        &source.as_device_chunk(),
                        dst.deref_mut(),
                        context.get_exec_stream(),
                    )?;
                }
                CompiledAddressSpaceRelationStrict::Not(offset) => {
                    add_ext_scalar_in_place(&mut dst, E::ONE, context)?;
                    let source = storage
                        .get_base_layer(GKRAddress::BaseLayerMemory(offset))
                        .clone_shared();
                    sub_into_x(
                        dst.deref_mut(),
                        &source.as_device_chunk(),
                        context.get_exec_stream(),
                    )?;
                }
            }

            match rel.address {
                CompiledAddressStrict::Constant(c) => {
                    let mut contribution = external_challenges
                        .permutation_argument_linearization_challenges
                        [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                    contribution.mul_assign_by_base(&BF::from_u32_unchecked(c));
                    add_ext_scalar_in_place(&mut dst, contribution, context)?;
                }
                CompiledAddressStrict::U16Space(offset) => {
                    let source = storage
                        .get_base_layer(GKRAddress::BaseLayerMemory(offset))
                        .clone_shared();
                    scale_and_add_base_column(
                        &mut dst,
                        &source,
                        external_challenges.permutation_argument_linearization_challenges
                            [MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX],
                        context,
                    )?;
                }
                CompiledAddressStrict::U32Space([low, high]) => {
                    for (challenge_idx, offset) in [
                        (MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX, low),
                        (MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX, high),
                    ] {
                        let source = storage
                            .get_base_layer(GKRAddress::BaseLayerMemory(offset))
                            .clone_shared();
                        scale_and_add_base_column(
                            &mut dst,
                            &source,
                            external_challenges.permutation_argument_linearization_challenges
                                [challenge_idx],
                            context,
                        )?;
                    }
                }
                CompiledAddressStrict::U32SpaceGeneric(..)
                | CompiledAddressStrict::U32SpaceSpecialIndirect { .. } => {
                    unimplemented!(
                        "unsupported GPU memory tuple address relation: {:?}",
                        rel.address
                    )
                }
            }

            let timestamp_low = storage
                .get_base_layer(GKRAddress::BaseLayerMemory(rel.timestamp[0]))
                .clone_shared();
            scale_and_add_base_column(
                &mut dst,
                &timestamp_low,
                external_challenges.permutation_argument_linearization_challenges
                    [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX],
                context,
            )?;
            if rel.timestamp_offset != 0 {
                let mut contribution = external_challenges
                    .permutation_argument_linearization_challenges
                    [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                contribution
                    .mul_assign_by_base(&BF::from_u32_unchecked(rel.timestamp_offset as u32));
                add_ext_scalar_in_place(&mut dst, contribution, context)?;
            }
            let timestamp_high = storage
                .get_base_layer(GKRAddress::BaseLayerMemory(rel.timestamp[1]))
                .clone_shared();
            scale_and_add_base_column(
                &mut dst,
                &timestamp_high,
                external_challenges.permutation_argument_linearization_challenges
                    [MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX],
                context,
            )?;

            match rel.value {
                RamWordRepresentation::U16Limbs(read_value) => {
                    for (challenge_idx, offset) in [
                        (MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX, read_value[0]),
                        (MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX, read_value[1]),
                    ] {
                        let source = storage
                            .get_base_layer(GKRAddress::BaseLayerMemory(offset))
                            .clone_shared();
                        scale_and_add_base_column(
                            &mut dst,
                            &source,
                            external_challenges.permutation_argument_linearization_challenges
                                [challenge_idx],
                            context,
                        )?;
                    }
                }
                RamWordRepresentation::U8Limbs(..) => {
                    unimplemented!("GPU forward memory tuples do not yet support byte-limb values")
                }
            }

            storage.insert_extension_at_layer(0, address, GpuExtensionFieldPoly::new(dst));
        }
        NoFieldGKRCacheRelation::LongLinear => {
            unimplemented!("unsupported GPU cache relation: {:?}", relation)
        }
    }

    Ok(())
}

fn schedule_dimension_reduction_forward<E>(
    storage: &mut GpuGKRStorage<BF, E>,
    compiled_circuit: &GKRCircuitArtifact<BF>,
    initial_trace_log_2: usize,
    final_trace_log_2: usize,
    forward_scratch: &GpuGKRForwardScratch,
    tracing_ranges: &mut Vec<Range>,
    context: &ProverContext,
) -> CudaResult<(
    usize,
    BTreeMap<usize, BTreeMap<OutputType, DimensionReducingInputOutput>>,
)>
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

        let mut layer_description = BTreeMap::new();
        let mut output_idx = 0;
        let input_trace_len = 1 << input_size_log_2;
        let output_trace_len = input_trace_len / 2;
        let even_indexes = forward_scratch.even_indexes(output_trace_len);
        let odd_indexes = forward_scratch.odd_indexes(output_trace_len);

        for (arg_type, inputs) in layer_inputs {
            let inputs: [_; 2] = inputs.try_into().unwrap();
            match arg_type {
                OutputType::PermutationProduct => {
                    let [read_set, write_set] = inputs;
                    let mut set_outputs = [GKRAddress::placeholder(); 2];
                    for (idx, input) in [read_set, write_set].into_iter().enumerate() {
                        let output = GKRAddress::InnerLayer {
                            layer: current_layer_idx + 1,
                            offset: output_idx,
                        };
                        output_idx += 1;
                        schedule_pairwise_product_reduction(
                            storage,
                            input,
                            output,
                            current_layer_idx + 1,
                            output_trace_len,
                            even_indexes,
                            odd_indexes,
                            context,
                        )?;
                        set_outputs[idx] = output;
                    }
                    layer_description.insert(
                        arg_type,
                        DimensionReducingInputOutput {
                            inputs: inputs.to_vec(),
                            output: set_outputs.to_vec(),
                        },
                    );
                }
                OutputType::Lookup16Bits
                | OutputType::LookupTimestamps
                | OutputType::GenericLookup => {
                    let [num, den] = inputs;
                    let new_num = GKRAddress::InnerLayer {
                        layer: current_layer_idx + 1,
                        offset: output_idx,
                    };
                    output_idx += 1;
                    let new_den = GKRAddress::InnerLayer {
                        layer: current_layer_idx + 1,
                        offset: output_idx,
                    };
                    output_idx += 1;
                    schedule_lookup_pair_reduction(
                        storage,
                        [num, den],
                        [new_num, new_den],
                        current_layer_idx + 1,
                        output_trace_len,
                        even_indexes,
                        odd_indexes,
                        context,
                    )?;
                    layer_description.insert(
                        arg_type,
                        DimensionReducingInputOutput {
                            inputs: inputs.to_vec(),
                            output: [new_num, new_den].to_vec(),
                        },
                    );
                }
            }
        }

        dimension_reduction_description.insert(current_layer_idx, layer_description);
        current_layer_idx += 1;
        round_range.end(stream)?;
        tracing_ranges.push(round_range);
    }

    Ok((current_layer_idx - 1, dimension_reduction_description))
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

fn gather_ext_rows_into_ext<E>(
    indexes: &era_cudart::slice::DeviceSlice<u32>,
    values: &era_cudart::slice::DeviceSlice<E>,
    values_offset: usize,
    values_len: usize,
    result: &mut DeviceAllocation<E>,
    context: &ProverContext,
) -> CudaResult<()>
where
    E: FieldExtension<BF> + Field,
{
    let degree = E::DEGREE;
    assert!(degree.is_power_of_two());
    assert_eq!(size_of::<E>(), size_of::<BF>() * degree);
    assert_eq!(align_of::<E>() % align_of::<BF>(), 0);
    assert_eq!(indexes.len(), result.len());
    assert!(values_len.is_power_of_two());
    assert!(values_offset + values_len <= values.len());

    let values_bf = unsafe {
        // SAFETY: `values_offset..values_offset + values_len` is bounds-checked above and the
        // extension field layout is represented as `degree` contiguous base-field coefficients.
        era_cudart::slice::DeviceSlice::from_raw_parts(
            values.as_ptr().add(values_offset).cast(),
            values_len * degree,
        )
    };
    let result_bf = unsafe {
        era_cudart::slice::DeviceSlice::from_raw_parts_mut(
            result.as_mut_ptr().cast(),
            result.len() * degree,
        )
    };
    let values_matrix = DeviceMatrix::new(values_bf, values_len * degree);
    let mut result_matrix = DeviceMatrixMut::new(result_bf, result.len() * degree);
    gather_rows(
        indexes,
        false,
        degree.trailing_zeros(),
        &values_matrix,
        &mut result_matrix,
        context.get_exec_stream(),
    )
}

fn schedule_pairwise_product_reduction<E>(
    storage: &mut GpuGKRStorage<BF, E>,
    input: GKRAddress,
    output: GKRAddress,
    output_layer: usize,
    output_trace_len: usize,
    even_indexes: &era_cudart::slice::DeviceSlice<u32>,
    odd_indexes: &era_cudart::slice::DeviceSlice<u32>,
    context: &ProverContext,
) -> CudaResult<()>
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
    let source = storage
        .try_get_ext_poly(input)
        .unwrap_or_else(|| panic!("missing dimension reduction input poly for {:?}", input))
        .clone_shared();
    let mut dst = alloc_ext(output_trace_len, context)?;
    gather_ext_rows_into_ext(
        even_indexes,
        source.backing.as_ref(),
        source.offset,
        source.len(),
        &mut dst,
        context,
    )?;
    let mut rhs = alloc_ext(output_trace_len, context)?;
    gather_ext_rows_into_ext(
        odd_indexes,
        source.backing.as_ref(),
        source.offset,
        source.len(),
        &mut rhs,
        context,
    )?;
    mul_into_x(
        dst.deref_mut(),
        &DeviceVectorChunk::new(&rhs, 0, output_trace_len),
        context.get_exec_stream(),
    )?;
    storage.insert_extension_at_layer(output_layer, output, GpuExtensionFieldPoly::new(dst));
    Ok(())
}

fn schedule_lookup_pair_reduction<E>(
    storage: &mut GpuGKRStorage<BF, E>,
    inputs: [GKRAddress; 2],
    outputs: [GKRAddress; 2],
    output_layer: usize,
    output_trace_len: usize,
    even_indexes: &era_cudart::slice::DeviceSlice<u32>,
    odd_indexes: &era_cudart::slice::DeviceSlice<u32>,
    context: &ProverContext,
) -> CudaResult<()>
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
    let num = storage
        .try_get_ext_poly(inputs[0])
        .unwrap_or_else(|| {
            panic!(
                "missing lookup reduction numerator poly for {:?}",
                inputs[0]
            )
        })
        .clone_shared();
    let den = storage
        .try_get_ext_poly(inputs[1])
        .unwrap_or_else(|| {
            panic!(
                "missing lookup reduction denominator poly for {:?}",
                inputs[1]
            )
        })
        .clone_shared();
    let mut new_num = alloc_ext(output_trace_len, context)?;
    gather_ext_rows_into_ext(
        even_indexes,
        num.backing.as_ref(),
        num.offset,
        num.len(),
        &mut new_num,
        context,
    )?;
    let mut den_odd = alloc_ext(output_trace_len, context)?;
    gather_ext_rows_into_ext(
        odd_indexes,
        den.backing.as_ref(),
        den.offset,
        den.len(),
        &mut den_odd,
        context,
    )?;
    mul_into_x(
        new_num.deref_mut(),
        &DeviceVectorChunk::new(&den_odd, 0, output_trace_len),
        context.get_exec_stream(),
    )?;

    let mut new_den = alloc_ext(output_trace_len, context)?;
    gather_ext_rows_into_ext(
        even_indexes,
        den.backing.as_ref(),
        den.offset,
        den.len(),
        &mut new_den,
        context,
    )?;
    mul_into_x(
        new_den.deref_mut(),
        &DeviceVectorChunk::new(&den_odd, 0, output_trace_len),
        context.get_exec_stream(),
    )?;

    let mut temp = alloc_ext(output_trace_len, context)?;
    gather_ext_rows_into_ext(
        odd_indexes,
        num.backing.as_ref(),
        num.offset,
        num.len(),
        &mut temp,
        context,
    )?;
    let mut den_even = alloc_ext(output_trace_len, context)?;
    gather_ext_rows_into_ext(
        even_indexes,
        den.backing.as_ref(),
        den.offset,
        den.len(),
        &mut den_even,
        context,
    )?;
    mul_into_x(
        temp.deref_mut(),
        &DeviceVectorChunk::new(&den_even, 0, output_trace_len),
        context.get_exec_stream(),
    )?;
    add_into_y(
        &DeviceVectorChunk::new(&temp, 0, output_trace_len),
        new_num.deref_mut(),
        context.get_exec_stream(),
    )?;

    storage.insert_extension_at_layer(
        output_layer,
        outputs[0],
        GpuExtensionFieldPoly::new(new_num),
    );
    storage.insert_extension_at_layer(
        output_layer,
        outputs[1],
        GpuExtensionFieldPoly::new(new_den),
    );
    Ok(())
}
