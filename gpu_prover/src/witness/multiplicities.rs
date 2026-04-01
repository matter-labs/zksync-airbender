use std::ops::DerefMut;

use super::NoFieldLinearRelation;
use crate::allocator::tracker::AllocationPlacement;
use crate::ops::cub::device_radix_sort::{get_sort_keys_temp_storage_bytes, sort_keys};
use crate::ops::cub::device_run_length_encode::{encode, get_encode_temp_storage_bytes};
use crate::ops::simple::set_to_zero;
use crate::primitives::context::{DeviceAllocation, ProverContext};
use crate::primitives::device_structures::{
    DeviceMatrixImpl, DeviceMatrixMut, DeviceMatrixMutImpl, MutPtrAndStride, PtrAndStride,
};
use crate::primitives::field::BF;
use crate::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};
use cs::definitions::gkr::NoFieldSingleColumnLookupRelation;
use cs::gkr_compiler::GKRCircuitArtifact;
use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::CudaSlice;

cuda_kernel!(GenerateMultiplicities,
    ab_generate_multiplicities_kernel(
        unique_indexes: *const u32,
        counts: *const u32,
        num_runs: *const u32,
        lookup_mapping: *mut u32,
        lookup_mapping_size: u32,
        multiplicities: MutPtrAndStride<BF>,
        multiplicities_size: u32,
    )
);

pub fn generate_generic_lookup_multiplicities(
    lookup_mapping: &mut impl DeviceMatrixMutImpl<u32>,
    multiplicities: &mut impl DeviceMatrixMutImpl<BF>,
    context: &ProverContext,
) -> CudaResult<()> {
    let stride = lookup_mapping.stride();
    assert!(stride.is_power_of_two());
    assert_eq!(stride, multiplicities.stride());
    let stream = context.get_exec_stream();
    // Multiplicity generation only writes entries present in lookup mappings.
    // Clear the whole destination first to avoid stale values in untouched rows.
    set_to_zero(multiplicities.slice_mut(), stream)?;
    let lookup_mapping_slice = lookup_mapping.slice();
    let lookup_mapping_len = lookup_mapping_slice.len();
    let mut sorted_lookup_mapping =
        context.alloc(lookup_mapping_len, AllocationPlacement::BestFit)?;
    assert!(lookup_mapping_len <= u32::MAX as usize);
    let lookup_mapping_size = lookup_mapping_len as u32;
    // Sort by full key width so placeholder values (e.g. u32::MAX) never alias
    // valid table indexes due to truncated radix bits.
    let lookup_mapping_bits_count = u32::BITS as i32;
    let lookup_mapping_sort_temp_storage_size = get_sort_keys_temp_storage_bytes::<u32>(
        false,
        lookup_mapping_size,
        0,
        lookup_mapping_bits_count,
    )?;
    let mut mapping_sort_temp_storage = context.alloc::<u8>(
        lookup_mapping_sort_temp_storage_size,
        AllocationPlacement::BestFit,
    )?;
    sort_keys(
        false,
        &mut mapping_sort_temp_storage,
        lookup_mapping_slice,
        &mut sorted_lookup_mapping,
        0,
        lookup_mapping_bits_count,
        stream,
    )?;
    drop(mapping_sort_temp_storage);
    let multiplicities_size = multiplicities.slice().len();
    let mut unique_lookup_mapping =
        context.alloc(multiplicities_size, AllocationPlacement::BestFit)?;
    let mut counts = context.alloc(multiplicities_size, AllocationPlacement::BestFit)?;
    let mut num_runs = context.alloc(1, AllocationPlacement::BestFit)?;
    let encode_temp_storage_bytes =
        get_encode_temp_storage_bytes::<u32>(lookup_mapping_size as i32)?;
    let mut encode_temp_storage =
        context.alloc::<u8>(encode_temp_storage_bytes, AllocationPlacement::BestFit)?;
    encode(
        &mut encode_temp_storage,
        &sorted_lookup_mapping,
        &mut unique_lookup_mapping,
        &mut counts,
        &mut num_runs[0],
        stream,
    )?;
    drop(encode_temp_storage);
    let unique_indexes = unique_lookup_mapping.as_ptr();
    let counts = counts.as_ptr();
    let num_runs = num_runs.as_ptr();
    let lookup_mapping_ptr = lookup_mapping.as_mut_ptr();
    let multiplicities_ptr = multiplicities.as_mut_ptr_and_stride();
    assert!(multiplicities_size <= u32::MAX as usize);
    let multiplicities_size = multiplicities_size as u32;
    let count = lookup_mapping_size.max(multiplicities_size);
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GenerateMultiplicitiesArguments::new(
        unique_indexes,
        counts,
        num_runs,
        lookup_mapping_ptr,
        lookup_mapping_size,
        multiplicities_ptr,
        multiplicities_size,
    );
    GenerateMultiplicitiesFunction::default().launch(&config, &args)
}

pub const MAX_LOOKUP_EXPRESSIONS_RELATIONS_COUNT: usize = 8;

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct LookupExpressions {
    relations_count: u32,
    relations: [NoFieldLinearRelation; MAX_LOOKUP_EXPRESSIONS_RELATIONS_COUNT],
}

impl From<&Vec<NoFieldSingleColumnLookupRelation>> for LookupExpressions {
    fn from(value: &Vec<NoFieldSingleColumnLookupRelation>) -> Self {
        let len = value.len();
        assert!(len <= MAX_LOOKUP_EXPRESSIONS_RELATIONS_COUNT);
        let mut relations =
            [NoFieldLinearRelation::default(); MAX_LOOKUP_EXPRESSIONS_RELATIONS_COUNT];
        for (src, dst) in value.iter().map(|r| &r.input).zip(relations.iter_mut()) {
            *dst = src.into();
        }
        Self {
            relations_count: len as u32,
            relations,
        }
    }
}

cuda_kernel!(GenerateRangeCheckLookupMappings,
    ab_generate_range_check_lookup_mapping_kernel(
        memory: PtrAndStride<BF>,
        witness: PtrAndStride<BF>,
        range_check_16_lookup_expressions: LookupExpressions,
        range_check_16_lookup_mapping: MutPtrAndStride<u32>,
        range_check_timestamp_lookup_expressions: LookupExpressions,
        range_check_timestamp_lookup_mapping: MutPtrAndStride<u32>,
        count: u32,
    )
);

pub fn generate_range_check_multiplicities(
    circuit: &GKRCircuitArtifact<BF>,
    memory: &impl DeviceMatrixImpl<BF>,
    witness: &mut impl DeviceMatrixMutImpl<BF>,
    context: &ProverContext,
) -> CudaResult<()> {
    let trace_len = circuit.trace_len;
    assert!(trace_len.is_power_of_two());
    let witness_layout = &circuit.witness_layout;
    let num_memory_cols = circuit.memory_layout.total_width;
    let num_witness_cols = witness_layout.total_width;
    assert_eq!(memory.stride(), trace_len);
    assert_eq!(memory.cols(), num_memory_cols,);
    assert_eq!(witness.stride(), trace_len);
    assert_eq!(witness.cols(), num_witness_cols,);
    let (
        mut range_check_16_lookup_mapping_allocation,
        mut range_check_timestamp_lookup_mapping_allocation,
    ) = generate_range_check_lookup_mappings(circuit, memory, witness, context)?;
    generate_range_check_multiplicities_from_mappings(
        circuit,
        &mut DeviceMatrixMut::new(&mut range_check_16_lookup_mapping_allocation, trace_len),
        &mut DeviceMatrixMut::new(
            &mut range_check_timestamp_lookup_mapping_allocation,
            trace_len,
        ),
        witness,
        context,
    )
}

pub fn generate_range_check_lookup_mappings(
    circuit: &GKRCircuitArtifact<BF>,
    memory: &impl DeviceMatrixImpl<BF>,
    witness: &impl DeviceMatrixImpl<BF>,
    context: &ProverContext,
) -> CudaResult<(DeviceAllocation<u32>, DeviceAllocation<u32>)> {
    let trace_len = circuit.trace_len;
    assert!(trace_len.is_power_of_two());
    let witness_layout = &circuit.witness_layout;
    let num_memory_cols = circuit.memory_layout.total_width;
    let num_witness_cols = witness_layout.total_width;
    assert_eq!(memory.stride(), trace_len);
    assert_eq!(memory.cols(), num_memory_cols);
    assert_eq!(witness.stride(), trace_len);
    assert_eq!(witness.cols(), num_witness_cols);
    let mut range_check_16_lookup_mapping_allocation = context.alloc(
        circuit.range_check_16_lookup_expressions.len() * trace_len,
        AllocationPlacement::BestFit,
    )?;
    set_to_zero(
        range_check_16_lookup_mapping_allocation.deref_mut(),
        context.get_exec_stream(),
    )?;
    let mut range_check_16_lookup_mapping =
        DeviceMatrixMut::new(&mut range_check_16_lookup_mapping_allocation, trace_len);
    let mut range_check_timestamp_lookup_mapping_allocation = context.alloc(
        circuit.timestamp_range_check_lookup_expressions.len() * trace_len,
        AllocationPlacement::BestFit,
    )?;
    set_to_zero(
        range_check_timestamp_lookup_mapping_allocation.deref_mut(),
        context.get_exec_stream(),
    )?;
    let mut range_check_timestamp_lookup_mapping = DeviceMatrixMut::new(
        &mut range_check_timestamp_lookup_mapping_allocation,
        trace_len,
    );
    {
        let range_check_16_lookup_expressions = (&circuit.range_check_16_lookup_expressions).into();
        let range_check_timestamp_lookup_expressions =
            (&circuit.timestamp_range_check_lookup_expressions).into();
        let stream = context.get_exec_stream();
        let witness = witness.as_ptr_and_stride();
        let memory = memory.as_ptr_and_stride();
        let (grid_dim, block_dim) =
            get_grid_block_dims_for_threads_count(WARP_SIZE * 4, trace_len as u32);
        let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
        let args = GenerateRangeCheckLookupMappingsArguments::new(
            memory,
            witness,
            range_check_16_lookup_expressions,
            range_check_16_lookup_mapping.as_mut_ptr_and_stride(),
            range_check_timestamp_lookup_expressions,
            range_check_timestamp_lookup_mapping.as_mut_ptr_and_stride(),
            trace_len as u32,
        );
        GenerateRangeCheckLookupMappingsFunction::default().launch(&config, &args)?;
    }
    Ok((
        range_check_16_lookup_mapping_allocation,
        range_check_timestamp_lookup_mapping_allocation,
    ))
}

pub fn generate_range_check_multiplicities_from_mappings(
    circuit: &GKRCircuitArtifact<BF>,
    range_check_16_lookup_mapping: &mut impl DeviceMatrixMutImpl<u32>,
    range_check_timestamp_lookup_mapping: &mut impl DeviceMatrixMutImpl<u32>,
    witness: &mut impl DeviceMatrixMutImpl<BF>,
    context: &ProverContext,
) -> CudaResult<()> {
    let trace_len = circuit.trace_len;
    assert!(trace_len.is_power_of_two());
    let witness_layout = &circuit.witness_layout;
    let num_witness_cols = witness_layout.total_width;
    assert_eq!(range_check_16_lookup_mapping.stride(), trace_len);
    assert_eq!(range_check_timestamp_lookup_mapping.stride(), trace_len);
    assert_eq!(witness.stride(), trace_len);
    assert_eq!(witness.cols(), num_witness_cols);
    let range_check_16_lookup_multiplicities_range = circuit
        .witness_layout
        .multiplicities_columns_for_range_check_16
        .clone();
    let range_check_16_lookup_multiplicities = &mut witness.slice_mut()
        [range_check_16_lookup_multiplicities_range.start * trace_len
            ..range_check_16_lookup_multiplicities_range.end * trace_len];
    generate_generic_lookup_multiplicities(
        range_check_16_lookup_mapping,
        &mut DeviceMatrixMut::new(range_check_16_lookup_multiplicities, trace_len),
        context,
    )?;
    let range_check_timestamp_lookup_multiplicities = &mut witness.slice_mut()[circuit
        .witness_layout
        .multiplicities_columns_for_timestamp_range_check
        * trace_len..][..trace_len];
    generate_generic_lookup_multiplicities(
        range_check_timestamp_lookup_mapping,
        &mut DeviceMatrixMut::new(range_check_timestamp_lookup_multiplicities, trace_len),
        context,
    )?;
    Ok(())
}
