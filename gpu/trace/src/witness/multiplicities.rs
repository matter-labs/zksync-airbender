use crate::upstream::{
    GKRCircuitArtifact, PrimeField, SingleColumnLookupRelation, TIMESTAMP_COLUMNS_NUM_BITS,
};
use crate::witness::LinearRelation;
use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::device_structures::{
    DeviceMatrixImpl, DeviceMatrixMut, DeviceMatrixMutImpl, MutPtrAndStride, PtrAndStride,
};
use gpu_core::primitives::field::BF;
use gpu_core::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};
use gpu_ops::simple::set_to_zero;
use gpu_prover_context::ProverContext;

pub const RANGE_CHECK_16_DOMAIN_SIZE: usize = 1 << 16;
pub const TIMESTAMP_RANGE_CHECK_DOMAIN_SIZE: usize = 1 << TIMESTAMP_COLUMNS_NUM_BITS;
const COUNTER_REPLICAS: usize = 8;

cuda_kernel!(CountMultiplicities,
    ab_count_multiplicities_kernel(
        lookup_mapping: *mut u32,
        lookup_mapping_size: u32,
        counter_shards: *mut BF,
        active_counts_len: u32,
        counter_replicas: u32,
    )
);

cuda_kernel!(ReduceConvertMultiplicities,
    ab_reduce_convert_multiplicities_kernel(
        counter_shards: *const BF,
        multiplicities: *mut BF,
        active_counts_len: u32,
        counter_replicas: u32,
    )
);

pub fn generate_lookup_multiplicities(
    lookup_mapping: &mut impl DeviceMatrixMutImpl<u32>,
    multiplicities: &mut impl DeviceMatrixMutImpl<BF>,
    active_counts_len: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    let stride = lookup_mapping.stride();
    assert!(stride.is_power_of_two());
    assert_eq!(stride, multiplicities.stride());
    let mapping_len = lookup_mapping.slice().len();
    let multiplicities_len = multiplicities.slice().len();
    let stream = context.get_exec_stream();
    set_to_zero(multiplicities.slice_mut(), stream)?;
    if mapping_len == 0 {
        return Ok(());
    }
    assert!(mapping_len < BF::CHARACTERISTICS_U32 as usize);
    assert!(active_counts_len > 0);
    assert!(active_counts_len <= multiplicities_len);
    let counter_storage_len = active_counts_len * COUNTER_REPLICAS;
    assert!(counter_storage_len <= u32::MAX as usize);

    let mapping_len = mapping_len as u32;
    let active_counts_len = active_counts_len as u32;
    let counter_replicas = COUNTER_REPLICAS as u32;
    let multiplicities_ptr = multiplicities.as_mut_ptr();
    let mut counter_storage = if counter_storage_len > multiplicities_len {
        let mut storage: DeviceAllocation<BF> =
            context.alloc(counter_storage_len, AllocationPlacement::BestFit)?;
        set_to_zero(&mut storage, stream)?;
        Some(storage)
    } else {
        None
    };
    let counter_shards = counter_storage
        .as_mut()
        .map_or(multiplicities_ptr, |storage| storage.as_mut_ptr());
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, mapping_len);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = CountMultiplicitiesArguments::new(
        lookup_mapping.as_mut_ptr(),
        mapping_len,
        counter_shards,
        active_counts_len,
        counter_replicas,
    );
    CountMultiplicitiesFunction::default().launch(&config, &args)?;

    let (grid_dim, block_dim) =
        get_grid_block_dims_for_threads_count(WARP_SIZE * 4, active_counts_len);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = ReduceConvertMultiplicitiesArguments::new(
        counter_shards,
        multiplicities_ptr,
        active_counts_len,
        counter_replicas,
    );
    ReduceConvertMultiplicitiesFunction::default().launch(&config, &args)?;
    if counter_storage.is_none() {
        set_to_zero(
            &mut multiplicities.slice_mut()[active_counts_len as usize..counter_storage_len],
            stream,
        )?;
    }
    Ok(())
}

// Sized for delegation layouts that need many lookup expressions per circuit.
// Blake currently needs 88 timestamp lookup expressions; keep modest headroom.
pub(crate) const MAX_LOOKUP_EXPRESSIONS_RELATIONS_COUNT: usize = 128;

#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub(crate) struct LookupExpressions {
    relations_count: u32,
    relations: [LinearRelation; MAX_LOOKUP_EXPRESSIONS_RELATIONS_COUNT],
}

impl Default for LookupExpressions {
    fn default() -> Self {
        Self {
            relations_count: 0,
            relations: [LinearRelation::default(); MAX_LOOKUP_EXPRESSIONS_RELATIONS_COUNT],
        }
    }
}

impl From<&Vec<SingleColumnLookupRelation>> for LookupExpressions {
    fn from(value: &Vec<SingleColumnLookupRelation>) -> Self {
        let len = value.len();
        assert!(len <= MAX_LOOKUP_EXPRESSIONS_RELATIONS_COUNT);
        let mut relations = [LinearRelation::default(); MAX_LOOKUP_EXPRESSIONS_RELATIONS_COUNT];
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
        scratch: PtrAndStride<BF>,
        range_check_16_lookup_expressions: LookupExpressions,
        range_check_16_lookup_mapping: MutPtrAndStride<u32>,
        range_check_timestamp_lookup_expressions: LookupExpressions,
        range_check_timestamp_lookup_mapping: MutPtrAndStride<u32>,
        count: u32,
    )
);

pub fn generate_range_check_lookup_mappings(
    circuit: &GKRCircuitArtifact<BF>,
    memory: &impl DeviceMatrixImpl<BF>,
    scratch: &impl DeviceMatrixImpl<BF>,
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
    assert_eq!(scratch.stride(), trace_len);
    assert_eq!(witness.stride(), trace_len);
    assert_eq!(witness.cols(), num_witness_cols);
    let (
        mut range_check_16_lookup_mapping_allocation,
        mut range_check_timestamp_lookup_mapping_allocation,
    ) = allocate_range_check_lookup_mappings(circuit, context)?;
    let mut range_check_16_lookup_mapping =
        DeviceMatrixMut::new(&mut range_check_16_lookup_mapping_allocation, trace_len);
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
        let scratch = scratch.as_ptr_and_stride();
        let (grid_dim, block_dim) =
            get_grid_block_dims_for_threads_count(WARP_SIZE * 4, trace_len as u32);
        let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
        let args = GenerateRangeCheckLookupMappingsArguments::new(
            memory,
            witness,
            scratch,
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

pub fn allocate_range_check_lookup_mappings(
    circuit: &GKRCircuitArtifact<BF>,
    context: &ProverContext,
) -> CudaResult<(DeviceAllocation<u32>, DeviceAllocation<u32>)> {
    let trace_len = circuit.trace_len;
    assert!(trace_len.is_power_of_two());
    let range_check_16_lookup_mapping_allocation = context.alloc(
        circuit.range_check_16_lookup_expressions.len() * trace_len,
        AllocationPlacement::BestFit,
    )?;
    let range_check_timestamp_lookup_mapping_allocation = context.alloc(
        circuit.timestamp_range_check_lookup_expressions.len() * trace_len,
        AllocationPlacement::BestFit,
    )?;
    Ok((
        range_check_16_lookup_mapping_allocation,
        range_check_timestamp_lookup_mapping_allocation,
    ))
}
