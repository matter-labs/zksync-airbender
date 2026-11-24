use crate::baby_bear::upstream::SingleColumnLookupRelation;
use crate::baby_bear::witness::LinearRelation;
use crate::upstream::{GKRCircuitArtifact, PrimeField, TIMESTAMP_COLUMNS_NUM_BITS};
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

crate::witness::multiplicities::define_lookup_multiplicities!(
    BF,
    BF,
    BF::CHARACTERISTICS_U32 as usize,
    allocate_counter_storage,
    ab_count_multiplicities_kernel,
    ab_reduce_convert_multiplicities_kernel
);

fn allocate_counter_storage(
    counter_storage_len: usize,
    multiplicities_len: usize,
    context: &ProverContext,
) -> CudaResult<Option<DeviceAllocation<BF>>> {
    if counter_storage_len > multiplicities_len {
        let mut storage = context.alloc(counter_storage_len, AllocationPlacement::BestFit)?;
        set_to_zero(&mut storage, context.get_exec_stream())?;
        Ok(Some(storage))
    } else {
        Ok(None)
    }
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
