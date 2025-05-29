use super::layout::DelegationProcessingLayout;
use super::ram_access::{
    RegisterAndIndirectAccessDescription, RegisterAndIndirectAccessTimestampComparisonAuxVars,
};
use super::trace_delegation::{DelegationTraceDevice, DelegationTraceRaw};
use super::BF;
use crate::device_structures::{
    DeviceMatrixImpl, DeviceMatrixMut, DeviceMatrixMutImpl, MutPtrAndStride,
};
use crate::prover::context::ProverContext;
use crate::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};
use cs::definitions::MemorySubtree;
use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;

const MAX_REGISTER_AND_INDIRECT_ACCESSES_COUNT: usize = 4;

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
struct DelegationMemorySubtree {
    delegation_processor_layout: DelegationProcessingLayout,
    register_and_indirect_accesses_count: u32,
    register_and_indirect_accesses:
        [RegisterAndIndirectAccessDescription; MAX_REGISTER_AND_INDIRECT_ACCESSES_COUNT],
}

impl From<&MemorySubtree> for DelegationMemorySubtree {
    fn from(value: &MemorySubtree) -> Self {
        assert!(value.shuffle_ram_inits_and_teardowns.is_none());
        assert!(value.shuffle_ram_access_sets.is_empty());
        assert!(value.delegation_request_layout.is_none());
        assert_eq!(value.batched_ram_accesses.len(), 0);
        let delegation_processor_layout = value.delegation_processor_layout.unwrap().into();
        let register_and_indirect_accesses_count =
            value.register_and_indirect_accesses.len() as u32;
        assert!(
            register_and_indirect_accesses_count <= MAX_REGISTER_AND_INDIRECT_ACCESSES_COUNT as u32
        );
        let mut register_and_indirect_accesses = [RegisterAndIndirectAccessDescription::default();
            MAX_REGISTER_AND_INDIRECT_ACCESSES_COUNT];
        for (i, value) in value.register_and_indirect_accesses.iter().enumerate() {
            register_and_indirect_accesses[i] = value.clone().into();
        }
        Self {
            delegation_processor_layout,
            register_and_indirect_accesses_count,
            register_and_indirect_accesses,
        }
    }
}

cuda_kernel!(GenerateMemoryValuesDelegation,
    generate_memory_values_delegation_kernel(
        subtree: DelegationMemorySubtree,
        trace: DelegationTraceRaw,
        memory: MutPtrAndStride<BF>,
        count: u32,
    )
);

cuda_kernel!(GenerateMemoryAndWitnessValuesDelegation,
    generate_memory_and_witness_values_delegation_kernel(
        subtree: DelegationMemorySubtree,
        aux_vars: RegisterAndIndirectAccessTimestampComparisonAuxVars,
        trace: DelegationTraceRaw,
        memory: MutPtrAndStride<BF>,
        witness: MutPtrAndStride<BF>,
        count: u32,
    )
);

pub(crate) fn generate_memory_values_delegation(
    subtree: &MemorySubtree,
    trace: &DelegationTraceDevice<impl ProverContext>,
    memory: &mut DeviceMatrixMut<BF>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = trace.num_requests;
    assert_eq!(memory.stride(), count + 1);
    assert_eq!(memory.cols(), subtree.total_width);
    assert!(count <= u32::MAX as usize);
    let count = count as u32;
    let subtree = subtree.into();
    let trace: DelegationTraceRaw = trace.into();
    let memory = memory.as_mut_ptr_and_stride();
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GenerateMemoryValuesDelegationArguments::new(subtree, trace, memory, count);
    GenerateMemoryValuesDelegationFunction::default().launch(&config, &args)
}

pub(crate) fn generate_memory_and_witness_values_delegation(
    subtree: &MemorySubtree,
    aux_vars: &cs::definitions::RegisterAndIndirectAccessTimestampComparisonAuxVars,
    trace: &DelegationTraceDevice<impl ProverContext>,
    memory: &mut DeviceMatrixMut<BF>,
    witness: &mut DeviceMatrixMut<BF>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = trace.num_requests;
    assert_eq!(memory.stride(), count + 1);
    assert_eq!(memory.cols(), subtree.total_width);
    assert_eq!(witness.stride(), count + 1);
    assert!(count <= u32::MAX as usize);
    let count = count as u32;
    let subtree = subtree.into();
    let aux_vars = aux_vars.into();
    let trace = trace.into();
    let memory = memory.as_mut_ptr_and_stride();
    let witness = witness.as_mut_ptr_and_stride();
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GenerateMemoryAndWitnessValuesDelegationArguments::new(
        subtree, aux_vars, trace, memory, witness, count,
    );
    GenerateMemoryAndWitnessValuesDelegationFunction::default().launch(&config, &args)
}
