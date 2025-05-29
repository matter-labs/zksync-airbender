use super::column::ColumnAddress;
use super::layout::{DelegationRequestLayout, ShuffleRamInitAndTeardownLayout};
use super::ram_access::{ShuffleRamAuxComparisonSet, ShuffleRamQueryColumns};
use super::trace_main::{
    MainTraceDevice, MainTraceRaw, ShuffleRamSetupAndTeardownDevice, ShuffleRamSetupAndTeardownRaw,
};
use super::BF;
use crate::device_structures::{
    DeviceMatrixImpl, DeviceMatrixMut, DeviceMatrixMutImpl, MutPtrAndStride,
};
use crate::prover::context::ProverContext;
use crate::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};
use cs::definitions::{MemorySubtree, TimestampScalar};
use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::CudaSlice;
use era_cudart::stream::CudaStream;

const MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT: usize = 4;

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
struct MainMemorySubtree {
    shuffle_ram_inits_and_teardowns: ShuffleRamInitAndTeardownLayout,
    shuffle_ram_access_sets_count: u32,
    shuffle_ram_access_sets: [ShuffleRamQueryColumns; MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT],
    delegation_request_layout: super::option::Option<DelegationRequestLayout>,
}

impl From<&MemorySubtree> for MainMemorySubtree {
    fn from(value: &MemorySubtree) -> Self {
        assert!(value.delegation_processor_layout.is_none());
        assert!(value.batched_ram_accesses.is_empty());
        assert!(value.register_and_indirect_accesses.is_empty());
        let shuffle_ram_inits_and_teardowns = value.shuffle_ram_inits_and_teardowns.unwrap().into();
        let shuffle_ram_access_sets_count = value.shuffle_ram_access_sets.len() as u32;
        assert!(shuffle_ram_access_sets_count <= MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT as u32);
        let mut shuffle_ram_access_sets =
            [ShuffleRamQueryColumns::default(); MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT];
        for (i, value) in value.shuffle_ram_access_sets.iter().enumerate() {
            shuffle_ram_access_sets[i] = value.clone().into();
        }
        let delegation_request_layout = value.delegation_request_layout.into();
        Self {
            shuffle_ram_inits_and_teardowns,
            shuffle_ram_access_sets_count,
            shuffle_ram_access_sets,
            delegation_request_layout,
        }
    }
}

#[repr(C)]
struct MemoryQueriesTimestampComparisonAuxVars {
    addresses_count: u32,
    addresses: [ColumnAddress; MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT],
}

impl From<&[cs::definitions::ColumnAddress]> for MemoryQueriesTimestampComparisonAuxVars {
    fn from(value: &[cs::definitions::ColumnAddress]) -> Self {
        let len = value.len();
        assert!(len <= MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT);
        let mut addresses = [ColumnAddress::default(); MAX_SHUFFLE_RAM_ACCESS_SETS_COUNT];
        for (i, &address) in value.iter().enumerate() {
            addresses[i] = address.into();
        }
        Self {
            addresses_count: len as u32,
            addresses,
        }
    }
}

cuda_kernel!(GenerateMemoryValuesMain,
    generate_memory_values_main_kernel(
        subtree: MainMemorySubtree,
        setup_and_teardown: ShuffleRamSetupAndTeardownRaw,
        trace: MainTraceRaw,
        memory: MutPtrAndStride<BF>,
        count: u32,
    )
);

cuda_kernel!(GenerateMemoryAndWitnessValuesMain,
    generate_memory_and_witness_values_main_kernel(
        subtree: MainMemorySubtree,
        memory_queries_timestamp_comparison_aux_vars: MemoryQueriesTimestampComparisonAuxVars,
        setup_and_teardown: ShuffleRamSetupAndTeardownRaw,
        lazy_init_address_aux_vars: ShuffleRamAuxComparisonSet,
        trace: MainTraceRaw,
        timestamp_high_from_circuit_sequence: TimestampScalar,
        memory: MutPtrAndStride<BF>,
        witness: MutPtrAndStride<BF>,
        count: u32,
    )
);

pub(crate) fn generate_memory_values_main(
    subtree: &MemorySubtree,
    setup_and_teardown: &ShuffleRamSetupAndTeardownDevice<impl ProverContext>,
    trace: &MainTraceDevice<impl ProverContext>,
    memory: &mut DeviceMatrixMut<BF>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = trace.cycle_data.len();
    assert_eq!(setup_and_teardown.lazy_init_data.len(), count);
    assert_eq!(memory.stride(), count + 1);
    assert_eq!(memory.cols(), subtree.total_width);
    assert!(count <= u32::MAX as usize);
    let count = count as u32;
    let subtree = subtree.into();
    let setup_and_teardown = setup_and_teardown.into();
    let trace = trace.into();
    let memory = memory.as_mut_ptr_and_stride();
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args =
        GenerateMemoryValuesMainArguments::new(subtree, setup_and_teardown, trace, memory, count);
    GenerateMemoryValuesMainFunction::default().launch(&config, &args)
}

pub(crate) fn generate_memory_and_witness_values_main(
    subtree: &MemorySubtree,
    memory_queries_timestamp_comparison_aux_vars: &[cs::definitions::ColumnAddress],
    setup_and_teardown: &ShuffleRamSetupAndTeardownDevice<impl ProverContext>,
    lazy_init_address_aux_vars: &cs::definitions::ShuffleRamAuxComparisonSet,
    trace: &MainTraceDevice<impl ProverContext>,
    timestamp_high_from_circuit_sequence: TimestampScalar,
    memory: &mut DeviceMatrixMut<BF>,
    witness: &mut DeviceMatrixMut<BF>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = trace.cycle_data.len();
    assert_eq!(setup_and_teardown.lazy_init_data.len(), count);
    assert_eq!(memory.stride(), count + 1);
    assert_eq!(memory.cols(), subtree.total_width);
    assert_eq!(witness.stride(), count + 1);
    assert!(count <= u32::MAX as usize);
    let count = count as u32;
    let subtree = subtree.into();
    let memory_queries_timestamp_comparison_aux_vars =
        memory_queries_timestamp_comparison_aux_vars.into();
    let setup_and_teardown = setup_and_teardown.into();
    let lazy_init_address_aux_vars = lazy_init_address_aux_vars.into();
    let trace = trace.into();
    let memory = memory.as_mut_ptr_and_stride();
    let witness = witness.as_mut_ptr_and_stride();
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GenerateMemoryAndWitnessValuesMainArguments::new(
        subtree,
        memory_queries_timestamp_comparison_aux_vars,
        setup_and_teardown,
        lazy_init_address_aux_vars,
        trace,
        timestamp_high_from_circuit_sequence,
        memory,
        witness,
        count,
    );
    GenerateMemoryAndWitnessValuesMainFunction::default().launch(&config, &args)
}
