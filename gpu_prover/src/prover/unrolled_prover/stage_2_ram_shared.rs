use crate::device_structures::{MutPtrAndStride, PtrAndStride};
use crate::field::BaseField;
use crate::prover::arg_utils::*;
use crate::utils::WARP_SIZE;

use cs::definitions::DelegationProcessingLayout;
use cs::one_row_compiler::CompiledCircuitArtifact;
use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;
use prover::definitions::{
    ExternalMachineStateArgumentChallenges, ExternalMemoryArgumentChallenges,
};

type BF = BaseField;

cuda_kernel!(
    LazyInitAndRamAccess,
    lazy_init_and_ram_access,
    memory_challenges: MemoryChallenges,
    shuffle_ram_accesses: ShuffleRamAccesses,
    lazy_init_teardown_layouts: LazyInitTeardownLayouts,
    setup_cols: PtrAndStride<BF>,
    memory_cols: PtrAndStride<BF>,
    stage_2_e4_cols: MutPtrAndStride<BF>,
    memory_timestamp_high_from_circuit_idx: BF,
    memory_args_start: u32,
    log_n: u32,
);

lazy_init_and_ram_access!(ab_lazy_init_and_ram_access_kernel);

cuda_kernel!(
    UnrolledGrandProductContributions,
    unrolled_grand_product_contributions,
    memory_challenges: MemoryChallenges,
    machine_state_challenges: MachineStateChallenges,
    lazy_init_teardown_layouts: LazyInitTeardownLayouts,
    shuffle_ram_accesses: ShuffleRamAccesses,
    machine_state_layout: MachineStateLayout,
    memory_cols: PtrAndStride<BF>,
    stage_2_e4_cols: MutPtrAndStride<BF>,
    ram_access_args_start: u32,
    mask_arg_col: u32,
    execute_col: u32,
    process_ram_access: bool,
    process_mask: bool,
    log_n: u32,
);

unrolled_grand_product_contributions!(ab_unrolled_grand_product_contributions_kernel);

cuda_kernel!(
    RegisterAndIndirectMemoryArgs,
    register_and_indirect_memory_args,
    memory_challenges: MemoryChallenges,
    register_and_indirect_accesses: RegisterAndIndirectAccesses,
    memory_cols: PtrAndStride<BF>,
    stage_2_e4_cols: MutPtrAndStride<BF>,
    memory_args_start: u32,
    log_n: u32,
);

register_and_indirect_memory_args!(ab_register_and_indirect_memory_args_kernel);

pub(crate) fn stage2_process_lazy_init_and_ram_access(
    circuit: &CompiledCircuitArtifact<BF>,
    challenges: MemoryChallenges,
    memory_timestamp_high_from_circuit_idx: BF,
    lazy_init_teardown_layouts: LazyInitTeardownLayouts,
    setup_cols: PtrAndStride<BF>,
    memory_cols: PtrAndStride<BF>,
    stage_2_e4_cols: MutPtrAndStride<BF>,
    memory_args_start: usize,
    log_n: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(lazy_init_teardown_layouts.process_shuffle_ram_init, true);
    let write_timestamp_in_setup_start = circuit.setup_layout.timestamp_setup_columns.start();
    let shuffle_ram_access_sets = &circuit.memory_layout.shuffle_ram_access_sets;
    let shuffle_ram_accesses =
        ShuffleRamAccesses::new(shuffle_ram_access_sets, write_timestamp_in_setup_start);
    let block_dim = WARP_SIZE * 4;
    let grid_dim = ((1 << log_n) + block_dim - 1) / block_dim;
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = LazyInitAndRamAccessArguments::new(
        challenges,
        shuffle_ram_accesses,
        lazy_init_teardown_layouts,
        setup_cols,
        memory_cols,
        stage_2_e4_cols,
        memory_timestamp_high_from_circuit_idx,
        memory_args_start as u32,
        log_n,
    );
    LazyInitAndRamAccessFunction(ab_lazy_init_and_ram_access_kernel).launch(&config, &args)
}

// Invokes a single kernel to conditionally handle lazy init, ram access,
// machine state permutation, and masking.
pub(crate) fn stage2_process_unrolled_grand_product_contributions<F: Fn(usize) -> usize>(
    circuit: &CompiledCircuitArtifact<BF>,
    memory_challenges: &ExternalMemoryArgumentChallenges,
    machine_state_challenges: &ExternalMachineStateArgumentChallenges,
    lazy_init_teardown_layouts: LazyInitTeardownLayouts,
    memory_cols: PtrAndStride<BF>,
    stage_2_e4_cols: MutPtrAndStride<BF>,
    log_n: u32,
    translate_e4_offset: &F,
    stream: &CudaStream,
) -> CudaResult<()> {
    let memory_challenges = MemoryChallenges::new(memory_challenges);
    let machine_state_challenges = MachineStateChallenges::new(machine_state_challenges);
    let intermediate_polys_for_memory_argument = &circuit
        .stage_2_layout
        .intermediate_polys_for_memory_argument;
    assert_eq!(
        intermediate_polys_for_memory_argument.num_elements(),
        circuit.memory_layout.shuffle_ram_access_sets.len(),
    );
    let intermediate_polys_for_permutation_masking = &circuit
        .stage_2_layout
        .intermediate_polys_for_permutation_masking;
    // lazy init circuit does not use masking
    if circuit
        .witness_layout
        .multiplicities_columns_for_timestamp_range_check
        .num_elements()
        == 0
    {
        assert_eq!(intermediate_polys_for_permutation_masking.num_elements(), 0);
    } else {
        assert_eq!(intermediate_polys_for_permutation_masking.num_elements(), 1);
    }
    let process_ram_access = intermediate_polys_for_memory_argument.num_elements() > 0;
    let process_mask = intermediate_polys_for_permutation_masking.num_elements() > 0;
    let (shuffle_ram_accesses, ram_access_args_start) = if process_ram_access {
        let cycle_timestamp_columns = circuit
            .memory_layout
            .intermediate_state_layout
            .unwrap()
            .timestamp;
        let shuffle_ram_access_sets = &circuit.memory_layout.shuffle_ram_access_sets;
        let shuffle_ram_accesses =
            ShuffleRamAccesses::new(shuffle_ram_access_sets, cycle_timestamp_columns.start());
        let ram_access_args_start =
            translate_e4_offset(intermediate_polys_for_memory_argument.start());
        (shuffle_ram_accesses, ram_access_args_start)
    } else {
        (ShuffleRamAccesses::default(), 0)
    };
    let machine_state_layout = MachineStateLayout::new(circuit, translate_e4_offset);
    let (mask_arg_col, execute_col) = if process_mask {
        let intermediate_state_layout = circuit.memory_layout.intermediate_state_layout.unwrap();
        (
            translate_e4_offset(intermediate_polys_for_permutation_masking.start()),
            intermediate_state_layout.execute.start(),
        )
    } else {
        (0, 0)
    };
    let block_dim = WARP_SIZE * 4;
    let grid_dim = ((1 << log_n) + block_dim - 1) / block_dim;
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = UnrolledGrandProductContributionsArguments::new(
        memory_challenges,
        machine_state_challenges,
        lazy_init_teardown_layouts,
        shuffle_ram_accesses,
        machine_state_layout,
        memory_cols,
        stage_2_e4_cols,
        ram_access_args_start as u32,
        mask_arg_col as u32,
        execute_col as u32,
        process_ram_access,
        process_mask,
        log_n,
    );
    UnrolledGrandProductContributionsFunction(ab_unrolled_grand_product_contributions_kernel)
        .launch(&config, &args)
}

pub(crate) fn stage2_process_registers_and_indirect_access_in_delegation(
    circuit: &CompiledCircuitArtifact<BF>,
    challenges: MemoryChallenges,
    layout: &DelegationProcessingLayout,
    memory_cols: PtrAndStride<BF>,
    stage_2_e4_cols: MutPtrAndStride<BF>,
    memory_args_start: usize,
    log_n: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let register_and_indirect_accesses = &circuit.memory_layout.register_and_indirect_accesses;
    assert!(register_and_indirect_accesses.len() > 0);
    let write_timestamp_col = layout.write_timestamp.start();
    let register_and_indirect_accesses = RegisterAndIndirectAccesses::new(
        &challenges,
        register_and_indirect_accesses,
        write_timestamp_col,
    );
    let block_dim = WARP_SIZE * 4;
    let grid_dim = ((1 << log_n) + block_dim - 1) / block_dim;
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = RegisterAndIndirectMemoryArgsArguments::new(
        challenges,
        register_and_indirect_accesses,
        memory_cols,
        stage_2_e4_cols,
        memory_args_start as u32,
        log_n,
    );
    RegisterAndIndirectMemoryArgsFunction(ab_register_and_indirect_memory_args_kernel)
        .launch(&config, &args)
}
