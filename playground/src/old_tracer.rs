use cs::definitions::split_timestamp;
use cs::one_row_compiler::CompiledCircuitArtifact;
use execution_utils::{find_binary_exit_point, get_padded_binary};
use fft::{adjust_to_zero_c0_var_length, GoodAllocator, LdePrecomputations, Twiddles};
use field::{Field, Mersenne31Complex, Mersenne31Field, Mersenne31Quartic};
use itertools::Itertools;
use prover::definitions::{
    produce_register_contribution_into_memory_accumulator_raw, AuxArgumentsBoundaryValues,
    ExternalChallenges, ExternalValues, OPTIMAL_FOLDING_PROPERTIES,
};
use prover::merkle_trees::{DefaultTreeConstructor, MerkleTreeCapVarLength, MerkleTreeConstructor};
use prover::prover_stages::stage5::Query;
use prover::prover_stages::{prove, Proof};
use prover::risc_v_simulator::abstractions::non_determinism::{
    NonDeterminismCSRSource, QuasiUARTSource,
};
use prover::risc_v_simulator::cycle::MachineConfig;
use prover::tracers::delegation::DelegationWitness;
use prover::tracers::main_cycle_optimized::CycleData;
use prover::tracers::oracles::chunk_lazy_init_and_teardown;
use prover::tracers::oracles::delegation_oracle::DelegationCircuitOracle;
use prover::tracers::oracles::main_risc_v_circuit::MainRiscVOracle;
use prover::transcript::Seed;
use prover::{
    evaluate_delegation_memory_witness, evaluate_memory_witness, evaluate_witness,
    DelegationMemoryOnlyWitnessEvaluationData, MemoryOnlyWitnessEvaluationData,
    ShuffleRamSetupAndTeardown, VectorMemoryImplWithRom, WitnessEvaluationAuxData,
};
use std::alloc::Global;
use std::collections::HashMap;
use std::ffi::CStr;
use std::io::Read;
use std::mem;
use std::mem::MaybeUninit;
use std::sync::Arc;
use trace_and_split::setups::{
    risc_v_cycles, DelegationCircuitPrecomputations, MainCircuitPrecomputations,
};
use trace_and_split::{
    fs_transform_for_memory_and_delegation_arguments, run_and_split_for_gpu, setups,
    FinalRegisterValue,
};
use trace_holder::RowMajorTrace;
use worker::Worker;

pub fn trace_execution_for_gpu<
    ND: NonDeterminismCSRSource<VectorMemoryImplWithRom>,
    C: MachineConfig,
    A: GoodAllocator,
>(
    num_instances_upper_bound: usize,
    bytecode: &[u32],
    mut non_determinism: ND,
    worker: &Worker,
) -> (
    Vec<CycleData<C, A>>,
    (
        usize, // number of empty ones to assume
        Vec<ShuffleRamSetupAndTeardown<A>>,
    ),
    HashMap<u16, Vec<DelegationWitness<A>>>,
    Vec<FinalRegisterValue>,
)
where
    [(); { C::SUPPORT_LOAD_LESS_THAN_WORD } as usize]:,
{
    let cycles_per_circuit = setups::num_cycles_for_machine::<C>();
    let max_cycles_to_run = num_instances_upper_bound * cycles_per_circuit;

    let delegation_factories = setups::delegation_factories_for_machine::<C, A>();

    let (
        final_pc,
        main_circuits_witness,
        delegation_circuits_witness,
        final_register_values,
        init_and_teardown_chunks,
    ) = run_and_split_for_gpu::<ND, C, A>(
        max_cycles_to_run,
        bytecode,
        &mut non_determinism,
        delegation_factories,
        worker,
    );

    println!(
        "Program finished execution with final pc = 0x{:08x} and final register state\n{}",
        final_pc,
        final_register_values
            .iter()
            .enumerate()
            .map(|(idx, r)| format!("x{} = {}", idx, r.value))
            .collect::<Vec<_>>()
            .join(", ")
    );

    // we just need to chunk inits/teardowns

    let init_and_teardown_chunks = chunk_lazy_init_and_teardown(
        main_circuits_witness.len(),
        cycles_per_circuit,
        &init_and_teardown_chunks,
        worker,
    );

    (
        main_circuits_witness,
        init_and_teardown_chunks,
        delegation_circuits_witness,
        final_register_values,
    )
}
