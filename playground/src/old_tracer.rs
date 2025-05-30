use fft::GoodAllocator;
use itertools::Itertools;
use prover::risc_v_simulator::abstractions::non_determinism::NonDeterminismCSRSource;
use prover::risc_v_simulator::cycle::MachineConfig;
use prover::tracers::delegation::DelegationWitness;
use prover::tracers::main_cycle_optimized::CycleData;
use prover::tracers::oracles::chunk_lazy_init_and_teardown;
use prover::{ShuffleRamSetupAndTeardown, VectorMemoryImplWithRom};
use std::collections::HashMap;
use trace_and_split::{run_and_split_for_gpu, setups, FinalRegisterValue};
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
) {
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
