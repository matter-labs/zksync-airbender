use crate::bincode_serialize_to_file;
use crate::DUMP_WITNESS_VAR;
use ::prover::gkr::witness_gen::delegation_circuits::evaluate_gkr_witness_for_delegation_circuit;
use circuit_common::DelegationCircuit;
use common_constants::TimestampScalar;
use common_constants::ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX;
use common_constants::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER;
use common_constants::BLAKE2S_DELEGATION_CSR_REGISTER;
use common_constants::BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER;
use common_constants::INITIAL_PC;
use common_constants::INITIAL_TIMESTAMP;
use common_constants::JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX;
use common_constants::KECCAK_SPECIAL5_CSR_REGISTER;
use common_constants::LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX;
use common_constants::LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX;
use common_constants::MUL_DIV_CIRCUIT_FAMILY_IDX;
use common_constants::SHIFT_BINARY_CIRCUIT_FAMILY_IDX;
use common_constants::TIMESTAMP_STEP;
use prover::cs::utils::split_timestamp;
use prover::definitions::FinalRegisterValue;
use prover::definitions::*;
use prover::fft::*;
use prover::field::baby_bear::base::BabyBearField;
use prover::field::baby_bear::ext4::BabyBearExt4;
use prover::field::*;
use prover::gkr::prover::GKRExternalChallenges;
use prover::gkr::prover::GKRProof;
use prover::gkr::prover_config::ProverConfig;
use prover::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
use prover::gkr::witness_gen::family_circuits::evaluate_gkr_witness_for_executor_family;
use prover::gkr::witness_gen::oracles::*;
use prover::merkle_trees::ColumnMajorMerkleTreeConstructor;
use prover::merkle_trees::DefaultTreeConstructor;
use prover::tracers::oracles::transpiler_oracles::delegation::DelegationOracle;
use prover::worker;
use riscv_transpiler::cycle::MachineConfig;
use riscv_transpiler::cycle::NUM_REGISTERS;
use riscv_transpiler::vm::Counters;
use riscv_transpiler::vm::DelegationsAndFamiliesCounters;
use riscv_transpiler::vm::RamWithRomRegion;
use riscv_transpiler::vm::Register;
use riscv_transpiler::vm::SimpleSnapshotter;
use riscv_transpiler::vm::SimpleTape;
use riscv_transpiler::vm::State;
use riscv_transpiler::witness::delegation::bigint::BigintAbiDescription;
use riscv_transpiler::witness::delegation::blake2_g_function::Blake2sGFunctionAbiDescription;
use riscv_transpiler::witness::delegation::blake2_round_function::Blake2sRoundFunctionAbiDescription;
use riscv_transpiler::witness::delegation::keccak_special5::KeccakSpecial5AbiDescription;
use riscv_transpiler::witness::DelegationAbiDescription;
use riscv_transpiler::witness::*;
use setups::DelegationCircuitSetup;
use setups::UnrolledCircuitSetupParams;
use setups::UnrolledCircuitWitnessEvalFn;
use std::alloc::Global;
use std::collections::BTreeMap;
use std::collections::HashMap;
use trace_and_split::commit_memory_tree_for_delegation_circuit;
use trace_and_split::commit_memory_tree_for_inits_and_teardowns;
use trace_and_split::commit_memory_tree_for_unrolled_mem_circuits;
use trace_and_split::commit_memory_tree_for_unrolled_nonmem_circuits;
use trace_and_split::fs_transform_unrolled_for_permutation_argument;

pub fn run_unrolled_machine_in_full<M: MachineConfig, C: Counters>(
    cycles_bound: usize,
    binary_image: &[u32],
    text_section: &[u32],
    ram_bound: usize,
    initial_counters: C,
    mut non_determinism: impl riscv_transpiler::vm::NonDeterminismCSRSource,
) -> (
    (u32, TimestampScalar),
    SimpleSnapshotter<C, { common_constants::ROM_SECOND_WORD_BITS }, Vec<(u32, (u32, u32))>>,
    C,
    RamWithRomRegion<{ common_constants::ROM_SECOND_WORD_BITS }>,
    [Register; NUM_REGISTERS],
    SimpleTape,
    State<C>,
) {
    use riscv_transpiler::ir::simple_instruction_set::*;
    use riscv_transpiler::vm::*;

    let instructions: Vec<Instruction> =
        preprocess_bytecode::<M::DecodingOptions, true>(&text_section);
    let tape = SimpleTape::new(&instructions);
    let mut ram = RamWithRomRegion::<{ common_constants::ROM_SECOND_WORD_BITS }>::from_rom_content(
        &binary_image,
        ram_bound,
    );

    let mut state = State::initial_with_counters(initial_counters);
    let mut snapshotter =
        SimpleSnapshotter::<C, { common_constants::ROM_SECOND_WORD_BITS }>::new_with_cycle_limit(
            cycles_bound,
            state,
        );

    let is_program_finished = VM::<C>::run_basic_unrolled::<_, _, _, BabyBearField>(
        &mut state,
        &mut ram,
        &mut snapshotter,
        &tape,
        cycles_bound,
        &mut non_determinism,
    );
    assert!(is_program_finished); // check that we reached looping state (ie. end state for our vm)

    let exact_cycles_passed = (state.timestamp - INITIAL_TIMESTAMP) / TIMESTAMP_STEP;
    println!("Passed exactly {} cycles", exact_cycles_passed);

    let counters = snapshotter.snapshots.last().unwrap().state.counters;
    let final_pc = state.pc;
    let final_timestamp = state.timestamp;

    (
        (final_pc, final_timestamp),
        snapshotter,
        counters,
        ram,
        state.registers,
        tape,
        state,
    )
}

pub fn make_tracer_buffers<T: Copy>(
    empty_value: T,
    mut num_calls: usize,
    capacity_per_circuit: usize,
) -> Vec<Vec<T>> {
    assert!(capacity_per_circuit.is_power_of_two());
    let mut result = Vec::new();
    while num_calls > 0 {
        let capacity;
        if num_calls >= capacity_per_circuit {
            capacity = capacity_per_circuit;
            num_calls -= capacity_per_circuit;
        } else {
            capacity = num_calls;
            num_calls = 0;
        }
        result.push(vec![empty_value; capacity]);
    }

    result
}

pub fn replay_non_mem_circuit_family<C: Counters, const FAMILY_IDX: u8>(
    initial_counters: C,
    snapshotter: &SimpleSnapshotter<
        C,
        { common_constants::ROM_SECOND_WORD_BITS },
        Vec<(u32, (u32, u32))>,
    >,
    tape: &SimpleTape,
    cycles_bound: usize,
    expected_final_state: &State<C>,
    capacity_per_circuit: usize,
    final_counters: C,
) -> Vec<Vec<NonMemoryOpcodeTracingDataWithTimestamp>> {
    use riscv_transpiler::replayer::ReplayerRam;
    use riscv_transpiler::replayer::ReplayerVM;
    use riscv_transpiler::vm::ReplayBuffer;

    let mut state = State::initial_with_counters(initial_counters);

    let mut ram_log_buffers = snapshotter
        .reads_buffer
        .make_range(0..snapshotter.reads_buffer.len());

    let mut ram = ReplayerRam::<{ common_constants::ROM_SECOND_WORD_BITS }> {
        ram_log: &mut ram_log_buffers,
    };

    let mut buffers = make_tracer_buffers::<NonMemoryOpcodeTracingDataWithTimestamp>(
        NonMemoryOpcodeTracingDataWithTimestamp::default(),
        final_counters.get_calls_to_circuit_family::<FAMILY_IDX>(),
        capacity_per_circuit,
    );
    let mut buffer_ref_mut: Vec<_> = buffers.iter_mut().map(|el| &mut el[..]).collect();
    let mut tracer = NonMemDestinationHolder::<FAMILY_IDX> {
        buffers: &mut buffer_ref_mut,
    };

    ReplayerVM::<C>::replay_basic_unrolled::<_, _, BabyBearField>(
        &mut state,
        &mut ram,
        tape,
        &mut (),
        cycles_bound,
        &mut tracer,
    );
    assert_eq!(expected_final_state.registers, state.registers);
    assert_eq!(expected_final_state.pc, state.pc);
    assert_eq!(expected_final_state.timestamp, state.timestamp);

    buffers
}

pub fn replay_mem_circuit_family<C: Counters, const FAMILY_IDX: u8>(
    initial_counters: C,
    snapshotter: &SimpleSnapshotter<
        C,
        { common_constants::ROM_SECOND_WORD_BITS },
        Vec<(u32, (u32, u32))>,
    >,
    tape: &SimpleTape,
    cycles_bound: usize,
    expected_final_state: &State<C>,
    capacity_per_circuit: usize,
    final_counters: C,
) -> Vec<Vec<MemoryOpcodeTracingDataWithTimestamp>> {
    use riscv_transpiler::replayer::ReplayerRam;
    use riscv_transpiler::replayer::ReplayerVM;
    use riscv_transpiler::vm::ReplayBuffer;

    let mut state = State::initial_with_counters(initial_counters);

    let mut ram_log_buffers = snapshotter
        .reads_buffer
        .make_range(0..snapshotter.reads_buffer.len());

    let mut ram = ReplayerRam::<{ common_constants::ROM_SECOND_WORD_BITS }> {
        ram_log: &mut ram_log_buffers,
    };

    let mut buffers = make_tracer_buffers::<MemoryOpcodeTracingDataWithTimestamp>(
        MemoryOpcodeTracingDataWithTimestamp::default(),
        final_counters.get_calls_to_circuit_family::<FAMILY_IDX>(),
        capacity_per_circuit,
    );
    let mut buffer_ref_mut: Vec<_> = buffers.iter_mut().map(|el| &mut el[..]).collect();
    let mut tracer = MemDestinationHolder::<FAMILY_IDX> {
        buffers: &mut buffer_ref_mut,
    };

    ReplayerVM::<C>::replay_basic_unrolled::<_, _, BabyBearField>(
        &mut state,
        &mut ram,
        tape,
        &mut (),
        cycles_bound,
        &mut tracer,
    );
    assert_eq!(expected_final_state.registers, state.registers);
    assert_eq!(expected_final_state.pc, state.pc);
    assert_eq!(expected_final_state.timestamp, state.timestamp);

    buffers
}

pub fn replay_delegation_circuit<
    C: Counters,
    D: DelegationAbiDescription,
    const REG_ACCESSES: usize,
    const INDIRECT_READS: usize,
    const INDIRECT_WRITES: usize,
    const VARIABLE_OFFSETS: usize,
>(
    initial_counters: C,
    snapshotter: &SimpleSnapshotter<
        C,
        { common_constants::ROM_SECOND_WORD_BITS },
        Vec<(u32, (u32, u32))>,
    >,
    tape: &SimpleTape,
    cycles_bound: usize,
    expected_final_state: &State<C>,
    capacity_per_circuit: usize,
    final_counters: C,
    counter_fn: impl Fn(&C) -> usize,
) -> Vec<Vec<DelegationWitness<REG_ACCESSES, INDIRECT_READS, INDIRECT_WRITES, VARIABLE_OFFSETS>>>
where
    [(); { D::DELEGATION_TYPE } as usize]:,
{
    use riscv_transpiler::replayer::ReplayerRam;
    use riscv_transpiler::replayer::ReplayerVM;
    use riscv_transpiler::vm::ReplayBuffer;

    let mut state = State::initial_with_counters(initial_counters);

    let mut ram_log_buffers = snapshotter
        .reads_buffer
        .make_range(0..snapshotter.reads_buffer.len());

    let mut ram = ReplayerRam::<{ common_constants::ROM_SECOND_WORD_BITS }> {
        ram_log: &mut ram_log_buffers,
    };

    let mut buffers = make_tracer_buffers::<_>(
        DelegationWitness::<REG_ACCESSES, INDIRECT_READS, INDIRECT_WRITES, VARIABLE_OFFSETS>::empty(
        ),
        counter_fn(&final_counters),
        capacity_per_circuit,
    );
    let mut buffer_ref_mut: Vec<_> = buffers.iter_mut().map(|el| &mut el[..]).collect();
    let mut tracer = DelegationDestinationHolder::<
        { D::DELEGATION_TYPE },
        REG_ACCESSES,
        INDIRECT_READS,
        INDIRECT_WRITES,
        VARIABLE_OFFSETS,
    > {
        buffers: &mut buffer_ref_mut,
    };

    ReplayerVM::<C>::replay_basic_unrolled::<_, _, BabyBearField>(
        &mut state,
        &mut ram,
        tape,
        &mut (),
        cycles_bound,
        &mut tracer,
    );
    assert_eq!(expected_final_state.registers, state.registers);
    assert_eq!(expected_final_state.pc, state.pc);
    assert_eq!(expected_final_state.timestamp, state.timestamp);

    buffers
}

pub fn prove_unrolled_execution_with_replayer<C: MachineConfig, A: GoodAllocator>(
    cycles_bound: usize,
    binary_image: &[u32],
    text_section: &[u32],
    use_caches: bool,
    non_determinism: impl riscv_transpiler::vm::NonDeterminismCSRSource,
    ram_bound: usize,
    worker: &worker::Worker,
    security_level: SecurityLevel,
    permutation_argument_pow_bits: u32,
) -> (
    full_statement_verifier::program_proof::ProgramProof,
    BTreeMap<u32, UnrolledCircuitSetupParams>,
) {
    let mut program_proof = full_statement_verifier::program_proof::ProgramProof {
        riscv_proofs: BTreeMap::new(),
        compiled_riscv_circuits: BTreeMap::new(),
        inits_and_teardown_proofs: Vec::new(),
        inits_and_teardowns_circuit: None,
        delegation_proofs: BTreeMap::new(),
        compiled_delegation_circuits: BTreeMap::new(),
        register_final_values: Vec::new(),
        final_pc: 0,
        final_timestamp: 0,
        end_params: [0u32; 8],
        recursion_chain_hash: None,
        recursion_chain_preimage: None,
        pow_challenge: 0,
    };

    let mut risc_v_setup_params = BTreeMap::new();

    assert!(
        ram_bound <= (1 << 30),
        "Large RAM sizes are no supported for now"
    );

    let mut family_chunk_sizes = HashMap::new();

    fn get_riscv_chunk_size<
        const B: bool,
        C: circuit_common::RiscVCycleCircuit<BabyBearField, B>,
    >(
        dst: &mut HashMap<u8, usize>,
    ) {
        assert!(dst
            .insert(C::CIRCUIT_FAMILY, 1 << C::DOMAIN_SIZE_LOG2)
            .is_none());
    }
    get_riscv_chunk_size::<false, crate::setups::AddSubLuiAuipcMopCircuit>(&mut family_chunk_sizes);
    get_riscv_chunk_size::<false, crate::setups::JumpBranchSltCircuit>(&mut family_chunk_sizes);
    get_riscv_chunk_size::<false, crate::setups::ShiftBinaryCircuit>(&mut family_chunk_sizes);
    get_riscv_chunk_size::<false, crate::setups::UnsignedMulDivCircuit>(&mut family_chunk_sizes);
    get_riscv_chunk_size::<true, crate::setups::LoadStoreWordOnlyCircuit>(&mut family_chunk_sizes);
    get_riscv_chunk_size::<true, crate::setups::LoadStoreSubwordOnlyCircuit>(
        &mut family_chunk_sizes,
    );

    let mut delegation_chunk_sizes = HashMap::new();
    fn get_delegation_chunk_size<C: circuit_common::DelegationCircuit<BabyBearField>>(
        dst: &mut HashMap<u16, usize>,
    ) {
        assert!(dst
            .insert(C::DELEGATION_TYPE_ID, 1 << C::DOMAIN_SIZE_LOG2)
            .is_none());
    }
    get_delegation_chunk_size::<crate::setups::BigIntDelegationCircuit>(
        &mut delegation_chunk_sizes,
    );
    get_delegation_chunk_size::<crate::setups::Blake2sWithCompressionDelegationCircuit>(
        &mut delegation_chunk_sizes,
    );
    get_delegation_chunk_size::<crate::setups::KeccakSpecial5DelegationCircuit>(
        &mut delegation_chunk_sizes,
    );
    get_delegation_chunk_size::<crate::setups::Blake2sGFunctionDelegationCircuit>(
        &mut delegation_chunk_sizes,
    );

    let (
        (final_pc, final_timestamp),
        snapshotter,
        counters,
        ram,
        registers,
        tape,
        expected_final_state,
    ) = run_unrolled_machine_in_full::<C, DelegationsAndFamiliesCounters>(
        cycles_bound,
        text_section,
        binary_image,
        ram_bound,
        DelegationsAndFamiliesCounters::default(),
        non_determinism,
    );

    println!(
        "Execution ended at PC = 0x{:08x} at timestamp {}",
        final_pc, final_timestamp
    );

    println!("Final usage: {:?}", &counters);

    let should_dump_witness = std::env::var(DUMP_WITNESS_VAR)
        .map(|el| el.parse::<u32>().unwrap_or(0) == 1)
        .unwrap_or(false);

    let mut memory_trees = vec![];

    let mut non_mem_circuits = BTreeMap::new();
    non_mem_circuits.insert(
        ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX,
        replay_non_mem_circuit_family::<
            DelegationsAndFamiliesCounters,
            ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX,
        >(
            DelegationsAndFamiliesCounters::default(),
            &snapshotter,
            &tape,
            cycles_bound,
            &expected_final_state,
            family_chunk_sizes[&ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX],
            counters,
        ),
    );
    non_mem_circuits.insert(
        JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX,
        replay_non_mem_circuit_family::<
            DelegationsAndFamiliesCounters,
            JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX,
        >(
            DelegationsAndFamiliesCounters::default(),
            &snapshotter,
            &tape,
            cycles_bound,
            &expected_final_state,
            family_chunk_sizes[&JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX],
            counters,
        ),
    );
    non_mem_circuits.insert(
        SHIFT_BINARY_CIRCUIT_FAMILY_IDX,
        replay_non_mem_circuit_family::<
            DelegationsAndFamiliesCounters,
            SHIFT_BINARY_CIRCUIT_FAMILY_IDX,
        >(
            DelegationsAndFamiliesCounters::default(),
            &snapshotter,
            &tape,
            cycles_bound,
            &expected_final_state,
            family_chunk_sizes[&SHIFT_BINARY_CIRCUIT_FAMILY_IDX],
            counters,
        ),
    );
    non_mem_circuits.insert(
        MUL_DIV_CIRCUIT_FAMILY_IDX,
        replay_non_mem_circuit_family::<DelegationsAndFamiliesCounters, MUL_DIV_CIRCUIT_FAMILY_IDX>(
            DelegationsAndFamiliesCounters::default(),
            &snapshotter,
            &tape,
            cycles_bound,
            &expected_final_state,
            family_chunk_sizes[&MUL_DIV_CIRCUIT_FAMILY_IDX],
            counters,
        ),
    );

    let mut mem_circuits = BTreeMap::new();
    mem_circuits.insert(
        LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX,
        replay_mem_circuit_family::<
            DelegationsAndFamiliesCounters,
            LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX,
        >(
            DelegationsAndFamiliesCounters::default(),
            &snapshotter,
            &tape,
            cycles_bound,
            &expected_final_state,
            family_chunk_sizes[&LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX],
            counters,
        ),
    );
    mem_circuits.insert(
        LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX,
        replay_mem_circuit_family::<
            DelegationsAndFamiliesCounters,
            LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX,
        >(
            DelegationsAndFamiliesCounters::default(),
            &snapshotter,
            &tape,
            cycles_bound,
            &expected_final_state,
            family_chunk_sizes[&LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX],
            counters,
        ),
    );
    let blake_circuits = replay_delegation_circuit::<
        DelegationsAndFamiliesCounters,
        Blake2sRoundFunctionAbiDescription,
        _,
        _,
        _,
        _,
    >(
        DelegationsAndFamiliesCounters::default(),
        &snapshotter,
        &tape,
        cycles_bound,
        &expected_final_state,
        delegation_chunk_sizes[&(BLAKE2S_DELEGATION_CSR_REGISTER as u16)],
        counters,
        |c| c.blake_calls,
    );
    let bigint_circuits = replay_delegation_circuit::<
        DelegationsAndFamiliesCounters,
        BigintAbiDescription,
        _,
        _,
        _,
        _,
    >(
        DelegationsAndFamiliesCounters::default(),
        &snapshotter,
        &tape,
        cycles_bound,
        &expected_final_state,
        delegation_chunk_sizes[&(BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16)],
        counters,
        |c| c.bigint_calls,
    );
    let keccak_special5_circuits = replay_delegation_circuit::<
        DelegationsAndFamiliesCounters,
        KeccakSpecial5AbiDescription,
        _,
        _,
        _,
        _,
    >(
        DelegationsAndFamiliesCounters::default(),
        &snapshotter,
        &tape,
        cycles_bound,
        &expected_final_state,
        delegation_chunk_sizes[&(KECCAK_SPECIAL5_CSR_REGISTER as u16)],
        counters,
        |c| c.keccak_calls,
    );
    let blake_g_function_circuits = replay_delegation_circuit::<
        DelegationsAndFamiliesCounters,
        Blake2sGFunctionAbiDescription,
        _,
        _,
        _,
        _,
    >(
        DelegationsAndFamiliesCounters::default(),
        &snapshotter,
        &tape,
        cycles_bound,
        &expected_final_state,
        delegation_chunk_sizes[&(BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER as u16)],
        counters,
        |c| c.blake_g_function_calls,
    );

    for (k, v) in non_mem_circuits.iter() {
        println!("{} circuits of family {}", v.len(), k);
    }
    for (k, v) in mem_circuits.iter() {
        println!("{} circuits of family {}", v.len(), k);
    }

    let setups = setups::get_unrolled_circuits_setups_for_machine_type::<C, Global>(
        binary_image,
        text_section,
        use_caches,
        worker,
    );
    for (k, v) in setups.iter() {
        program_proof
            .compiled_riscv_circuits
            .insert(*k as u32, v.compiled_circuit.clone());
    }
    let inits_and_teardowns_setup =
        setups::inits_and_teardowns_circuit_setup::<Global>(use_caches, worker);
    program_proof.inits_and_teardowns_circuit =
        Some(inits_and_teardowns_setup.compiled_circuit.clone());
    let blake_round_function_setup =
        setups::get_blake2_with_compression_circuit_setup(use_caches, worker);
    let bigint_setup = setups::get_bigint_with_control_circuit_setup(use_caches, worker);
    let keccak_special5_setup = setups::get_keccak_special5_circuit_setup(use_caches, worker);
    let blake_g_function_setup = setups::get_blake2_g_function_circuit_setup(use_caches, worker);

    for el in [
        &blake_round_function_setup,
        &bigint_setup,
        &keccak_special5_setup,
        &blake_g_function_setup,
    ] {
        program_proof
            .compiled_delegation_circuits
            .insert(el.delegation_type as u32, el.compiled_circuit.clone());
    }

    // restructure inits/teardowns
    let shuffle_ram_touched_addresses = ram.collect_inits_and_teardowns(&worker, Global);

    let total_unique_teardowns: usize = shuffle_ram_touched_addresses
        .iter()
        .map(|el| el.len())
        .sum();

    println!("Touched {} unique addresses", total_unique_teardowns);

    assert_eq!(
        (setups::inits_and_teardowns::NUM_INIT_AND_TEARDOWN_SETS
            << setups::inits_and_teardowns::TRACE_LEN_LOG2)
            << setups::inits_and_teardowns::WORD_BITS,
        1 << 30
    );

    let mut inits_and_teardowns =
        Vec::with_capacity(setups::inits_and_teardowns::NUM_INIT_AND_TEARDOWN_SETS);
    for _ in 0..setups::inits_and_teardowns::NUM_INIT_AND_TEARDOWN_SETS {
        let a = Vec::with_capacity(1 << setups::inits_and_teardowns::TRACE_LEN_LOG2);
        let b = Vec::with_capacity(1 << setups::inits_and_teardowns::TRACE_LEN_LOG2);
        let c = Vec::with_capacity(1 << setups::inits_and_teardowns::TRACE_LEN_LOG2);
        let d = Vec::with_capacity(1 << setups::inits_and_teardowns::TRACE_LEN_LOG2);

        inits_and_teardowns.push(([a, b], [c, d]));
    }

    ram.collect_inits_and_teardowns_into_columns::<BabyBearField, _>(
        &worker,
        setups::inits_and_teardowns::TRACE_LEN_LOG2 as usize,
        0,
        &mut inits_and_teardowns,
    );

    let register_final_state = registers.map(|el| FinalRegisterValue {
        value: el.value,
        last_access_timestamp: el.timestamp,
    });
    program_proof.register_final_values = register_final_state.to_vec();
    program_proof.final_pc = final_pc;
    program_proof.final_timestamp = final_timestamp;

    let mut twiddles = HashMap::new();

    // commit memory trees
    for (family_idx, witness_chunks) in non_mem_circuits.iter() {
        if witness_chunks.is_empty() {
            continue;
        }

        let mut family_caps = vec![];
        let setup = &setups[family_idx];
        let UnrolledCircuitWitnessEvalFn::NonMemory {
            decoder_table,
            default_pc_value_in_padding,
            ..
        } = setup.witness_eval_fn.as_ref().unwrap()
        else {
            unreachable!()
        };
        let trace_len = setup.trace_len;
        let prover_config = prover::gkr::prover_config::example_configs::config_for_security_level_under_pessimistic_conjecture(trace_len.trailing_zeros() as usize, security_level);
        let twiddles_for_size = twiddles
            .entry(trace_len)
            .or_insert_with(|| Twiddles::new(trace_len, worker));

        for chunk in witness_chunks.iter() {
            let cap = commit_memory_tree_for_unrolled_nonmem_circuits::<
                BabyBearField,
                DefaultTreeConstructor,
                Global,
                Global,
            >(
                &setup.compiled_circuit,
                &chunk,
                &*twiddles_for_size,
                &prover_config,
                *default_pc_value_in_padding,
                decoder_table,
                worker,
            );

            family_caps.push(cap);
        }
        memory_trees.push((*family_idx as u32, family_caps));
    }

    for (family_idx, witness_chunks) in mem_circuits.iter() {
        if witness_chunks.is_empty() {
            continue;
        }

        let mut family_caps = vec![];
        let setup = &setups[family_idx];
        let UnrolledCircuitWitnessEvalFn::Memory { decoder_table, .. } =
            setup.witness_eval_fn.as_ref().unwrap()
        else {
            unreachable!()
        };
        let trace_len = setup.trace_len;
        let prover_config = prover::gkr::prover_config::example_configs::config_for_security_level_under_pessimistic_conjecture(trace_len.trailing_zeros() as usize, security_level);
        let twiddles_for_size = twiddles
            .entry(trace_len)
            .or_insert_with(|| Twiddles::new(trace_len, worker));

        for chunk in witness_chunks.iter() {
            let cap = commit_memory_tree_for_unrolled_mem_circuits::<
                BabyBearField,
                DefaultTreeConstructor,
                Global,
                Global,
            >(
                &setup.compiled_circuit,
                &chunk,
                &*twiddles_for_size,
                &prover_config,
                decoder_table,
                worker,
            );

            family_caps.push(cap);
        }
        memory_trees.push((*family_idx as u32, family_caps));
    }

    // and inits and teardowns
    let mut inits_and_teardown_trees = vec![];
    {
        let trace_len = inits_and_teardowns_setup.trace_len;
        let twiddles_for_size = twiddles
            .entry(trace_len)
            .or_insert_with(|| Twiddles::new(trace_len, worker));
        let prover_config = prover::gkr::prover_config::example_configs::config_for_security_level_under_pessimistic_conjecture(trace_len.trailing_zeros() as usize, security_level);
        let cap = commit_memory_tree_for_inits_and_teardowns::<
            BabyBearField,
            DefaultTreeConstructor,
            Global,
            Global,
        >(
            &inits_and_teardowns_setup.compiled_circuit,
            inits_and_teardowns.clone(),
            &*twiddles_for_size,
            &prover_config,
            worker,
        );

        inits_and_teardown_trees.push(cap);
    }

    // same for delegation circuits
    #[cfg(feature = "timing_logs")]
    let now = std::time::Instant::now();
    let mut delegation_memory_trees = BTreeMap::new();
    {
        type DelegationDescription = Blake2sRoundFunctionAbiDescription;
        let delegation_type = <setups::Blake2sWithCompressionDelegationCircuit as DelegationCircuit<BabyBearField>>::DELEGATION_TYPE_ID;
        let delegation_circuits = &blake_circuits;
        let setup = &blake_round_function_setup;
        if delegation_circuits.is_empty() == false {
            let trace_len = setup.trace_len;
            let prover_config = prover::gkr::prover_config::example_configs::config_for_security_level_under_pessimistic_conjecture(trace_len.trailing_zeros() as usize, security_level);
            let twiddles_for_size = twiddles
                .entry(trace_len)
                .or_insert_with(|| Twiddles::new(trace_len, worker));

            let mut per_tree_set = vec![];
            for el in delegation_circuits.iter() {
                let caps = commit_memory_tree_for_delegation_circuit::<
                    BabyBearField,
                    DefaultTreeConstructor,
                    A,
                    A,
                    DelegationDescription,
                    _,
                    _,
                    _,
                    _,
                >(
                    &setup.compiled_circuit,
                    el,
                    &*twiddles_for_size,
                    &prover_config,
                    worker,
                );
                per_tree_set.push(caps);
            }

            delegation_memory_trees.insert(delegation_type, per_tree_set);
        }
    }
    {
        type DelegationDescription = BigintAbiDescription;
        let delegation_type = <setups::BigIntDelegationCircuit as DelegationCircuit<
            BabyBearField,
        >>::DELEGATION_TYPE_ID;
        let delegation_circuits = &bigint_circuits;
        let setup = &bigint_setup;
        if delegation_circuits.is_empty() == false {
            let trace_len = setup.trace_len;
            let prover_config = prover::gkr::prover_config::example_configs::config_for_security_level_under_pessimistic_conjecture(trace_len.trailing_zeros() as usize, security_level);
            let twiddles_for_size = twiddles
                .entry(trace_len)
                .or_insert_with(|| Twiddles::new(trace_len, worker));

            let mut per_tree_set = vec![];
            for el in delegation_circuits.iter() {
                let caps = commit_memory_tree_for_delegation_circuit::<
                    BabyBearField,
                    DefaultTreeConstructor,
                    A,
                    A,
                    DelegationDescription,
                    _,
                    _,
                    _,
                    _,
                >(
                    &setup.compiled_circuit,
                    el,
                    &*twiddles_for_size,
                    &prover_config,
                    worker,
                );
                per_tree_set.push(caps);
            }

            delegation_memory_trees.insert(delegation_type, per_tree_set);
        }
    }
    {
        type DelegationDescription = KeccakSpecial5AbiDescription;
        let delegation_type = <setups::KeccakSpecial5DelegationCircuit as DelegationCircuit<
            BabyBearField,
        >>::DELEGATION_TYPE_ID;
        let delegation_circuits = &keccak_special5_circuits;
        let setup = &keccak_special5_setup;
        if delegation_circuits.is_empty() == false {
            let trace_len = setup.trace_len;
            let prover_config = prover::gkr::prover_config::example_configs::config_for_security_level_under_pessimistic_conjecture(trace_len.trailing_zeros() as usize, security_level);
            let twiddles_for_size = twiddles
                .entry(trace_len)
                .or_insert_with(|| Twiddles::new(trace_len, worker));

            let mut per_tree_set = vec![];
            for el in delegation_circuits.iter() {
                let caps = commit_memory_tree_for_delegation_circuit::<
                    BabyBearField,
                    DefaultTreeConstructor,
                    A,
                    A,
                    DelegationDescription,
                    _,
                    _,
                    _,
                    _,
                >(
                    &setup.compiled_circuit,
                    el,
                    &*twiddles_for_size,
                    &prover_config,
                    worker,
                );
                per_tree_set.push(caps);
            }

            delegation_memory_trees.insert(delegation_type, per_tree_set);
        }
    }

    {
        type DelegationDescription = Blake2sGFunctionAbiDescription;
        let delegation_type = <setups::Blake2sGFunctionDelegationCircuit as DelegationCircuit<
            BabyBearField,
        >>::DELEGATION_TYPE_ID;
        let delegation_circuits = &blake_g_function_circuits;
        let setup = &blake_g_function_setup;
        if delegation_circuits.is_empty() == false {
            let trace_len = setup.trace_len;
            let prover_config = prover::gkr::prover_config::example_configs::config_for_security_level_under_pessimistic_conjecture(trace_len.trailing_zeros() as usize, security_level);
            let twiddles_for_size = twiddles
                .entry(trace_len)
                .or_insert_with(|| Twiddles::new(trace_len, worker));

            let mut per_tree_set = vec![];
            for el in delegation_circuits.iter() {
                let caps = commit_memory_tree_for_delegation_circuit::<
                    BabyBearField,
                    DefaultTreeConstructor,
                    A,
                    A,
                    DelegationDescription,
                    _,
                    _,
                    _,
                    _,
                >(
                    &setup.compiled_circuit,
                    el,
                    &*twiddles_for_size,
                    &prover_config,
                    worker,
                );
                per_tree_set.push(caps);
            }

            delegation_memory_trees.insert(delegation_type, per_tree_set);
        }
    }

    #[cfg(feature = "timing_logs")]
    println!(
        "=== Commitment for {} delegation circuits memory trees took {:?}",
        delegation_memory_trees
            .iter()
            .map(|el| el.1.len())
            .sum::<usize>(),
        now.elapsed()
    );

    #[cfg(feature = "debug_logs")]
    println!("Will create FS transformation challenge for memory and delegation arguments");

    let delegation_memory_trees_vec: Vec<(u32, Vec<prover::merkle_trees::MerkleTreeCapVarLength>)> =
        delegation_memory_trees
            .iter()
            .map(|(k, v)| (*k as u32, v.clone()))
            .collect();

    // commit memory challenges
    let all_challenges_seed = fs_transform_unrolled_for_permutation_argument::<true>(
        &register_final_state,
        final_pc,
        final_timestamp,
        &memory_trees,
        &inits_and_teardown_trees,
        &delegation_memory_trees_vec,
    );

    #[cfg(feature = "debug_logs")]
    println!("FS transformation memory seed is {:?}", all_challenges_seed);

    let pow_challenge = if permutation_argument_pow_bits > 0 {
        #[cfg(feature = "debug_logs")]
        println!(
            "Searching for PoW for {} bits",
            permutation_argument_pow_bits
        );
        #[cfg(feature = "timing_logs")]
        let now = std::time::Instant::now();
        let pow_challenge =
            Transcript::search_pow(&all_challenges_seed, permutation_argument_pow_bits, worker).1;
        #[cfg(feature = "timing_logs")]
        println!(
            "PoW for {} took {:?}",
            permutation_argument_pow_bits,
            now.elapsed()
        );
        pow_challenge
    } else {
        0
    };
    program_proof.pow_challenge = pow_challenge;

    let external_challenges =
        GKRExternalChallenges::<BabyBearField, BabyBearExt4>::draw_from_transcript_seed(
            all_challenges_seed,
            permutation_argument_pow_bits as usize,
            pow_challenge,
        );

    // let external_challenges = {
    //     use prover::cs::definitions::NUM_PERMUTATION_ARGUMENT_KEY_PARTS;
    //     let memory_argument_alpha = BabyBearExt4::from_array_of_base([
    //         BabyBearField::new(2),
    //         BabyBearField::new(5),
    //         BabyBearField::new(42),
    //         BabyBearField::new(123),
    //     ]);
    //     let permutation_argument_additive_part = BabyBearExt4::from_array_of_base([
    //         BabyBearField::new(7),
    //         BabyBearField::new(11),
    //         BabyBearField::new(1024),
    //         BabyBearField::new(8000),
    //     ]);

    //     let permutation_argument_linearization_challenges: [BabyBearExt4;
    //         NUM_PERMUTATION_ARGUMENT_KEY_PARTS - 1] =
    //         materialize_powers_serial_starting_with_elem::<_, Global>(
    //             memory_argument_alpha,
    //             NUM_PERMUTATION_ARGUMENT_KEY_PARTS - 1,
    //         )
    //         .try_into()
    //         .unwrap();

    //     let external_challenges = GKRExternalChallenges::<BabyBearField, BabyBearExt4> {
    //         permutation_argument_linearization_challenges,
    //         permutation_argument_additive_part,
    //         _marker: std::marker::PhantomData,
    //     };

    //     external_challenges
    // };

    #[cfg(feature = "debug_logs")]
    println!("External challenges = {:?}", external_challenges);

    let register_final_state_raw =
        register_final_state.map(|el| (el.value, split_timestamp(el.last_access_timestamp)));

    let mut permutation_argument_accumulator =
        produce_initial_permutation_product_contribution::<BabyBearField, BabyBearExt4>(
            &register_final_state_raw,
            INITIAL_PC,
            split_timestamp(INITIAL_TIMESTAMP),
            final_pc,
            split_timestamp(final_timestamp),
            &external_challenges,
        );

    let mut aux_memory_trees = vec![];

    // println!(
    //     "Producing proofs for main RISC-V circuit, {} proofs in total",
    //     main_circuits_witness.len()
    // );

    use prover::gkr::prover::*;

    // now prove one by one
    let mut main_proofs = BTreeMap::new();
    for (family_idx, witness_chunks) in non_mem_circuits.into_iter() {
        if witness_chunks.is_empty() {
            // for consistency
            main_proofs.insert(family_idx, vec![]);

            let setup = &setups[&family_idx];
            let trace_len = setup.trace_len;
            let prover_config = prover::gkr::prover_config::example_configs::config_for_security_level_under_pessimistic_conjecture(trace_len.trailing_zeros() as usize, security_level);
            let twiddles_for_size = twiddles
                .entry(trace_len)
                .or_insert_with(|| Twiddles::new(trace_len, worker));
            let setup_commitment = setup.setup.commit::<DefaultTreeConstructor>(
                &*twiddles_for_size,
                prover_config.lde_factor,
                prover_config.whir_schedule.whir_steps_schedule[0],
                prover_config.cap_size,
                trace_len.trailing_zeros() as usize,
                &worker,
            );

            risc_v_setup_params.insert(
                family_idx as u32,
                UnrolledCircuitSetupParams {
                    family_idx: family_idx as u32,
                    capacity: trace_len as u32,
                    setup_caps: MerkleTreeCap {
                        cap: <DefaultTreeConstructor as ColumnMajorMerkleTreeConstructor<
                            BabyBearField,
                        >>::get_cap(&setup_commitment.tree)
                        .cap
                        .try_into()
                        .unwrap(),
                    },
                },
            );
            continue;
        }

        let mut family_caps = vec![];
        let mut family_proofs = vec![];

        let setup = &setups[&family_idx];
        let trace_len = setup.trace_len;
        let prover_config = prover::gkr::prover_config::example_configs::config_for_security_level_under_pessimistic_conjecture(trace_len.trailing_zeros() as usize, security_level);
        let twiddles_for_size = twiddles
            .entry(trace_len)
            .or_insert_with(|| Twiddles::new(trace_len, worker));
        let setup_commitment = setup.setup.commit::<DefaultTreeConstructor>(
            &*twiddles_for_size,
            prover_config.lde_factor,
            prover_config.whir_schedule.whir_steps_schedule[0],
            prover_config.cap_size,
            trace_len.trailing_zeros() as usize,
            &worker,
        );

        risc_v_setup_params.insert(
            family_idx as u32,
            UnrolledCircuitSetupParams {
                family_idx: family_idx as u32,
                capacity: trace_len as u32,
                setup_caps: MerkleTreeCap {
                    cap: <DefaultTreeConstructor as ColumnMajorMerkleTreeConstructor<
                        BabyBearField,
                    >>::get_cap(&setup_commitment.tree)
                    .cap
                    .try_into()
                    .unwrap(),
                },
            },
        );

        let UnrolledCircuitWitnessEvalFn::NonMemory {
            decoder_table,
            default_pc_value_in_padding,
            witness_fn,
        } = setup.witness_eval_fn.as_ref().unwrap()
        else {
            unreachable!()
        };

        println!(
            "Will prove {} instances of family {} circuits",
            witness_chunks.len(),
            family_idx
        );

        for (idx, chunk) in witness_chunks.into_iter().enumerate() {
            if should_dump_witness {
                println!(
                    "Will serialize witness for family {} circuit {}",
                    family_idx, idx
                );
                bincode_serialize_to_file(
                    &chunk,
                    // &chunk.realloc_to_global(),
                    &format!("family_{}_circuit_{}_oracle_witness.bin", family_idx, idx),
                );
                println!("Serialization is done");
            }

            let oracle = NonMemoryCircuitOracle {
                inner: &chunk,
                decoder_table,
                default_pc_value_in_padding: *default_pc_value_in_padding,
            };

            #[cfg(feature = "timing_logs")]
            let now = std::time::Instant::now();
            let witness_trace = evaluate_gkr_witness_for_executor_family::<BabyBearField, _, _, _>(
                &setup.compiled_circuit,
                *witness_fn,
                trace_len,
                &oracle,
                &setup.table_driver,
                &worker,
                None,
                Global,
                Global,
            );
            #[cfg(feature = "timing_logs")]
            println!(
                "Witness generation for unrolled circuit type {} took {:?}",
                family_idx,
                now.elapsed()
            );

            // if crate::PRECHECK_SATISFIED {
            //     println!("Will evaluate basic satisfiability checks for main circuit");

            //     assert!(check_satisfied(
            //         &precomputation.compiled_circuit,
            //         &witness_trace.exec_trace,
            //         witness_trace.num_witness_columns
            //     ));
            // }

            let now = std::time::Instant::now();
            let proof =
                prove_configured_with_gkr::<BabyBearField, BabyBearExt4, DefaultTreeConstructor>(
                    &setup.compiled_circuit,
                    &external_challenges,
                    witness_trace,
                    &setup.setup,
                    &setup_commitment,
                    &*twiddles_for_size,
                    &prover_config,
                    vec![],
                    trace_len,
                    &worker,
                );
            println!(
                "Proving time for unrolled circuit type {} is {:?}",
                family_idx,
                now.elapsed()
            );

            program_proof
                .riscv_proofs
                .entry(family_idx as u32)
                .or_default()
                .push(proof.clone());

            // {
            //     serialize_to_file(&proof, &format!("riscv_proof_{}", circuit_sequence));
            // }

            permutation_argument_accumulator.mul_assign(&proof.grand_product_accumulator_computed);

            family_caps.push(proof.whir_proof.memory_commitment.commitment.cap.clone());
            family_proofs.push(proof);
        }
        aux_memory_trees.push((family_idx as u32, family_caps));
        main_proofs.insert(family_idx, family_proofs);
    }

    for (family_idx, witness_chunks) in mem_circuits.into_iter() {
        if witness_chunks.is_empty() {
            // for consistency
            main_proofs.insert(family_idx, vec![]);

            let setup = &setups[&family_idx];
            let trace_len = setup.trace_len;
            let prover_config = prover::gkr::prover_config::example_configs::config_for_security_level_under_pessimistic_conjecture(trace_len.trailing_zeros() as usize, security_level);
            let twiddles_for_size = twiddles
                .entry(trace_len)
                .or_insert_with(|| Twiddles::new(trace_len, worker));
            let setup_commitment = setup.setup.commit::<DefaultTreeConstructor>(
                &*twiddles_for_size,
                prover_config.lde_factor,
                prover_config.whir_schedule.whir_steps_schedule[0],
                prover_config.cap_size,
                trace_len.trailing_zeros() as usize,
                &worker,
            );

            risc_v_setup_params.insert(
                family_idx as u32,
                UnrolledCircuitSetupParams {
                    family_idx: family_idx as u32,
                    capacity: trace_len as u32,
                    setup_caps: MerkleTreeCap {
                        cap: <DefaultTreeConstructor as ColumnMajorMerkleTreeConstructor<
                            BabyBearField,
                        >>::get_cap(&setup_commitment.tree)
                        .cap
                        .try_into()
                        .unwrap(),
                    },
                },
            );
            continue;
        }

        let mut family_caps = vec![];
        let mut family_proofs = vec![];

        let setup = &setups[&family_idx];
        let trace_len = setup.trace_len;
        let prover_config = prover::gkr::prover_config::example_configs::config_for_security_level_under_pessimistic_conjecture(trace_len.trailing_zeros() as usize, security_level);
        let twiddles_for_size = twiddles
            .entry(trace_len)
            .or_insert_with(|| Twiddles::new(trace_len, worker));
        let setup_commitment = setup.setup.commit::<DefaultTreeConstructor>(
            &*twiddles_for_size,
            prover_config.lde_factor,
            prover_config.whir_schedule.whir_steps_schedule[0],
            prover_config.cap_size,
            trace_len.trailing_zeros() as usize,
            &worker,
        );

        risc_v_setup_params.insert(
            family_idx as u32,
            UnrolledCircuitSetupParams {
                family_idx: family_idx as u32,
                capacity: trace_len as u32,
                setup_caps: MerkleTreeCap {
                    cap: <DefaultTreeConstructor as ColumnMajorMerkleTreeConstructor<
                        BabyBearField,
                    >>::get_cap(&setup_commitment.tree)
                    .cap
                    .try_into()
                    .unwrap(),
                },
            },
        );

        let UnrolledCircuitWitnessEvalFn::Memory {
            decoder_table,
            witness_fn,
        } = setup.witness_eval_fn.as_ref().unwrap()
        else {
            unreachable!()
        };

        println!(
            "Will prove {} instances of family {} circuits",
            witness_chunks.len(),
            family_idx
        );

        for (idx, chunk) in witness_chunks.into_iter().enumerate() {
            if should_dump_witness {
                println!(
                    "Will serialize witness for family {} circuit {}",
                    family_idx, idx
                );
                bincode_serialize_to_file(
                    &chunk,
                    // &chunk.realloc_to_global(),
                    &format!("family_{}_circuit_{}_oracle_witness.bin", family_idx, idx),
                );
                println!("Serialization is done");
            }

            let oracle = MemoryCircuitOracle {
                inner: &chunk[..],
                decoder_table,
            };

            #[cfg(feature = "timing_logs")]
            let now = std::time::Instant::now();
            let witness_trace = evaluate_gkr_witness_for_executor_family::<BabyBearField, _, _, _>(
                &setup.compiled_circuit,
                *witness_fn,
                trace_len,
                &oracle,
                &setup.table_driver,
                &worker,
                None,
                Global,
                Global,
            );
            #[cfg(feature = "timing_logs")]
            println!(
                "Witness generation for unrolled circuit type {} took {:?}",
                family_idx,
                now.elapsed()
            );

            // if crate::PRECHECK_SATISFIED {
            //     println!("Will evaluate basic satisfiability checks for main circuit");

            //     assert!(check_satisfied(
            //         &precomputation.compiled_circuit,
            //         &witness_trace.exec_trace,
            //         witness_trace.num_witness_columns
            //     ));
            // }

            let now = std::time::Instant::now();
            let proof =
                prove_configured_with_gkr::<BabyBearField, BabyBearExt4, DefaultTreeConstructor>(
                    &setup.compiled_circuit,
                    &external_challenges,
                    witness_trace,
                    &setup.setup,
                    &setup_commitment,
                    &*twiddles_for_size,
                    &prover_config,
                    vec![],
                    trace_len,
                    &worker,
                );
            println!(
                "Proving time for unrolled circuit type {} is {:?}",
                family_idx,
                now.elapsed()
            );

            program_proof
                .riscv_proofs
                .entry(family_idx as u32)
                .or_default()
                .push(proof.clone());

            // {
            //     serialize_to_file(&proof, &format!("riscv_proof_{}", circuit_sequence));
            // }

            permutation_argument_accumulator.mul_assign(&proof.grand_product_accumulator_computed);

            family_caps.push(proof.whir_proof.memory_commitment.commitment.cap.clone());
            family_proofs.push(proof);
        }
        aux_memory_trees.push((family_idx as u32, family_caps));
        main_proofs.insert(family_idx, family_proofs);
    }

    // inits and teardowns
    let mut aux_inits_and_teardown_trees = vec![];
    let mut inits_and_teardowns_proofs = vec![];
    {
        let setup = &inits_and_teardowns_setup;
        let trace_len = setup.trace_len;
        let prover_config = prover::gkr::prover_config::example_configs::config_for_security_level_under_pessimistic_conjecture(trace_len.trailing_zeros() as usize, security_level);
        let twiddles_for_size = twiddles
            .entry(trace_len)
            .or_insert_with(|| Twiddles::new(trace_len, worker));
        let setup_commitment = setup.setup.commit(
            &*twiddles_for_size,
            prover_config.lde_factor,
            prover_config.whir_schedule.whir_steps_schedule[0],
            prover_config.cap_size,
            trace_len.trailing_zeros() as usize,
            &worker,
        );

        use prover::gkr::witness_gen::family_circuits::evaluate_init_and_teardown_memory_witness;
        use prover::gkr::witness_gen::family_circuits::GKRFullWitnessTrace;

        let witness_inner = evaluate_init_and_teardown_memory_witness(
            inits_and_teardowns,
            &setup.compiled_circuit,
            Global,
            Global,
        );

        let witness_trace = GKRFullWitnessTrace {
            column_major_memory_trace: witness_inner,
            column_major_witness_trace: Vec::new(),
            column_major_scratch_space_trace: Vec::new(),
            generic_lookup_mapping: Vec::new(),
            range_check_16_lookup_mapping: Vec::new(),
            timestamp_range_check_lookup_mapping: Vec::new(),
        };

        let inits_and_teardowns_top_bits: Vec<_> =
            (0..setup.compiled_circuit.memory_layout.teardown_sets.len())
                .map(|el| el as u32)
                .collect();

        #[cfg(feature = "timing_logs")]
        let now = std::time::Instant::now();
        let proof = prove_configured_with_gkr::<BabyBearField, BabyBearExt4, DefaultTreeConstructor>(
            &setup.compiled_circuit,
            &external_challenges,
            witness_trace,
            &setup.setup,
            &setup_commitment,
            &*twiddles_for_size,
            &prover_config,
            inits_and_teardowns_top_bits,
            trace_len,
            &worker,
        );

        program_proof.inits_and_teardown_proofs.push(proof.clone());

        #[cfg(feature = "timing_logs")]
        println!(
            "Proving time for inits and teardowns circuit is {:?}",
            now.elapsed()
        );

        permutation_argument_accumulator.mul_assign(&proof.grand_product_accumulator_computed);

        aux_inits_and_teardown_trees
            .push(proof.whir_proof.memory_commitment.commitment.cap.clone());
        inits_and_teardowns_proofs.push(proof);
    }

    // all the same for delegation circuit
    let mut aux_delegation_memory_trees = vec![];
    let mut delegation_proofs = vec![];
    let delegation_proving_start = std::time::Instant::now();
    let mut delegation_proofs_count = 0;

    {
        type DelegationDescription = Blake2sRoundFunctionAbiDescription;
        let delegation_type = <setups::Blake2sWithCompressionDelegationCircuit as DelegationCircuit<BabyBearField>>::DELEGATION_TYPE_ID;
        let delegation_circuits = blake_circuits;
        let setup = &blake_round_function_setup;
        let witness_eval_fn = setups::blake2_with_compression_witness_eval_fn;
        if delegation_circuits.is_empty() == false {
            let trace_len = setup.trace_len;
            let prover_config = prover::gkr::prover_config::example_configs::config_for_security_level_under_pessimistic_conjecture(trace_len.trailing_zeros() as usize, security_level);
            let (proofs, per_tree_set) =
                prove_delegation_circuit::<Global, DelegationDescription, _, _, _, _>(
                    &delegation_circuits[..],
                    &external_challenges,
                    setup,
                    witness_eval_fn,
                    delegation_type as u16,
                    &mut permutation_argument_accumulator,
                    &mut delegation_proofs_count,
                    should_dump_witness,
                    &mut twiddles,
                    &prover_config,
                    worker,
                );

            program_proof
                .delegation_proofs
                .insert(delegation_type as u32, proofs.clone());

            aux_delegation_memory_trees.push((delegation_type as u32, per_tree_set));
            delegation_proofs.push((delegation_type, proofs));
        }
    }
    {
        type DelegationDescription = BigintAbiDescription;
        let delegation_type = <setups::BigIntDelegationCircuit as DelegationCircuit<
            BabyBearField,
        >>::DELEGATION_TYPE_ID;
        let delegation_circuits = bigint_circuits;
        let setup = &bigint_setup;
        let witness_eval_fn = setups::bigint_witness_eval_fn;
        if delegation_circuits.is_empty() == false {
            let trace_len = setup.trace_len;
            let prover_config = prover::gkr::prover_config::example_configs::config_for_security_level_under_pessimistic_conjecture(trace_len.trailing_zeros() as usize, security_level);
            let (proofs, per_tree_set) =
                prove_delegation_circuit::<Global, DelegationDescription, _, _, _, _>(
                    &delegation_circuits[..],
                    &external_challenges,
                    setup,
                    witness_eval_fn,
                    delegation_type as u16,
                    &mut permutation_argument_accumulator,
                    &mut delegation_proofs_count,
                    should_dump_witness,
                    &mut twiddles,
                    &prover_config,
                    worker,
                );

            program_proof
                .delegation_proofs
                .insert(delegation_type as u32, proofs.clone());

            aux_delegation_memory_trees.push((delegation_type as u32, per_tree_set));
            delegation_proofs.push((delegation_type, proofs));
        }
    }
    {
        type DelegationDescription = KeccakSpecial5AbiDescription;
        let delegation_type = <setups::KeccakSpecial5DelegationCircuit as DelegationCircuit<
            BabyBearField,
        >>::DELEGATION_TYPE_ID;
        let delegation_circuits = keccak_special5_circuits;
        let setup = &keccak_special5_setup;
        let witness_eval_fn = setups::keccak_special5_witness_eval_fn;
        if delegation_circuits.is_empty() == false {
            let trace_len = setup.trace_len;
            let prover_config = prover::gkr::prover_config::example_configs::config_for_security_level_under_pessimistic_conjecture(trace_len.trailing_zeros() as usize, security_level);
            let (proofs, per_tree_set) =
                prove_delegation_circuit::<Global, DelegationDescription, _, _, _, _>(
                    &delegation_circuits[..],
                    &external_challenges,
                    setup,
                    witness_eval_fn,
                    delegation_type as u16,
                    &mut permutation_argument_accumulator,
                    &mut delegation_proofs_count,
                    should_dump_witness,
                    &mut twiddles,
                    &prover_config,
                    worker,
                );

            program_proof
                .delegation_proofs
                .insert(delegation_type as u32, proofs.clone());

            aux_delegation_memory_trees.push((delegation_type as u32, per_tree_set));
            delegation_proofs.push((delegation_type, proofs));
        }
    }
    {
        type DelegationDescription = Blake2sGFunctionAbiDescription;
        let delegation_type = <setups::Blake2sGFunctionDelegationCircuit as DelegationCircuit<
            BabyBearField,
        >>::DELEGATION_TYPE_ID;
        let delegation_circuits = blake_g_function_circuits;
        let setup = &blake_g_function_setup;
        let witness_eval_fn = setups::blake2_g_function_witness_eval_fn;
        if delegation_circuits.is_empty() == false {
            let trace_len = setup.trace_len;
            let prover_config = prover::gkr::prover_config::example_configs::config_for_security_level_under_pessimistic_conjecture(trace_len.trailing_zeros() as usize, security_level);
            let (proofs, per_tree_set) =
                prove_delegation_circuit::<Global, DelegationDescription, _, _, _, _>(
                    &delegation_circuits[..],
                    &external_challenges,
                    setup,
                    witness_eval_fn,
                    delegation_type as u16,
                    &mut permutation_argument_accumulator,
                    &mut delegation_proofs_count,
                    should_dump_witness,
                    &mut twiddles,
                    &prover_config,
                    worker,
                );

            program_proof
                .delegation_proofs
                .insert(delegation_type as u32, proofs.clone());

            aux_delegation_memory_trees.push((delegation_type as u32, per_tree_set));
            delegation_proofs.push((delegation_type, proofs));
        }
    }

    if delegation_proofs_count > 0 {
        println!(
            "=== Total delegation proving time: {:?} for {} circuits - avg: {:?}",
            delegation_proving_start.elapsed(),
            delegation_proofs_count,
            delegation_proving_start.elapsed() / (delegation_proofs_count as u32)
        )
    }

    assert_eq!(&aux_memory_trees, &memory_trees);
    assert_eq!(&aux_inits_and_teardown_trees, &inits_and_teardown_trees);
    assert_eq!(&aux_delegation_memory_trees, &delegation_memory_trees_vec);

    // compare challenge
    let aux_all_challenges_seed = fs_transform_unrolled_for_permutation_argument::<true>(
        &register_final_state,
        final_pc,
        final_timestamp,
        &aux_memory_trees,
        &aux_inits_and_teardown_trees,
        &aux_delegation_memory_trees,
    );

    assert_eq!(aux_all_challenges_seed, all_challenges_seed);

    assert_eq!(permutation_argument_accumulator, BabyBearExt4::ONE);

    (program_proof, risc_v_setup_params)
}

pub(crate) fn prove_delegation_circuit<
    A: GoodAllocator,
    D: DelegationAbiDescription,
    const REG_ACCESSES: usize,
    const INDIRECT_READS: usize,
    const INDIRECT_WRITES: usize,
    const VARIABLE_OFFSETS: usize,
>(
    witnesses: &[Vec<
        riscv_transpiler::witness::DelegationWitness<
            REG_ACCESSES,
            INDIRECT_READS,
            INDIRECT_WRITES,
            VARIABLE_OFFSETS,
        >,
        A,
    >],
    external_challenges: &GKRExternalChallenges<BabyBearField, BabyBearExt4>,
    setup: &DelegationCircuitSetup,
    witness_eval_fn: fn(
        &'_ mut ColumnMajorWitnessProxy<
            '_,
            DelegationOracle<
                '_,
                D,
                REG_ACCESSES,
                INDIRECT_READS,
                INDIRECT_WRITES,
                VARIABLE_OFFSETS,
            >,
            BabyBearField,
        >,
    ),
    delegation_type: u16,
    permutation_argument_grand_product: &mut BabyBearExt4,
    delegation_proofs_count: &mut usize,
    should_dump_witness: bool,
    twiddles: &mut HashMap<usize, Twiddles<BabyBearField, Global>>,
    prover_config: &ProverConfig,
    worker: &worker::Worker,
) -> (
    Vec<GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor>>,
    Vec<prover::merkle_trees::MerkleTreeCapVarLength>,
) {
    if witnesses.is_empty() {
        return (vec![], vec![]);
    }

    let trace_len = setup.trace_len;
    let twiddles_for_size = twiddles
        .entry(trace_len)
        .or_insert_with(|| Twiddles::new(trace_len, worker));
    let setup_commitment = setup.setup.commit(
        &*twiddles_for_size,
        prover_config.lde_factor,
        prover_config.whir_schedule.whir_steps_schedule[0],
        prover_config.cap_size,
        trace_len.trailing_zeros() as usize,
        &worker,
    );

    let mut per_tree_set = vec![];

    let mut per_delegation_type_proofs = vec![];
    for (_circuit_idx, el) in witnesses.iter().enumerate() {
        *delegation_proofs_count += 1;
        let oracle = DelegationOracle::<D, _, _, _, _> {
            cycle_data: el,
            marker: core::marker::PhantomData,
        };

        if should_dump_witness {
            // println!(
            //     "Will serialize witness for delegaiton circuit {}",
            //     delegation_type
            // );
            // bincode_serialize_to_file(
            //     &oracle.cycle_data,
            //     &format!(
            //         "delegation_circuit_{}_{}_oracle_witness.bin",
            //         delegation_type, _circuit_idx
            //     ),
            // );
            // println!("Serialization is done");
        }

        #[cfg(feature = "timing_logs")]
        let now = std::time::Instant::now();
        let witness_trace = evaluate_gkr_witness_for_delegation_circuit::<
            BabyBearField,
            DelegationOracle<'_, D, _, _, _, _>,
            _,
            _,
        >(
            &setup.compiled_circuit,
            witness_eval_fn,
            setup.trace_len,
            &oracle,
            &setup.table_driver,
            worker,
            Global,
            Global,
        );
        #[cfg(feature = "timing_logs")]
        println!(
            "Witness generation for delegation circuit type {} took {:?}",
            delegation_type,
            now.elapsed()
        );

        // if crate::PRECHECK_SATISFIED {
        //     println!(
        //         "Will evaluate basic satisfiability checks for delegation circuit {}",
        //         delegation_type
        //     );

        //     assert!(check_satisfied(
        //         &prec.compiled_circuit.compiled_circuit,
        //         &witness_trace.exec_trace,
        //         witness_trace.num_witness_columns
        //     ));
        // }

        // and prove
        use ::prover::gkr::prover::prove_configured_with_gkr;

        #[cfg(feature = "timing_logs")]
        let now = std::time::Instant::now();
        assert!(delegation_type < 1 << 12);
        let proof = prove_configured_with_gkr::<BabyBearField, BabyBearExt4, DefaultTreeConstructor>(
            &setup.compiled_circuit,
            &external_challenges,
            witness_trace,
            &setup.setup,
            &setup_commitment,
            &*twiddles_for_size,
            prover_config,
            vec![],
            trace_len,
            &worker,
        );
        #[cfg(feature = "timing_logs")]
        println!(
            "Proving for delegation circuit type {} took {:?}",
            delegation_type,
            now.elapsed()
        );

        permutation_argument_grand_product.mul_assign(&proof.grand_product_accumulator_computed);

        per_tree_set.push(proof.whir_proof.memory_commitment.commitment.cap.clone());
        per_delegation_type_proofs.push(proof);
    }

    (per_delegation_type_proofs, per_tree_set)
}

#[cfg(test)]
pub(crate) mod test {
    use test_utils::skip_if_ci;

    use super::*;
    use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
    use riscv_transpiler::cycle::IMStandardIsaConfigUnsignedMulDivOnly;
    use std::alloc::Global;
    use std::path::Path;

    #[cfg(test)]
    #[test]
    #[ignore = "manual heavy proving test"]
    #[serial_test::serial(prover_examples_proof_artifacts)]
    fn test_prove_unrolled_fibonacci() {
        skip_if_ci!();

        let use_caches = true;
        let (_, binary_image) =
            setups::read_and_pad_binary(&Path::new("../../examples/basic_fibonacci/app.bin"));
        let (_, text_section) =
            setups::read_and_pad_binary(&Path::new("../../examples/basic_fibonacci/app.text"));

        // setups::pad_bytecode_for_proving(&mut binary);

        let worker = worker::Worker::new_with_num_threads(8);
        let non_determinism_source = QuasiUARTSource::new_with_reads(vec![15, 1]);

        let (program_proof, setups) = prove_unrolled_execution_with_replayer::<
            IMStandardIsaConfigUnsignedMulDivOnly,
            Global,
        >(
            1 << 24,
            &binary_image,
            &text_section,
            use_caches,
            non_determinism_source,
            1 << 30,
            &worker,
            SecurityLevel::Sec80,
            0,
        );

        bincode_serialize_to_file(&program_proof, "tmp_proof.bin");
        let setups: Vec<_> = setups.into_iter().map(|(_, v)| v).collect();
        bincode_serialize_to_file(&setups, "tmp_setup.bin");
    }

    #[cfg(feature = "verifiers")]
    #[test]
    #[ignore = "manual heavy proving test"]
    #[serial_test::serial(prover_examples_proof_artifacts)]
    fn test_verify_simple_fib() {
        skip_if_ci!();
        use crate::bincode_deserialize_from_file;
        use full_statement_verifier::program_proof::ProgramProof;
        use full_statement_verifier::unrolled_circuit_params::NUM_BASE_LAYER_CIRCUITS;
        use setups::*;
        use verifier_common::errors::DebugErrorCreator;

        let program_proof: ProgramProof = bincode_deserialize_from_file("tmp_proof.bin");
        let risc_v_setups: Vec<UnrolledCircuitSetupParams> =
            bincode_deserialize_from_file("tmp_setup.bin");
        assert_eq!(risc_v_setups.len(), NUM_BASE_LAYER_CIRCUITS);

        let responses = program_proof.flatten_for_verification();
        std::thread::Builder::new()
            .name("verifier thread".to_string())
            .stack_size(1 << 27)
            .spawn(move || {
                let families_setups: Vec<u32> = risc_v_setups
                    .iter()
                    .map(|el| MerkleTreeCap::flatten_single(&el.setup_caps).to_vec())
                    .flatten()
                    .collect();

                let mut it = families_setups.into_iter().chain(responses.into_iter());
                // prover::nd_source_std::set_iterator(it);

                let verification_result =
                    full_statement_verifier::unrolled_proof_statement::verify_unrolled_base_layer::<
                        _,
                        DebugErrorCreator,
                        true,
                    >(&mut i);
                dbg!(&verification_result);
                assert!(verification_result.is_ok());
            })
            .expect("must spawn")
            .join()
            .expect("must verify");
    }

    #[cfg(feature = "verifiers")]
    #[test]
    #[ignore = "manual heavy proving test"]
    #[serial_test::serial(prover_examples_proof_artifacts)]
    fn test_verify_individual_proof() {
        skip_if_ci!();
        use crate::bincode_deserialize_from_file;
        use full_statement_verifier::program_proof::ProgramProof;
        use setups::*;
        use verifier_common::errors::DebugErrorCreator;
        let circuit_family = 3;
        let verifier_idx = 2;

        let program_proof: ProgramProof = bincode_deserialize_from_file("tmp_proof.bin");
        let proof = &program_proof.riscv_proofs[&circuit_family][0];
        let compiled_circuit = &program_proof.compiled_riscv_circuits[&circuit_family];
        let responses =
            ::verifier_common::gkr::flatten::flatten_gkr_proof_for_nds(proof, compiled_circuit);
        let external_challenges = proof.external_challenges;

        std::thread::Builder::new()
            .name("verifier thread".to_string())
            .stack_size(1 << 27)
            .spawn(move || {
                let mut it = responses.into_iter();
                // prover::nd_source_std::set_iterator(it);

                let (family, verifier_fn) =
                    full_statement_verifier::unrolled_circuit_params::unrolled_circuit_verifiers_for_base_layer::<
                        _,
                        DebugErrorCreator,
                    >()[verifier_idx];
                assert_eq!(family, circuit_family);
                let verification_result = (verifier_fn)(&external_challenges, &mut it);
                // dbg!(&verification_result);
                match &verification_result {
                    Ok(..) => {},
                    Err(e) => {
                        dbg!(e);
                    }
                }
                assert!(verification_result.is_ok());
            })
            .expect("must spawn")
            .join()
            .expect("must verify");
    }
}
