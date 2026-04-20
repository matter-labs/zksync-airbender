use crate::bincode_serialize_to_file;
use crate::DUMP_WITNESS_VAR;
use crate::MEMORY_DELEGATION_POW_BITS;
use circuit_common::DelegationCircuit;
use common_constants::TimestampScalar;
use common_constants::ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX;
use common_constants::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER;
use common_constants::BLAKE2S_DELEGATION_CSR_REGISTER;
use common_constants::INITIAL_TIMESTAMP;
use common_constants::JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX;
use common_constants::KECCAK_SPECIAL5_CSR_REGISTER;
use common_constants::LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX;
use common_constants::LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX;
use common_constants::MUL_DIV_CIRCUIT_FAMILY_IDX;
use common_constants::SHIFT_BINARY_CIRCUIT_FAMILY_IDX;
use common_constants::TIMESTAMP_STEP;
use prover::cs::utils::split_timestamp;
use prover::definitions::*;
use prover::fft::*;
use prover::field::baby_bear::base::BabyBearField;
use prover::field::baby_bear::ext4::BabyBearExt4;
use prover::field::*;
use prover::gkr::prover::GKRExternalChallenges;
use prover::gkr::prover::GKRProof;
use prover::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
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
use riscv_transpiler::witness::delegation::blake2_round_function::Blake2sRoundFunctionAbiDescription;
use riscv_transpiler::witness::delegation::keccak_special5::KeccakSpecial5AbiDescription;
use riscv_transpiler::witness::DelegationAbiDescription;
use riscv_transpiler::witness::*;
use setups::CircuitSetup;
use setups::DelegationCircuitSetup;
use setups::UnrolledCircuitWitnessEvalFn;
use std::alloc::Global;
use std::collections::BTreeMap;
use std::collections::HashMap;
use trace_and_split::commit_memory_tree_for_delegation_circuit;
use trace_and_split::commit_memory_tree_for_inits_and_teardowns;
use trace_and_split::commit_memory_tree_for_unrolled_mem_circuits;
use trace_and_split::commit_memory_tree_for_unrolled_nonmem_circuits;
use trace_and_split::fs_transform_for_permutation_argument;
use trace_and_split::FinalRegisterValue;
use trace_and_split::ENTRY_POINT;

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
    assert_eq!(expected_final_state, &state);

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
    assert_eq!(expected_final_state, &state);

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
    assert_eq!(expected_final_state, &state);

    buffers
}

pub fn prove_unrolled_execution_with_replayer<C: MachineConfig, A: GoodAllocator>(
    cycles_bound: usize,
    binary_image: &[u32],
    text_section: &[u32],
    use_caches: bool,
    mut non_determinism: impl riscv_transpiler::vm::NonDeterminismCSRSource,
    unrolled_circuits_setups: &BTreeMap<u8, CircuitSetup<A>>,
    delegation_circuits_setups: &BTreeMap<u16, DelegationCircuitSetup>,
    ram_bound: usize,
    worker: &worker::Worker,
) -> (
    BTreeMap<u8, Vec<GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor>>>,
    Vec<GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor>>,
    Vec<(
        u16,
        Vec<GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor>>,
    )>,
    [FinalRegisterValue; 32],
    (u32, TimestampScalar),
    u64,
) {
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

    for (k, v) in non_mem_circuits.iter() {
        println!("{} circuits of family {}", v.len(), k);
    }
    for (k, v) in mem_circuits.iter() {
        println!("{} circuits of family {}", v.len(), k);
    }

    let setups = setups::get_unrolled_circuits_setups_for_machine_type(
        binary_image,
        text_section,
        use_caches,
        worker,
    );
    let inits_and_teardowns_setup = setups::inits_and_teardowns_circuit_setup(use_caches, worker);
    let blake_round_function_setup =
        setups::get_blake2_with_compression_circuit_setup(use_caches, worker);
    let bigint_setup = setups::get_bigint_with_control_circuit_setup(use_caches, worker);
    let keccak_special5_setup = setups::get_keccak_special5_circuit_setup(use_caches, worker);

    // restructure inits/teardowns
    let shuffle_ram_touched_addresses = ram.collect_inits_and_teardowns(&worker, Global);

    let total_unique_teardowns: usize = shuffle_ram_touched_addresses
        .iter()
        .map(|el| el.len())
        .sum();

    println!("Touched {} unique addresses", total_unique_teardowns);

    use setups::inits_and_teardowns::*;
    const WORD_BITS: u32 = 2;

    assert_eq!(
        (NUM_INIT_AND_TEARDOWN_SETS << TRACE_LEN_LOG2) << WORD_BITS,
        1 << 30
    );

    let mut inits_and_teardowns = Vec::with_capacity(NUM_INIT_AND_TEARDOWN_SETS);
    for _ in 0..NUM_INIT_AND_TEARDOWN_SETS {
        let a = Vec::with_capacity(1 << TRACE_LEN_LOG2);
        let b = Vec::with_capacity(1 << TRACE_LEN_LOG2);
        let c = Vec::with_capacity(1 << TRACE_LEN_LOG2);
        let d = Vec::with_capacity(1 << TRACE_LEN_LOG2);

        inits_and_teardowns.push(([a, b], [c, d]));
    }

    ram.collect_inits_and_teardowns_into_columns::<BabyBearField, _>(
        &worker,
        TRACE_LEN_LOG2 as usize,
        0,
        &mut inits_and_teardowns,
    );

    let register_final_state = registers.map(|el| FinalRegisterValue {
        value: el.value,
        last_access_timestamp: el.timestamp,
    });

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
        let twiddles_for_size = twiddles
            .entry(trace_len)
            .or_insert_with(|| Twiddles::new(trace_len, worker));

        for chunk in witness_chunks.iter() {
            let cap = commit_memory_tree_for_unrolled_nonmem_circuits(
                &setup.compiled_circuit,
                &chunk,
                &*twiddles_for_size,
                DEFAULT_CAP_SIZE,
                DEFAULT_LDE_FACTOR,
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
        let twiddles_for_size = twiddles
            .entry(trace_len)
            .or_insert_with(|| Twiddles::new(trace_len, worker));

        for chunk in witness_chunks.iter() {
            let cap = commit_memory_tree_for_unrolled_mem_circuits(
                &setup.compiled_circuit,
                &chunk,
                &*twiddles_for_size,
                DEFAULT_CAP_SIZE,
                DEFAULT_LDE_FACTOR,
                decoder_table,
                worker,
            );

            family_caps.push(cap);
        }
        memory_trees.push((*family_idx as u32, family_caps));
    }

    // and inits and teardowns
    let mut inits_and_teardown_trees = vec![];
    let mut previous_aux: Option<AuxArgumentsBoundaryValues> = None;
    {
        let trace_len = inits_and_teardowns_setup.trace_len;
        let twiddles_for_size = twiddles
            .entry(trace_len)
            .or_insert_with(|| Twiddles::new(trace_len, worker));
        let cap = commit_memory_tree_for_inits_and_teardowns(
            &inits_and_teardowns_setup.compiled_circuit,
            inits_and_teardowns,
            &*twiddles_for_size,
            DEFAULT_CAP_SIZE,
            DEFAULT_LDE_FACTOR,
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
        let delegation_type = setups::Blake2sWithCompressionDelegationCircuit::DELEGATION_TYPE_ID;
        let delegation_circuits = &blake_circuits;
        let setup = &blake_round_function_setup;
        if delegation_circuits.is_empty() == false {
            let trace_len = setup.trace_len;
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
                    DEFAULT_CAP_SIZE,
                    DEFAULT_LDE_FACTOR,
                    worker,
                );
                per_tree_set.push(caps);
            }

            delegation_memory_trees.insert(delegation_type, per_tree_set);
        }
    }
    {
        type DelegationDescription = BigintAbiDescription;
        let delegation_type = setups::BigIntDelegationCircuit::DELEGATION_TYPE_ID;
        let delegation_circuits = &bigint_circuits;
        let setup = &bigint_setup;
        if delegation_circuits.is_empty() == false {
            let trace_len = setup.trace_len;
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
                    DEFAULT_CAP_SIZE,
                    DEFAULT_LDE_FACTOR,
                    worker,
                );
                per_tree_set.push(caps);
            }

            delegation_memory_trees.insert(delegation_type, per_tree_set);
        }
    }
    {
        type DelegationDescription = KeccakSpecial5AbiDescription;
        let delegation_type = setups::KeccakSpecial5DelegationCircuit::DELEGATION_TYPE_ID;
        let delegation_circuits = &keccak_special5_circuits;
        let setup = &keccak_special5_setup;
        if delegation_circuits.is_empty() == false {
            let trace_len = setup.trace_len;
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
                    DEFAULT_CAP_SIZE,
                    DEFAULT_LDE_FACTOR,
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
    let all_challenges_seed = fs_transform_for_permutation_argument(
        &register_final_state,
        final_pc,
        final_timestamp,
        &memory_trees,
        &inits_and_teardown_trees,
        &delegation_memory_trees_vec,
    );

    #[cfg(feature = "debug_logs")]
    println!("FS transformation memory seed is {:?}", all_challenges_seed);

    let pow_challenge = if MEMORY_DELEGATION_POW_BITS > 0 {
        #[cfg(feature = "debug_logs")]
        println!("Searching for PoW for {} bits", MEMORY_DELEGATION_POW_BITS);
        #[cfg(feature = "timing_logs")]
        let now = std::time::Instant::now();
        let pow_challenge = Transcript::search_pow(
            &all_challenges_seed,
            MEMORY_DELEGATION_POW_BITS as u32,
            worker,
        )
        .1;
        #[cfg(feature = "timing_logs")]
        println!(
            "PoW for {} took {:?}",
            MEMORY_DELEGATION_POW_BITS,
            now.elapsed()
        );
        pow_challenge
    } else {
        0
    };

    let external_challenges = GKRExternalChallenges::<BabyBearField, BabyBearExt4> {
        permutation_argument_linearization_challenges,
        permutation_argument_additive_part,
        _marker: std::marker::PhantomData,
    };

    let external_challenges = ExternalChallenges::draw_from_transcript_seed_with_state_permutation(
        all_challenges_seed,
        MEMORY_DELEGATION_POW_BITS,
        pow_challenge,
    );

    #[cfg(feature = "debug_logs")]
    println!("External challenges = {:?}", external_challenges);

    let input = register_final_state
        .iter()
        .map(|el| (el.value, split_timestamp(el.last_access_timestamp)))
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();
    let mut permutation_argument_grand_product =
        produce_register_contribution_into_memory_accumulator_raw(
            &input,
            external_challenges
                .memory_argument
                .memory_argument_linearization_challenges,
            external_challenges.memory_argument.memory_argument_gamma,
        );
    let pc_permutation_contribution = produce_pc_into_permutation_accumulator_raw(
        ENTRY_POINT,
        split_timestamp(INITIAL_TIMESTAMP),
        final_pc,
        split_timestamp(final_timestamp),
        &external_challenges
            .machine_state_permutation_argument
            .unwrap()
            .linearization_challenges,
        &external_challenges
            .machine_state_permutation_argument
            .unwrap()
            .additive_term,
    );
    permutation_argument_grand_product.mul_assign(&pc_permutation_contribution);

    let mut aux_memory_trees = vec![];

    // println!(
    //     "Producing proofs for main RISC-V circuit, {} proofs in total",
    //     main_circuits_witness.len()
    // );

    // now prove one by one
    let mut main_proofs = BTreeMap::new();
    for (family_idx, witness_chunks) in non_mem_circuits.into_iter() {
        if witness_chunks.is_empty() {
            // for consistency
            main_proofs.insert(family_idx, vec![]);
            continue;
        }

        let mut family_caps = vec![];
        let mut family_proofs = vec![];

        let precomputation = &unrolled_circuits_precomputations[&family_idx];
        let UnrolledCircuitWitnessEvalFn::NonMemory {
            decoder_table,
            default_pc_value_in_padding,
            witness_fn,
        } = precomputation
            .witness_eval_fn_for_gpu_tracer
            .as_ref()
            .unwrap()
        else {
            unreachable!()
        };

        for (idx, chunk) in witness_chunks.into_iter().enumerate() {
            if should_dump_witness {
                println!(
                    "Will serialize witness for family {} circuit {}",
                    family_idx, idx
                );
                bincode_serialize_to_file(
                    &chunk.realloc_to_global(),
                    &format!("family_{}_circuit_{}_oracle_witness.bin", family_idx, idx),
                );
                println!("Serialization is done");
            }

            let oracle = NonMemoryCircuitOracle {
                inner: &chunk.data,
                decoder_table,
                default_pc_value_in_padding: *default_pc_value_in_padding,
            };

            #[cfg(feature = "timing_logs")]
            let now = std::time::Instant::now();
            let witness_trace = prover::unrolled::evaluate_witness_for_executor_family::<_, A>(
                &precomputation.compiled_circuit,
                *witness_fn,
                precomputation.trace_len - 1,
                &oracle,
                &precomputation.table_driver,
                &worker,
                A::default(),
            );
            #[cfg(feature = "timing_logs")]
            println!(
                "Witness generation for unrolled circuit type {} took {:?}",
                family_idx,
                now.elapsed()
            );

            if crate::PRECHECK_SATISFIED {
                println!("Will evaluate basic satisfiability checks for main circuit");

                assert!(check_satisfied(
                    &precomputation.compiled_circuit,
                    &witness_trace.exec_trace,
                    witness_trace.num_witness_columns
                ));
            }

            let now = std::time::Instant::now();
            let (_, proof) =
                prover::prover_stages::unrolled_prover::prove_configured_for_unrolled_circuits::<
                    DEFAULT_TRACE_PADDING_MULTIPLE,
                    A,
                    DefaultTreeConstructor,
                >(
                    &precomputation.compiled_circuit,
                    &[],
                    &external_challenges,
                    witness_trace,
                    &[],
                    &precomputation.setup,
                    &precomputation.twiddles,
                    &precomputation.lde_precomputations,
                    None,
                    precomputation.lde_factor,
                    precomputation.tree_cap_size,
                    &crate::SECURITY_CONFIG.for_prover(),
                    &worker,
                );
            println!(
                "Proving time for unrolled circuit type {} is {:?}",
                family_idx,
                now.elapsed()
            );

            // {
            //     serialize_to_file(&proof, &format!("riscv_proof_{}", circuit_sequence));
            // }

            permutation_argument_grand_product
                .mul_assign(&proof.permutation_grand_product_accumulator);
            if let Some(delegation_argument_accumulator) = proof.delegation_argument_accumulator {
                assert_eq!(
                    family_idx,
                    common_constants::circuit_families::SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX
                );
                delegation_argument_sum.add_assign(&delegation_argument_accumulator);
            } else {
                assert_ne!(
                    family_idx,
                    common_constants::circuit_families::SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX
                );
            }

            family_caps.push(proof.memory_tree_caps.clone());
            family_proofs.push(proof);
        }
        aux_memory_trees.push((family_idx as u32, family_caps));
        main_proofs.insert(family_idx, family_proofs);
    }

    for (family_idx, witness_chunks) in mem_circuits.into_iter() {
        if witness_chunks.is_empty() {
            // for consistency
            main_proofs.insert(family_idx, vec![]);
            continue;
        }

        let mut family_caps = vec![];
        let mut family_proofs = vec![];

        let precomputation = &unrolled_circuits_precomputations[&family_idx];
        let UnrolledCircuitWitnessEvalFn::Memory {
            decoder_table,
            witness_fn,
        } = precomputation
            .witness_eval_fn_for_gpu_tracer
            .as_ref()
            .unwrap()
        else {
            unreachable!()
        };

        for (idx, chunk) in witness_chunks.into_iter().enumerate() {
            if should_dump_witness {
                println!(
                    "Will serialize witness for family {} circuit {}",
                    family_idx, idx
                );
                bincode_serialize_to_file(
                    &chunk.realloc_to_global(),
                    &format!("family_{}_circuit_{}_oracle_witness.bin", family_idx, idx),
                );
                println!("Serialization is done");
            }

            let oracle = MemoryCircuitOracle {
                inner: &chunk.data[..],
                decoder_table,
            };

            #[cfg(feature = "timing_logs")]
            let now = std::time::Instant::now();
            let witness_trace = prover::unrolled::evaluate_witness_for_executor_family::<_, A>(
                &precomputation.compiled_circuit,
                *witness_fn,
                precomputation.trace_len - 1,
                &oracle,
                &precomputation.table_driver,
                &worker,
                A::default(),
            );
            #[cfg(feature = "timing_logs")]
            println!(
                "Witness generation for unrolled circuit type {} took {:?}",
                family_idx,
                now.elapsed()
            );

            if crate::PRECHECK_SATISFIED {
                println!("Will evaluate basic satisfiability checks for main circuit");

                assert!(check_satisfied(
                    &precomputation.compiled_circuit,
                    &witness_trace.exec_trace,
                    witness_trace.num_witness_columns
                ));
            }

            let now = std::time::Instant::now();
            let (_, proof) =
                prover::prover_stages::unrolled_prover::prove_configured_for_unrolled_circuits::<
                    DEFAULT_TRACE_PADDING_MULTIPLE,
                    A,
                    DefaultTreeConstructor,
                >(
                    &precomputation.compiled_circuit,
                    &[],
                    &external_challenges,
                    witness_trace,
                    &[],
                    &precomputation.setup,
                    &precomputation.twiddles,
                    &precomputation.lde_precomputations,
                    None,
                    precomputation.lde_factor,
                    precomputation.tree_cap_size,
                    &crate::SECURITY_CONFIG.for_prover(),
                    &worker,
                );
            println!(
                "Proving time for unrolled circuit type {} is {:?}",
                family_idx,
                now.elapsed()
            );

            // {
            //     serialize_to_file(&proof, &format!("riscv_proof_{}", circuit_sequence));
            // }

            assert!(proof.delegation_argument_accumulator.is_none());

            permutation_argument_grand_product
                .mul_assign(&proof.permutation_grand_product_accumulator);

            family_caps.push(proof.memory_tree_caps.clone());
            family_proofs.push(proof);
        }
        aux_memory_trees.push((family_idx as u32, family_caps));
        main_proofs.insert(family_idx, family_proofs);
    }

    // inits and teardowns
    let mut aux_inits_and_teardown_trees = vec![];
    let mut inits_and_teardowns_proofs = vec![];
    for witness_chunk in inits_and_teardowns.into_iter() {
        #[cfg(feature = "timing_logs")]
        let now = std::time::Instant::now();
        let witness_trace = evaluate_init_and_teardown_witness::<A>(
            &inits_and_teardowns_precomputation.compiled_circuit,
            inits_and_teardowns_precomputation.trace_len - 1,
            &witness_chunk.lazy_init_data,
            &worker,
            A::default(),
        );
        #[cfg(feature = "timing_logs")]
        println!(
            "Witness generation for inits and teardowns circuit took {:?}",
            now.elapsed()
        );

        let WitnessEvaluationData {
            aux_data,
            exec_trace,
            num_witness_columns,
            lookup_mapping,
        } = witness_trace;
        let witness_trace = WitnessEvaluationDataForExecutionFamily {
            aux_data: ExecutorFamilyWitnessEvaluationAuxData {},
            exec_trace,
            num_witness_columns,
            lookup_mapping,
        };

        #[cfg(feature = "timing_logs")]
        let now = std::time::Instant::now();
        let (_, proof) =
            prover::prover_stages::unrolled_prover::prove_configured_for_unrolled_circuits::<
                DEFAULT_TRACE_PADDING_MULTIPLE,
                A,
                DefaultTreeConstructor,
            >(
                &inits_and_teardowns_precomputation.compiled_circuit,
                &[],
                &external_challenges,
                witness_trace,
                &aux_data.aux_boundary_data,
                &inits_and_teardowns_precomputation.setup,
                &inits_and_teardowns_precomputation.twiddles,
                &inits_and_teardowns_precomputation.lde_precomputations,
                None,
                inits_and_teardowns_precomputation.lde_factor,
                inits_and_teardowns_precomputation.tree_cap_size,
                &crate::SECURITY_CONFIG.for_prover(),
                &worker,
            );
        #[cfg(feature = "timing_logs")]
        println!(
            "Proving time for inits and teardowns circuit is {:?}",
            now.elapsed()
        );

        permutation_argument_grand_product.mul_assign(&proof.permutation_grand_product_accumulator);

        aux_inits_and_teardown_trees.push(proof.memory_tree_caps.clone());
        inits_and_teardowns_proofs.push(proof);
    }

    // all the same for delegation circuit
    let mut aux_delegation_memory_trees = vec![];
    let mut delegation_proofs = vec![];
    let delegation_proving_start = std::time::Instant::now();
    let mut delegation_proofs_count = 0;

    {
        type DelegationDescription = Blake2sRoundFunctionAbiDescription;
        let delegation_type = setups::blake2_with_compression::DELEGATION_TYPE_ID;
        let delegation_circuits = blake_circuits;
        let witness_eval_fn = setups::blake2_with_compression::witness_eval_fn_for_replayer;
        if delegation_circuits.is_empty() == false {
            let idx = delegation_circuits_precomputations
                .iter()
                .position(|el| el.0 == DelegationDescription::DELEGATION_TYPE as u32)
                .unwrap();
            let prec = &delegation_circuits_precomputations[idx].1;
            let (proofs, per_tree_set) = prove_delegation_circuit_with_replayer_format::<
                A,
                DelegationDescription,
                _,
                _,
                _,
                _,
            >(
                &delegation_circuits,
                external_challenges,
                prec,
                witness_eval_fn,
                delegation_type as u16,
                &mut permutation_argument_grand_product,
                &mut delegation_argument_sum,
                &mut delegation_proofs_count,
                should_dump_witness,
                worker,
            );

            aux_delegation_memory_trees.push((delegation_type as u32, per_tree_set));
            delegation_proofs.push((delegation_type as u32, proofs));
        }
    }
    {
        type DelegationDescription = BigintAbiDescription;
        let delegation_type = setups::bigint_with_control::DELEGATION_TYPE_ID;
        let delegation_circuits = bigint_circuits;
        let witness_eval_fn = setups::bigint_with_control::witness_eval_fn_for_replayer;
        if delegation_circuits.is_empty() == false {
            let idx = delegation_circuits_precomputations
                .iter()
                .position(|el| el.0 == DelegationDescription::DELEGATION_TYPE as u32)
                .unwrap();
            let prec = &delegation_circuits_precomputations[idx].1;
            let (proofs, per_tree_set) = prove_delegation_circuit_with_replayer_format::<
                A,
                DelegationDescription,
                _,
                _,
                _,
                _,
            >(
                &delegation_circuits,
                external_challenges,
                prec,
                witness_eval_fn,
                delegation_type as u16,
                &mut permutation_argument_grand_product,
                &mut delegation_argument_sum,
                &mut delegation_proofs_count,
                should_dump_witness,
                worker,
            );

            aux_delegation_memory_trees.push((delegation_type as u32, per_tree_set));
            delegation_proofs.push((delegation_type as u32, proofs));
        }
    }
    {
        type DelegationDescription = KeccakSpecial5AbiDescription;
        let delegation_type = setups::keccak_special5::DELEGATION_TYPE_ID;
        let delegation_circuits = keccak_circuits;
        let witness_eval_fn = setups::keccak_special5::witness_eval_fn_for_replayer;
        if delegation_circuits.is_empty() == false {
            let idx = delegation_circuits_precomputations
                .iter()
                .position(|el| el.0 == DelegationDescription::DELEGATION_TYPE as u32)
                .unwrap();
            let prec = &delegation_circuits_precomputations[idx].1;
            let (proofs, per_tree_set) = prove_delegation_circuit_with_replayer_format::<
                A,
                DelegationDescription,
                _,
                _,
                _,
                _,
            >(
                &delegation_circuits,
                external_challenges,
                prec,
                witness_eval_fn,
                delegation_type as u16,
                &mut permutation_argument_grand_product,
                &mut delegation_argument_sum,
                &mut delegation_proofs_count,
                should_dump_witness,
                worker,
            );

            aux_delegation_memory_trees.push((delegation_type as u32, per_tree_set));
            delegation_proofs.push((delegation_type as u32, proofs));
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

    assert_eq!(delegation_argument_sum, Mersenne31Quartic::ZERO);
    assert_eq!(permutation_argument_grand_product, Mersenne31Quartic::ONE);

    assert_eq!(&aux_memory_trees, &memory_trees);
    assert_eq!(&aux_inits_and_teardown_trees, &inits_and_teardown_trees);
    assert_eq!(&aux_delegation_memory_trees, &delegation_memory_trees);

    // compare challenge
    let aux_all_challenges_seed =
        fs_transform_for_memory_and_delegation_arguments_for_unrolled_circuits(
            &register_final_state,
            final_pc,
            final_timestamp,
            &aux_memory_trees,
            &aux_inits_and_teardown_trees,
            &aux_delegation_memory_trees,
        );

    assert_eq!(aux_all_challenges_seed, all_challenges_seed);

    (
        main_proofs,
        inits_and_teardowns_proofs,
        delegation_proofs,
        register_final_state,
        (final_pc, final_timestamp),
        pow_challenge,
    )
}

fn prove_delegation_circuit_with_replayer_format<
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
    external_challenges: ExternalChallenges,
    setup: DelegationCircuitSetup,
    witness_eval_fn: fn(
        &mut ColumnMajorWitnessProxy<
            '_,
            DelegationOracle<
                '_,
                D,
                REG_ACCESSES,
                INDIRECT_READS,
                INDIRECT_WRITES,
                VARIABLE_OFFSETS,
            >,
        >,
    ),
    delegation_type: u16,
    permutation_argument_grand_product: &mut BabyBearExt4,
    delegation_proofs_count: &mut usize,
    should_dump_witness: bool,
    worker: &worker::Worker,
) -> (
    Vec<GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor>>,
    Vec<prover::merkle_trees::MerkleTreeCapVarLength>,
) {
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
        let witness_trace = prover::evaluate_witness::<DelegationOracle<'_, D, _, _, _, _>, A>(
            &prec.compiled_circuit.compiled_circuit,
            witness_eval_fn,
            prec.compiled_circuit.num_requests_per_circuit,
            &oracle,
            &[],
            &prec.compiled_circuit.table_driver,
            0,
            worker,
            A::default(),
        );
        #[cfg(feature = "timing_logs")]
        println!(
            "Witness generation for delegation circuit type {} took {:?}",
            delegation_type,
            now.elapsed()
        );

        if crate::PRECHECK_SATISFIED {
            println!(
                "Will evaluate basic satisfiability checks for delegation circuit {}",
                delegation_type
            );

            assert!(check_satisfied(
                &prec.compiled_circuit.compiled_circuit,
                &witness_trace.exec_trace,
                witness_trace.num_witness_columns
            ));
        }

        // and prove
        let external_values = ExternalValues {
            challenges: external_challenges,
            aux_boundary_values: AuxArgumentsBoundaryValues::default(),
        };

        #[cfg(feature = "timing_logs")]
        let now = std::time::Instant::now();
        assert!(delegation_type < 1 << 12);
        let (_, proof) = prover::prover_stages::prove(
            &prec.compiled_circuit.compiled_circuit,
            &[],
            &external_values,
            witness_trace,
            &prec.setup,
            &prec.twiddles,
            &prec.lde_precomputations,
            0,
            Some(delegation_type as u16),
            prec.lde_factor,
            prec.tree_cap_size,
            &crate::SECURITY_CONFIG.for_prover(),
            worker,
        );
        #[cfg(feature = "timing_logs")]
        println!(
            "Proving for delegation circuit type {} took {:?}",
            delegation_type,
            now.elapsed()
        );

        permutation_argument_grand_product.mul_assign(&proof.memory_grand_product_accumulator);
        delegation_argument_sum.sub_assign(&proof.delegation_argument_accumulator.unwrap());

        per_tree_set.push(proof.memory_tree_caps.clone());

        per_delegation_type_proofs.push(proof);
    }

    (per_delegation_type_proofs, per_tree_set)
}

#[cfg(test)]
pub(crate) mod test {
    use test_utils::skip_if_ci;

    use super::*;
    use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
    use riscv_transpiler::cycle::IMStandardIsaConfigWithUnsignedMulDiv;
    use std::alloc::Global;
    use std::path::Path;

    #[cfg(feature = "verifiers")]
    mod verifiers_only {
        use super::*;
        use crate::cs::one_row_compiler::CompiledCircuitArtifact;
        use common_constants::TimestampScalar;
        use prover::prover_stages::unrolled_prover::UnrolledModeProof;

        #[derive(Clone, Debug, Hash, serde::Serialize, serde::Deserialize)]
        pub(super) struct UnrolledProgramProof {
            pub final_pc: u32,
            pub final_timestamp: TimestampScalar,
            pub compiled_circuit_families: BTreeMap<u8, CompiledCircuitArtifact<Mersenne31Field>>,
            pub circuit_families_proofs: BTreeMap<u8, Vec<UnrolledModeProof>>,
            pub compiled_inits_and_teardowns: CompiledCircuitArtifact<Mersenne31Field>,
            pub inits_and_teardowns_proofs: Vec<UnrolledModeProof>,
            pub delegation_proofs: BTreeMap<u32, Vec<Proof>>,
            pub register_final_values: [FinalRegisterValue; 32],
            pub recursion_chain_preimage: Option<[u32; 16]>,
            pub recursion_chain_hash: Option<[u32; 8]>,
        }

        impl UnrolledProgramProof {
            pub fn flatten_into_responses(&self, allowed_delegation_circuits: &[u32]) -> Vec<u32> {
                let mut responses = Vec::with_capacity(32 + 32 * 2);

                assert_eq!(self.register_final_values.len(), 32);
                // registers
                for final_values in self.register_final_values.iter() {
                    responses.push(final_values.value);
                    let (low, high) = split_timestamp(final_values.last_access_timestamp);
                    responses.push(low);
                    responses.push(high);
                }

                // final PC and timestamp
                {
                    responses.push(self.final_pc);
                    let (low, high) = split_timestamp(self.final_timestamp);
                    responses.push(low);
                    responses.push(high);
                }

                // families ones
                for (family, proofs) in self.circuit_families_proofs.iter() {
                    responses.push(proofs.len() as u32);
                    for proof in proofs.iter() {
                        let t = verifier_common::proof_flattener::flatten_full_unrolled_proof(
                            proof,
                            &self.compiled_circuit_families[family],
                        );
                        responses.extend(t);
                    }
                }

                // inits and teardowns
                {
                    responses.push(self.inits_and_teardowns_proofs.len() as u32);
                    for proof in self.inits_and_teardowns_proofs.iter() {
                        let t = verifier_common::proof_flattener::flatten_full_unrolled_proof(
                            proof,
                            &self.compiled_inits_and_teardowns,
                        );
                        responses.extend(t);
                    }
                }

                // then for every allowed delegation circuit
                for delegation_type in allowed_delegation_circuits.iter() {
                    if *delegation_type == common_constants::NON_DETERMINISM_CSR {
                        continue;
                    }
                    if let Some(proofs) = self.delegation_proofs.get(&delegation_type) {
                        responses.push(proofs.len() as u32);
                        for proof in proofs.iter() {
                            let t = verifier_common::proof_flattener::flatten_full_proof(proof, 0);
                            responses.extend(t);
                        }
                    } else {
                        responses.push(0);
                    }
                }

                if let Some(preimage) = self.recursion_chain_preimage {
                    responses.extend(preimage);
                }

                responses
            }
        }
    }

    #[cfg(feature = "verifiers")]
    use verifiers_only::UnrolledProgramProof;

    #[cfg(test)]
    #[test]
    #[ignore = "manual heavy proving test"]
    #[serial_test::serial(prover_examples_proof_artifacts)]
    fn test_prove_unrolled_fibonacci() {
        skip_if_ci!();
        let (_, binary_image) =
            setups::read_and_pad_binary(&Path::new("../../examples/basic_fibonacci/app.bin"));
        let (_, text_section) =
            setups::read_and_pad_binary(&Path::new("../../examples/basic_fibonacci/app.text"));

        // setups::pad_bytecode_for_proving(&mut binary);

        let worker = worker::Worker::new_with_num_threads(8);
        println!("Performing precomputations for circuit families");
        let families_precomps =
            setups::unrolled_circuits::get_unrolled_circuits_setups_for_machine_type::<
                IMStandardIsaConfigWithUnsignedMulDiv,
                _,
                _,
            >(&binary_image, &text_section, &worker);

        println!("Performing precomputations for inits and teardowns");
        let inits_and_teardowns_precomps =
            setups::unrolled_circuits::inits_and_teardowns_circuit_setup(
                &binary_image,
                &text_section,
                &worker,
            );

        println!("Performing precomputations for delegation circuits");
        let delegation_precomputations = setups::all_delegation_circuits_precomputations(&worker);

        let non_determinism_source = QuasiUARTSource::new_with_reads(vec![15, 1]);

        let (
            main_proofs,
            inits_and_teardowns_proofs,
            delegation_proofs,
            register_final_state,
            (final_pc, final_timestamp),
            pow_challenge,
        ) = prove_unrolled_execution_with_replayer::<
            IMStandardIsaConfigWithUnsignedMulDiv,
            Global,
            { common_constants::rom::ROM_SECOND_WORD_BITS },
        >(
            1 << 24,
            &binary_image,
            &text_section,
            non_determinism_source,
            &families_precomps,
            &inits_and_teardowns_precomps,
            &delegation_precomputations,
            1 << 32,
            &worker,
        );

        bincode_serialize_to_file(
            &(
                main_proofs,
                inits_and_teardowns_proofs,
                delegation_proofs,
                register_final_state,
                (final_pc, final_timestamp),
                pow_challenge,
            ),
            "tmp_proof.bin",
        );
    }

    // #[cfg(feature = "verifiers")]
    // #[test]
    // #[ignore = "manual heavy proving test"]
    // #[serial_test::serial(prover_examples_proof_artifacts)]
    // fn test_verify_simple_fib() {
    //     skip_if_ci!();
    //     use crate::bincode_deserialize_from_file;
    //     use crate::deserialize_from_file;
    //     use setups::*;

    //     let t: (
    //         BTreeMap<u8, Vec<UnrolledModeProof>>,
    //         Vec<UnrolledModeProof>,
    //         Vec<(u32, Vec<Proof>)>,
    //         [FinalRegisterValue; 32],
    //         (u32, TimestampScalar),
    //     ) = bincode_deserialize_from_file("tmp_proof.bin");
    //     let (
    //         main_proofs,
    //         inits_and_teardowns_proofs,
    //         delegation_proofs,
    //         register_final_state,
    //         (final_pc, final_timestamp),
    //     ) = t;

    //     let (_, binary_image) =
    //         setups::read_and_pad_binary(&Path::new("../../examples/basic_fibonacci/app.bin"));
    //     let compiled_circuits_set =
    //         setups::unrolled_circuits::get_unrolled_circuits_artifacts_for_machine_type::<
    //             IMStandardIsaConfigWithUnsignedMulDiv,
    //         >(&binary_image);

    //     // flatten and set iterator
    //     let CompiledCircuitsSet {
    //         compiled_circuit_families,
    //         compiled_inits_and_teardowns,
    //     } = compiled_circuits_set;

    //     let program_proofs = UnrolledProgramProof {
    //         final_pc,
    //         final_timestamp,
    //         compiled_circuit_families,
    //         circuit_families_proofs: main_proofs,
    //         compiled_inits_and_teardowns: compiled_inits_and_teardowns.unwrap(),
    //         inits_and_teardowns_proofs,
    //         delegation_proofs: BTreeMap::from_iter(delegation_proofs.into_iter()),
    //         register_final_values: register_final_state,
    //         recursion_chain_hash: None,
    //         recursion_chain_preimage: None,
    //     };

    //     let responses = program_proofs
    //         .flatten_into_responses(IMStandardIsaConfigWithUnsignedMulDiv::ALLOWED_DELEGATION_CSRS);
    //     let t: (Vec<UnrolledCircuitSetupParams>, [MerkleTreeCap<CAP_SIZE>; NUM_COSETS]) = deserialize_from_file("../setups/42c88bf092af93acc4a3bf780b64dc98a36ba03b54d7acd886dbd9b3eff90285_42c88bf092af93acc4a3bf780b64dc98a36ba03b54d7acd886dbd9b3eff90285.json");
    //     let (setups, inits_and_teardowns_setup) = t;

    //     std::thread::Builder::new()
    //             .name("verifier thread".to_string())
    //             .stack_size(1 << 27)
    //             .spawn(move || {

    //                 let families_setups: Vec<_> = setups.iter().map(|el| &el.setup_caps).collect();

    //                 let it = responses.into_iter();
    //                 prover::nd_source_std::set_iterator(it);

    //                 #[allow(invalid_value)]
    //                 let _ = unsafe {
    //                     full_statement_verifier::unrolled_proof_statement::verify_full_statement_for_unrolled_circuits::<true, { setups::inits_and_teardowns::NUM_INIT_AND_TEARDOWN_SETS }>(
    //                         &families_setups,
    //                         full_statement_verifier::unrolled_proof_statement::FULL_UNSIGNED_MACHINE_UNROLLED_CIRCUITS_VERIFICATION_PARAMETERS,
    //                         (&inits_and_teardowns_setup, full_statement_verifier::unrolled_proof_statement::INITS_AND_TEARDOWNS_VERIFIER_PTR),
    //                         full_statement_verifier::imports::BASE_LAYER_DELEGATION_CIRCUITS_VERIFICATION_PARAMETERS,
    //                     )
    //                 };
    //             })
    //             .expect("must spawn")
    //             .join()
    //             .expect("must verify");
    // }
}
