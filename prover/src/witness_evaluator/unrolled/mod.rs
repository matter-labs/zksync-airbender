use core::mem::MaybeUninit;

use super::*;
use crate::tracers::unrolled::tracer::*;
use riscv_transpiler::cycle::MachineConfig;
use riscv_transpiler::machine_mode_only_unrolled::UnifiedOpcodeTracingDataWithTimestamp;
use riscv_transpiler::witness::delegation::bigint::BigintDelegationWitness;
use riscv_transpiler::witness::delegation::blake2_round_function::Blake2sRoundFunctionDelegationWitness;
use riscv_transpiler::witness::delegation::keccak_special5::KeccakSpecial5DelegationWitness;

mod family_circuits;

pub use self::family_circuits::*;

pub fn run_unrolled_machine<
    C: MachineConfig,
    A: GoodAllocator,
    const ROM_BOUND_SECOND_WORD_BITS: usize,
>(
    initial_pc: u32,
    text_section: &[u32],
    rom_image: &[u32],
    cycles_upper_bound: usize,
    ram_bound_bytes: usize,
    non_determinism: &mut impl riscv_transpiler::vm::NonDeterminismCSRSource,
    opcode_family_chunk_sizes: HashMap<u8, usize>,
    delegation_chunk_sizes: HashMap<u16, usize>,
    worker: &Worker,
) -> (
    u32,
    TimestampScalar,
    usize,
    HashMap<u8, Vec<NonMemTracingFamilyChunk<A>>>,
    HashMap<u8, Vec<MemTracingFamilyChunk<A>>>,
    (
        Vec<Vec<Blake2sRoundFunctionDelegationWitness, A>>,
        Vec<Vec<BigintDelegationWitness, A>>,
        Vec<Vec<KeccakSpecial5DelegationWitness, A>>,
    ),
    [RamShuffleMemStateRecord; NUM_REGISTERS], // register final values
    Vec<Vec<(u32, (TimestampScalar, u32)), A>>, // lazy iniy/teardown data - all unique words touched, sorted ascending, but not in one vector
) {
    use riscv_transpiler::ir::*;
    use riscv_transpiler::vm::*;
    use riscv_transpiler::witness::*;
    use riscv_transpiler::*;

    assert_eq!(initial_pc, 0);
    assert!(1 << (16 + ROM_BOUND_SECOND_WORD_BITS) <= ram_bound_bytes);
    assert!(text_section.len() * 4 <= ram_bound_bytes);
    assert!(rom_image.len() * 4 <= ram_bound_bytes);
    let mut ram = RamWithRomRegion::from_rom_content(rom_image, ram_bound_bytes);

    let preprocessed_bytecode: Vec<_> = if core::any::TypeId::of::<C>()
        == core::any::TypeId::of::<riscv_transpiler::cycle::IMStandardIsaConfig>()
    {
        riscv_transpiler::ir::preprocess_bytecode::<FullMachineDecoderConfig>(text_section)
    } else if core::any::TypeId::of::<C>()
        == core::any::TypeId::of::<riscv_transpiler::cycle::IMStandardIsaConfigWithUnsignedMulDiv>()
    {
        riscv_transpiler::ir::preprocess_bytecode::<FullUnsignedMachineDecoderConfig>(text_section)
    } else if core::any::TypeId::of::<C>()
        == core::any::TypeId::of::<riscv_transpiler::cycle::IWithoutByteAccessIsaConfigWithDelegation>(
        )
    {
        riscv_transpiler::ir::preprocess_bytecode::<ReducedMachineDecoderConfig>(text_section)
    } else {
        panic!("Unknown machine config {}", core::any::type_name::<C>());
    };

    let tape = SimpleTape::new(&preprocessed_bytecode);

    type CountersT = DelegationsAndFamiliesCounters;

    let mut state = State::initial_with_counters(CountersT::default());
    let mut snapshotter = SimpleSnapshotter::new_with_cycle_limit(cycles_upper_bound, state);

    let now = std::time::Instant::now();
    let is_program_finished = VM::<CountersT>::run_basic_unrolled::<
        SimpleSnapshotter<CountersT, ROM_BOUND_SECOND_WORD_BITS>,
        RamWithRomRegion<ROM_BOUND_SECOND_WORD_BITS>,
        _,
    >(
        &mut state,
        &mut ram,
        &mut snapshotter,
        &tape,
        cycles_upper_bound,
        non_determinism,
    );
    assert!(
        is_program_finished,
        "program failed to finish over {} cycles",
        cycles_upper_bound
    ); // check that we reached looping state (ie. end state for our vm)

    let elapsed = now.elapsed();

    let register_final_values = state.registers.map(|el| RamShuffleMemStateRecord {
        current_value: el.value,
        last_access_timestamp: el.timestamp,
    });

    let exact_cycles_passed = (state.timestamp - INITIAL_TIMESTAMP) / TIMESTAMP_STEP;
    let final_pc = state.pc;
    let final_timestamp = state.timestamp;

    println!("Passed exactly {} cycles", exact_cycles_passed);
    println!(
        "Simulator performance is {} MHz",
        (exact_cycles_passed as f64) / (elapsed.as_micros() as f64)
    );

    let inits_and_teardowns = ram.collect_inits_and_teardowns(worker, A::default());

    // now replay. We will replay in parallel inside of every circuit family for simplicity

    let replay_subword_mem_circuits = core::any::TypeId::of::<C>()
        != core::any::TypeId::of::<
            riscv_transpiler::cycle::IWithoutByteAccessIsaConfigWithDelegation,
        >();
    let replay_blake_only_delegations = core::any::TypeId::of::<C>()
        == core::any::TypeId::of::<
            riscv_transpiler::cycle::IWithoutByteAccessIsaConfigWithDelegation,
        >();
    let replay_mul_circuits = core::any::TypeId::of::<C>()
        != core::any::TypeId::of::<
            riscv_transpiler::cycle::IWithoutByteAccessIsaConfigWithDelegation,
        >();

    let mut non_mem_circuits = HashMap::new();
    {
        let Some(cycles_per_circuit) = opcode_family_chunk_sizes
            .get(&ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX)
            .copied()
        else {
            panic!(
                "Must have chunk size for family {}",
                ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX
            );
        };
        let t = replay_non_mem::<
            ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX,
            A,
            ROM_BOUND_SECOND_WORD_BITS,
        >(&tape, &snapshotter, cycles_per_circuit, worker);
        non_mem_circuits.insert(ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX, t);
    }
    {
        let Some(cycles_per_circuit) = opcode_family_chunk_sizes
            .get(&JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX)
            .copied()
        else {
            panic!(
                "Must have chunk size for family {}",
                JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX
            );
        };
        let t = replay_non_mem::<JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX, A, ROM_BOUND_SECOND_WORD_BITS>(
            &tape,
            &snapshotter,
            cycles_per_circuit,
            worker,
        );
        non_mem_circuits.insert(JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX, t);
    }
    {
        let Some(cycles_per_circuit) = opcode_family_chunk_sizes
            .get(&SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX)
            .copied()
        else {
            panic!(
                "Must have chunk size for family {}",
                SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX
            );
        };
        let t = replay_non_mem::<SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX, A, ROM_BOUND_SECOND_WORD_BITS>(
            &tape,
            &snapshotter,
            cycles_per_circuit,
            worker,
        );
        non_mem_circuits.insert(SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX, t);
    }
    if replay_mul_circuits {
        let Some(cycles_per_circuit) = opcode_family_chunk_sizes
            .get(&MUL_DIV_CIRCUIT_FAMILY_IDX)
            .copied()
        else {
            panic!(
                "Must have chunk size for family {}",
                MUL_DIV_CIRCUIT_FAMILY_IDX
            );
        };
        let t = replay_non_mem::<MUL_DIV_CIRCUIT_FAMILY_IDX, A, ROM_BOUND_SECOND_WORD_BITS>(
            &tape,
            &snapshotter,
            cycles_per_circuit,
            worker,
        );
        non_mem_circuits.insert(MUL_DIV_CIRCUIT_FAMILY_IDX, t);
    }

    let mut mem_circuits = HashMap::new();
    {
        let Some(cycles_per_circuit) = opcode_family_chunk_sizes
            .get(&LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX)
            .copied()
        else {
            panic!(
                "Must have chunk size for family {}",
                LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX
            );
        };
        let t = replay_mem::<LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX, A, ROM_BOUND_SECOND_WORD_BITS>(
            &tape,
            &snapshotter,
            cycles_per_circuit,
            worker,
        );
        mem_circuits.insert(LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX, t);
    }
    if replay_subword_mem_circuits {
        let Some(cycles_per_circuit) = opcode_family_chunk_sizes
            .get(&LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX)
            .copied()
        else {
            panic!(
                "Must have chunk size for family {}",
                LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX
            );
        };
        let t = replay_mem::<
            LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX,
            A,
            ROM_BOUND_SECOND_WORD_BITS,
        >(&tape, &snapshotter, cycles_per_circuit, worker);
        mem_circuits.insert(LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX, t);
    }

    let blake_circuits = {
        let Some(cycles_per_circuit) = delegation_chunk_sizes
            .get(&(common_constants::blake2s_with_control::BLAKE2S_DELEGATION_CSR_REGISTER as u16))
            .copied()
        else {
            panic!(
                "Must have chunk size for work type {}",
                common_constants::blake2s_with_control::BLAKE2S_DELEGATION_CSR_REGISTER
            );
        };

        replay_generic_work::<
            A,
            ROM_BOUND_SECOND_WORD_BITS,
            BlakeDelegationDestinationHolderConstructor,
            _,
            _,
        >(
            &tape,
            &snapshotter,
            cycles_per_circuit,
            |cycles: &DelegationsAndFamiliesCounters| cycles.blake_calls,
            common_constants::blake2s_with_control::BLAKE2S_DELEGATION_CSR_REGISTER as usize,
            worker,
        )
    };

    let bigint_circuits = if replay_blake_only_delegations {
        vec![]
    } else {
        let Some(cycles_per_circuit) = delegation_chunk_sizes
            .get(
                &(common_constants::bigint_with_control::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER
                    as u16),
            )
            .copied()
        else {
            panic!(
                "Must have chunk size for work type {}",
                common_constants::bigint_with_control::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER
            );
        };

        replay_generic_work::<
            A,
            ROM_BOUND_SECOND_WORD_BITS,
            BigintDelegationDestinationHolderConstructor,
            _,
            _,
        >(
            &tape,
            &snapshotter,
            cycles_per_circuit,
            |cycles: &DelegationsAndFamiliesCounters| cycles.bigint_calls,
            common_constants::bigint_with_control::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as usize,
            worker,
        )
    };

    let keccak_circuits = if replay_blake_only_delegations {
        vec![]
    } else {
        let Some(cycles_per_circuit) = delegation_chunk_sizes
            .get(&(common_constants::keccak_special5::KECCAK_SPECIAL5_CSR_REGISTER as u16))
            .copied()
        else {
            panic!(
                "Must have chunk size for work type {}",
                common_constants::keccak_special5::KECCAK_SPECIAL5_CSR_REGISTER
            );
        };

        replay_generic_work::<
            A,
            ROM_BOUND_SECOND_WORD_BITS,
            KeccakDelegationDestinationHolderConstructor,
            _,
            _,
        >(
            &tape,
            &snapshotter,
            cycles_per_circuit,
            |cycles: &DelegationsAndFamiliesCounters| cycles.keccak_calls,
            common_constants::keccak_special5::KECCAK_SPECIAL5_CSR_REGISTER as usize,
            worker,
        )
    };

    (
        final_pc,
        final_timestamp,
        exact_cycles_passed as usize,
        non_mem_circuits,
        mem_circuits,
        (blake_circuits, bigint_circuits, keccak_circuits),
        register_final_values,
        inits_and_teardowns,
    )
}

pub fn run_unified_machine<
    C: MachineConfig,
    A: GoodAllocator,
    const ROM_BOUND_SECOND_WORD_BITS: usize,
>(
    initial_pc: u32,
    text_section: &[u32],
    rom_image: &[u32],
    cycles_upper_bound: usize,
    ram_bound_bytes: usize,
    non_determinism: &mut impl riscv_transpiler::vm::NonDeterminismCSRSource,
    chunk_size: usize,
    delegation_chunk_sizes: HashMap<u16, usize>,
    worker: &Worker,
) -> (
    u32,
    TimestampScalar,
    usize,
    Vec<Vec<UnifiedOpcodeTracingDataWithTimestamp, A>>,
    (
        Vec<Vec<Blake2sRoundFunctionDelegationWitness, A>>,
        Vec<Vec<BigintDelegationWitness, A>>,
        Vec<Vec<KeccakSpecial5DelegationWitness, A>>,
    ),
    [RamShuffleMemStateRecord; NUM_REGISTERS], // register final values
    Vec<Vec<(u32, (TimestampScalar, u32)), A>>, // lazy iniy/teardown data - all unique words touched, sorted ascending, but not in one vector
) {
    use riscv_transpiler::ir::*;
    use riscv_transpiler::vm::*;
    use riscv_transpiler::witness::*;
    use riscv_transpiler::*;

    assert_eq!(initial_pc, 0);
    assert!(1 << (16 + ROM_BOUND_SECOND_WORD_BITS) <= ram_bound_bytes);
    assert!(text_section.len() * 4 <= ram_bound_bytes);
    assert!(rom_image.len() * 4 <= ram_bound_bytes);
    let mut ram = RamWithRomRegion::from_rom_content(rom_image, ram_bound_bytes);

    let preprocessed_bytecode: Vec<_> = if core::any::TypeId::of::<C>()
        == core::any::TypeId::of::<riscv_transpiler::cycle::IMStandardIsaConfig>()
    {
        riscv_transpiler::ir::preprocess_bytecode::<FullMachineDecoderConfig>(text_section)
    } else if core::any::TypeId::of::<C>()
        == core::any::TypeId::of::<riscv_transpiler::cycle::IMStandardIsaConfigWithUnsignedMulDiv>()
    {
        riscv_transpiler::ir::preprocess_bytecode::<FullUnsignedMachineDecoderConfig>(text_section)
    } else if core::any::TypeId::of::<C>()
        == core::any::TypeId::of::<riscv_transpiler::cycle::IWithoutByteAccessIsaConfigWithDelegation>(
        )
    {
        riscv_transpiler::ir::preprocess_bytecode::<ReducedMachineDecoderConfig>(text_section)
    } else {
        panic!("Unknown machine config {}", core::any::type_name::<C>());
    };
    let tape = SimpleTape::new(&preprocessed_bytecode);

    type CountersT = DelegationsAndUnifiedCounters;

    let mut state = State::initial_with_counters(CountersT::default());
    let mut snapshotter = SimpleSnapshotter::new_with_cycle_limit(cycles_upper_bound, state);

    let now = std::time::Instant::now();
    let is_program_finished = VM::<CountersT>::run_basic_unrolled::<
        SimpleSnapshotter<CountersT, ROM_BOUND_SECOND_WORD_BITS>,
        RamWithRomRegion<ROM_BOUND_SECOND_WORD_BITS>,
        _,
    >(
        &mut state,
        &mut ram,
        &mut snapshotter,
        &tape,
        cycles_upper_bound,
        non_determinism,
    );
    assert!(
        is_program_finished,
        "program failed to finish over {} cycles",
        cycles_upper_bound
    ); // check that we reached looping state (ie. end state for our vm)

    let elapsed = now.elapsed();

    let register_final_values = state.registers.map(|el| RamShuffleMemStateRecord {
        current_value: el.value,
        last_access_timestamp: el.timestamp,
    });

    let _total_snapshots = snapshotter.snapshots.len();
    let exact_cycles_passed = (state.timestamp - INITIAL_TIMESTAMP) / TIMESTAMP_STEP;
    let final_pc = state.pc;
    let final_timestamp = state.timestamp;

    println!("Passed exactly {} cycles", exact_cycles_passed);
    println!(
        "Simulator performance is {} MHz",
        (exact_cycles_passed as f64) / (elapsed.as_micros() as f64)
    );

    let inits_and_teardowns = ram.collect_inits_and_teardowns(worker, A::default());

    // now replay. We will replay in parallel inside of every circuit family for simplicity
    let replay_blake_only_delegations = core::any::TypeId::of::<C>()
        == core::any::TypeId::of::<
            riscv_transpiler::cycle::IWithoutByteAccessIsaConfigWithDelegation,
        >();
    let _replay_mul_circuits = core::any::TypeId::of::<C>()
        != core::any::TypeId::of::<
            riscv_transpiler::cycle::IWithoutByteAccessIsaConfigWithDelegation,
        >();

    let main_circuits = {
        let t = replay_generic_work::<
            A,
            ROM_BOUND_SECOND_WORD_BITS,
            UnifiedCircuitDestinationHolderConstructor,
            _,
            _,
        >(
            &tape,
            &snapshotter,
            chunk_size,
            |counters| counters.get_calls_to_circuit_family::<REDUCED_MACHINE_CIRCUIT_FAMILY_IDX>(),
            REDUCED_MACHINE_CIRCUIT_FAMILY_IDX as usize,
            worker,
        );

        t
    };

    let blake_circuits = {
        let Some(cycles_per_circuit) = delegation_chunk_sizes
            .get(&(common_constants::blake2s_with_control::BLAKE2S_DELEGATION_CSR_REGISTER as u16))
            .copied()
        else {
            panic!(
                "Must have chunk size for work type {}",
                common_constants::blake2s_with_control::BLAKE2S_DELEGATION_CSR_REGISTER
            );
        };

        replay_generic_work::<
            A,
            ROM_BOUND_SECOND_WORD_BITS,
            BlakeDelegationDestinationHolderConstructor,
            _,
            _,
        >(
            &tape,
            &snapshotter,
            cycles_per_circuit,
            |cycles| cycles.blake_calls,
            common_constants::blake2s_with_control::BLAKE2S_DELEGATION_CSR_REGISTER as usize,
            worker,
        )
    };

    let bigint_circuits = if replay_blake_only_delegations {
        vec![]
    } else {
        let Some(cycles_per_circuit) = delegation_chunk_sizes
            .get(
                &(common_constants::bigint_with_control::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER
                    as u16),
            )
            .copied()
        else {
            panic!(
                "Must have chunk size for work type {}",
                common_constants::bigint_with_control::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER
            );
        };

        replay_generic_work::<
            A,
            ROM_BOUND_SECOND_WORD_BITS,
            BigintDelegationDestinationHolderConstructor,
            _,
            _,
        >(
            &tape,
            &snapshotter,
            cycles_per_circuit,
            |cycles| cycles.bigint_calls,
            common_constants::bigint_with_control::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as usize,
            worker,
        )
    };

    let keccak_circuits = if replay_blake_only_delegations {
        vec![]
    } else {
        let Some(cycles_per_circuit) = delegation_chunk_sizes
            .get(&(common_constants::keccak_special5::KECCAK_SPECIAL5_CSR_REGISTER as u16))
            .copied()
        else {
            panic!(
                "Must have chunk size for work type {}",
                common_constants::keccak_special5::KECCAK_SPECIAL5_CSR_REGISTER
            );
        };

        replay_generic_work::<
            A,
            ROM_BOUND_SECOND_WORD_BITS,
            KeccakDelegationDestinationHolderConstructor,
            _,
            _,
        >(
            &tape,
            &snapshotter,
            cycles_per_circuit,
            |cycles| cycles.keccak_calls,
            common_constants::keccak_special5::KECCAK_SPECIAL5_CSR_REGISTER as usize,
            worker,
        )
    };

    (
        final_pc,
        final_timestamp,
        exact_cycles_passed as usize,
        main_circuits,
        (blake_circuits, bigint_circuits, keccak_circuits),
        register_final_values,
        inits_and_teardowns,
    )
}

pub(crate) fn replay_non_mem<
    const FAMILY_IDX: u8,
    A: GoodAllocator,
    const ROM_BOUND_SECOND_WORD_BITS: usize,
>(
    tape: &impl riscv_transpiler::vm::InstructionTape,
    snapshotter: &riscv_transpiler::vm::SimpleSnapshotter<
        riscv_transpiler::vm::DelegationsAndFamiliesCounters,
        ROM_BOUND_SECOND_WORD_BITS,
    >,
    cycles_per_circuit: usize,
    worker: &Worker,
) -> Vec<NonMemTracingFamilyChunk<A>> {
    use riscv_transpiler::machine_mode_only_unrolled::*;
    use riscv_transpiler::vm::Counters;

    let counters = snapshotter
        .snapshots
        .last()
        .expect("at least one counter")
        .state
        .counters;
    let num_calls = counters.get_calls_to_circuit_family::<FAMILY_IDX>();
    if num_calls == 0 {
        return Vec::new();
    }

    let num_circuits = num_calls.div_ceil(cycles_per_circuit);

    println!(
        "In total {} calls to circuits for family {}",
        num_calls, FAMILY_IDX
    );

    println!(
        "In total {} of circuits for family {}",
        num_circuits, FAMILY_IDX
    );

    let initial_state = snapshotter.initial_snapshot.state;
    let last_state = snapshotter
        .snapshots
        .last()
        .expect("at least one counter")
        .state;
    assert_eq!(
        (last_state.timestamp - initial_state.timestamp) % TIMESTAMP_STEP,
        0
    );
    let total_num_cycles = (last_state.timestamp - initial_state.timestamp) / TIMESTAMP_STEP;

    // allocate ALL of them - not that we can not use macro as it DOES NOT preserve capacity
    let mut total_witness: Vec<_> =
        core::iter::repeat_with(|| Vec::with_capacity_in(cycles_per_circuit, A::default()))
            .take(num_circuits)
            .collect();

    // now there is no concrete solution what is the most optimal strategy here, but let's assume that frequency of particular opcodes
    // is well spread over the cycles

    let total_snapshots = snapshotter.snapshots.len();
    let average_calls_per_worker = num_calls.div_ceil(worker.get_num_cores());

    let mut witness_buffers: Vec<_> = total_witness
        .iter_mut()
        .map(|el| &mut el.spare_capacity_mut()[..cycles_per_circuit])
        .collect();

    let now = std::time::Instant::now();

    worker.scope(total_snapshots, |scope, _| {
        let mut starting_snapshot = snapshotter.initial_snapshot;
        let last_snapshot = *snapshotter.snapshots.last().expect("at least one snapshot");
        let mut current_snapshot = starting_snapshot;
        let mut snapshots_iter = snapshotter.snapshots.iter();
        let mut ram_range_start = 0;

        let mut total_snapshots_processed = 0;

        // split snapshots over workers
        for _i in 0..worker.get_num_cores() {
            if current_snapshot == last_snapshot {
                break;
            }

            let initial_snapshot_idx = total_snapshots_processed;

            'inner: while current_snapshot
                .state
                .counters
                .get_calls_to_circuit_family::<FAMILY_IDX>(
            ) - starting_snapshot
                .state
                .counters
                .get_calls_to_circuit_family::<FAMILY_IDX>(
            ) < average_calls_per_worker
            {
                if let Some(next_snapshot) = snapshots_iter.next() {
                    total_snapshots_processed += 1;
                    current_snapshot = *next_snapshot;
                } else {
                    break 'inner;
                }
            }

            let start_chunk_idx = starting_snapshot
                .state
                .counters
                .get_calls_to_circuit_family::<FAMILY_IDX>(
            ) / cycles_per_circuit;
            let start_chunk_offset = starting_snapshot
                .state
                .counters
                .get_calls_to_circuit_family::<FAMILY_IDX>(
            ) % cycles_per_circuit;

            let end_chunk_idx = current_snapshot
                .state
                .counters
                .get_calls_to_circuit_family::<FAMILY_IDX>(
            ) / cycles_per_circuit;
            let end_chunk_offset = current_snapshot
                .state
                .counters
                .get_calls_to_circuit_family::<FAMILY_IDX>(
            ) % cycles_per_circuit;

            let mut chunks = vec![];
            let mut offset = start_chunk_offset;
            unsafe {
                // Lazy to go via splits
                for src_chunk in start_chunk_idx..=end_chunk_idx {
                    if src_chunk == end_chunk_idx {
                        if end_chunk_offset > offset {
                            let range = offset..end_chunk_offset;
                            offset = end_chunk_offset;
                            let chunk = (&mut witness_buffers[src_chunk][range]
                                as *mut [MaybeUninit<NonMemoryOpcodeTracingDataWithTimestamp>])
                                .as_mut_unchecked();
                            chunks.push(chunk);

                        }
                    } else {
                        let range = offset..;
                        offset = 0;
                        let chunk = (&mut witness_buffers[src_chunk][range]
                            as *mut [MaybeUninit<NonMemoryOpcodeTracingDataWithTimestamp>])
                            .as_mut_unchecked();
                        chunks.push(chunk);
                    }
                }
            }

            let ram_range_end = current_snapshot.reads_end;

            let ram_range =
                ram_range_start..ram_range_end;

            assert_eq!((current_snapshot.state.timestamp - starting_snapshot.state.timestamp) % TIMESTAMP_STEP, 0);
            let num_cycles = (current_snapshot.state.timestamp - starting_snapshot.state.timestamp) / TIMESTAMP_STEP;

            use riscv_transpiler::replayer::*;
            use riscv_transpiler::witness::*;
            use riscv_transpiler::vm::ReplayBuffer;

            let tape_ref = tape;
            let snapshotter_ref = &snapshotter;

            let expected_final_snapshot_state = current_snapshot.state;

            // spawn replayer
            scope.spawn(move |_| {
                let mut ram_log_buffers = snapshotter_ref.reads_buffer.make_range(ram_range);
                let mut ram = ReplayerRam::<ROM_BOUND_SECOND_WORD_BITS> {
                    ram_log: &mut ram_log_buffers,
                };

                let mut chunks = chunks;
                let mut tracer =
                    UninitNonMemDestinationHolder::<FAMILY_IDX> {
                        buffers: &mut chunks,
                    };
                let mut state = starting_snapshot.state;
                ReplayerVM::<riscv_transpiler::vm::DelegationsAndFamiliesCounters>::replay_basic_unrolled::<_, _>(
                    &mut state,
                    &mut ram,
                    tape_ref,
                    &mut (),
                    num_cycles as usize,
                    &mut tracer,
                );
                assert_eq!(expected_final_snapshot_state.pc, state.pc, "diverged in thread {}: snapshots range {}..{}", _i, initial_snapshot_idx, total_snapshots_processed);
                assert_eq!(expected_final_snapshot_state.timestamp, state.timestamp, "diverged in thread {}: snapshots range {}..{}", _i, initial_snapshot_idx, total_snapshots_processed);
                assert_eq!(expected_final_snapshot_state.registers, state.registers, "diverged in thread {}: snapshots range {}..{}", _i, initial_snapshot_idx, total_snapshots_processed);
            });

            ram_range_start = ram_range_end;
            starting_snapshot = current_snapshot;
        }

        assert_eq!(ram_range_start, snapshotter.reads_buffer.len());
    });
    let elapsed = now.elapsed();

    println!(
        "Parallel replay performance is {} MHz ({} cycles) at {} cores for family {}",
        (total_num_cycles as f64) / (elapsed.as_micros() as f64),
        total_num_cycles,
        worker.get_num_cores(),
        FAMILY_IDX,
    );

    let last_chunk_init_size = num_calls % cycles_per_circuit;

    // cast to init and return

    let mut result = Vec::with_capacity(num_circuits);
    for (i, el) in total_witness.into_iter().enumerate() {
        let mut el = el;
        if i == num_circuits - 1 {
            unsafe {
                el.set_len(last_chunk_init_size);
            }
        } else {
            unsafe {
                el.set_len(cycles_per_circuit);
            }
        }
        result.push(NonMemTracingFamilyChunk {
            num_cycles: cycles_per_circuit,
            data: el,
        });
    }

    assert_eq!(
        result.iter().map(|el| el.data.len()).sum::<usize>(),
        num_calls
    );

    result
}

pub(crate) fn replay_mem<
    const FAMILY_IDX: u8,
    A: GoodAllocator,
    const ROM_BOUND_SECOND_WORD_BITS: usize,
>(
    tape: &impl riscv_transpiler::vm::InstructionTape,
    snapshotter: &riscv_transpiler::vm::SimpleSnapshotter<
        riscv_transpiler::vm::DelegationsAndFamiliesCounters,
        ROM_BOUND_SECOND_WORD_BITS,
    >,
    cycles_per_circuit: usize,
    worker: &Worker,
) -> Vec<MemTracingFamilyChunk<A>> {
    use riscv_transpiler::machine_mode_only_unrolled::*;
    use riscv_transpiler::vm::Counters;

    let counters = snapshotter
        .snapshots
        .last()
        .expect("at least one counter")
        .state
        .counters;
    let num_calls = counters.get_calls_to_circuit_family::<FAMILY_IDX>();
    if num_calls == 0 {
        return Vec::new();
    }

    let num_circuits = num_calls.div_ceil(cycles_per_circuit);

    println!(
        "In total {} calls to circuits for family {}",
        num_calls, FAMILY_IDX
    );

    println!(
        "In total {} of circuits for family {}",
        num_circuits, FAMILY_IDX
    );

    let initial_state = snapshotter.initial_snapshot.state;
    let last_state = snapshotter
        .snapshots
        .last()
        .expect("at least one counter")
        .state;
    assert_eq!(
        (last_state.timestamp - initial_state.timestamp) % TIMESTAMP_STEP,
        0
    );
    let total_num_cycles = (last_state.timestamp - initial_state.timestamp) / TIMESTAMP_STEP;

    // allocate ALL of them - not that we can not use macro as it DOES NOT preserve capacity
    let mut total_witness: Vec<_> =
        core::iter::repeat_with(|| Vec::with_capacity_in(cycles_per_circuit, A::default()))
            .take(num_circuits)
            .collect();

    // now there is no concrete solution what is the most optimal strategy here, but let's assume that frequency of particular opcodes
    // is well spread over the cycles

    let total_snapshots = snapshotter.snapshots.len();
    let average_calls_per_worker = num_calls.div_ceil(worker.get_num_cores());

    let mut witness_buffers: Vec<_> = total_witness
        .iter_mut()
        .map(|el| &mut el.spare_capacity_mut()[..cycles_per_circuit])
        .collect();

    let now = std::time::Instant::now();
    worker.scope(total_snapshots, |scope, _| {
        let mut starting_snapshot = snapshotter.initial_snapshot;
        let last_snapshot = *snapshotter.snapshots.last().expect("at least one snapshot");
        let mut current_snapshot = starting_snapshot;
        let mut snapshots_iter = snapshotter.snapshots.iter();
        let mut ram_range_start = 0;

        let mut total_snapshots_processed = 0;

        // split snapshots over workers
        for _i in 0..worker.get_num_cores() {
            if current_snapshot == last_snapshot {
                break;
            }

            let initial_snapshot_idx = total_snapshots_processed;

            'inner: while current_snapshot
                .state
                .counters
                .get_calls_to_circuit_family::<FAMILY_IDX>(
            ) - starting_snapshot
                .state
                .counters
                .get_calls_to_circuit_family::<FAMILY_IDX>(
            ) < average_calls_per_worker
            {
                if let Some(next_snapshot) = snapshots_iter.next() {
                    total_snapshots_processed += 1;
                    current_snapshot = *next_snapshot;
                } else {
                    break 'inner;
                }
            }

            let start_chunk_idx = starting_snapshot
                .state
                .counters
                .get_calls_to_circuit_family::<FAMILY_IDX>(
            ) / cycles_per_circuit;
            let start_chunk_offset = starting_snapshot
                .state
                .counters
                .get_calls_to_circuit_family::<FAMILY_IDX>(
            ) % cycles_per_circuit;

            let end_chunk_idx = current_snapshot
                .state
                .counters
                .get_calls_to_circuit_family::<FAMILY_IDX>(
            ) / cycles_per_circuit;
            let end_chunk_offset = current_snapshot
                .state
                .counters
                .get_calls_to_circuit_family::<FAMILY_IDX>(
            ) % cycles_per_circuit;

            let mut chunks = vec![];
            let mut offset = start_chunk_offset;
            unsafe {
                // Lazy to go via splits
                for src_chunk in start_chunk_idx..=end_chunk_idx {
                    if src_chunk == end_chunk_idx {
                        if end_chunk_offset > offset {
                            let range = offset..end_chunk_offset;
                            offset = end_chunk_offset;
                            let chunk = (&mut witness_buffers[src_chunk][range]
                                as *mut [MaybeUninit<MemoryOpcodeTracingDataWithTimestamp>])
                                .as_mut_unchecked();
                            chunks.push(chunk);
                        }
                    } else {
                        let range = offset..;
                        offset = 0;
                        let chunk = (&mut witness_buffers[src_chunk][range]
                            as *mut [MaybeUninit<MemoryOpcodeTracingDataWithTimestamp>])
                            .as_mut_unchecked();
                        chunks.push(chunk);
                    }
                }
            }

            let ram_range_end = current_snapshot.reads_end;

            let ram_range =
                ram_range_start..ram_range_end;

            assert_eq!((current_snapshot.state.timestamp - starting_snapshot.state.timestamp) % TIMESTAMP_STEP, 0);
            let num_cycles = (current_snapshot.state.timestamp - starting_snapshot.state.timestamp) / TIMESTAMP_STEP;


            use riscv_transpiler::replayer::*;
            use riscv_transpiler::witness::*;
            use riscv_transpiler::vm::ReplayBuffer;

            let tape_ref = tape;
            let snapshotter_ref = &snapshotter;

            let expected_final_snapshot_state = current_snapshot.state;

            // spawn replayer
            scope.spawn(move |_| {
                let mut ram_log_buffers = snapshotter_ref.reads_buffer.make_range(ram_range);

                let mut ram = ReplayerRam::<ROM_BOUND_SECOND_WORD_BITS> {
                    ram_log: &mut ram_log_buffers,
                };

                let mut chunks = chunks;
                let mut tracer =
                    UninitMemDestinationHolder::<FAMILY_IDX> {
                        buffers: &mut chunks,
                    };
                let mut state = starting_snapshot.state;
                ReplayerVM::<riscv_transpiler::vm::DelegationsAndFamiliesCounters>::replay_basic_unrolled::<_, _>(
                    &mut state,
                    &mut ram,
                    tape_ref,
                    &mut (),
                    num_cycles as usize,
                    &mut tracer,
                );

                assert_eq!(expected_final_snapshot_state.pc, state.pc, "diverged in thread {}: snapshots range {}..{}", _i, initial_snapshot_idx, total_snapshots_processed);
                assert_eq!(expected_final_snapshot_state.timestamp, state.timestamp, "diverged in thread {}: snapshots range {}..{}", _i, initial_snapshot_idx, total_snapshots_processed);
                assert_eq!(expected_final_snapshot_state.registers, state.registers, "diverged in thread {}: snapshots range {}..{}", _i, initial_snapshot_idx, total_snapshots_processed);
            });

            ram_range_start = ram_range_end;
            starting_snapshot = current_snapshot;
        }

        assert_eq!(ram_range_start, snapshotter.reads_buffer.len());
    });
    let elapsed = now.elapsed();

    println!(
        "Parallel replay performance is {} MHz ({} cycles) at {} cores for family {}",
        (total_num_cycles as f64) / (elapsed.as_micros() as f64),
        total_num_cycles,
        worker.get_num_cores(),
        FAMILY_IDX,
    );

    let last_chunk_init_size = num_calls % cycles_per_circuit;

    // cast to init and return

    let mut result = Vec::with_capacity(num_circuits);
    for (i, el) in total_witness.into_iter().enumerate() {
        let mut el = el;
        if i == num_circuits - 1 {
            unsafe {
                el.set_len(last_chunk_init_size);
            }
        } else {
            unsafe {
                el.set_len(cycles_per_circuit);
            }
        }
        result.push(MemTracingFamilyChunk {
            num_cycles: cycles_per_circuit,
            data: el,
        });
    }

    assert_eq!(
        result.iter().map(|el| el.data.len()).sum::<usize>(),
        num_calls
    );

    result
}

pub(crate) fn replay_generic_work<
    A: GoodAllocator,
    const ROM_BOUND_SECOND_WORD_BITS: usize,
    D: riscv_transpiler::witness::DestinationHolderConstructor,
    C: riscv_transpiler::vm::Counters,
    FN: Fn(&C) -> usize,
>(
    tape: &impl riscv_transpiler::vm::InstructionTape,
    snapshotter: &riscv_transpiler::vm::SimpleSnapshotter<C, ROM_BOUND_SECOND_WORD_BITS>,
    cycles_per_circuit: usize,
    cycles_fn: FN,
    work_type_idx: usize,
    worker: &Worker,
) -> Vec<Vec<D::Element, A>> {
    let counters = snapshotter
        .snapshots
        .last()
        .expect("at least one counter")
        .state
        .counters;
    let num_calls = cycles_fn(&counters);
    if num_calls == 0 {
        return Vec::new();
    }

    let num_circuits = num_calls.div_ceil(cycles_per_circuit);

    println!(
        "In total {} of circuits for type {}",
        num_circuits, work_type_idx
    );

    let initial_state = snapshotter.initial_snapshot.state;
    let last_state = snapshotter
        .snapshots
        .last()
        .expect("at least one counter")
        .state;
    assert_eq!(
        (last_state.timestamp - initial_state.timestamp) % TIMESTAMP_STEP,
        0
    );
    let total_num_cycles = (last_state.timestamp - initial_state.timestamp) / TIMESTAMP_STEP;

    // allocate ALL of them - not that we can not use macro as it DOES NOT preserve capacity
    let mut total_witness: Vec<Vec<D::Element, A>> =
        core::iter::repeat_with(|| Vec::with_capacity_in(cycles_per_circuit, A::default()))
            .take(num_circuits)
            .collect();

    // now there is no concrete solution what is the most optimal strategy here, but let's assume that frequency of particular opcodes
    // is well spread over the cycles

    let total_snapshots = snapshotter.snapshots.len();
    let average_calls_per_worker = num_calls.div_ceil(worker.get_num_cores());

    let mut witness_buffers: Vec<_> = total_witness
        .iter_mut()
        .map(|el| &mut el.spare_capacity_mut()[..cycles_per_circuit])
        .collect();

    let now = std::time::Instant::now();
    worker.scope(total_snapshots, |scope, _| {
        let mut starting_snapshot = snapshotter.initial_snapshot;
        let last_snapshot = *snapshotter.snapshots.last().expect("at least one snapshot");
        let mut current_snapshot = starting_snapshot;
        let mut snapshots_iter = snapshotter.snapshots.iter();
        let mut ram_range_start = 0;

        let mut total_snapshots_processed = 0;

        // split snapshots over workers
        for _i in 0..worker.get_num_cores() {
            if current_snapshot == last_snapshot {
                break;
            }

            let initial_snapshot_idx = total_snapshots_processed;

            'inner: while cycles_fn(&current_snapshot.state.counters)
                - cycles_fn(&starting_snapshot.state.counters)
                < average_calls_per_worker
            {
                if let Some(next_snapshot) = snapshots_iter.next() {
                    total_snapshots_processed += 1;
                    current_snapshot = *next_snapshot;
                } else {
                    break 'inner;
                }
            }

            let initial_calls = cycles_fn(&starting_snapshot.state.counters);
            let ending_calls = cycles_fn(&current_snapshot.state.counters);

            let start_chunk_idx = initial_calls / cycles_per_circuit;
            let start_chunk_offset = initial_calls % cycles_per_circuit;

            let end_chunk_idx = ending_calls / cycles_per_circuit;
            let end_chunk_offset = ending_calls % cycles_per_circuit;

            let mut chunks = vec![];
            let mut offset = start_chunk_offset;
            unsafe {
                // Lazy to go via splits
                for src_chunk in start_chunk_idx..=end_chunk_idx {
                    if src_chunk == end_chunk_idx {
                        if end_chunk_offset > offset {
                            let range = offset..end_chunk_offset;
                            offset = end_chunk_offset;
                            let chunk = (&mut witness_buffers[src_chunk][range]
                                as *mut [MaybeUninit<D::Element>])
                                .as_mut_unchecked();
                            chunks.push(chunk);
                        }
                    } else {
                        let range = offset..;
                        offset = 0;
                        let chunk = (&mut witness_buffers[src_chunk][range]
                            as *mut [MaybeUninit<D::Element>])
                            .as_mut_unchecked();
                        chunks.push(chunk);
                    }
                }
            }

            let ram_range_end = current_snapshot.reads_end;

            let ram_range = ram_range_start..ram_range_end;

            assert_eq!(
                (current_snapshot.state.timestamp - starting_snapshot.state.timestamp)
                    % TIMESTAMP_STEP,
                0
            );
            let num_cycles = (current_snapshot.state.timestamp - starting_snapshot.state.timestamp)
                / TIMESTAMP_STEP;

            use riscv_transpiler::replayer::*;
            use riscv_transpiler::vm::ReplayBuffer;

            let tape_ref = tape;
            let snapshotter_ref = &snapshotter;

            let expected_final_snapshot_state = current_snapshot.state;

            // spawn replayer
            scope.spawn(move |_| {
                let mut ram_log_buffers = snapshotter_ref.reads_buffer.make_range(ram_range);
                let mut ram = ReplayerRam::<ROM_BOUND_SECOND_WORD_BITS> {
                    ram_log: &mut ram_log_buffers,
                };

                let mut chunks = chunks;
                let mut tracer = D::make_uninit_tracer(&mut chunks);
                let mut state = starting_snapshot.state;
                ReplayerVM::<C>::replay_basic_unrolled::<_, _>(
                    &mut state,
                    &mut ram,
                    tape_ref,
                    &mut (),
                    num_cycles as usize,
                    &mut tracer,
                );

                assert_eq!(
                    expected_final_snapshot_state.pc, state.pc,
                    "diverged in thread {}: snapshots range {}..{}",
                    _i, initial_snapshot_idx, total_snapshots_processed
                );
                assert_eq!(
                    expected_final_snapshot_state.timestamp, state.timestamp,
                    "diverged in thread {}: snapshots range {}..{}",
                    _i, initial_snapshot_idx, total_snapshots_processed
                );
                assert_eq!(
                    expected_final_snapshot_state.registers, state.registers,
                    "diverged in thread {}: snapshots range {}..{}",
                    _i, initial_snapshot_idx, total_snapshots_processed
                );
            });

            ram_range_start = ram_range_end;
            starting_snapshot = current_snapshot;
        }

        assert!(snapshots_iter.next().is_none());
    });
    let elapsed = now.elapsed();

    println!(
        "Parallel replay performance is {} MHz ({} cycles) at {} cores for type {}",
        (total_num_cycles as f64) / (elapsed.as_micros() as f64),
        total_num_cycles,
        worker.get_num_cores(),
        work_type_idx,
    );

    let last_chunk_init_size = num_calls % cycles_per_circuit;

    // cast to init and return

    let mut result = Vec::with_capacity(num_circuits);
    for (i, el) in total_witness.into_iter().enumerate() {
        let mut el = el;
        if i == num_circuits - 1 {
            unsafe {
                el.set_len(last_chunk_init_size);
            }
        } else {
            unsafe {
                el.set_len(cycles_per_circuit);
            }
        }
        result.push(el);
    }

    assert_eq!(result.iter().map(|el| el.len()).sum::<usize>(), num_calls);

    result
}
