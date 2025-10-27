use core::mem::MaybeUninit;

use super::*;
use crate::tracers::delegation::DelegationWitness;
use crate::tracers::unrolled::tracer::*;
use crate::tracers::unrolled::word_specialized_tracer::WordSpecializedTracer;
use cs::machine::machine_configurations::full_isa_with_delegation_no_exceptions::FullIsaMachineWithDelegationNoExceptionHandling;
use cs::machine::machine_configurations::full_isa_with_delegation_no_exceptions_no_signed_mul_div::FullIsaMachineWithDelegationNoExceptionHandlingNoSignedMulDiv;
use cs::machine::machine_configurations::minimal_no_exceptions_with_delegation::MinimalMachineNoExceptionHandlingWithDelegation;
use risc_v_simulator::cycle::MachineConfig;
use risc_v_simulator::machine_mode_only_unrolled::{
    DelegationCSRProcessor, RiscV32StateForUnrolledProver,
};
use riscv_transpiler::witness::delegation::bigint::BigintDelegationWitness;
use riscv_transpiler::witness::delegation::blake2_round_function::Blake2sRoundFunctionDelegationWitness;
use riscv_transpiler::witness::delegation::keccak_special5::KeccakSpecial5DelegationWitness;

mod family_circuits;

pub use self::family_circuits::*;

pub fn run_unrolled_machine_for_num_cycles<
    CSR: DelegationCSRProcessor,
    C: MachineConfig,
    A: GoodAllocator,
>(
    num_cycles: usize,
    initial_pc: u32,
    mut custom_csr_processor: CSR,
    memory: &mut VectorMemoryImplWithRom,
    rom_address_space_bound: usize,
    non_determinism: &mut impl NonDeterminismCSRSource<VectorMemoryImplWithRom>,
    opcode_family_chunk_factories: HashMap<
        u8,
        Box<dyn Fn() -> NonMemTracingFamilyChunk<A> + Send + Sync + 'static>,
    >,
    mem_family_chunk_factory: Box<dyn Fn() -> MemTracingFamilyChunk<A> + Send + Sync + 'static>,
    delegation_factories: HashMap<
        u16,
        Box<dyn Fn() -> DelegationWitness<A> + Send + Sync + 'static>,
    >,
    ram_bound: usize,
    worker: &Worker,
) -> (
    u32,
    HashMap<u8, Vec<NonMemTracingFamilyChunk<A>>>,
    Vec<MemTracingFamilyChunk<A>>,
    HashMap<u16, Vec<DelegationWitness<A>>>,
    [RamShuffleMemStateRecord; NUM_REGISTERS], // register final values
    Vec<Vec<(u32, (TimestampScalar, u32)), A>>, // lazy iniy/teardown data - all unique words touched, sorted ascending, but not in one vector
) {
    use crate::tracers::main_cycle_optimized::DelegationTracingData;
    use crate::tracers::main_cycle_optimized::RamTracingData;

    let now = std::time::Instant::now();

    let mut state = RiscV32StateForUnrolledProver::<C>::initial(initial_pc);

    let ram_tracer =
        RamTracingData::<true>::new_for_ram_size_and_rom_bound(ram_bound, rom_address_space_bound);
    let delegation_tracer = DelegationTracingData {
        all_per_type_logs: HashMap::new(),
        delegation_witness_factories: delegation_factories,
        current_per_type_logs: HashMap::new(),
        num_traced_registers: 0,
        mem_reads_offset: 0,
        mem_writes_offset: 0,
    };

    // important - in out memory implementation first access in every chunk is timestamped as (trace_size * circuit_idx) + 4,
    // so we take care of it

    let mut tracer = UnrolledGPUFriendlyTracer::<C, A, true, true, true>::new(
        ram_tracer,
        opcode_family_chunk_factories,
        mem_family_chunk_factory,
        delegation_tracer,
    );

    state.run_cycles(
        memory,
        &mut tracer,
        non_determinism,
        &mut custom_csr_processor,
        num_cycles,
    );

    let UnrolledGPUFriendlyTracer {
        bookkeeping_aux_data,
        current_timestamp,
        current_family_chunks,
        completed_family_chunks,
        current_mem_family_chunk,
        completed_mem_family_chunks,
        delegation_tracer,
        ..
    } = tracer;

    let mut completed_family_chunks = completed_family_chunks;
    for (i, el) in current_family_chunks.into_iter().enumerate() {
        completed_family_chunks
            .entry((i + 1) as u8)
            .or_insert(vec![])
            .push(el);
    }

    let mut completed_mem_family_chunks = completed_mem_family_chunks;
    completed_mem_family_chunks.push(current_mem_family_chunk);

    let cycles_passed = (current_timestamp - INITIAL_TIMESTAMP) / TIMESTAMP_STEP;

    println!("Finished over {} cycles", cycles_passed);

    let RamTracingData {
        register_last_live_timestamps,
        ram_words_last_live_timestamps,
        access_bitmask,
        num_touched_ram_cells,
        ..
    } = bookkeeping_aux_data;

    dbg!(num_touched_ram_cells);

    // now we can co-join touched memory cells, their final values and timestamps

    let memory_final_state = memory.clone().get_final_ram_state();
    let memory_state_ref = &memory_final_state;
    let ram_words_last_live_timestamps_ref = &ram_words_last_live_timestamps;

    // parallel collect
    // first we will walk over access_bitmask and collect subparts
    let mut chunks: Vec<Vec<(u32, (TimestampScalar, u32)), A>> =
        vec![Vec::new_in(A::default()).clone(); worker.get_num_cores()];
    let mut dst = &mut chunks[..];
    worker.scope(access_bitmask.len(), |scope, geometry| {
        for thread_idx in 0..geometry.len() {
            let chunk_size = geometry.get_chunk_size(thread_idx);
            let chunk_start = geometry.get_chunk_start_pos(thread_idx);
            let range = chunk_start..(chunk_start + chunk_size);
            let (el, rest) = dst.split_at_mut(1);
            dst = rest;
            let src = &access_bitmask[range];

            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                let el = &mut el[0];
                for (idx, word) in src.iter().enumerate() {
                    for bit_idx in 0..usize::BITS {
                        let word_idx =
                            (chunk_start + idx) * (usize::BITS as usize) + (bit_idx as usize);
                        let phys_address = word_idx << 2;
                        let word_is_used = *word & (1 << bit_idx) > 0;
                        if word_is_used {
                            let word_value = memory_state_ref[word_idx];
                            let last_timestamp: TimestampScalar =
                                ram_words_last_live_timestamps_ref[word_idx];
                            el.push((phys_address as u32, (last_timestamp, word_value)));
                        }
                    }
                }
            });
        }
    });

    let register_final_values = std::array::from_fn(|i| {
        let ts = register_last_live_timestamps[i];
        let value = state.registers[i];

        RamShuffleMemStateRecord {
            last_access_timestamp: ts,
            current_value: value,
        }
    });

    let DelegationTracingData {
        all_per_type_logs,
        current_per_type_logs,
        ..
    } = delegation_tracer;

    let mut all_per_type_logs = all_per_type_logs;
    for (delegation_type, current_data) in current_per_type_logs.into_iter() {
        // we use a convention that not executing delegation is checked
        // by looking at the lengths, so we do NOT pad here

        // let mut current_data = current_data;
        // current_data.pad();

        if current_data.is_empty() == false {
            all_per_type_logs
                .entry(delegation_type)
                .or_insert(vec![])
                .push(current_data);
        }
    }

    let elapsed = now.elapsed();

    let freq = (cycles_passed as f64) / elapsed.as_secs_f64() / 1_000_000f64;
    println!("Simulator frequency is {} MHz", freq);

    (
        state.pc,
        completed_family_chunks,
        completed_mem_family_chunks,
        all_per_type_logs,
        register_final_values,
        chunks,
    )
}

pub fn run_unrolled_machine_for_num_cycles_with_word_memory_ops_specialization<
    CSR: DelegationCSRProcessor,
    C: MachineConfig,
    A: GoodAllocator,
>(
    num_cycles: usize,
    initial_pc: u32,
    mut custom_csr_processor: CSR,
    memory: &mut VectorMemoryImplWithRom,
    rom_address_space_bound: usize,
    non_determinism: &mut impl NonDeterminismCSRSource<VectorMemoryImplWithRom>,
    opcode_family_chunk_factories: HashMap<
        u8,
        Box<dyn Fn() -> NonMemTracingFamilyChunk<A> + Send + Sync + 'static>,
    >,
    word_sized_mem_family_chunk_factory: Box<
        dyn Fn() -> MemTracingFamilyChunk<A> + Send + Sync + 'static,
    >,
    subword_sized_mem_family_chunk_factory: Box<
        dyn Fn() -> MemTracingFamilyChunk<A> + Send + Sync + 'static,
    >,
    delegation_factories: HashMap<
        u16,
        Box<dyn Fn() -> DelegationWitness<A> + Send + Sync + 'static>,
    >,
    ram_bound: usize,
    worker: &Worker,
) -> (
    u32,
    TimestampScalar,
    usize,
    HashMap<u8, Vec<NonMemTracingFamilyChunk<A>>>,
    (Vec<MemTracingFamilyChunk<A>>, Vec<MemTracingFamilyChunk<A>>),
    HashMap<u16, Vec<DelegationWitness<A>>>,
    [RamShuffleMemStateRecord; NUM_REGISTERS], // register final values
    Vec<Vec<(u32, (TimestampScalar, u32)), A>>, // lazy iniy/teardown data - all unique words touched, sorted ascending, but not in one vector
) {
    use crate::tracers::main_cycle_optimized::DelegationTracingData;
    use crate::tracers::main_cycle_optimized::RamTracingData;

    let now = std::time::Instant::now();

    let mut state = RiscV32StateForUnrolledProver::<C>::initial(initial_pc);

    let ram_tracer =
        RamTracingData::<true>::new_for_ram_size_and_rom_bound(ram_bound, rom_address_space_bound);
    let delegation_tracer = DelegationTracingData::<A> {
        all_per_type_logs: HashMap::new(),
        delegation_witness_factories: delegation_factories,
        current_per_type_logs: HashMap::new(),
        num_traced_registers: 0,
        mem_reads_offset: 0,
        mem_writes_offset: 0,
    };

    // important - in out memory implementation first access in every chunk is timestamped as (trace_size * circuit_idx) + 4,
    // so we take care of it

    let mut tracer = WordSpecializedTracer::<C, A, true, true, true>::new(
        ram_tracer,
        opcode_family_chunk_factories,
        word_sized_mem_family_chunk_factory,
        subword_sized_mem_family_chunk_factory,
        delegation_tracer,
    );

    let cycles_used = state.run_cycles(
        memory,
        &mut tracer,
        non_determinism,
        &mut custom_csr_processor,
        num_cycles,
    );

    println!("Execution completed after {} cycles", cycles_used);

    let WordSpecializedTracer {
        bookkeeping_aux_data,
        current_timestamp,
        current_family_chunks,
        completed_family_chunks,
        current_word_sized_mem_family_chunk,
        current_subword_sized_mem_family_chunk,
        completed_word_sized_mem_family_chunks,
        completed_subword_sized_mem_family_chunks,
        delegation_tracer,
        ..
    } = tracer;

    let mut completed_family_chunks = completed_family_chunks;
    for (i, el) in current_family_chunks.into_iter().enumerate() {
        completed_family_chunks
            .entry((i + 1) as u8)
            .or_insert(vec![])
            .push(el);
    }

    let mut completed_word_sized_mem_family_chunks = completed_word_sized_mem_family_chunks;
    completed_word_sized_mem_family_chunks.push(current_word_sized_mem_family_chunk);

    let mut completed_subword_sized_mem_family_chunks = completed_subword_sized_mem_family_chunks;
    completed_subword_sized_mem_family_chunks.push(current_subword_sized_mem_family_chunk);

    let cycles_passed = (current_timestamp - INITIAL_TIMESTAMP) / TIMESTAMP_STEP;
    assert_eq!(cycles_used as u64, cycles_passed);

    let RamTracingData {
        register_last_live_timestamps,
        ram_words_last_live_timestamps,
        access_bitmask,
        num_touched_ram_cells,
        ..
    } = bookkeeping_aux_data;

    println!("{} unique memory cells touched", num_touched_ram_cells);

    // now we can co-join touched memory cells, their final values and timestamps

    let memory_final_state = memory.clone().get_final_ram_state();
    let memory_state_ref = &memory_final_state;
    let ram_words_last_live_timestamps_ref = &ram_words_last_live_timestamps;

    // parallel collect
    // first we will walk over access_bitmask and collect subparts
    let mut chunks: Vec<Vec<(u32, (TimestampScalar, u32)), A>> =
        vec![Vec::new_in(A::default()).clone(); worker.get_num_cores()];
    let mut dst = &mut chunks[..];
    worker.scope(access_bitmask.len(), |scope, geometry| {
        for thread_idx in 0..geometry.len() {
            let chunk_size = geometry.get_chunk_size(thread_idx);
            let chunk_start = geometry.get_chunk_start_pos(thread_idx);
            let range = chunk_start..(chunk_start + chunk_size);
            let (el, rest) = dst.split_at_mut(1);
            dst = rest;
            let src = &access_bitmask[range];

            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                let el = &mut el[0];
                for (idx, word) in src.iter().enumerate() {
                    for bit_idx in 0..usize::BITS {
                        let word_idx =
                            (chunk_start + idx) * (usize::BITS as usize) + (bit_idx as usize);
                        let phys_address = word_idx << 2;
                        let word_is_used = *word & (1 << bit_idx) > 0;
                        if word_is_used {
                            let word_value = memory_state_ref[word_idx];
                            let last_timestamp: TimestampScalar =
                                ram_words_last_live_timestamps_ref[word_idx];
                            el.push((phys_address as u32, (last_timestamp, word_value)));
                        }
                    }
                }
            });
        }
    });

    let register_final_values = std::array::from_fn(|i| {
        let ts = register_last_live_timestamps[i];
        let value = state.registers[i];

        RamShuffleMemStateRecord {
            last_access_timestamp: ts,
            current_value: value,
        }
    });

    let DelegationTracingData {
        all_per_type_logs,
        current_per_type_logs,
        ..
    } = delegation_tracer;

    let mut all_per_type_logs = all_per_type_logs;
    for (delegation_type, current_data) in current_per_type_logs.into_iter() {
        // we use a convention that not executing delegation is checked
        // by looking at the lengths, so we do NOT pad here

        // let mut current_data = current_data;
        // current_data.pad();

        if current_data.is_empty() == false {
            all_per_type_logs
                .entry(delegation_type)
                .or_insert(vec![])
                .push(current_data);
        }
    }

    let elapsed = now.elapsed();

    let freq = (cycles_passed as f64) / elapsed.as_secs_f64() / 1_000_000f64;
    println!("Simulator frequency is {} MHz", freq);

    let final_pc = state.pc;
    let final_timestamp = state.timestamp;

    (
        final_pc,
        final_timestamp,
        cycles_used,
        completed_family_chunks,
        (
            completed_word_sized_mem_family_chunks,
            completed_subword_sized_mem_family_chunks,
        ),
        all_per_type_logs,
        register_final_values,
        chunks,
    )
}

pub fn run_unrolled_machine<
    C: MachineConfig,
    A: GoodAllocator,
    const ROM_BOUND_SECOND_WORD_BITS: usize,
>(
    initial_pc: u32,
    text_section: &[u32],
    rom_image: &[u32],
    replayer_max_snapshots: usize,
    replayer_snapshot_period: usize,
    ram_bound_bytes: usize,
    non_determinism: &mut impl riscv_transpiler::vm::NonDeterminismCSRSource<
        riscv_transpiler::vm::RamWithRomRegion<ROM_BOUND_SECOND_WORD_BITS>,
    >,
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
    use riscv_transpiler::vm::*;
    use riscv_transpiler::witness::*;
    use riscv_transpiler::*;

    assert_eq!(initial_pc, 0);
    assert!(1 << (16 + ROM_BOUND_SECOND_WORD_BITS) <= ram_bound_bytes);
    assert!(text_section.len() * 4 <= ram_bound_bytes);
    assert!(rom_image.len() * 4 <= ram_bound_bytes);
    let mut ram = RamWithRomRegion::from_rom_content(rom_image, ram_bound_bytes);

    // use crate::cs::machine::ops::unrolled::process_binary_into_separate_tables_ext;
    // let preprocessed_data = if core::any::TypeId::of::<C>() == core::any::TypeId::of::<FullIsaMachineWithDelegationNoExceptionHandling>() {
    //     process_binary_into_separate_tables_ext::<Mersenne31Field, true, Global>(
    //         &text_section_u32,
    //         &opcodes_for_full_machine_with_mem_word_access_specialization(),
    //         1 << (16 + ROM_BOUND_SECOND_WORD_BITS - 2),
    //         &[
    //             NON_DETERMINISM_CSR as u16,
    //             BLAKE2S_DELEGATION_CSR_REGISTER as u16,
    //             BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16,
    //             KECCAK_SPECIAL5_CSR_REGISTER as u16,
    //         ],
    //     )
    // } else if core::any::TypeId::of::<C>() == core::any::TypeId::of::<FullIsaMachineWithDelegationNoExceptionHandlingNoSignedMulDiv>() {
    //     process_binary_into_separate_tables_ext::<Mersenne31Field, true, Global>(
    //         &text_section_u32,
    //         &opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization(),
    //         1 << (16 + ROM_BOUND_SECOND_WORD_BITS - 2),
    //         &[
    //             NON_DETERMINISM_CSR as u16,
    //             BLAKE2S_DELEGATION_CSR_REGISTER as u16,
    //             BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16,
    //             KECCAK_SPECIAL5_CSR_REGISTER as u16,
    //         ],
    //     )
    // } else if core::any::TypeId::of::<C>() == core::any::TypeId::of::<MinimalMachineNoExceptionHandlingWithDelegation>() {
    //         process_binary_into_separate_tables_ext::<Mersenne31Field, true, Global>(
    //         &text_section_u32,
    //         &opcodes_for_reduced_machine(),
    //         1 << (16 + ROM_BOUND_SECOND_WORD_BITS - 2),
    //         &[
    //             NON_DETERMINISM_CSR as u16,
    //             BLAKE2S_DELEGATION_CSR_REGISTER as u16,
    //         ],
    //     )
    // } else {
    //     panic!("Unknown machine config {}", core::any::type_name::<C>());
    // };

    let preprocessed_bytecode: Vec<_> = text_section
        .iter()
        .map(|el| {
            let opcode = *el;
            use riscv_transpiler::ir::*;
            if core::any::TypeId::of::<C>()
                == core::any::TypeId::of::<risc_v_simulator::cycle::IMStandardIsaConfig>()
            {
                decode::<FullMachineDecoderConfig>(opcode)
            } else if core::any::TypeId::of::<C>()
                == core::any::TypeId::of::<
                    risc_v_simulator::cycle::IMStandardIsaConfigWithUnsignedMulDiv,
                >()
            {
                decode::<FullUnsignedMachineDecoderConfig>(opcode)
            } else if core::any::TypeId::of::<C>()
                == core::any::TypeId::of::<
                    risc_v_simulator::cycle::IWithoutByteAccessIsaConfigWithDelegation,
                >()
            {
                decode::<ReducedMachineDecoderConfig>(opcode)
            } else {
                panic!("Unknown machine config {}", core::any::type_name::<C>());
            }
        })
        .collect();
    let tape = SimpleTape::new(&preprocessed_bytecode);

    let cycles_upper_bound = replayer_snapshot_period * replayer_max_snapshots;

    type CountersT = DelegationsAndFamiliesCounters;

    let mut state = State::initial_with_counters(CountersT::default());
    let mut snapshotter = SimpleSnapshotter::new_with_cycle_limit(
        cycles_upper_bound,
        replayer_snapshot_period,
        state,
    );

    let now = std::time::Instant::now();
    let is_program_finished = VM::<CountersT>::run_basic_unrolled::<
        SimpleSnapshotter<CountersT, ROM_BOUND_SECOND_WORD_BITS>,
        RamWithRomRegion<ROM_BOUND_SECOND_WORD_BITS>,
        _,
    >(
        &mut state,
        replayer_max_snapshots,
        &mut ram,
        &mut snapshotter,
        &tape,
        replayer_snapshot_period,
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

    let total_snapshots = snapshotter.snapshots.len();
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
            risc_v_simulator::cycle::IWithoutByteAccessIsaConfigWithDelegation,
        >();
    let replay_blake_only_delegations = core::any::TypeId::of::<C>()
        == core::any::TypeId::of::<
            risc_v_simulator::cycle::IWithoutByteAccessIsaConfigWithDelegation,
        >();
    let replay_mul_circuits = core::any::TypeId::of::<C>()
        != core::any::TypeId::of::<
            risc_v_simulator::cycle::IWithoutByteAccessIsaConfigWithDelegation,
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
        >(
            &tape,
            &snapshotter,
            replayer_snapshot_period,
            cycles_per_circuit,
            worker,
        );
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
            replayer_snapshot_period,
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
            replayer_snapshot_period,
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
            replayer_snapshot_period,
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
            replayer_snapshot_period,
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
        >(
            &tape,
            &snapshotter,
            replayer_snapshot_period,
            cycles_per_circuit,
            worker,
        );
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
        >(
            &tape,
            &snapshotter,
            replayer_snapshot_period,
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
        >(
            &tape,
            &snapshotter,
            replayer_snapshot_period,
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
        >(
            &tape,
            &snapshotter,
            replayer_snapshot_period,
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

fn replay_non_mem<
    const FAMILY_IDX: u8,
    A: GoodAllocator,
    const ROM_BOUND_SECOND_WORD_BITS: usize,
>(
    tape: &impl riscv_transpiler::vm::InstructionTape,
    snapshotter: &riscv_transpiler::vm::SimpleSnapshotter<
        riscv_transpiler::vm::DelegationsAndFamiliesCounters,
        ROM_BOUND_SECOND_WORD_BITS,
    >,
    replayer_snapshot_period: usize,
    cycles_per_circuit: usize,
    worker: &Worker,
) -> Vec<NonMemTracingFamilyChunk<A>> {
    use risc_v_simulator::machine_mode_only_unrolled::*;
    use riscv_transpiler::vm::Counters;

    let cycles_upper_bound = replayer_snapshot_period * snapshotter.snapshots.len();

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
        "In total {} of circuits for family {}",
        num_circuits, FAMILY_IDX
    );

    // allocate ALL of them
    let mut total_witness =
        vec![Vec::with_capacity_in(cycles_per_circuit, A::default()); num_circuits];

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

        // split snapshots over workers
        for _i in 0..worker.get_num_cores() {
            if current_snapshot == last_snapshot {
                break;
            }

            let mut num_snapshots = 0;
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
                    num_snapshots += 1;
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
                        if end_chunk_offset > 0 {
                            let range = 0..end_chunk_offset;
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

            let ram_range =
                starting_snapshot.memory_reads_start..current_snapshot.memory_reads_end;
            let nd_range = starting_snapshot.non_determinism_reads_start
                ..current_snapshot.non_determinism_reads_end;

            use riscv_transpiler::replayer::*;
            use riscv_transpiler::witness::*;

            let mut ram = ReplayerRam::<ROM_BOUND_SECOND_WORD_BITS> {
                ram_log: &snapshotter.reads_buffer[ram_range],
            };
            let mut nd = ReplayerNonDeterminism {
                non_determinism_reads_log: &snapshotter.non_determinism_reads_buffer[nd_range],
            };

            let tape_ref = tape;

            // spawn replayer
            scope.spawn(move |_| {
                let mut chunks = chunks;
                let mut tracer =
                    UninitNonMemDestinationHolder::<FAMILY_IDX> {
                        buffers: &mut chunks,
                    };
                let mut state = starting_snapshot.state;
                ReplayerVM::<riscv_transpiler::vm::DelegationsAndFamiliesCounters>::replay_basic_unrolled::<_, _>(
                    &mut state,
                    num_snapshots,
                    &mut ram,
                    tape_ref,
                    replayer_snapshot_period,
                    &mut nd,
                    &mut tracer,
                );
            });

            starting_snapshot = current_snapshot;
        }
    });
    let elapsed = now.elapsed();

    println!(
        "Parallel replay performance is {} MHz ({} total snapshots with period of {} cycles) at {} cores for family {}",
        (cycles_upper_bound as f64) / (elapsed.as_micros() as f64),
        total_snapshots,
        replayer_snapshot_period,
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

    result
}

fn replay_mem<const FAMILY_IDX: u8, A: GoodAllocator, const ROM_BOUND_SECOND_WORD_BITS: usize>(
    tape: &impl riscv_transpiler::vm::InstructionTape,
    snapshotter: &riscv_transpiler::vm::SimpleSnapshotter<
        riscv_transpiler::vm::DelegationsAndFamiliesCounters,
        ROM_BOUND_SECOND_WORD_BITS,
    >,
    replayer_snapshot_period: usize,
    cycles_per_circuit: usize,
    worker: &Worker,
) -> Vec<MemTracingFamilyChunk<A>> {
    use risc_v_simulator::machine_mode_only_unrolled::*;
    use riscv_transpiler::vm::Counters;

    let cycles_upper_bound = replayer_snapshot_period * snapshotter.snapshots.len();

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
        "In total {} of circuits for family {}",
        num_circuits, FAMILY_IDX
    );

    // allocate ALL of them
    let mut total_witness =
        vec![Vec::with_capacity_in(cycles_per_circuit, A::default()); num_circuits];

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

        // split snapshots over workers
        for _i in 0..worker.get_num_cores() {
            if current_snapshot == last_snapshot {
                break;
            }

            let mut num_snapshots = 0;
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
                    num_snapshots += 1;
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
                        if end_chunk_offset > 0 {
                            let range = 0..end_chunk_offset;
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

            let ram_range =
                starting_snapshot.memory_reads_start..current_snapshot.memory_reads_end;
            let nd_range = starting_snapshot.non_determinism_reads_start
                ..current_snapshot.non_determinism_reads_end;

            use riscv_transpiler::replayer::*;
            use riscv_transpiler::witness::*;

            let mut ram = ReplayerRam::<ROM_BOUND_SECOND_WORD_BITS> {
                ram_log: &snapshotter.reads_buffer[ram_range],
            };
            let mut nd = ReplayerNonDeterminism {
                non_determinism_reads_log: &snapshotter.non_determinism_reads_buffer[nd_range],
            };

            let tape_ref = tape;

            // spawn replayer
            scope.spawn(move |_| {
                let mut chunks = chunks;
                let mut tracer =
                    UninitMemDestinationHolder::<FAMILY_IDX> {
                        buffers: &mut chunks,
                    };
                let mut state = starting_snapshot.state;
                ReplayerVM::<riscv_transpiler::vm::DelegationsAndFamiliesCounters>::replay_basic_unrolled::<_, _>(
                    &mut state,
                    num_snapshots,
                    &mut ram,
                    tape_ref,
                    replayer_snapshot_period,
                    &mut nd,
                    &mut tracer,
                );
            });

            starting_snapshot = current_snapshot;
        }
    });
    let elapsed = now.elapsed();

    println!(
        "Parallel replay performance is {} MHz ({} total snapshots with period of {} cycles) at {} cores for family {}",
        (cycles_upper_bound as f64) / (elapsed.as_micros() as f64),
        total_snapshots,
        replayer_snapshot_period,
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

    result
}

fn replay_generic_work<
    A: GoodAllocator,
    const ROM_BOUND_SECOND_WORD_BITS: usize,
    D: riscv_transpiler::witness::DestinationHolderConstructor,
    FN: Fn(&riscv_transpiler::vm::DelegationsAndFamiliesCounters) -> usize,
>(
    tape: &impl riscv_transpiler::vm::InstructionTape,
    snapshotter: &riscv_transpiler::vm::SimpleSnapshotter<
        riscv_transpiler::vm::DelegationsAndFamiliesCounters,
        ROM_BOUND_SECOND_WORD_BITS,
    >,
    replayer_snapshot_period: usize,
    cycles_per_circuit: usize,
    cycles_fn: FN,
    work_type_idx: usize,
    worker: &Worker,
) -> Vec<Vec<D::Element, A>> {
    use risc_v_simulator::machine_mode_only_unrolled::*;
    use riscv_transpiler::vm::Counters;
    use riscv_transpiler::witness::DestinationHolderConstructor;

    let cycles_upper_bound = replayer_snapshot_period * snapshotter.snapshots.len();

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

    // allocate ALL of them
    let mut total_witness: Vec<Vec<D::Element, A>> =
        vec![Vec::with_capacity_in(cycles_per_circuit, A::default()); num_circuits];

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

        // split snapshots over workers
        for _i in 0..worker.get_num_cores() {
            if current_snapshot == last_snapshot {
                break;
            }

            let mut num_snapshots = 0;
            'inner: while cycles_fn(&current_snapshot
                .state
                .counters) - cycles_fn(&starting_snapshot
                .state
                .counters) < average_calls_per_worker
            {
                if let Some(next_snapshot) = snapshots_iter.next() {
                    num_snapshots += 1;
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
                        if end_chunk_offset > 0 {
                            let range = 0..end_chunk_offset;
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

            let ram_range =
                starting_snapshot.memory_reads_start..current_snapshot.memory_reads_end;
            let nd_range = starting_snapshot.non_determinism_reads_start
                ..current_snapshot.non_determinism_reads_end;

            use riscv_transpiler::replayer::*;
            use riscv_transpiler::witness::*;

            let mut ram = ReplayerRam::<ROM_BOUND_SECOND_WORD_BITS> {
                ram_log: &snapshotter.reads_buffer[ram_range],
            };
            let mut nd = ReplayerNonDeterminism {
                non_determinism_reads_log: &snapshotter.non_determinism_reads_buffer[nd_range],
            };

            let tape_ref = tape;

            // spawn replayer
            scope.spawn(move |_| {
                let mut chunks = chunks;
                let mut tracer = D::make_uninit_tracer(&mut chunks);
                let mut state = starting_snapshot.state;
                ReplayerVM::<riscv_transpiler::vm::DelegationsAndFamiliesCounters>::replay_basic_unrolled::<_, _>(
                    &mut state,
                    num_snapshots,
                    &mut ram,
                    tape_ref,
                    replayer_snapshot_period,
                    &mut nd,
                    &mut tracer,
                );
            });
            starting_snapshot = current_snapshot;
        }

        assert!(snapshots_iter.next().is_none());
    });
    let elapsed = now.elapsed();

    println!(
        "Parallel replay performance is {} MHz ({} total snapshots with period of {} cycles) at {} cores for type {}",
        (cycles_upper_bound as f64) / (elapsed.as_micros() as f64),
        total_snapshots,
        replayer_snapshot_period,
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

    result
}
