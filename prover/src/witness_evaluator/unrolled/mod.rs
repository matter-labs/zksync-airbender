use super::*;
use crate::tracers::delegation::DelegationWitness;
use crate::tracers::unrolled::tracer::*;
use crate::tracers::unrolled::word_specialized_tracer::WordSpecializedTracer;
use risc_v_simulator::cycle::MachineConfig;
use risc_v_simulator::machine_mode_only_unrolled::{
    DelegationCSRProcessor, RiscV32StateForUnrolledProver, INITIAL_TIMESTAMP,
};

mod family_circuits;

pub use self::family_circuits::*;

pub fn run_unrolled_machine_for_num_cycles<CSR: DelegationCSRProcessor, C: MachineConfig>(
    num_cycles: usize,
    initial_pc: u32,
    mut custom_csr_processor: CSR,
    memory: &mut VectorMemoryImplWithRom,
    rom_address_space_bound: usize,
    non_determinism_replies: Vec<u32>,
    opcode_family_chunk_factories: HashMap<u8, Box<dyn Fn() -> NonMemTracingFamilyChunk>>,
    mem_family_chunk_factory: Box<dyn Fn() -> MemTracingFamilyChunk>,
    delegation_factories: HashMap<u16, Box<dyn Fn() -> DelegationWitness>>,
    worker: &Worker,
) -> (
    u32,
    HashMap<u8, Vec<NonMemTracingFamilyChunk>>,
    Vec<MemTracingFamilyChunk>,
    HashMap<u16, Vec<DelegationWitness>>,
    [RamShuffleMemStateRecord; NUM_REGISTERS], // register final values
    Vec<Vec<(u32, (TimestampScalar, u32))>>, // lazy iniy/teardown data - all unique words touched, sorted ascending, but not in one vector
) {
    use crate::tracers::main_cycle_optimized::DelegationTracingData;
    use crate::tracers::main_cycle_optimized::RamTracingData;

    let now = std::time::Instant::now();

    let mut state = RiscV32StateForUnrolledProver::<C>::initial(initial_pc);

    let ram_tracer =
        RamTracingData::<true>::new_for_ram_size_and_rom_bound(1 << 32, rom_address_space_bound);
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

    let mut non_determinism = QuasiUARTSource::new_with_reads(non_determinism_replies);

    let mut tracer = UnrolledGPUFriendlyTracer::<C, Global, true, true, true>::new(
        ram_tracer,
        opcode_family_chunk_factories,
        mem_family_chunk_factory,
        delegation_tracer,
    );

    state.run_cycles(
        memory,
        &mut tracer,
        &mut non_determinism,
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
    let mut chunks: Vec<Vec<(u32, (TimestampScalar, u32))>> =
        vec![vec![].clone(); worker.get_num_cores()];
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
>(
    num_cycles: usize,
    initial_pc: u32,
    mut custom_csr_processor: CSR,
    memory: &mut VectorMemoryImplWithRom,
    rom_address_space_bound: usize,
    non_determinism_replies: Vec<u32>,
    opcode_family_chunk_factories: HashMap<u8, Box<dyn Fn() -> NonMemTracingFamilyChunk>>,
    word_sized_mem_family_chunk_factory: Box<dyn Fn() -> MemTracingFamilyChunk>,
    subword_sized_mem_family_chunk_factory: Box<dyn Fn() -> MemTracingFamilyChunk>,
    delegation_factories: HashMap<u16, Box<dyn Fn() -> DelegationWitness>>,
    worker: &Worker,
) -> (
    u32,
    HashMap<u8, Vec<NonMemTracingFamilyChunk>>,
    (Vec<MemTracingFamilyChunk>, Vec<MemTracingFamilyChunk>),
    HashMap<u16, Vec<DelegationWitness>>,
    [RamShuffleMemStateRecord; NUM_REGISTERS], // register final values
    Vec<Vec<(u32, (TimestampScalar, u32))>>, // lazy iniy/teardown data - all unique words touched, sorted ascending, but not in one vector
) {
    use crate::tracers::main_cycle_optimized::DelegationTracingData;
    use crate::tracers::main_cycle_optimized::RamTracingData;

    let now = std::time::Instant::now();

    let mut state = RiscV32StateForUnrolledProver::<C>::initial(initial_pc);

    let ram_tracer =
        RamTracingData::<true>::new_for_ram_size_and_rom_bound(1 << 32, rom_address_space_bound);
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

    let mut non_determinism = QuasiUARTSource::new_with_reads(non_determinism_replies);

    let mut tracer = WordSpecializedTracer::<C, Global, true, true, true>::new(
        ram_tracer,
        opcode_family_chunk_factories,
        word_sized_mem_family_chunk_factory,
        subword_sized_mem_family_chunk_factory,
        delegation_tracer,
    );

    state.run_cycles(
        memory,
        &mut tracer,
        &mut non_determinism,
        &mut custom_csr_processor,
        num_cycles,
    );

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
    let mut chunks: Vec<Vec<(u32, (TimestampScalar, u32))>> =
        vec![vec![].clone(); worker.get_num_cores()];
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
        (
            completed_word_sized_mem_family_chunks,
            completed_subword_sized_mem_family_chunks,
        ),
        all_per_type_logs,
        register_final_values,
        chunks,
    )
}
