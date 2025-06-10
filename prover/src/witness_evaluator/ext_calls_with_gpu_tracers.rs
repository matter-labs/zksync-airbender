use super::ext_calls::*;
use super::*;
use crate::tracers::delegation::bigint_with_control_factory_fn;
use crate::tracers::delegation::blake2_with_control_factory_fn;
use crate::tracers::delegation::DelegationWitness;
use crate::tracers::main_cycle_optimized::CycleData;
use crate::tracers::oracles::delegation_oracle::DelegationCircuitOracle;
use crate::tracers::oracles::main_risc_v_circuit::MainRiscVOracle;
use crate::witness_evaluator::new::evaluate_witness;
use crate::witness_evaluator::new::SimpleWitnessProxy;
use risc_v_simulator::cycle::state_new::DelegationCSRProcessor;
use risc_v_simulator::cycle::MachineConfig;
use risc_v_simulator::delegations::u256_ops_with_control::U256_OPS_WITH_CONTROL_ACCESS_ID;

#[allow(unused_assignments)]
/// Runs a given binary for that many steps, to generate witness and delegation work.
pub fn dev_run_all_and_make_witness_ext_with_gpu_tracers<
    M: Machine<Mersenne31Field>,
    C: MachineConfig,
    CSR: DelegationCSRProcessor,
    const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize,
>(
    machine: M,
    compiled_machine: &CompiledCircuitArtifact<Mersenne31Field>,
    witnes_eval_fn_ptr: fn(&mut SimpleWitnessProxy<'_, MainRiscVOracle<'_, C>>),
    delegation_witness_eval_fns: HashMap<
        u32,
        fn(&mut SimpleWitnessProxy<'_, DelegationCircuitOracle<'_>>),
    >,
    delegation_compiled_machines: &[(u32, DelegationProcessorDescription)],
    binary: &[u32],
    num_cycles: usize,
    trace_len: usize,
    csr_processor: CSR,
    csr_table: Option<LookupWrapper<Mersenne31Field>>,
    non_determinism_responses: Vec<u32>,
    worker: &Worker,
) -> (
    Vec<WitnessEvaluationData<DEFAULT_TRACE_PADDING_MULTIPLE, Global>>,
    [RamShuffleMemStateRecord; NUM_REGISTERS],
    Vec<DelegationWorkForType<Global>>,
)
where
    [(); { <M as Machine<Mersenne31Field>>::ASSUME_TRUSTED_CODE } as usize]:,
    [(); { <M as Machine<Mersenne31Field>>::OUTPUT_EXACT_EXCEPTIONS } as usize]:,
{
    use crate::tracers::oracles::chunk_lazy_init_and_teardown;
    use cs::tables::*;
    use risc_v_simulator::delegations::blake2_round_function_with_compression_mode::BLAKE2_ROUND_FUNCTION_WITH_EXTENDED_CONTROL_ACCESS_ID;

    assert!(trace_len.is_power_of_two());
    assert_eq!(num_cycles % (trace_len - 1), 0);

    const ENTRY_POINT: u32 = 0;

    assert!(<M as Machine<Mersenne31Field>>::USE_ROM_FOR_BYTECODE);

    // we should check that our worst-case multiplicities do not overflow field
    let capacity = 1 << (Mersenne31Field::CHAR_BITS - 1);
    assert!(
        compiled_machine
            .witness_layout
            .range_check_8_columns
            .num_elements()
            * trace_len
            <= capacity
    );
    assert!(
        compiled_machine
            .witness_layout
            .range_check_16_columns
            .num_elements()
            * trace_len
            <= capacity
    );
    assert!(compiled_machine.witness_layout.width_3_lookups.len() * trace_len <= capacity);

    let mut memory = VectorMemoryImplWithRom::new_for_byte_size(
        1 << 30,
        1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS),
    ); // use 1 GB RAM
    for (idx, insn) in binary.iter().enumerate() {
        memory.populate(ENTRY_POINT + idx as u32 * 4, *insn);
    }

    let mut factories = HashMap::new();
    for (delegation_type, circuit) in delegation_compiled_machines.iter() {
        if *delegation_type == BLAKE2_ROUND_FUNCTION_WITH_EXTENDED_CONTROL_ACCESS_ID {
            let num_requests_per_circuit = circuit.num_requests_per_circuit;
            let delegation_type = *delegation_type as u16;
            let factory_fn =
                move || blake2_with_control_factory_fn(delegation_type, num_requests_per_circuit);
            factories.insert(
                delegation_type,
                Box::new(factory_fn) as Box<(dyn Fn() -> DelegationWitness)>,
            );
        } else if *delegation_type == U256_OPS_WITH_CONTROL_ACCESS_ID {
            let num_requests_per_circuit = circuit.num_requests_per_circuit;
            let delegation_type = *delegation_type as u16;
            let factory_fn =
                move || bigint_with_control_factory_fn(delegation_type, num_requests_per_circuit);
            factories.insert(
                delegation_type,
                Box::new(factory_fn) as Box<(dyn Fn() -> DelegationWitness)>,
            );
        } else {
            panic!(
                "delegation type {} is unsupported for tests",
                delegation_type
            )
        }
    }

    let (final_pc, main_traces, mut delegation_traces, teardown, register_final_values) =
        dev_run_for_num_cycles_under_convention_ext_with_gpu_tracers(
            num_cycles,
            trace_len,
            ENTRY_POINT,
            csr_processor,
            &mut memory,
            1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS),
            non_determinism_responses,
            factories,
        );

    assert!(final_pc % 4 == 0);
    assert_eq!(binary[(final_pc / 4) as usize], 111); // "jal x0, 0"

    let num_chunks = num_cycles / (trace_len - 1);
    let chunk_size = trace_len - 1;

    let mut table_driver = create_table_driver::<_, _, ROM_ADDRESS_SPACE_SECOND_WORD_BITS>(machine);
    // add preimage into table driver
    let rom_table = create_table_for_rom_image::<_, ROM_ADDRESS_SPACE_SECOND_WORD_BITS>(
        &binary,
        TableType::RomRead.to_table_id(),
    );
    table_driver.add_table_with_content(TableType::RomRead, LookupWrapper::Dimensional3(rom_table));
    if let Some(csr_table) = csr_table.clone() {
        table_driver.add_table_with_content(TableType::SpecialCSRProperties, csr_table);
    }

    let (num_trivial, inits_and_teardowns) =
        chunk_lazy_init_and_teardown::<Global>(num_chunks, chunk_size, &[teardown], worker);

    assert_eq!(num_trivial, 0, "trivial padding is not expected in tests");

    let mut result = Vec::with_capacity(num_chunks);

    let mut it = inits_and_teardowns.into_iter();
    let mut tracers_it = main_traces.into_iter();

    for circuit_idx in 0..num_chunks {
        let setups_and_teardowns_chunk = it.next().unwrap();
        let state_tracer = tracers_it.next().unwrap();

        let oracle = MainRiscVOracle {
            cycle_data: &state_tracer,
        };

        #[cfg(feature = "debug_logs")]
        println!("Evaluating witness");
        #[cfg(feature = "timing_logs")]
        let now = std::time::Instant::now();

        let chunk = evaluate_witness(
            &compiled_machine,
            witnes_eval_fn_ptr,
            chunk_size,
            &oracle,
            &setups_and_teardowns_chunk.lazy_init_data,
            &table_driver,
            circuit_idx,
            &worker,
            Global,
        );

        #[cfg(feature = "timing_logs")]
        println!(
            "Full witness evaluation for RISC-V circuit took {:?}",
            now.elapsed()
        );

        #[cfg(feature = "debug_logs")]
        println!("Evaluating memory-only witness for main RISC-V circuit");
        #[cfg(feature = "timing_logs")]
        let now = std::time::Instant::now();
        let memory_chunk = evaluate_memory_witness(
            &compiled_machine,
            chunk_size,
            &oracle,
            &setups_and_teardowns_chunk.lazy_init_data,
            &worker,
            Global,
        );

        #[cfg(feature = "timing_logs")]
        dbg!(now.elapsed());

        {
            let mut a = chunk.exec_trace.row_view(0..trace_len);
            let mut b = memory_chunk.memory_trace.row_view(0..trace_len);

            assert_eq!(a.width() - chunk.num_witness_columns, b.width());
            unsafe {
                for row in 0..trace_len {
                    let mut equal = true;
                    for (_, (a, b)) in a
                        .current_row_split(chunk.num_witness_columns)
                        .1
                        .iter()
                        .zip(b.current_row_ref().iter())
                        .enumerate()
                    {
                        if a != b {
                            equal = false;
                            // panic!("Witness evaluator diverged for memory column {} at row {}: full witness outputs {}, memory only generation outputs {}", i, row, a, b);
                        }
                    }

                    if equal == false {
                        panic!(
                            "Row {}: Full witness generation returned memory row\n{:?}\nMemory only generation returned\n{:?}",
                            row,
                            a
                            .current_row_split(chunk.num_witness_columns)
                            .1,
                            b.current_row_ref()
                        );
                    }

                    a.advance_row();
                    b.advance_row();
                }
            }
        }

        result.push(chunk);
    }

    assert!(it.next().is_none());
    assert!(tracers_it.next().is_none());

    let mut delegation_circuits = vec![];
    let mut keys: Vec<u16> = delegation_traces.keys().copied().collect();
    keys.sort();
    for delegation_type in keys.into_iter() {
        let circuit_idx = delegation_compiled_machines
            .iter()
            .position(|el| el.0 == delegation_type as u32)
            .expect("must have a matching compiled delegation circuit");
        let (_, circuit) = &delegation_compiled_machines[circuit_idx];

        assert!(circuit.trace_len.is_power_of_two());
        assert_eq!(circuit.num_requests_per_circuit + 1, circuit.trace_len);

        let capacity = circuit.num_requests_per_circuit;

        let delegation_requests = delegation_traces.remove(&delegation_type).unwrap();

        let mut work_unit = DelegationWorkForType {
            delegation_type: delegation_type as u16,
            num_requests_per_circuit: circuit.num_requests_per_circuit,
            trace_len: circuit.trace_len,
            table_driver: circuit.table_driver.clone(),
            compiled_circuit: circuit.compiled_circuit.clone(),
            work_units: Vec::with_capacity(delegation_requests.len()),
        };

        for chunk in delegation_requests.iter() {
            // evaluate a witness and memory-only witness for each

            // serialize_to_file(&chunk.to_vec(), "blake2_extended_delegation_oracle");

            let oracle = DelegationCircuitOracle { cycle_data: chunk };
            #[cfg(feature = "debug_logs")]
            println!(
                "Evaluating memory-only witness for delegation circuit {}",
                delegation_type
            );
            let mem_only_witness = evaluate_delegation_memory_witness(
                &circuit.compiled_circuit,
                capacity,
                &oracle,
                worker,
                Global,
            );

            let eval_fn = delegation_witness_eval_fns[&(delegation_type as u32)];

            #[cfg(feature = "debug_logs")]
            println!(
                "Evaluating witness for delegation circuit {}",
                delegation_type
            );
            let full_witness = evaluate_witness(
                &circuit.compiled_circuit,
                eval_fn,
                capacity,
                &oracle,
                &[],
                &circuit.table_driver,
                0,
                worker,
                Global,
            );

            {
                // compare memory witness as usual
                let mut a = full_witness.exec_trace.row_view(0..capacity);
                let mut b = mem_only_witness.memory_trace.row_view(0..capacity);

                assert_eq!(a.width() - full_witness.num_witness_columns, b.width());
                unsafe {
                    for row in 0..capacity {
                        let mut equal = true;
                        let a_row = a.current_row_split(full_witness.num_witness_columns).1;
                        let b_row = b.current_row_ref();
                        for (i, (a_value, b_value)) in a_row.iter().zip(b_row.iter()).enumerate() {
                            if a_value != b_value {
                                equal = false;
                                println!("{:?}", &a_row[..=i]);
                                println!("{:?}", &b_row[..=i]);
                                panic!("Witness evaluator diverged for memory column {} at row {}: full witness outputs {}, memory only generation outputs {}", i, row, a_value, b_value);
                            }
                        }

                        if equal == false {
                            panic!("Row {}: Full witness generation returned memory row\n{:?}\nMemory only witness generation for delegation circuits returned\n{:?}", row, a.current_row_ref(), b.current_row_ref());
                        }

                        a.advance_row();
                        b.advance_row();
                    }
                }
            }

            let instance = DelegationProcessorWitness {
                witness: full_witness,
            };

            work_unit.work_units.push(instance);
        }

        delegation_circuits.push(work_unit);
    }

    (result, register_final_values, delegation_circuits)
}

pub fn dev_run_for_num_cycles_under_convention_ext_with_gpu_tracers<
    CSR: DelegationCSRProcessor,
    C: MachineConfig,
>(
    num_cycles: usize,
    trace_size: usize,
    initial_pc: u32,
    mut custom_csr_processor: CSR,
    memory: &mut VectorMemoryImplWithRom,
    rom_address_space_bound: usize,
    non_determinism_responses: Vec<u32>,
    delegation_factories: HashMap<u16, Box<dyn Fn() -> DelegationWitness>>,
) -> (
    u32,
    Vec<CycleData<C>>,
    HashMap<u16, Vec<DelegationWitness>>,
    Vec<(u32, (TimestampScalar, u32))>, // lazy iniy/teardown data - all unique words touched
    [RamShuffleMemStateRecord; NUM_REGISTERS], // register final values
) {
    use crate::tracers::main_cycle_optimized::DelegationTracingData;
    use crate::tracers::main_cycle_optimized::GPUFriendlyTracer;
    use crate::tracers::main_cycle_optimized::RamTracingData;
    use risc_v_simulator::cycle::state_new::RiscV32StateForUnrolledProver;
    assert!(trace_size.is_power_of_two());

    let mut state = RiscV32StateForUnrolledProver::<C>::initial(initial_pc);

    let bookkeeping_aux_data =
        RamTracingData::<true>::new_for_ram_size_and_rom_bound(1 << 30, rom_address_space_bound); // use 1 GB RAM
    let delegation_tracer = DelegationTracingData {
        all_per_type_logs: HashMap::new(),
        delegation_witness_factories: delegation_factories,
        current_per_type_logs: HashMap::new(),
        num_traced_registers: 0,
        mem_reads_offset: 0,
        mem_writes_offset: 0,
    };

    assert!(trace_size.is_power_of_two());
    let num_cycles_in_chunk = trace_size - 1;
    // important - in out memory implementation first access in every chunk is timestamped as (trace_size * circuit_idx) + 4,
    // so we take care of it
    let mut non_determinism = QuasiUARTSource::new_with_reads(non_determinism_responses);

    let mut num_traces_to_use = num_cycles / num_cycles_in_chunk;
    if num_cycles % num_cycles_in_chunk != 0 {
        num_traces_to_use += 1;
    }

    let initial_ts = timestamp_from_chunk_cycle_and_sequence(0, num_cycles_in_chunk, 0);
    let mut tracer = GPUFriendlyTracer::<_, _, true, true, true>::new(
        initial_ts,
        bookkeeping_aux_data,
        delegation_tracer,
        num_cycles_in_chunk,
        num_traces_to_use,
    );

    let mut end_reached = false;

    for chunk_idx in 0..num_traces_to_use {
        if chunk_idx != 0 {
            let timestamp =
                timestamp_from_chunk_cycle_and_sequence(0, num_cycles_in_chunk, chunk_idx);
            tracer.prepare_for_next_chunk(timestamp);
        }

        dbg!(tracer.current_timestamp);

        let finished = state.run_cycles(
            memory,
            &mut tracer,
            &mut non_determinism,
            &mut custom_csr_processor,
            num_cycles_in_chunk,
        );

        if finished {
            end_reached = true;
            break;
        };
    }

    assert!(end_reached, "program execution did not finish");

    let GPUFriendlyTracer {
        bookkeeping_aux_data,
        trace_chunk,
        traced_chunks,
        delegation_tracer,
        ..
    } = tracer;

    // put latest chunk manually in traced ones
    let mut traced_chunks = traced_chunks;
    traced_chunks.push(trace_chunk);

    let RamTracingData {
        register_last_live_timestamps,
        ram_words_last_live_timestamps,
        access_bitmask,
        num_touched_ram_cells,
        ..
    } = bookkeeping_aux_data;

    dbg!(num_touched_ram_cells);
    let ram = memory.clone().get_final_ram_state();

    let mut teardown_data: Vec<(u32, (TimestampScalar, u32))> =
        Vec::with_capacity(num_touched_ram_cells);
    for (bitmask_word_idx, bitmask) in access_bitmask.iter().enumerate() {
        for bit_idx in 0..usize::BITS {
            let word_idx = bitmask_word_idx * (usize::BITS as usize) + (bit_idx as usize);
            let phys_address = word_idx << 2;
            let word_is_used = *bitmask & (1 << bit_idx) > 0;
            if word_is_used {
                let word_value = ram[word_idx];
                let last_timestamp: TimestampScalar = ram_words_last_live_timestamps[word_idx];
                teardown_data.push((phys_address as u32, (last_timestamp, word_value)));
            }
        }
    }

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

    (
        state.pc,
        traced_chunks,
        all_per_type_logs,
        teardown_data,
        register_final_values,
    )
}
