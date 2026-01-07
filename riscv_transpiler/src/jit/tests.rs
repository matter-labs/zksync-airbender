use risc_v_simulator::abstractions::non_determinism::QuasiUARTSource;

use super::*;
use crate::{
    jit::minimal_tracer::{ChunkPostSnapshot, PreallocatedSnapshots},
    replayer::ReplayerVM,
    vm::test::*,
};
use std::{alloc::Global, io::Read, path::Path};

#[test]
fn test_jit_simple_fibonacci() {
    let path = std::env::current_dir().unwrap();
    println!("The current directory is {}", path.display());

    // let (_, binary) = read_binary(&Path::new("riscv_transpiler/examples/fibonacci/app.bin"));
    // let (_, text) = read_binary(&Path::new("riscv_transpiler/examples/fibonacci/app.text"));

    // let (_, binary) = read_binary(&Path::new("examples/fibonacci/app.bin"));
    // let (_, text) = read_binary(&Path::new("examples/fibonacci/app.text"));

    let (_, binary) = read_binary(&Path::new("examples/keccak_f1600/app.bin"));
    let (_, text) = read_binary(&Path::new("examples/keccak_f1600/app.text"));

    JittedCode::<_>::run_alternative_simulator(&text, &mut (), &binary, None);
}

#[test]
fn test_jit_recursive_verifier() {
    let path = std::env::current_dir().unwrap();
    println!("The current directory is {}", path.display());

    let (_, binary) = read_binary(&Path::new(
        "examples/recursive_verifier/recursion_in_unrolled_layer.bin",
    ));
    let (_, text) = read_binary(&Path::new(
        "examples/recursive_verifier/recursion_in_unrolled_layer.text",
    ));

    let mut responses = std::fs::File::open("examples/recursive_verifier/responses.bin").unwrap();
    let mut buff = vec![];
    responses.read_to_end(&mut buff).unwrap();
    let resposnes: Vec<u32> = buff
        .as_chunks::<4>()
        .0
        .iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();
    let mut source = QuasiUARTSource::new_with_reads(resposnes);

    JittedCode::<_>::run_alternative_simulator(&text, &mut source, &binary, None);
}

#[test]
fn test_ensure_proof_correctness() {
    use crate::ir::*;

    let path = std::env::current_dir().unwrap();
    println!("The current directory is {}", path.display());

    let (_, binary) = read_binary(&Path::new(
        "examples/recursive_verifier/recursion_in_unrolled_layer.bin",
    ));
    let (_, text) = read_binary(&Path::new(
        "examples/recursive_verifier/recursion_in_unrolled_layer.text",
    ));

    let mut responses = std::fs::File::open("examples/recursive_verifier/responses.bin").unwrap();
    let mut buff = vec![];
    responses.read_to_end(&mut buff).unwrap();
    let resposnes: Vec<u32> = buff
        .as_chunks::<4>()
        .0
        .iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();
    let mut source = QuasiUARTSource::new_with_reads(resposnes);

    let instructions: Vec<Instruction> = preprocess_bytecode::<ReducedMachineDecoderConfig>(&text);
    let tape = SimpleTape::new(&instructions);
    let mut ram =
        RamWithRomRegion::<{ common_constants::rom::ROM_SECOND_WORD_BITS }>::from_rom_content(
            &binary,
            1 << 30,
        );

    let cycles_bound = 1 << 31;

    let mut state = State::initial_with_counters(DelegationsAndFamiliesCounters::default());

    let now = std::time::Instant::now();
    VM::run_basic_unrolled::<_, _, _>(
        &mut state,
        &mut ram,
        &mut (),
        &tape,
        cycles_bound,
        &mut source,
    );
}

#[test]
fn test_few_instr() {
    use std::collections::HashMap;

    // let source = [
    //     "addi x1, x0, 1234",
    //     "addi x2, x0, 4",
    //     "sw x1, 4(x2)"
    // ];

    // let source = [
    //     "addi x1, x0, 1234",
    //     "addi x2, x0, 4",
    //     "sh x1, 2(x2)"
    // ];

    let source = [
        "addi x1, x0, 1234",
        "addi x2, x0, 4",
        "sb x1, 0(x2)",
        "addi x4, x0, 8",
        "lb x3, -4(x4)",
    ];

    let mut empty_hash: HashMap<String, u32> = HashMap::new();
    let mut text = vec![];
    for el in source.into_iter() {
        let encoding = lib_rv32_asm::assemble_ir(el, &mut empty_hash, 0)
            .unwrap()
            .unwrap();
        text.push(encoding);
    }
    text.push(0x0000006f);

    JittedCode::<_>::run_alternative_simulator(&text, &mut (), &[], None);
}

#[test]
fn test_jit_full_block() {
    let path = std::env::current_dir().unwrap();
    println!("The current directory is {}", path.display());

    let (_, binary) = read_binary(&Path::new("examples/zksync_os/app.bin"));
    let (_, text) = read_binary(&Path::new("examples/zksync_os/app.text"));

    let (witness, _) = read_binary(&Path::new("examples/zksync_os/23620012_witness"));
    let witness = hex::decode(core::str::from_utf8(&witness).unwrap()).unwrap();
    let witness: Vec<_> = witness
        .as_chunks::<4>()
        .0
        .iter()
        .map(|el| u32::from_be_bytes(*el))
        .collect();
    let mut source = QuasiUARTSource::new_with_reads(witness);

    let (state, _) = JittedCode::<_>::run_alternative_simulator(&text, &mut source, &binary, None);

    println!("PC = 0x{:08x}", state.pc);
    dbg!(state.registers);
}

fn run_reference_for_num_cycles(
    binary: &[u32],
    text: &[u32],
    mut source: impl NonDeterminismCSRSource,
    timestamp_bound: TimestampScalar,
) -> (
    State<DelegationsAndFamiliesCounters>,
    RamWithRomRegion<{ common_constants::rom::ROM_SECOND_WORD_BITS }>,
) {
    use crate::ir::*;

    let instructions: Vec<Instruction> =
        preprocess_bytecode::<FullUnsignedMachineDecoderConfig>(text);
    let tape = SimpleTape::new(&instructions);
    let mut ram =
        RamWithRomRegion::<{ common_constants::rom::ROM_SECOND_WORD_BITS }>::from_rom_content(
            &binary,
            1 << 30,
        );

    let mut state = State::initial_with_counters(DelegationsAndFamiliesCounters::default());

    VM::run_by_timestamp_bound::<_, _, _>(
        &mut state,
        &mut ram,
        &mut (),
        &tape,
        timestamp_bound,
        &mut source,
    );

    (state, ram)
}

fn run_reference_for_num_cycles_with_snapshots(
    binary: &[u32],
    text: &[u32],
    mut source: impl NonDeterminismCSRSource,
    timestamp_bound: TimestampScalar,
    reduced_isa: bool,
) -> (
    State<DelegationsAndFamiliesCounters>,
    RamWithRomRegion<{ common_constants::rom::ROM_SECOND_WORD_BITS }>,
    SimpleSnapshotter<
        DelegationsAndFamiliesCounters,
        { common_constants::rom::ROM_SECOND_WORD_BITS },
    >,
) {
    use crate::ir::*;

    let instructions = if reduced_isa {
        preprocess_bytecode::<ReducedMachineDecoderConfig>(text)
    } else {
        preprocess_bytecode::<FullUnsignedMachineDecoderConfig>(text)
    };
    let tape = SimpleTape::new(&instructions);
    let mut ram =
        RamWithRomRegion::<{ common_constants::rom::ROM_SECOND_WORD_BITS }>::from_rom_content(
            &binary,
            1 << 30,
        );

    let mut state = State::initial_with_counters(DelegationsAndFamiliesCounters::default());
    let mut snapshotter = SimpleSnapshotter::<_, {common_constants::rom::ROM_SECOND_WORD_BITS }>::new_with_cycle_limit(1 << 31, state);

    VM::run_by_timestamp_bound::<_, _, _>(
        &mut state,
        &mut ram,
        &mut snapshotter,
        // &mut (),
        &tape,
        timestamp_bound,
        &mut source,
    );

    (state, ram, snapshotter)
}

#[test]
fn test_reference_block_exec() {
    use crate::ir::*;

    let (_, binary) = read_binary(&Path::new("examples/zksync_os/app.bin"));
    let (_, text) = read_binary(&Path::new("examples/zksync_os/app.text"));

    let (witness, _) = read_binary(&Path::new("examples/zksync_os/23620012_witness"));
    let witness = hex::decode(core::str::from_utf8(&witness).unwrap()).unwrap();
    let witness: Vec<_> = witness
        .as_chunks::<4>()
        .0
        .iter()
        .map(|el| u32::from_be_bytes(*el))
        .collect();
    let mut source = QuasiUARTSource::new_with_reads(witness);

    let instructions: Vec<Instruction> =
        preprocess_bytecode::<FullUnsignedMachineDecoderConfig>(&text);
    let tape = SimpleTape::new(&instructions);
    let mut ram =
        RamWithRomRegion::<{ common_constants::rom::ROM_SECOND_WORD_BITS }>::from_rom_content(
            &binary,
            1 << 30,
        );

    let cycles_bound = 1 << 31;

    let mut state = State::initial_with_counters(DelegationsAndFamiliesCounters::default());
    let mut snapshotter = SimpleSnapshotter::<_, { common_constants::rom::ROM_SECOND_WORD_BITS }>::new_with_cycle_limit(cycles_bound, state);

    let now = std::time::Instant::now();
    VM::run_basic_unrolled::<_, _, _>(
        &mut state,
        &mut ram,
        &mut snapshotter,
        &tape,
        cycles_bound,
        &mut source,
    );
    let elapsed = now.elapsed();

    println!("PC = 0x{:08x}", state.pc);
    dbg!(state.registers.map(|el| el.value));
}

#[test]
fn run_and_compare() {
    let (_, binary) = read_binary(&Path::new("examples/zksync_os/app.bin"));
    let (_, text) = read_binary(&Path::new("examples/zksync_os/app.text"));

    let (witness, _) = read_binary(&Path::new("examples/zksync_os/23620012_witness"));
    let witness = hex::decode(core::str::from_utf8(&witness).unwrap()).unwrap();
    let witness: Vec<_> = witness
        .as_chunks::<4>()
        .0
        .iter()
        .map(|el| u32::from_be_bytes(*el))
        .collect();
    let mut source = QuasiUARTSource::new_with_reads(witness);

    let step = 1 << 19;
    let initial_step = 762314752;
    let upper_bound = (1 << 30) - 8;

    let mut previous_cycles_taken = 0;

    let mut num_steps = initial_step;
    while num_steps < upper_bound {
        // let (jit_state, jit_memory) = JittedCode::run_alternative_simulator(
        //     &text,
        //     &mut source.clone(),
        //     &binary,
        //     Some(num_steps),
        // );

        let (jit_state, jit_memory, jit_last_trace_chunk) =
            JittedCode::run_alternative_simulator_with_last_snapshot(
                &text,
                &mut source.clone(),
                &binary,
                Some(num_steps),
            );

        let cycles_taken = (jit_state.timestamp - INITIAL_TIMESTAMP) / TIMESTAMP_STEP;
        if cycles_taken == previous_cycles_taken {
            break;
        }
        previous_cycles_taken = cycles_taken;

        // let (reference_state, reference_ram) =
        //     run_reference_for_num_cycles(&binary, &text, source.clone(), jit_state.timestamp);

        let (reference_state, reference_ram, reference_snapshotter) =
            run_reference_for_num_cycles_with_snapshots(
                &binary,
                &text,
                source.clone(),
                jit_state.timestamp,
                false,
            );

        assert_eq!(
            reference_state.timestamp, jit_state.timestamp,
            "TIMESTAMP diverged after {} steps",
            num_steps
        );
        if reference_state.pc != jit_state.pc {
            panic!(
                "PC diverged after {} steps: expected 0x{:08x}, got 0x{:08x}",
                num_steps, reference_state.pc, jit_state.pc,
            );
        }

        // println!("Final instr = 0x{:08x}", text[(reference_state.pc as usize/4) - 1]);

        assert_eq!(
            reference_state.counters.add_sub_family as u32,
            jit_state.counters[CounterType::AddSubLui as u8 as usize]
        );
        assert_eq!(
            reference_state.counters.slt_branch_family as u32,
            jit_state.counters[CounterType::BranchSlt as u8 as usize]
        );
        assert_eq!(
            reference_state.counters.binary_shift_csr_family as u32,
            jit_state.counters[CounterType::ShiftBinaryCsr as u8 as usize]
        );
        assert_eq!(
            reference_state.counters.mul_div_family as u32,
            jit_state.counters[CounterType::MulDiv as u8 as usize]
        );
        assert_eq!(
            reference_state.counters.word_size_mem_family as u32,
            jit_state.counters[CounterType::MemWord as u8 as usize]
        );
        assert_eq!(
            reference_state.counters.subword_size_mem_family as u32,
            jit_state.counters[CounterType::MemSubword as u8 as usize]
        );
        assert_eq!(
            reference_state.counters.blake_calls as u32,
            jit_state.counters[CounterType::BlakeDelegation as u8 as usize]
        );
        assert_eq!(
            reference_state.counters.bigint_calls as u32,
            jit_state.counters[CounterType::BigintDelegation as u8 as usize]
        );
        assert_eq!(
            reference_state.counters.keccak_calls as u32,
            jit_state.counters[CounterType::KeccakDelegation as u8 as usize]
        );

        let mut equal_state = true;
        for (reg_idx, ((reference, jit_value), jit_ts)) in reference_state
            .registers
            .iter()
            .zip(jit_state.registers.iter())
            .zip(jit_state.register_timestamps.iter())
            .enumerate()
        {
            if reference.value != *jit_value {
                println!(
                    "VALUE diverged for x{} after {} steps:\nreference\n{}\njitted\n{}",
                    reg_idx, num_steps, reference.value, jit_value
                );
                equal_state = false;
            }
            if reference.timestamp != *jit_ts {
                println!(
                    "TIMESTAMP diverged for x{} after {} steps:\nreference\n{}\njitted\n{}",
                    reg_idx, num_steps, reference.timestamp, jit_ts
                );
                equal_state = false;
            }
        }

        assert_eq!(reference_ram.backing.len(), jit_memory.memory.len());
        for (word_idx, ((reference_value, jit_value), jit_ts)) in reference_ram
            .backing
            .iter()
            .zip(jit_memory.memory.iter())
            .zip(jit_memory.timestamps.iter())
            .enumerate()
        {
            assert_eq!(
                reference_value.value, *jit_value,
                "VALUE diverged for word {} after {} steps",
                word_idx, num_steps
            );
            assert_eq!(
                reference_value.timestamp, *jit_ts,
                "TIMESTAMP diverged for word {} after {} steps",
                word_idx, num_steps
            );
        }

        // compare the end of snapshotter
        let (jit_snapshot_values, jit_snapshot_tses) = jit_last_trace_chunk.data();
        println!("Snapshot tail length is {}", jit_snapshot_values.len());
        if jit_snapshot_values.len() > 0 {
            let length = jit_snapshot_values.len();
            let last_reference = &reference_snapshotter.reads_buffer
                [(reference_snapshotter.reads_buffer.len() - length)..];

            assert_eq!(last_reference.len(), length);
            let mut num_diffs = 0;
            for (
                idx,
                (((reference_value, (reference_ts_low, reference_ts_high)), jit_value), jit_ts),
            ) in last_reference
                .iter()
                .zip(jit_snapshot_values.iter())
                .zip(jit_snapshot_tses.iter())
                .enumerate()
            {
                if *reference_value != *jit_value {
                    println!(
                        "VALUE diverged at snapshot index {}: expected {}, got {}",
                        idx, reference_value, jit_value
                    );
                    equal_state = false;
                    num_diffs += 1;
                    if num_diffs >= 32 {
                        panic!();
                    }
                }
                let reference_ts = ((*reference_ts_high as u64) << 32) | (*reference_ts_low as u64);
                if reference_ts != *jit_ts {
                    println!(
                        "TIMESTAMP diverged at snapshot index {}: expected {}, got {}",
                        idx, reference_ts, jit_ts
                    );
                    equal_state = false;
                    num_diffs += 1;
                    if num_diffs >= 32 {
                        panic!();
                    }
                }
            }
        }

        if equal_state == false {
            panic!("State diverged");
        }

        println!("Passed for {} cycles", num_steps);

        num_steps += step;
    }
}

#[test]
fn run_recursion_and_compare() {
    let (_, binary) = read_binary(&Path::new(
        "examples/recursive_verifier/recursion_in_unrolled_layer.bin",
    ));
    let (_, text) = read_binary(&Path::new(
        "examples/recursive_verifier/recursion_in_unrolled_layer.text",
    ));

    let mut responses = std::fs::File::open("examples/recursive_verifier/responses.bin").unwrap();
    let mut buff = vec![];
    responses.read_to_end(&mut buff).unwrap();
    let resposnes: Vec<u32> = buff
        .as_chunks::<4>()
        .0
        .iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();
    let mut source = QuasiUARTSource::new_with_reads(resposnes);

    let step = 1 << 16;
    let initial_step = 836694;
    let upper_bound = (1 << 30) - 8;

    let mut previous_cycles_taken = 0;

    let mut num_steps = initial_step;
    while num_steps < upper_bound {
        // let (jit_state, jit_memory) = JittedCode::run_alternative_simulator(
        //     &text,
        //     &mut source.clone(),
        //     &binary,
        //     Some(num_steps),
        // );

        let (jit_state, jit_memory, jit_last_trace_chunk) =
            JittedCode::run_alternative_simulator_with_last_snapshot(
                &text,
                &mut source.clone(),
                &binary,
                Some(num_steps),
            );

        let cycles_taken = (jit_state.timestamp - INITIAL_TIMESTAMP) / TIMESTAMP_STEP;
        if cycles_taken == previous_cycles_taken {
            break;
        }
        previous_cycles_taken = cycles_taken;

        // let (reference_state, reference_ram) =
        //     run_reference_for_num_cycles(&binary, &text, source.clone(), jit_state.timestamp);

        let (reference_state, reference_ram, reference_snapshotter) =
            run_reference_for_num_cycles_with_snapshots(
                &binary,
                &text,
                source.clone(),
                jit_state.timestamp,
                true,
            );

        assert_eq!(
            reference_state.timestamp, jit_state.timestamp,
            "TIMESTAMP diverged after {} steps",
            num_steps
        );
        if reference_state.pc != jit_state.pc {
            panic!(
                "PC diverged after {} steps: expected 0x{:08x}, got 0x{:08x}",
                num_steps, reference_state.pc, jit_state.pc,
            );
        }

        // println!("Final instr = 0x{:08x}", text[(reference_state.pc as usize/4) - 1]);

        assert_eq!(
            reference_state.counters.add_sub_family as u32,
            jit_state.counters[CounterType::AddSubLui as u8 as usize]
        );
        assert_eq!(
            reference_state.counters.slt_branch_family as u32,
            jit_state.counters[CounterType::BranchSlt as u8 as usize]
        );
        assert_eq!(
            reference_state.counters.binary_shift_csr_family as u32,
            jit_state.counters[CounterType::ShiftBinaryCsr as u8 as usize]
        );
        assert_eq!(
            reference_state.counters.mul_div_family as u32,
            jit_state.counters[CounterType::MulDiv as u8 as usize]
        );
        assert_eq!(
            reference_state.counters.word_size_mem_family as u32,
            jit_state.counters[CounterType::MemWord as u8 as usize]
        );
        assert_eq!(
            reference_state.counters.subword_size_mem_family as u32,
            jit_state.counters[CounterType::MemSubword as u8 as usize]
        );
        assert_eq!(
            reference_state.counters.blake_calls as u32,
            jit_state.counters[CounterType::BlakeDelegation as u8 as usize]
        );
        assert_eq!(
            reference_state.counters.bigint_calls as u32,
            jit_state.counters[CounterType::BigintDelegation as u8 as usize]
        );
        assert_eq!(
            reference_state.counters.keccak_calls as u32,
            jit_state.counters[CounterType::KeccakDelegation as u8 as usize]
        );

        let mut equal_state = true;
        for (reg_idx, ((reference, jit_value), jit_ts)) in reference_state
            .registers
            .iter()
            .zip(jit_state.registers.iter())
            .zip(jit_state.register_timestamps.iter())
            .enumerate()
        {
            if reference.value != *jit_value {
                println!(
                    "VALUE diverged for x{} after {} steps:\nreference\n{}\njitted\n{}",
                    reg_idx, num_steps, reference.value, jit_value
                );
                equal_state = false;
            }
            if reference.timestamp != *jit_ts {
                println!(
                    "TIMESTAMP diverged for x{} after {} steps:\nreference\n{}\njitted\n{}",
                    reg_idx, num_steps, reference.timestamp, jit_ts
                );
                equal_state = false;
            }
        }

        assert_eq!(reference_ram.backing.len(), jit_memory.memory.len());
        for (word_idx, ((reference_value, jit_value), jit_ts)) in reference_ram
            .backing
            .iter()
            .zip(jit_memory.memory.iter())
            .zip(jit_memory.timestamps.iter())
            .enumerate()
        {
            assert_eq!(
                reference_value.value, *jit_value,
                "VALUE diverged for word {} after {} steps",
                word_idx, num_steps
            );
            assert_eq!(
                reference_value.timestamp, *jit_ts,
                "TIMESTAMP diverged for word {} after {} steps",
                word_idx, num_steps
            );
        }

        // compare the end of snapshotter
        let (jit_snapshot_values, jit_snapshot_tses) = jit_last_trace_chunk.data();
        println!("Snapshot tail length is {}", jit_snapshot_values.len());
        if jit_snapshot_values.len() > 0 {
            let length = jit_snapshot_values.len();
            let last_reference = &reference_snapshotter.reads_buffer
                [(reference_snapshotter.reads_buffer.len() - length)..];

            assert_eq!(last_reference.len(), length);
            let mut num_diffs = 0;
            for (
                idx,
                (((reference_value, (reference_ts_low, reference_ts_high)), jit_value), jit_ts),
            ) in last_reference
                .iter()
                .zip(jit_snapshot_values.iter())
                .zip(jit_snapshot_tses.iter())
                .enumerate()
            {
                if *reference_value != *jit_value {
                    println!(
                        "VALUE diverged at snapshot index {}: expected {}, got {}",
                        idx, reference_value, jit_value
                    );
                    equal_state = false;
                    num_diffs += 1;
                    if num_diffs >= 32 {
                        panic!();
                    }
                }
                let reference_ts = ((*reference_ts_high as u64) << 32) | (*reference_ts_low as u64);
                if reference_ts != *jit_ts {
                    println!(
                        "TIMESTAMP diverged at snapshot index {}: expected {}, got {}",
                        idx, reference_ts, jit_ts
                    );
                    equal_state = false;
                    num_diffs += 1;
                    if num_diffs >= 32 {
                        panic!();
                    }
                }
            }
        }

        if equal_state == false {
            dbg!(&jit_state.pc);
            println!(
                "Last opcode = 0x{:08x}",
                text[((jit_state.pc as usize) - 4) / 4]
            );
            dbg!(&jit_state.registers);
            panic!("State diverged");
        }

        println!("Passed for {} cycles", num_steps);

        num_steps += step;
    }
}

#[test]
fn test_perf_with_trace_keeping() {
    let path = std::env::current_dir().unwrap();
    println!("The current directory is {}", path.display());

    let (_, binary) = read_binary(&Path::new("examples/zksync_os/app.bin"));
    let (_, text) = read_binary(&Path::new("examples/zksync_os/app.text"));

    let (witness, _) = read_binary(&Path::new("examples/zksync_os/23620012_witness"));
    let witness = hex::decode(core::str::from_utf8(&witness).unwrap()).unwrap();
    let witness: Vec<_> = witness
        .as_chunks::<4>()
        .0
        .iter()
        .map(|el| u32::from_be_bytes(*el))
        .collect();
    let mut source = QuasiUARTSource::new_with_reads(witness);

    let simulator = JittedCode::<_>::preprocess_bytecode(&text, None);

    let mut implementation = PreallocatedSnapshots::<1024, _>::new_in(Global, &mut source);
    let initial_chunk = implementation.initial_snapshot();
    let mut context = Context { implementation };
    let mut memory: Box<MemoryHolder> = unsafe {
        let mut memory: Box<MemoryHolder> = Box::new_zeroed().assume_init();

        memory
    };

    println!("Running");
    simulator.run(&mut context, &mut memory, initial_chunk, &binary);

    // println!("PC = 0x{:08x}", state.pc);
    // dbg!(state.registers);
}

#[test]
fn test_replayer_over_jit() {
    use crate::ir::*;
    let path = std::env::current_dir().unwrap();
    println!("The current directory is {}", path.display());

    let (_, binary) = read_binary(&Path::new("examples/zksync_os/app.bin"));
    let (_, text) = read_binary(&Path::new("examples/zksync_os/app.text"));

    let (witness, _) = read_binary(&Path::new("examples/zksync_os/23620012_witness"));
    let witness = hex::decode(core::str::from_utf8(&witness).unwrap()).unwrap();
    let witness: Vec<_> = witness
        .as_chunks::<4>()
        .0
        .iter()
        .map(|el| u32::from_be_bytes(*el))
        .collect();
    let mut source = QuasiUARTSource::new_with_reads(witness);

    let simulator = JittedCode::<_>::preprocess_bytecode(&text, None);

    let mut implementation = PreallocatedSnapshots::<1024, _>::new_in(Global, &mut source);
    let initial_chunk = implementation.initial_snapshot();
    let mut context = Context { implementation };
    let mut memory: Box<MemoryHolder> = unsafe {
        let mut memory: Box<MemoryHolder> = Box::new_zeroed().assume_init();

        memory
    };

    let instructions: Vec<Instruction> =
        preprocess_bytecode::<FullUnsignedMachineDecoderConfig>(&text);
    let tape = SimpleTape::new(&instructions);

    println!("Running");
    simulator.run(&mut context, &mut memory, initial_chunk, &binary);

    let implementation = context.implementation;
    let mut jit_state = MachineState::initial();

    println!("Total of {} snapshots", implementation.snapshots().len());
    for (snapshot_idx, snapshot) in implementation.snapshots().iter().enumerate() {
        let ChunkPostSnapshot {
            state_with_counters,
            trace_chunk,
        } = snapshot;

        let (values, timestamps) = trace_chunk.data();

        let mut replaying_ram = ReplayerMemChunks {
            chunks: &mut [(values, timestamps)],
        };
        let mut state = jit_state.as_replayer_state();
        let final_timestamp = state_with_counters.timestamp;

        let _ = ReplayerVM::replay_by_timestamp_bound(
            &mut state,
            &mut replaying_ram,
            &tape,
            &mut (),
            final_timestamp,
            &mut (),
        );
        let mut state_with_counters = *state_with_counters;
        state_with_counters.timestamp = state_with_counters
            .timestamp
            .next_multiple_of(TIMESTAMP_STEP);

        let mut final_state = state_with_counters.as_replayer_state();
        state.counters = Default::default();
        final_state.counters = Default::default();
        assert_eq!(state, final_state, "diverged at snapshot {}", snapshot_idx);
        jit_state = state_with_counters;

        println!("Snapshot {} passed", snapshot_idx);
    }

    // println!("PC = 0x{:08x}", state.pc);
    // dbg!(state.registers);
}
