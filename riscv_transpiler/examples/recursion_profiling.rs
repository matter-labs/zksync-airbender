//! Profiling harness for the recursion-verifier simulation workloads in
//! `examples/test_inputs/recursion_profiling/recursion-witnesses`.
//!
//! Usage:
//!   recursion_profiling hist <program-base> <nd-file>
//!       dynamic opcode histogram from the reference interpreter (any host)
//!   recursion_profiling digest <program-base> <nd-file> [flat|default]
//!       run the x86-64 JIT and print a digest of the captured witness (all trace chunks,
//!       machine state at every snapshot, final memory and memory timestamps)
//!   recursion_profiling jit <program-base> <nd-file> [default|flat] [repeats]
//!       run the x86-64 JIT (reduced machine), print the frequency. MOP field comes from
//!       `RISCV_MOP_FIELD` (`babybear` if unset, or `babybear_assume_canonical`)
//!
//! `<program-base>` is the path without the `.bin` / `.text` extension.

#![feature(allocator_api)]

use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use riscv_transpiler::ir::simple_instruction_set::{
    preprocess_bytecode, Instruction, InstructionName,
};
use riscv_transpiler::ir::ReducedMachineDecoderConfig;

fn read_words(path: &str) -> Vec<u32> {
    let bytes = std::fs::read(path).unwrap_or_else(|e| panic!("can not read {}: {}", path, e));
    assert_eq!(bytes.len() % 4, 0);
    bytes
        .as_chunks::<4>()
        .0
        .iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect()
}

fn location(reg: u8) -> &'static str {
    match reg {
        0 => "zero",
        10 | 11 | 12 | 13 | 14 | 15 | 16 | 28 => "gpr",
        _ => "xmm",
    }
}

fn histogram(text: &[u32], binary: &[u32], responses: Vec<u32>) {
    use riscv_transpiler::vm::*;

    let instructions: Vec<Instruction> =
        preprocess_bytecode::<ReducedMachineDecoderConfig, false>(text);
    let tape = SimpleTape::new(&instructions);
    let mut ram =
        RamWithRomRegion::<{ common_constants::rom::ROM_SECOND_WORD_BITS }>::from_rom_content(
            binary,
            1 << 30,
        );
    let mut source = QuasiUARTSource::new_with_reads(responses);
    let mut state = State::initial_with_counters(DelegationsAndFamiliesCounters::default());

    let mut per_pc = vec![0u64; instructions.len()];
    let mut cycles = 0u64;
    let mut mop_operands = 0u64;
    let mut non_canonical = 0u64;
    loop {
        let pc = state.pc;
        per_pc[(pc >> 2) as usize] += 1;
        {
            // are MOP operands already canonical (BabyBear raw repr < p) in practice?
            use InstructionName as Op;
            const P: u32 = 0x7800_0001;
            let instr = instructions[(pc >> 2) as usize];
            if matches!(
                instr.name,
                Op::ZimopAdd | Op::ZimopSub | Op::ZimopMul | Op::ZimopFMA
            ) {
                mop_operands += 2;
                non_canonical += (state.registers[instr.rs1 as usize].value >= P) as u64;
                non_canonical += (state.registers[instr.rs2 as usize].value >= P) as u64;
                if instr.name == Op::ZimopFMA {
                    mop_operands += 1;
                    non_canonical += (state.registers[instr.rd as usize].value >= P) as u64;
                }
            }
        }
        VM::<DelegationsAndFamiliesCounters>::run_step::<
            _,
            _,
            _,
            field::baby_bear::base::BabyBearField,
        >(&mut state, &mut ram, &mut (), &tape, &mut source);
        state.timestamp += common_constants::TIMESTAMP_STEP;
        cycles += 1;
        if state.pc == pc {
            break;
        }
    }

    println!("Total cycles: {}", cycles);
    println!(
        "MOP operands: {}, of them non-canonical: {}",
        mop_operands, non_canonical
    );
    println!("Final counters: {:?}", state.counters);

    use std::collections::BTreeMap;
    let mut by_name: BTreeMap<String, u64> = BTreeMap::new();
    // operand placement of the instruction, as seen by the JIT: rs1/rs2/rd in host GPR or vector lane
    let mut by_placement: BTreeMap<String, u64> = BTreeMap::new();
    let mut xmm_reads = 0u64;
    let mut xmm_writes = 0u64;
    let mut reg_reads = [0u64; 32];
    let mut reg_writes = [0u64; 32];
    for (instr, count) in instructions.iter().zip(per_pc.iter().copied()) {
        if count == 0 {
            continue;
        }
        use InstructionName as Op;
        let mut name = format!("{:?}", instr.name);
        if instr.rs2 == 0 && matches!(instr.name, Op::Add | Op::ZimopAdd) {
            name.push_str("(imm/x0)");
        }
        *by_name.entry(name).or_default() += count;

        let reads: &[u8] = match instr.name {
            Op::ZimopFMA | Op::ZimopTriAdd => &[instr.rs1, instr.rs2, instr.rd],
            Op::Lw | Op::Lh | Op::Lhu | Op::Lb | Op::Lbu | Op::Jalr => &[instr.rs1],
            Op::Jal | Op::Auipc | Op::Nop | Op::ZicsrDelegation | Op::ZicsrNonDeterminismRead => {
                &[]
            }
            _ => &[instr.rs1, instr.rs2],
        };
        let writes = !matches!(
            instr.name,
            Op::Sw | Op::Sh | Op::Sb | Op::Branch | Op::Nop | Op::ZicsrDelegation
        ) && instr.rd != 0;
        for r in reads.iter().copied() {
            reg_reads[r as usize] += count;
            if location(r) == "xmm" {
                xmm_reads += count;
            }
        }
        if writes {
            reg_writes[instr.rd as usize] += count;
            if location(instr.rd) == "xmm" {
                xmm_writes += count;
            }
        }
        if matches!(
            instr.name,
            Op::ZimopAdd | Op::ZimopSub | Op::ZimopMul | Op::ZimopFMA
        ) {
            let key = format!(
                "{:?} rs1={} rs2={} rd={}",
                instr.name,
                location(instr.rs1),
                location(instr.rs2),
                location(instr.rd)
            );
            *by_placement.entry(key).or_default() += count;
        }
    }

    let mut by_name: Vec<_> = by_name.into_iter().collect();
    by_name.sort_by_key(|el| std::cmp::Reverse(el.1));
    println!("--- dynamic opcode histogram ---");
    for (name, count) in by_name {
        println!(
            "{:>32} {:>12} {:6.2}%",
            name,
            count,
            count as f64 * 100.0 / cycles as f64
        );
    }
    let mut by_placement: Vec<_> = by_placement.into_iter().collect();
    by_placement.sort_by_key(|el| std::cmp::Reverse(el.1));
    println!("--- MOP operand placement ---");
    for (name, count) in by_placement {
        println!(
            "{:>44} {:>12} {:6.2}%",
            name,
            count,
            count as f64 * 100.0 / cycles as f64
        );
    }
    println!(
        "vector-lane register reads (pextrd): {} ({:.3} per cycle), writes (pinsrd): {} ({:.3} per cycle)",
        xmm_reads,
        xmm_reads as f64 / cycles as f64,
        xmm_writes,
        xmm_writes as f64 / cycles as f64
    );
    println!("--- per-register reads / writes (share of cycles) ---");
    let mut regs: Vec<usize> = (0..32).collect();
    regs.sort_by_key(|r| std::cmp::Reverse(reg_reads[*r] + reg_writes[*r]));
    for r in regs {
        println!(
            "x{:<2} {:>4} reads {:6.2}% writes {:6.2}%",
            r,
            location(r as u8),
            reg_reads[r] as f64 * 100.0 / cycles as f64,
            reg_writes[r] as f64 * 100.0 / cycles as f64
        );
    }
}

#[cfg(target_arch = "x86_64")]
fn jit(text: &[u32], binary: &[u32], responses: Vec<u32>, flattened: bool, repeats: usize) {
    use riscv_transpiler::jit::*;
    use std::ptr::NonNull;

    let ram_config = JitRunnerRam::Medium;
    let field = if std::env::var_os("RISCV_MOP_FIELD").is_some() {
        mop_field()
    } else {
        MopField::BabyBear
    };
    println!("MOP field: {:?}", field);
    let instructions: Vec<Instruction> =
        preprocess_bytecode::<ReducedMachineDecoderConfig, false>(text);

    // The code is compiled ONCE and re-run: under Rosetta the first run pays for the
    // translation of the JITted code, so only the repeated runs are representative.
    let flat_runner = JittedCode::<FlattenedContextImpl<'_>>::preprocess_bytecode(
        &instructions,
        None,
        field,
        ram_config,
    );
    let default_runner = JittedCode::<DefaultContextImpl<'_, QuasiUARTSource>>::preprocess_bytecode(
        &instructions,
        None,
        field,
        ram_config,
    );
    let mut memory: Box<MemoryHolder> =
        MemoryHolder::allocate_zeroed(ram_config, Default::default());
    let mut trace: Box<TraceChunk> = unsafe { Box::new_zeroed().assume_init() };
    for _ in 0..repeats {
        memory.memory_mut().fill(0);
        memory.memory_and_timestamps_mut().1.fill(0);
        trace.len = 0;
        let trace_ptr = unsafe { NonNull::new_unchecked(trace.as_mut() as *mut _) };
        let state = if flattened {
            let mut context = Context::new(FlattenedContextImpl::new(&responses), ram_config);
            flat_runner.run(&mut context, memory.as_mut(), trace_ptr, binary);
            context.take_final_state().expect("must finish execution")
        } else {
            let mut source = QuasiUARTSource::new_with_reads(responses.clone());
            let mut context = Context::new(DefaultContextImpl::new(&mut source), ram_config);
            default_runner.run(&mut context, memory.as_mut(), trace_ptr, binary);
            context.take_final_state().expect("must finish execution")
        };
        println!("Final counters: {:?}", state.as_replayer_state().counters);
    }
}

/// Context that digests everything the JIT hands out: every trace chunk (values and
/// timestamps) and the machine state (registers, register timestamps, PC, timestamp, counters)
/// at every snapshot. Two runs with equal digests captured the same witness.
#[cfg(target_arch = "x86_64")]
mod digest {
    use riscv_transpiler::jit::*;
    use std::ptr::NonNull;

    pub struct DigestingContext<'a, const FLATTENED: bool> {
        pub responses: &'a [u32],
        pub position: usize,
        pub digest: u64,
        pub num_chunks: usize,
        pub trace_len: usize,
        pub final_state: Option<MachineState>,
    }

    #[inline(always)]
    pub fn absorb(digest: &mut u64, value: u64) {
        *digest = (*digest ^ value)
            .wrapping_mul(0x9e37_79b9_7f4a_7c15)
            .rotate_left(29);
    }

    impl<'a, const FLATTENED: bool> DigestingContext<'a, FLATTENED> {
        fn absorb_snapshot(&mut self, trace_chunk: &TraceChunk, machine_state: &MachineState) {
            let len = trace_chunk.len as usize;
            self.num_chunks += 1;
            self.trace_len += len;
            absorb(&mut self.digest, len as u64);
            for i in 0..len {
                absorb(&mut self.digest, trace_chunk.values[i] as u64);
                absorb(&mut self.digest, trace_chunk.timestamps[i]);
            }
            let state = machine_state.as_replayer_state();
            for register in state.registers.iter() {
                absorb(&mut self.digest, register.value as u64);
                absorb(&mut self.digest, register.timestamp);
            }
            absorb(&mut self.digest, state.pc as u64);
            absorb(&mut self.digest, machine_state.timestamp);
            for counter in machine_state.counters.values.iter() {
                absorb(&mut self.digest, *counter);
            }
        }
    }

    impl<'a, const FLATTENED: bool> ContextImpl for DigestingContext<'a, FLATTENED> {
        const PROVIDES_FLATTENED_NON_DETERMINISM: bool = FLATTENED;

        fn nondeterminism_as_raw_ptr(&self) -> Option<*const u32> {
            FLATTENED.then(|| self.responses.as_ptr())
        }

        fn read_nondeterminism(&mut self) -> u32 {
            assert!(!FLATTENED, "responses are flattened");
            let value = self.responses[self.position];
            self.position += 1;

            value
        }

        fn write_nondeterminism(&mut self, _value: u32, _memory: &[u32]) {}

        fn receive_trace(
            &mut self,
            mut trace_chunk: NonNull<TraceChunk>,
            machine_state: &MachineState,
        ) -> NonNull<TraceChunk> {
            let chunk = unsafe { trace_chunk.as_mut() };
            self.absorb_snapshot(chunk, machine_state);
            chunk.len = 0;

            trace_chunk
        }

        fn receive_final_trace_piece(
            &mut self,
            trace_chunk: NonNull<TraceChunk>,
            machine_state: &MachineState,
        ) {
            self.absorb_snapshot(unsafe { trace_chunk.as_ref() }, machine_state);
            self.final_state = Some(*machine_state);
        }

        fn take_final_state(&mut self) -> Option<MachineState> {
            self.final_state.take()
        }

        fn final_state_ref(&'_ self) -> Option<&'_ MachineState> {
            self.final_state.as_ref()
        }
    }
}

#[cfg(target_arch = "x86_64")]
fn witness_digest<const FLATTENED: bool>(text: &[u32], binary: &[u32], responses: Vec<u32>) {
    use riscv_transpiler::jit::*;
    use std::ptr::NonNull;

    let ram_config = JitRunnerRam::Medium;
    let field = if std::env::var_os("RISCV_MOP_FIELD").is_some() {
        mop_field()
    } else {
        MopField::BabyBear
    };
    let instructions: Vec<Instruction> =
        preprocess_bytecode::<ReducedMachineDecoderConfig, false>(text);
    let runner = JittedCode::<digest::DigestingContext<'_, FLATTENED>>::preprocess_bytecode(
        &instructions,
        None,
        field,
        ram_config,
    );
    let mut memory: Box<MemoryHolder> =
        MemoryHolder::allocate_zeroed(ram_config, Default::default());
    let mut trace: Box<TraceChunk> = unsafe { Box::new_zeroed().assume_init() };
    let trace_ptr = unsafe { NonNull::new_unchecked(trace.as_mut() as *mut _) };
    let mut context = Context::new(
        digest::DigestingContext {
            responses: &responses,
            position: 0,
            digest: 0,
            num_chunks: 0,
            trace_len: 0,
            final_state: None,
        },
        ram_config,
    );
    runner.run(&mut context, memory.as_mut(), trace_ptr, binary);
    let context = context.into_implementation();
    let state = context.final_state.expect("must finish execution");

    let mut memory_digest = 0u64;
    let (values, timestamps) = memory.memory_and_timestamps_mut();
    for value in values.iter() {
        digest::absorb(&mut memory_digest, *value as u64);
    }
    for timestamp in timestamps.iter() {
        digest::absorb(&mut memory_digest, *timestamp);
    }

    println!(
        "field {:?}, flattened responses {}: {} snapshots, {} trace elements, final pc 0x{:08x}, final timestamp {}",
        field, FLATTENED, context.num_chunks, context.trace_len, state.pc, state.timestamp
    );
    println!(
        "WITNESS DIGEST trace+snapshots 0x{:016x} memory+timestamps 0x{:016x}",
        context.digest, memory_digest
    );
}

#[cfg(not(target_arch = "x86_64"))]
fn witness_digest<const FLATTENED: bool>(_text: &[u32], _binary: &[u32], _responses: Vec<u32>) {
    panic!("JIT is only available on x86-64");
}

#[cfg(not(target_arch = "x86_64"))]
fn jit(_text: &[u32], _binary: &[u32], _responses: Vec<u32>, _flattened: bool, _repeats: usize) {
    panic!("JIT is only available on x86-64 (use --target x86_64-apple-darwin under Rosetta)");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    assert!(
        args.len() >= 4,
        "usage: {} <hist|jit> <program-base> <nd-file> [default|flat] [repeats]",
        args[0]
    );
    let binary = read_words(&format!("{}.bin", args[2]));
    let text = read_words(&format!("{}.text", args[2]));
    let responses = read_words(&args[3]);

    match args[1].as_str() {
        "hist" => histogram(&text, &binary, responses),
        "digest" => match args.get(4).map(|s| s.as_str()) {
            None | Some("flat") => witness_digest::<true>(&text, &binary, responses),
            Some("default") => witness_digest::<false>(&text, &binary, responses),
            Some(other) => panic!("unknown context kind {}", other),
        },
        "jit" => {
            let flattened = match args.get(4).map(|s| s.as_str()) {
                None | Some("default") => false,
                Some("flat") => true,
                Some(other) => panic!("unknown context kind {}", other),
            };
            let repeats = args.get(5).map(|s| s.parse().unwrap()).unwrap_or(1);
            jit(&text, &binary, responses, flattened, repeats)
        }
        other => panic!("unknown mode {}", other),
    }
}
