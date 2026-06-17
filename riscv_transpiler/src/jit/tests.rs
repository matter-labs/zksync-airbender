use crate::abstractions::non_determinism::QuasiUARTSource;

use super::*;
use crate::ir::{
    simple_instruction_set::{preprocess_bytecode, Instruction, InstructionName},
    FullUnsignedMachineDecoderConfig, ReducedMachineDecoderConfig,
};
use crate::{
    jit::minimal_tracer::{ChunkPostSnapshot, PreallocatedSnapshots},
    replayer::ReplayerVM,
    vm::test::*,
};
use field::Mersenne31Field;
use std::{alloc::Global, io::Read, path::Path};

#[cfg(test)]
use test_utils::skip_if_ci;

fn assemble_single_instruction(instruction: &str) -> u32 {
    let mut labels = std::collections::HashMap::new();
    lib_rv32_asm::assemble_ir(instruction, &mut labels, 0)
        .expect("single-instruction assembly should succeed")
        .expect("single-instruction assembly should emit one opcode")
}

fn run_jit_program(program: &[u32]) {
    JittedCode::<_>::run_alternative_simulator(program, &mut (), &[], None);
}

/// Assert that an unsupported instruction aborts the process (with `expected`
/// somewhere in its output) by re-running the current test in a subprocess.
///
/// We can not use `#[should_panic]` or `catch_unwind` here because the JIT-runtime
/// panic is raised from an `extern "sysv64"` callback reached from JIT-generated
/// code. Rust treats that path as non-unwinding, so the process aborts instead of
/// producing a catchable unwind. Some instructions are instead rejected earlier,
/// while decoding the bytecode into the intermediate `Instruction` representation;
/// those abort with a decode-time panic message rather than the JIT-runtime one.
fn assert_jit_aborts(test_name: &str, fixture_env_var: &str, instruction: &str, expected: &str) {
    let output = std::process::Command::new(
        std::env::current_exe().expect("test binary path should be available"),
    )
    .env(fixture_env_var, instruction)
    .arg("--exact")
    .arg(test_name)
    .arg("--nocapture")
    .output()
    .expect("subprocess should launch");

    assert!(
        !output.status.success(),
        "expected subprocess for `{instruction}` to abort, but it exited successfully",
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let combined_output = format!("{stdout}\n{stderr}");
    assert!(
        combined_output.contains(expected),
        "expected `{expected}` in output for `{instruction}`, got:\n{combined_output}",
    );
}

#[test]
#[serial_test::serial]
fn test_jit_unsupported_instructions_trap_at_runtime() {
    let fixture_env_var = "RISCV_TRANSPILER_UNSUPPORTED_INSTRUCTION_FIXTURE";
    // Instructions that decode into the intermediate representation (as `Illegal`
    // or an unsupported opcode) but are lowered to a JIT-runtime execution panic.
    let runtime_trapped = [
        "mulhsu x0, x1, x2",
        "div x0, x1, x2",
        "rem x0, x1, x2",
        "fence",
    ];
    // Environment calls have no JIT/VM lowering at all and are rejected while the
    // bytecode is decoded into the intermediate representation.
    let decode_rejected = ["ecall", "ebreak"];

    if let Ok(instruction) = std::env::var(fixture_env_var) {
        run_jit_program(&[assemble_single_instruction(&instruction)]);
    } else {
        let test_name = "jit::tests::test_jit_unsupported_instructions_trap_at_runtime";
        for instruction in runtime_trapped {
            assert_jit_aborts(
                test_name,
                fixture_env_var,
                instruction,
                "Runtime explicitly panicked",
            );
        }
        for instruction in decode_rejected {
            assert_jit_aborts(
                test_name,
                fixture_env_var,
                instruction,
                "Unknown system funct3",
            );
        }
    }
}

#[test]
#[serial_test::serial]
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
#[serial_test::serial]
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
    let responses: Vec<u32> = buff
        .as_chunks::<4>()
        .0
        .iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();
    let mut source = QuasiUARTSource::new_with_reads(responses);

    JittedCode::<_>::run_alternative_simulator(&text, &mut source, &binary, None);
}

#[test]
#[serial_test::serial]
fn test_ensure_proof_correctness() {
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
    let responses: Vec<u32> = buff
        .as_chunks::<4>()
        .0
        .iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();
    let mut source = QuasiUARTSource::new_with_reads(responses);

    let instructions: Vec<Instruction> =
        preprocess_bytecode::<ReducedMachineDecoderConfig, true>(&text);
    let tape = SimpleTape::new(&instructions);
    let mut ram =
        RamWithRomRegion::<{ common_constants::rom::ROM_SECOND_WORD_BITS }>::from_rom_content(
            &binary,
            1 << 30,
        );

    let cycles_bound = 1 << 31;

    let mut state = State::initial_with_counters(DelegationsAndFamiliesCounters::default());

    let _now = std::time::Instant::now();
    VM::<DelegationsAndFamiliesCounters>::run_basic_unrolled::<_, _, _, Mersenne31Field>(
        &mut state,
        &mut ram,
        &mut (),
        &tape,
        cycles_bound,
        &mut source,
    );
}

#[test]
#[serial_test::serial]
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
#[serial_test::serial]
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
    dbg!(state.materialized_registers());
}

#[test]
#[serial_test::serial]
fn test_jit_full_block_with_flattened_responder() {
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
    let (state, _) = JittedCode::run_with_flattened_context(&text, &witness[..], &binary, None);
    println!("PC = 0x{:08x}", state.pc);
    dbg!(state.materialized_registers());
}

/// Execution-weighted opportunity for op-fusion on the full block. Runs the
/// reference VM, tallies per-PC execution counts, then sums each fusion pattern's
/// first-instruction executions to report the ceiling (share of all executed
/// instructions a given fusion could touch). Run:
///   cargo test --features jit --release --lib -- jit::tests::test_fusion_opportunity --ignored --nocapture
#[test]
#[ignore = "runs full reference VM; explicit --ignored --nocapture"]
#[serial_test::serial]
fn test_fusion_opportunity() {
    let (_, binary) = read_binary(&Path::new("examples/zksync_os/app.bin"));
    let (_, text) = read_binary(&Path::new("examples/zksync_os/app.text"));
    let (witness, _) = read_binary(&Path::new("examples/zksync_os/23620012_witness"));
    let witness = hex::decode(core::str::from_utf8(&witness).unwrap()).unwrap();
    let witness: Vec<u32> = witness
        .as_chunks::<4>()
        .0
        .iter()
        .map(|el| u32::from_be_bytes(*el))
        .collect();

    let instructions: Vec<Instruction> =
        preprocess_bytecode::<FullUnsignedMachineDecoderConfig, true>(&text);
    let tape = SimpleTape::new(&instructions);
    let mut ram =
        RamWithRomRegion::<{ common_constants::rom::ROM_SECOND_WORD_BITS }>::from_rom_content(
            &binary,
            1 << 30,
        );
    let mut nd = QuasiUARTSource::new_with_reads(witness);
    let mut state = State::initial_with_counters(DelegationsAndFamiliesCounters::default());

    let mut exec = vec![0u64; instructions.len()];
    let bound = u64::MAX / 2;
    while state.timestamp < bound {
        let pc = state.pc;
        let idx = (pc / 4) as usize;
        if idx < exec.len() {
            exec[idx] += 1;
        }
        VM::<DelegationsAndFamiliesCounters>::run_step::<(), _, _, Mersenne31Field>(
            &mut state, &mut ram, &mut (), &tape, &mut nd,
        );
        state.timestamp += TIMESTAMP_STEP;
        if state.pc == pc {
            break;
        }
    }
    let total: u64 = exec.iter().sum();

    use InstructionName::*;
    let is_lui = |a: &Instruction| a.name == Add && a.rs1 == 0 && a.rs2 == 0;
    let is_addi = |a: &Instruction| a.name == Add && a.rs2 == 0;
    let is_mem = |a: &Instruction| matches!(a.name, Lw | Sw | Lb | Lbu | Lh | Lhu | Sb | Sh);

    let (mut lui_addi, mut auipc_jalr, mut auipc_mem, mut slli_add, mut seq_word_mem) =
        (0u64, 0u64, 0u64, 0u64, 0u64);
    // arithmetic-idiom fusions (added):
    let (mut widen_mul, mut comb_div, mut srli_andi, mut srli_lt, mut rotation) =
        (0u64, 0u64, 0u64, 0u64, 0u64);
    for i in 0..instructions.len().saturating_sub(1) {
        let a = &instructions[i];
        let b = &instructions[i + 1];
        let w = exec[i];
        if w == 0 {
            continue;
        }
        if is_lui(a) && is_addi(b) && b.rs1 == a.rd && a.rd != 0 {
            lui_addi += w;
        }
        if a.name == Auipc && b.name == Jalr && b.rs1 == a.rd && a.rd != 0 {
            auipc_jalr += w;
        }
        if a.name == Auipc && is_mem(b) && b.rs1 == a.rd && a.rd != 0 {
            auipc_mem += w;
        }
        if a.name == Sll && a.rs2 == 0 && b.name == Add && b.rs2 != 0 && (b.rs1 == a.rd || b.rs2 == a.rd) && a.rd != 0 {
            slli_add += w;
        }
        if a.name == b.name
            && matches!(a.name, Lw | Sw)
            && a.rs1 == b.rs1
            && b.imm == a.imm.wrapping_add(4)
        {
            seq_word_mem += w;
        }
        // widening multiply: mul + mulhu with the same inputs (one x86 `mul`).
        let same_inputs = a.rs1 == b.rs1 && a.rs2 == b.rs2 && a.rs2 != 0;
        if same_inputs
            && ((a.name == Mul && b.name == Mulhu) || (a.name == Mulhu && b.name == Mul))
        {
            widen_mul += w;
        }
        // combined division: divu + remu with the same inputs (one x86 `div`).
        if same_inputs
            && ((a.name == Divu && b.name == Remu) || (a.name == Remu && b.name == Divu))
        {
            comb_div += w;
        }
        // bit extract: SRLI then ANDI on the result.
        if a.name == Srl && a.rs2 == 0 && b.name == And && b.rs2 == 0 && b.rs1 == a.rd && a.rd != 0 {
            srli_andi += w;
        }
        // bit test: SRLI then SLT/SLTU consuming the result.
        if a.name == Srl
            && a.rs2 == 0
            && matches!(b.name, Slt | Sltu)
            && (b.rs1 == a.rd || b.rs2 == a.rd)
            && a.rd != 0
        {
            srli_lt += w;
        }
    }
    // rotation: SRLI(k) + SLLI(32-k) on the same source, combined by XOR/OR (any
    // order of the shift pair). 3-instruction window.
    for i in 0..instructions.len().saturating_sub(2) {
        let w = exec[i];
        if w == 0 {
            continue;
        }
        let a = &instructions[i];
        let b = &instructions[i + 1];
        let c = &instructions[i + 2];
        let (srl, sll) = if a.name == Srl && b.name == Sll {
            (a, b)
        } else if a.name == Sll && b.name == Srl {
            (b, a)
        } else {
            continue;
        };
        let shift_pair = srl.rs2 == 0
            && sll.rs2 == 0
            && srl.rs1 == sll.rs1
            && srl.imm >= 1
            && srl.imm <= 31
            && srl.imm + sll.imm == 32;
        let combines = matches!(c.name, Xor | Or)
            && c.rs2 != 0
            && ((c.rs1 == srl.rd && c.rs2 == sll.rd) || (c.rs1 == sll.rd && c.rs2 == srl.rd));
        if shift_pair && combines {
            rotation += w;
        }
    }

    let pct = |x: u64| (x as f64) * 100.0 / (total as f64);
    println!("=== fusion opportunity (executed instructions = {}) ===", total);
    println!("LUI+ADDI      : {:>12} pairs  ({:.2}% of executed)", lui_addi, pct(lui_addi));
    println!("AUIPC+JALR    : {:>12} pairs  ({:.2}%)", auipc_jalr, pct(auipc_jalr));
    println!("AUIPC+mem     : {:>12} pairs  ({:.2}%)", auipc_mem, pct(auipc_mem));
    println!("SLLI+ADD      : {:>12} pairs  ({:.2}%)", slli_add, pct(slli_add));
    println!("seq word LW/SW: {:>12} pairs  ({:.2}%)", seq_word_mem, pct(seq_word_mem));
    println!("widening mul  : {:>12} pairs  ({:.2}%)", widen_mul, pct(widen_mul));
    println!("combined div  : {:>12} pairs  ({:.2}%)", comb_div, pct(comb_div));
    println!("SRLI+ANDI     : {:>12} pairs  ({:.2}%)", srli_andi, pct(srli_andi));
    println!("SRLI+SLT/SLTU : {:>12} pairs  ({:.2}%)", srli_lt, pct(srli_lt));
    println!("rotation(3op) : {:>12} sites  ({:.2}%)", rotation, pct(rotation));
    let any = lui_addi + auipc_jalr + auipc_mem + slli_add + seq_word_mem;
    println!("sum (orig 5, upper bound): {} ({:.2}%)", any, pct(any));

    // Execution-weighted run-length distribution for consecutive word LW/SW
    // (same opcode, same base, stride ±4). Run length determines how well the
    // fixed per-run savings (one flush, one chunk check, one base load) amortize.
    let mut by_len: std::collections::BTreeMap<usize, u64> = std::collections::BTreeMap::new();
    let mut run_execs = 0u64;
    let mut words_in_runs = 0u64;
    let mut j = 0usize;
    while j < instructions.len() {
        let a = &instructions[j];
        if matches!(a.name, Lw | Sw) && j + 1 < instructions.len() {
            let b = &instructions[j + 1];
            let stride = b.imm.wrapping_sub(a.imm);
            if b.name == a.name && b.rs1 == a.rs1 && (stride == 4 || stride == 4u32.wrapping_neg()) {
                let mut l = 2usize;
                while j + l < instructions.len() {
                    let p = &instructions[j + l - 1];
                    let q = &instructions[j + l];
                    if q.name == a.name && q.rs1 == a.rs1 && q.imm == p.imm.wrapping_add(stride) {
                        l += 1;
                    } else {
                        break;
                    }
                }
                let w = exec[j];
                if w > 0 {
                    *by_len.entry(l).or_default() += w;
                    run_execs += w;
                    words_in_runs += w * (l as u64);
                }
                j += l;
                continue;
            }
        }
        j += 1;
    }
    println!("\n=== seq word LW/SW run-length distribution (execution-weighted) ===");
    println!("run-executions={}  words-in-runs={} ({:.2}% of executed)  avg run len={:.2}",
        run_execs, words_in_runs, pct(words_in_runs),
        if run_execs > 0 { words_in_runs as f64 / run_execs as f64 } else { 0.0 });
    for (l, w) in &by_len {
        println!("  len {:>2}: {:>12} run-execs ({:>5.2}% of run-execs, {:>5.2}% of all words)",
            l, w, (*w as f64) * 100.0 / (run_execs.max(1) as f64), pct(*w * (*l as u64)));
    }
}

/// How well do static fusion + the ABI return-site heuristic cover the *observed*
/// dynamic JALR targets? If coverage is total, the dynamic artifact (and the
/// Stage-B fallback) is never exercised on this block.
#[test]
#[ignore = "artifact build; run explicitly with --ignored --nocapture"]
#[serial_test::serial]
fn test_abi_jalr_coverage() {
    use crate::control_flow_artifact::build_control_flow_artifact;
    use std::collections::BTreeSet;

    let (_, binary) = read_binary(&Path::new("examples/zksync_os/app.bin"));
    let (_, text) = read_binary(&Path::new("examples/zksync_os/app.text"));
    let (witness, _) = read_binary(&Path::new("examples/zksync_os/23620012_witness"));
    let witness = hex::decode(core::str::from_utf8(&witness).unwrap()).unwrap();
    let witness: Vec<u32> = witness
        .as_chunks::<4>()
        .0
        .iter()
        .map(|el| u32::from_be_bytes(*el))
        .collect();

    let instructions: Vec<Instruction> =
        preprocess_bytecode::<FullUnsignedMachineDecoderConfig, true>(&text);
    let artifact = build_control_flow_artifact(
        &instructions,
        &binary,
        vec![QuasiUARTSource::new_with_reads(witness)],
        u64::MAX / 2,
    );

    // Static-only + ABI return-site coverage (NO dynamic targets).
    let mut static_entries: BTreeSet<u32> = BTreeSet::new();
    static_entries.insert(0);
    static_entries.extend(artifact.jal_targets.values().copied());
    for (site, t) in &artifact.branch_targets {
        static_entries.insert(*t);
        static_entries.insert(site.wrapping_add(4));
    }
    for ts in artifact.jalr_static_targets.values() {
        static_entries.extend(ts.iter().copied());
    }
    for (i, instr) in instructions.iter().enumerate() {
        if instr.rd == 1 && matches!(instr.name, InstructionName::Jal | InstructionName::Jalr) {
            static_entries.insert((i as u32) * 4 + 4);
        }
    }

    let mut total_targets = 0usize;
    let mut covered = 0usize;
    let mut uncovered_transfers = 0u64;
    let mut total_transfers = 0u64;
    for (_site, tc) in &artifact.jalr_dynamic_targets {
        for (t, count) in tc {
            total_targets += 1;
            total_transfers += *count;
            if static_entries.contains(t) {
                covered += 1;
            } else {
                uncovered_transfers += *count;
            }
        }
    }
    println!(
        "JALR dynamic targets: {}/{} covered by static+ABI; uncovered dynamic transfers (would fall back) = {}/{}",
        covered, total_targets, uncovered_transfers, total_transfers
    );
}

/// Full-block performance test for the LAZY (batched-timestamp) path. Builds the
/// control-flow artifact from the witness, then runs the whole block to completion
/// (prints simulator MHz via `runner.run`).
#[test]
#[serial_test::serial]
fn test_jit_full_block_with_flattened_responder_lazy() {
    use crate::control_flow_artifact::build_control_flow_artifact;

    let (_, binary) = read_binary(&Path::new("examples/zksync_os/app.bin"));
    let (_, text) = read_binary(&Path::new("examples/zksync_os/app.text"));

    let (witness, _) = read_binary(&Path::new("examples/zksync_os/23620012_witness"));
    let witness = hex::decode(core::str::from_utf8(&witness).unwrap()).unwrap();
    let witness: Vec<u32> = witness
        .as_chunks::<4>()
        .0
        .iter()
        .map(|el| u32::from_be_bytes(*el))
        .collect();

    let instructions_for_artifact: Vec<Instruction> =
        preprocess_bytecode::<FullUnsignedMachineDecoderConfig, true>(&text);
    let artifact = build_control_flow_artifact(
        &instructions_for_artifact,
        &binary,
        vec![QuasiUARTSource::new_with_reads(witness.clone())],
        u64::MAX / 2,
    );

    let (state, _) = JittedCode::run_with_flattened_context_lazy(
        &text,
        &witness[..],
        &binary,
        None,
        &artifact,
    );
    println!("PC = 0x{:08x}", state.pc);
}

/// Static + dynamic bytecode instrumentation for the full zkSync OS block.
/// Heavy (runs the reference VM over the whole block), so it is ignored by default.
/// Run with:
///   cargo test --features jit --release --lib \
///     jit::tests::test_bytecode_analysis_full_block -- --ignored --nocapture
#[test]
#[ignore = "analysis pass; run explicitly with --ignored --nocapture"]
#[serial_test::serial]
fn test_bytecode_analysis_full_block() {
    use crate::analysis::{analyze_dynamic_execution, analyze_static_bytecode};

    let (binary_raw, binary) = read_binary(&Path::new("examples/zksync_os/app.bin"));
    let _ = binary_raw;
    let (_, text) = read_binary(&Path::new("examples/zksync_os/app.text"));

    let (witness, _) = read_binary(&Path::new("examples/zksync_os/23620012_witness"));
    let witness = hex::decode(core::str::from_utf8(&witness).unwrap()).unwrap();
    let witness: Vec<u32> = witness
        .as_chunks::<4>()
        .0
        .iter()
        .map(|el| u32::from_be_bytes(*el))
        .collect();

    // Decode like the replayer (PROTECT_AGAINST_MID_DELEGATION_JUMPS = true) so the
    // dynamic pass can execute delegations as single ops.
    let instructions: Vec<Instruction> =
        preprocess_bytecode::<FullUnsignedMachineDecoderConfig, true>(&text);

    println!("{}", analyze_static_bytecode(&instructions));

    let mut source = QuasiUARTSource::new_with_reads(witness);
    let stats =
        analyze_dynamic_execution(&instructions, &binary, &mut source, u64::MAX / 2);
    println!("{}", stats);
}

/// Build the control-flow target artifact (static JAL/BRANCH/JALR-fusion targets +
/// dynamic JALR targets) for the full zkSync OS block, print its summary, and
/// round-trip it through disk. Heavy (runs the reference VM), so ignored by default.
/// Run with:
///   cargo test --features jit --release --lib \
///     jit::tests::test_build_cfg_artifact_full_block -- --ignored --nocapture
#[test]
#[ignore = "artifact build; run explicitly with --ignored --nocapture"]
#[serial_test::serial]
fn test_build_cfg_artifact_full_block() {
    use crate::control_flow_artifact::{build_control_flow_artifact, ControlFlowArtifact};

    let (_, binary) = read_binary(&Path::new("examples/zksync_os/app.bin"));
    let (_, text) = read_binary(&Path::new("examples/zksync_os/app.text"));

    let (witness, _) = read_binary(&Path::new("examples/zksync_os/23620012_witness"));
    let witness = hex::decode(core::str::from_utf8(&witness).unwrap()).unwrap();
    let witness: Vec<u32> = witness
        .as_chunks::<4>()
        .0
        .iter()
        .map(|el| u32::from_be_bytes(*el))
        .collect();

    let instructions: Vec<Instruction> =
        preprocess_bytecode::<FullUnsignedMachineDecoderConfig, true>(&text);

    // Supply one or more non-determinism instances here; more diverse instances
    // improve dynamic JALR target coverage. We only have one witness fixture.
    let nd_sources = vec![QuasiUARTSource::new_with_reads(witness)];

    let artifact =
        build_control_flow_artifact(&instructions, &binary, nd_sources, u64::MAX / 2);
    println!("{}", artifact);

    // Serialize to disk and verify the round-trip.
    let path = std::env::temp_dir().join("zksync_os_cfg_artifact.txt");
    artifact.save_to_file(&path).expect("save artifact");
    println!("artifact written to {}", path.display());
    let reloaded = ControlFlowArtifact::load_from_file(&path).expect("load artifact");
    assert_eq!(artifact, reloaded, "artifact serialization round-trip mismatch");
    println!("round-trip OK");
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
    let instructions: Vec<Instruction> =
        preprocess_bytecode::<FullUnsignedMachineDecoderConfig, true>(text);
    let tape = SimpleTape::new(&instructions);
    let mut ram =
        RamWithRomRegion::<{ common_constants::rom::ROM_SECOND_WORD_BITS }>::from_rom_content(
            &binary,
            1 << 30,
        );

    let mut state = State::initial_with_counters(DelegationsAndFamiliesCounters::default());

    VM::<DelegationsAndFamiliesCounters>::run_by_timestamp_bound::<_, _, _, Mersenne31Field>(
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
    let instructions = if reduced_isa {
        preprocess_bytecode::<ReducedMachineDecoderConfig, true>(text)
    } else {
        preprocess_bytecode::<FullUnsignedMachineDecoderConfig, true>(text)
    };
    let tape = SimpleTape::new(&instructions);
    let mut ram =
        RamWithRomRegion::<{ common_constants::rom::ROM_SECOND_WORD_BITS }>::from_rom_content(
            &binary,
            1 << 30,
        );

    let mut state = State::initial_with_counters(DelegationsAndFamiliesCounters::default());
    let mut snapshotter = SimpleSnapshotter::<_, {common_constants::rom::ROM_SECOND_WORD_BITS }>::new_with_cycle_limit(1 << 31, state);

    VM::<DelegationsAndFamiliesCounters>::run_by_timestamp_bound::<_, _, _, Mersenne31Field>(
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
#[serial_test::serial]
fn test_reference_block_exec() {
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
        preprocess_bytecode::<FullUnsignedMachineDecoderConfig, true>(&text);
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
    VM::<DelegationsAndFamiliesCounters>::run_basic_unrolled::<_, _, _, Mersenne31Field>(
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
#[serial_test::serial]
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
            reference_state.counters.add_sub_family as u64,
            jit_state.counters[CounterType::AddSubLui as u8 as usize]
        );
        assert_eq!(
            reference_state.counters.slt_branch_family as u64,
            jit_state.counters[CounterType::BranchSlt as u8 as usize]
        );
        assert_eq!(
            reference_state.counters.binary_shift_family as u64,
            jit_state.counters[CounterType::ShiftBinaryCsr as u8 as usize]
        );
        assert_eq!(
            reference_state.counters.mul_div_family as u64,
            jit_state.counters[CounterType::MulDiv as u8 as usize]
        );
        assert_eq!(
            reference_state.counters.word_size_mem_family as u64,
            jit_state.counters[CounterType::MemWord as u8 as usize]
        );
        assert_eq!(
            reference_state.counters.subword_size_mem_family as u64,
            jit_state.counters[CounterType::MemSubword as u8 as usize]
        );
        assert_eq!(
            reference_state.counters.blake_calls as u64,
            jit_state.counters[CounterType::BlakeDelegation as u8 as usize]
        );
        assert_eq!(
            reference_state.counters.bigint_calls as u64,
            jit_state.counters[CounterType::BigintDelegation as u8 as usize]
        );
        assert_eq!(
            reference_state.counters.keccak_calls as u64,
            jit_state.counters[CounterType::KeccakDelegation as u8 as usize]
        );

        let mut equal_state = true;
        let jit_regs = jit_state.materialized_registers();
        for (reg_idx, ((reference, jit_value), jit_ts)) in reference_state
            .registers
            .iter()
            .zip(jit_regs.iter())
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

/// Bit-exact comparison of the LAZY (batched-timestamp) JIT path against the
/// reference VM, at a single representative cycle bound (fast to iterate). Builds
/// the control-flow artifact from the witness, then runs the lazy constructor.
#[test]
#[serial_test::serial]
fn run_and_compare_lazy() {
    use crate::control_flow_artifact::build_control_flow_artifact;

    let (_, binary) = read_binary(&Path::new("examples/zksync_os/app.bin"));
    let (_, text) = read_binary(&Path::new("examples/zksync_os/app.text"));

    let (witness, _) = read_binary(&Path::new("examples/zksync_os/23620012_witness"));
    let witness = hex::decode(core::str::from_utf8(&witness).unwrap()).unwrap();
    let witness: Vec<u32> = witness
        .as_chunks::<4>()
        .0
        .iter()
        .map(|el| u32::from_be_bytes(*el))
        .collect();

    let instructions_for_artifact: Vec<Instruction> =
        preprocess_bytecode::<FullUnsignedMachineDecoderConfig, true>(&text);
    let artifact = build_control_flow_artifact(
        &instructions_for_artifact,
        &binary,
        vec![QuasiUARTSource::new_with_reads(witness.clone())],
        u64::MAX / 2,
    );
    println!("{}", artifact);

    let source = QuasiUARTSource::new_with_reads(witness);

    let num_steps: u32 = 762314752;

    let (jit_state, jit_memory, jit_last_trace_chunk) =
        JittedCode::run_alternative_simulator_with_last_snapshot_lazy(
            &text,
            &mut source.clone(),
            &binary,
            Some(num_steps),
            &artifact,
        );

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
        "TIMESTAMP diverged"
    );
    assert_eq!(reference_state.pc, jit_state.pc, "PC diverged");

    let counter_pairs = [
        (reference_state.counters.add_sub_family, CounterType::AddSubLui),
        (reference_state.counters.slt_branch_family, CounterType::BranchSlt),
        (reference_state.counters.binary_shift_family, CounterType::ShiftBinaryCsr),
        (reference_state.counters.mul_div_family, CounterType::MulDiv),
        (reference_state.counters.word_size_mem_family, CounterType::MemWord),
        (reference_state.counters.subword_size_mem_family, CounterType::MemSubword),
        (reference_state.counters.blake_calls, CounterType::BlakeDelegation),
        (reference_state.counters.bigint_calls, CounterType::BigintDelegation),
        (reference_state.counters.keccak_calls, CounterType::KeccakDelegation),
    ];
    for (reference, ct) in counter_pairs {
        assert_eq!(
            reference as u64,
            jit_state.counters[ct as u8 as usize],
            "counter {:?} diverged",
            ct as u8
        );
    }

    let mut equal_state = true;
    let jit_regs = jit_state.materialized_registers();
    for (reg_idx, ((reference, jit_value), jit_ts)) in reference_state
        .registers
        .iter()
        .zip(jit_regs.iter())
        .zip(jit_state.register_timestamps.iter())
        .enumerate()
    {
        if reference.value != *jit_value {
            println!(
                "VALUE diverged for x{}: reference {} jitted {}",
                reg_idx, reference.value, jit_value
            );
            equal_state = false;
        }
        if reference.timestamp != *jit_ts {
            println!(
                "TIMESTAMP diverged for x{}: reference {} jitted {}",
                reg_idx, reference.timestamp, jit_ts
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
            "MEM VALUE diverged for word {}",
            word_idx
        );
        assert_eq!(
            reference_value.timestamp, *jit_ts,
            "MEM TIMESTAMP diverged for word {}",
            word_idx
        );
    }

    let (jit_snapshot_values, jit_snapshot_tses) = jit_last_trace_chunk.data();
    println!("Snapshot tail length is {}", jit_snapshot_values.len());
    if jit_snapshot_values.len() > 0 {
        let length = jit_snapshot_values.len();
        let last_reference = &reference_snapshotter.reads_buffer
            [(reference_snapshotter.reads_buffer.len() - length)..];
        assert_eq!(last_reference.len(), length);
        let mut num_diffs = 0;
        for (idx, (((reference_value, (reference_ts_low, reference_ts_high)), jit_value), jit_ts)) in
            last_reference
                .iter()
                .zip(jit_snapshot_values.iter())
                .zip(jit_snapshot_tses.iter())
                .enumerate()
        {
            if *reference_value != *jit_value {
                println!(
                    "SNAPSHOT VALUE diverged at {}: expected {}, got {}",
                    idx, reference_value, jit_value
                );
                equal_state = false;
                num_diffs += 1;
            }
            let reference_ts = ((*reference_ts_high as u64) << 32) | (*reference_ts_low as u64);
            if reference_ts != *jit_ts {
                println!(
                    "SNAPSHOT TIMESTAMP diverged at {}: expected {}, got {}",
                    idx, reference_ts, jit_ts
                );
                equal_state = false;
                num_diffs += 1;
            }
            if num_diffs >= 32 {
                panic!();
            }
        }
    }

    if !equal_state {
        panic!("State diverged");
    }
    println!("Lazy path bit-exact for {} cycles", num_steps);
}

#[cfg(test)]
#[ignore = "long-running manual consistency test"]
#[test]
#[serial_test::serial]
fn run_recursion_and_compare() {
    skip_if_ci!();
    let (_, binary) = read_binary(&Path::new(
        "examples/recursive_verifier/recursion_in_unrolled_layer.bin",
    ));
    let (_, text) = read_binary(&Path::new(
        "examples/recursive_verifier/recursion_in_unrolled_layer.text",
    ));

    let mut responses = std::fs::File::open("examples/recursive_verifier/responses.bin").unwrap();
    let mut buff = vec![];
    responses.read_to_end(&mut buff).unwrap();
    let responses: Vec<u32> = buff
        .as_chunks::<4>()
        .0
        .iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();
    let mut source = QuasiUARTSource::new_with_reads(responses);

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
            reference_state.counters.add_sub_family as u64,
            jit_state.counters[CounterType::AddSubLui as u8 as usize]
        );
        assert_eq!(
            reference_state.counters.slt_branch_family as u64,
            jit_state.counters[CounterType::BranchSlt as u8 as usize]
        );
        assert_eq!(
            reference_state.counters.binary_shift_family as u64,
            jit_state.counters[CounterType::ShiftBinaryCsr as u8 as usize]
        );
        assert_eq!(
            reference_state.counters.mul_div_family as u64,
            jit_state.counters[CounterType::MulDiv as u8 as usize]
        );
        assert_eq!(
            reference_state.counters.word_size_mem_family as u64,
            jit_state.counters[CounterType::MemWord as u8 as usize]
        );
        assert_eq!(
            reference_state.counters.subword_size_mem_family as u64,
            jit_state.counters[CounterType::MemSubword as u8 as usize]
        );
        assert_eq!(
            reference_state.counters.blake_calls as u64,
            jit_state.counters[CounterType::BlakeDelegation as u8 as usize]
        );
        assert_eq!(
            reference_state.counters.bigint_calls as u64,
            jit_state.counters[CounterType::BigintDelegation as u8 as usize]
        );
        assert_eq!(
            reference_state.counters.keccak_calls as u64,
            jit_state.counters[CounterType::KeccakDelegation as u8 as usize]
        );

        let mut equal_state = true;
        let jit_regs = jit_state.materialized_registers();
        for (reg_idx, ((reference, jit_value), jit_ts)) in reference_state
            .registers
            .iter()
            .zip(jit_regs.iter())
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
            dbg!(&jit_state.materialized_registers());
            panic!("State diverged");
        }

        println!("Passed for {} cycles", num_steps);

        num_steps += step;
    }
}

#[cfg(test)]
#[ignore = "manual profiling smoke test"]
#[test]
#[serial_test::serial]
fn test_perf_with_trace_keeping() {
    skip_if_ci!();
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

    let instructions = preprocess_bytecode::<FullUnsignedMachineDecoderConfig, false>(&text);
    let simulator = JittedCode::<_>::preprocess_bytecode(&instructions, None);

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
    // dbg!(state.materialized_registers());
}

#[test]
#[serial_test::serial]
fn test_replayer_over_jit() {
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

    let jit_instructions = preprocess_bytecode::<FullUnsignedMachineDecoderConfig, false>(&text);
    let simulator = JittedCode::<_>::preprocess_bytecode(&jit_instructions, None);

    let mut implementation = PreallocatedSnapshots::<1024, _>::new_in(Global, &mut source);
    let initial_chunk = implementation.initial_snapshot();
    let mut context = Context { implementation };
    let mut memory: Box<MemoryHolder> = unsafe {
        let mut memory: Box<MemoryHolder> = Box::new_zeroed().assume_init();

        memory
    };

    let instructions: Vec<Instruction> =
        preprocess_bytecode::<FullUnsignedMachineDecoderConfig, true>(&text);
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

        let _ = ReplayerVM::replay_by_timestamp_bound::<_, _, Mersenne31Field>(
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
    // dbg!(state.materialized_registers());
}
