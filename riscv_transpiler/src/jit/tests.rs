use crate::abstractions::non_determinism::QuasiUARTSource;

use super::*;
use crate::ir::{
    simple_instruction_set::{preprocess_bytecode, Instruction, InstructionName},
    FullUnsignedMachineDecoderConfig, ReducedMachineDecoderConfig,
};
use crate::{jit::minimal_tracer::PreallocatedSnapshots, vm::test::*};
// Used only by `test_replayer_over_jit` (gated to the `xmm_ts` mechanism).
#[cfg(feature = "xmm_ts")]
use crate::{jit::minimal_tracer::ChunkPostSnapshot, replayer::ReplayerVM};
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

/// `ZimopIXorRot` (MOP-I xor-rotate) computes `rd = (rd_old ^ rs1).rotate_right(imm)` — the
/// exact formula of the reference `binary_shifts_family::mopi::mopi_xor_rot`. The default JIT
/// decoder config never emits this opcode, so build instruction streams directly and check the
/// JIT's result against the reference formula across the register-placement cases that exercise
/// the asm: GPR-mapped vs XMM-resident rd/rs1, rs1 == rd (xor -> 0), rs1 == x0, and rot == 0.
#[test]
#[serial_test::serial]
fn test_jit_zimop_ixor_rot() {
    use InstructionName::{Add, Jal, ZimopIXorRot};

    // (rs1, rd, v1, v2, rot). GPR-mapped regs are {10,11,12,13,14,15,16,28}; the rest are
    // XMM-resident. v1 -> rs1, v2 -> rd's OLD value.
    let cases: &[(u8, u8, u32, u32, u32)] = &[
        (10, 11, 0xDEAD_BEEF, 0x1234_5678, 7), // both GPR-mapped
        (5, 11, 0xDEAD_BEEF, 0x1234_5678, 13), // rs1 XMM-resident, rd GPR-mapped
        (11, 6, 0xDEAD_BEEF, 0x1234_5678, 1),  // rs1 GPR-mapped, rd XMM-resident
        (7, 9, 0xCAFE_BABE, 0x0F0F_0F0F, 31),  // both XMM-resident
        (12, 12, 0, 0xABCD_1234, 5),           // rs1 == rd (xor -> 0)
        (0, 13, 0, 0x8000_0001, 3),            // rs1 == x0 (xor with 0)
        (14, 17, 0xFFFF_FFFF, 0x0000_0001, 0), // rot == 0 (identity rotate)
    ];

    for &(rs1, rd, v1, v2, rot) in cases {
        let mut prog: Vec<Instruction> = Vec::new();
        if rs1 != 0 && rs1 != rd {
            prog.push(Instruction::new(Add, 0, 0, rs1, v1)); // rs1 = v1
        }
        prog.push(Instruction::new(Add, 0, 0, rd, v2)); // rd = v2 (its OLD value)
        prog.push(Instruction::new(ZimopIXorRot, rs1, 0, rd, rot));
        prog.push(Instruction::new(Jal, 0, 0, 0, 0)); // jal x0, 0 = self-loop = exit

        // rs1's value as actually seen by the opcode after setup.
        let rs1_value = if rs1 == 0 {
            0
        } else if rs1 == rd {
            v2
        } else {
            v1
        };
        let expected = (v2 ^ rs1_value).rotate_right(rot);

        let (state, _mem) =
            JittedCode::<_>::run_alternative_simulator_from_instructions(&prog, &mut (), &[], None);
        let got = state.materialized_registers()[rd as usize];
        assert_eq!(
            got, expected,
            "ZimopIXorRot mismatch: rs1=x{rs1} rd=x{rd} v1={v1:#010x} v2={v2:#010x} rot={rot} -> got {got:#010x}, expected {expected:#010x}"
        );
    }
}

/// `ZimopTriAdd` (MOP tri-add) computes `rd = rs1 + rs2 + rd_old` (wrapping) — the exact
/// formula of the reference `add_sub_family::mop::mop_tri_add`. The default JIT decoder config
/// never emits it, so build instruction streams directly and check the JIT's result against the
/// reference formula across register placements (GPR-mapped vs XMM-resident rd/rs1/rs2) and the
/// aliasing edge cases that stress accumulating in EAX: rs1==rd, rs2==rd, rs1==rs2, rs?==x0.
#[test]
#[serial_test::serial]
fn test_jit_zimop_tri_add() {
    use InstructionName::{Add, Jal, ZimopTriAdd};

    // (rs1, rs2, rd, v1, v2, v_rd). v1->rs1, v2->rs2, v_rd->rd's OLD value.
    let cases: &[(u8, u8, u8, u32, u32, u32)] = &[
        (10, 11, 12, 0x1111_1111, 0x2222_2222, 0x3333_3333), // all GPR-mapped
        (5, 6, 7, 0x1111_1111, 0x2222_2222, 0x3333_3333),    // all XMM-resident
        (5, 11, 6, 0xAAAA_0000, 0x0000_5555, 0x0F0F_0F0F),   // mixed
        (10, 11, 10, 0x1234_5678, 0x9abc_def0, 0),           // rs1 == rd
        (11, 12, 12, 0x0000_0007, 0x1234_5678, 0),           // rs2 == rd
        (9, 9, 13, 0x4000_0001, 0, 0x0000_0002),             // rs1 == rs2
        (0, 14, 15, 0, 0x8000_0000, 0x8000_0001),            // rs1 == x0
        (16, 0, 17, 0xFFFF_FFFF, 0, 0x0000_0002),            // rs2 == x0 (wraps)
    ];

    for &(rs1, rs2, rd, v1, v2, v_rd) in cases {
        // Set up rs1, rs2 and rd's old value. The LAST write to a given reg wins, so write rd
        // last to guarantee its OLD value is exactly v_rd.
        let mut prog: Vec<Instruction> = Vec::new();
        let mut set = |prog: &mut Vec<Instruction>, reg: u8, val: u32| {
            if reg != 0 {
                prog.push(Instruction::new(Add, 0, 0, reg, val));
            }
        };
        set(&mut prog, rs1, v1);
        set(&mut prog, rs2, v2);
        set(&mut prog, rd, v_rd);
        prog.push(Instruction::new(ZimopTriAdd, rs1, rs2, rd, 0));
        prog.push(Instruction::new(Jal, 0, 0, 0, 0)); // exit

        // Value actually surviving in a register after setup, honoring last-write-wins for the
        // write order rs1, rs2, rd (so rd > rs2 > rs1 when they alias); x0 always reads 0.
        let val_of = |reg: u8| -> u32 {
            if reg == 0 {
                0
            } else if reg == rd {
                v_rd
            } else if reg == rs2 {
                v2
            } else if reg == rs1 {
                v1
            } else {
                unreachable!()
            }
        };
        let expected = val_of(rs1).wrapping_add(val_of(rs2)).wrapping_add(v_rd);

        let (state, _mem) =
            JittedCode::<_>::run_alternative_simulator_from_instructions(&prog, &mut (), &[], None);
        let got = state.materialized_registers()[rd as usize];
        assert_eq!(
            got, expected,
            "ZimopTriAdd mismatch: rs1=x{rs1} rs2=x{rs2} rd=x{rd} v1={v1:#010x} v2={v2:#010x} v_rd={v_rd:#010x} -> got {got:#010x}, expected {expected:#010x}"
        );
    }
}

/// The MOP prime-field opcodes (ZimopAdd/Sub/Mul/FMA) computed by the env-selected field
/// emitter (M31 default, BabyBear via `RISCV_MOP_FIELD`) must match the reference `field` crate
/// exactly. The default decoder config never emits these as a field choice, so build instruction
/// streams directly, run the JIT under each field, and compare to `from_raw_repr_with_reduction`
/// + the field op + `as_u32_raw_repr_reduced`. Covers GPR-mapped / XMM-resident placements,
/// rs2 == x0 (the M31 add fast path), and inputs above the modulus (exercising reduction).
#[test]
#[serial_test::serial]
fn test_jit_zimop_field_ops() {
    use InstructionName::{Add, Jal, ZimopAdd, ZimopFMA, ZimopMul, ZimopSub};

    fn field_expected<F: field::PrimeField>(op: InstructionName, a: u32, b: u32, c: u32) -> u32 {
        use field::Field;
        let fa = F::from_raw_repr_with_reduction(a);
        let fb = F::from_raw_repr_with_reduction(b);
        let mut res = match op {
            ZimopAdd => {
                let mut x = fa;
                x.add_assign(&fb);
                x
            }
            ZimopSub => {
                let mut x = fa;
                x.sub_assign(&fb);
                x
            }
            ZimopMul => {
                let mut x = fa;
                x.mul_assign(&fb);
                x
            }
            ZimopFMA => {
                let mut x = F::from_raw_repr_with_reduction(c);
                x.add_assign_product(&fa, &fb);
                x
            }
            _ => unreachable!(),
        };
        res.as_u32_raw_repr_reduced()
    }

    // Distinct (rs1, rs2, rd) so no aliasing; covers all-GPR-mapped, all-XMM-resident, mixed, and
    // rs2 == x0 (the M31 add fast path). (Each case rebuilds a JIT — keep the matrix modest.)
    let placements: &[(u8, u8, u8)] = &[(10, 11, 12), (5, 6, 7), (5, 11, 6), (11, 0, 12)];
    // (v1 -> rs1, v2 -> rs2, v_rd -> rd's old value); above the moduli to force reduction, plus 0.
    let values: &[(u32, u32, u32)] = &[
        (0x7fff_fffe, 0x7fff_ffff, 0x8000_0000),
        (0x7800_0000, 0x7800_0001, 0xffff_ffff),
        (0xdead_beef, 0x1234_5678, 0xcafe_babe),
        (0, 0, 0),
    ];
    let ops = [ZimopAdd, ZimopSub, ZimopMul, ZimopFMA];

    for field_env in ["m31", "babybear"] {
        std::env::set_var("RISCV_MOP_FIELD", field_env);
        for &op in &ops {
            for &(rs1, rs2, rd) in placements {
                for &(v1, v2, v_rd) in values {
                    let mut prog: Vec<Instruction> = Vec::new();
                    let mut set = |p: &mut Vec<Instruction>, reg: u8, val: u32| {
                        if reg != 0 {
                            p.push(Instruction::new(Add, 0, 0, reg, val));
                        }
                    };
                    set(&mut prog, rs1, v1);
                    set(&mut prog, rs2, v2);
                    set(&mut prog, rd, v_rd);
                    prog.push(Instruction::new(op, rs1, rs2, rd, 0));
                    prog.push(Instruction::new(Jal, 0, 0, 0, 0)); // exit

                    // raw register values seen by the opcode (rs2 == x0 reads 0).
                    let a = v1;
                    let b = if rs2 == 0 { 0 } else { v2 };
                    let c = v_rd;
                    let expected = match field_env {
                        "m31" => field_expected::<field::Mersenne31Field>(op, a, b, c),
                        _ => field_expected::<field::baby_bear::base::BabyBearField>(op, a, b, c),
                    };

                    let (state, _mem) =
                        JittedCode::<_>::run_alternative_simulator_from_instructions(
                            &prog,
                            &mut (),
                            &[],
                            None,
                        );
                    let got = state.materialized_registers()[rd as usize];
                    assert_eq!(
                        got, expected,
                        "{field_env} {op:?}: rs1=x{rs1}({a:#010x}) rs2=x{rs2}({b:#010x}) rd=x{rd}({c:#010x}) -> got {got:#010x}, expected {expected:#010x}"
                    );
                }
            }
        }
    }
    std::env::remove_var("RISCV_MOP_FIELD"); // restore default (M31) for other tests
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

fn dump_replayer_state(s: &State<DelegationsAndFamiliesCounters>) -> String {
    let mut out = String::new();
    for (i, r) in s.registers.iter().enumerate() {
        out.push_str(&format!("x{:02} value={} ts={}\n", i, r.value, r.timestamp));
    }
    out.push_str(&format!("pc={} timestamp={}\n", s.pc, s.timestamp));
    let c = &s.counters;
    out.push_str(&format!(
        "counters add_sub={} slt_branch={} shift={} mul_div={} mem_word={} mem_subword={} blake={} bigint={} keccak={} blake_g={}\n",
        c.add_sub_family, c.slt_branch_family, c.binary_shift_family, c.mul_div_family,
        c.word_size_mem_family, c.subword_size_mem_family, c.blake_calls, c.bigint_calls,
        c.keccak_calls, c.blake_g_function_calls,
    ));
    out
}

/// Exhaustive packed_ts verification against the authoritative non-assembly reference VM.
/// Runs the JIT to completion, reconstructs the final state via `as_replayer_state` (which
/// under `packed_ts` scans the (32x33x33) buffer and merges the delegation post-cycle
/// effects from `register_timestamps`), then runs the reference VM to the same final
/// timestamp and asserts equality of EVERY register value + timestamp and EVERY memory
/// word value + timestamp. Meaningful under `--features "jit packed_ts"`; also passes
/// without it (then `as_replayer_state` reads the field directly).
///   cargo test --features "jit packed_ts" --release --lib packed_ts_vs_reference -- --exact jit::tests::packed_ts_vs_reference --nocapture
#[test]
#[serial_test::serial]
fn packed_ts_vs_reference() {
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

    let source = QuasiUARTSource::new_with_reads(witness);
    // Bound comfortably above the full block (~558M cycles); execution halts on its own.
    let num_steps: u32 = 762314752;

    let (jit_state, jit_memory, _chunk) = JittedCode::run_alternative_simulator_with_last_snapshot(
        &text,
        &mut source.clone(),
        &binary,
        Some(num_steps),
    );
    let reconstructed = jit_state.as_replayer_state();

    let (reference_state, reference_ram, _snap) = run_reference_for_num_cycles_with_snapshots(
        &binary,
        &text,
        source.clone(),
        jit_state.timestamp,
        false,
    );

    let mut diffs = 0usize;
    if reconstructed.pc != reference_state.pc {
        println!(
            "PC: recon 0x{:08x} ref 0x{:08x}",
            reconstructed.pc, reference_state.pc
        );
        diffs += 1;
    }
    if reconstructed.timestamp != reference_state.timestamp {
        println!(
            "TIMESTAMP: recon {} ref {}",
            reconstructed.timestamp, reference_state.timestamp
        );
        diffs += 1;
    }
    for i in 0..32 {
        let (rc, rf) = (reconstructed.registers[i], reference_state.registers[i]);
        if rc.value != rf.value {
            println!("x{:02} VALUE: recon {} ref {}", i, rc.value, rf.value);
            diffs += 1;
        }
        if rc.timestamp != rf.timestamp {
            println!(
                "x{:02} TIMESTAMP: recon {} ref {}",
                i, rc.timestamp, rf.timestamp
            );
            diffs += 1;
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
        if reference_value.value != *jit_value {
            println!(
                "MEM[{}] VALUE: ref {} jit {}",
                word_idx, reference_value.value, jit_value
            );
            diffs += 1;
        }
        if reference_value.timestamp != *jit_ts {
            println!(
                "MEM[{}] TIMESTAMP: ref {} jit {}",
                word_idx, reference_value.timestamp, jit_ts
            );
            diffs += 1;
        }
        if diffs >= 60 {
            println!("... (stopping diff report)");
            break;
        }
    }
    assert_eq!(
        diffs, 0,
        "reconstructed state diverged from the reference VM"
    );
    println!(
        "packed_ts_vs_reference: reconstructed state MATCHES reference (32 regs + {} mem words) at cycle ts={}",
        jit_memory.memory.len(),
        jit_state.timestamp
    );
}

/// packed_ts verification. Runs the full block and computes the final replayer State
/// (`as_replayer_state`, which under `packed_ts` reconstructs register timestamps by
/// scanning the (32x33x33) buffer; otherwise reads `register_timestamps`).
///
///   * built WITHOUT `packed_ts`: writes the eager State to a temp file (the baseline).
///   * built WITH    `packed_ts`: reads that baseline and compares; prints the first
///     differing lines and panics on mismatch.
///
/// Procedure:
///   cargo test --features jit            --release --lib packed_ts_state_roundtrip -- --exact jit::tests::packed_ts_state_roundtrip --nocapture
///   cargo test --features "jit packed_ts" --release --lib packed_ts_state_roundtrip -- --exact jit::tests::packed_ts_state_roundtrip --nocapture
#[test]
#[serial_test::serial]
fn packed_ts_state_roundtrip() {
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

    let (state, _) = JittedCode::run_with_flattened_context(&text, &witness[..], &binary, None);
    let replayer = state.as_replayer_state();
    let dump = dump_replayer_state(&replayer);

    let path = std::env::temp_dir().join("packed_ts_state_baseline.txt");

    #[cfg(feature = "xmm_ts")]
    {
        std::fs::write(&path, dump.as_bytes()).expect("write baseline");
        println!(
            "[baseline] wrote eager replayer State to {} ({} bytes)",
            path.display(),
            dump.len()
        );
    }
    #[cfg(not(feature = "xmm_ts"))]
    {
        let baseline = std::fs::read_to_string(&path).expect(
            "baseline missing — run this test WITHOUT the packed_ts feature first to write it",
        );
        if baseline == dump {
            println!("[packed_ts] reconstructed State MATCHES the eager baseline");
        } else {
            let mut diffs = 0;
            for (i, (a, b)) in baseline.lines().zip(dump.lines()).enumerate() {
                if a != b {
                    println!("DIFF line {}:\n  eager : {}\n  packed: {}", i, a, b);
                    diffs += 1;
                    if diffs >= 40 {
                        println!("... (more diffs)");
                        break;
                    }
                }
            }
            if baseline.lines().count() != dump.lines().count() {
                println!(
                    "line count differs: eager={} packed={}",
                    baseline.lines().count(),
                    dump.lines().count()
                );
            }
            panic!("packed_ts reconstructed State diverged from eager baseline");
        }
    }
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
            &mut state,
            &mut ram,
            &mut (),
            &tape,
            &mut nd,
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
        if a.name == Sll
            && a.rs2 == 0
            && b.name == Add
            && b.rs2 != 0
            && (b.rs1 == a.rd || b.rs2 == a.rd)
            && a.rd != 0
        {
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
        if same_inputs && ((a.name == Mul && b.name == Mulhu) || (a.name == Mulhu && b.name == Mul))
        {
            widen_mul += w;
        }
        // combined division: divu + remu with the same inputs (one x86 `div`).
        if same_inputs && ((a.name == Divu && b.name == Remu) || (a.name == Remu && b.name == Divu))
        {
            comb_div += w;
        }
        // bit extract: SRLI then ANDI on the result.
        if a.name == Srl && a.rs2 == 0 && b.name == And && b.rs2 == 0 && b.rs1 == a.rd && a.rd != 0
        {
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
    println!(
        "=== fusion opportunity (executed instructions = {}) ===",
        total
    );
    println!(
        "LUI+ADDI      : {:>12} pairs  ({:.2}% of executed)",
        lui_addi,
        pct(lui_addi)
    );
    println!(
        "AUIPC+JALR    : {:>12} pairs  ({:.2}%)",
        auipc_jalr,
        pct(auipc_jalr)
    );
    println!(
        "AUIPC+mem     : {:>12} pairs  ({:.2}%)",
        auipc_mem,
        pct(auipc_mem)
    );
    println!(
        "SLLI+ADD      : {:>12} pairs  ({:.2}%)",
        slli_add,
        pct(slli_add)
    );
    println!(
        "seq word LW/SW: {:>12} pairs  ({:.2}%)",
        seq_word_mem,
        pct(seq_word_mem)
    );
    println!(
        "widening mul  : {:>12} pairs  ({:.2}%)",
        widen_mul,
        pct(widen_mul)
    );
    println!(
        "combined div  : {:>12} pairs  ({:.2}%)",
        comb_div,
        pct(comb_div)
    );
    println!(
        "SRLI+ANDI     : {:>12} pairs  ({:.2}%)",
        srli_andi,
        pct(srli_andi)
    );
    println!(
        "SRLI+SLT/SLTU : {:>12} pairs  ({:.2}%)",
        srli_lt,
        pct(srli_lt)
    );
    println!(
        "rotation(3op) : {:>12} sites  ({:.2}%)",
        rotation,
        pct(rotation)
    );
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
            if b.name == a.name && b.rs1 == a.rs1 && (stride == 4 || stride == 4u32.wrapping_neg())
            {
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
    // XMM-resident register reuse within pure-ALU runs (opportunity for caching a
    // value in a GPR to skip a repeated pextrd/pinsrd). A control-flow or memory/
    // delegation/ND instruction clobbers the scratch GPRs, so the cache cannot
    // persist across it — windows are bounded by such boundaries.
    let xmm_resident = |r: u32| {
        r != 0 && crate::jit::RV_REG_TO_XMM_SLOT[r as usize] != crate::jit::RV_XMM_SLOT_NONE
    };
    let touched = |ins: &Instruction| -> Vec<u32> {
        use InstructionName::*;
        let (rd, rs1, rs2) = (ins.rd as u32, ins.rs1 as u32, ins.rs2 as u32);
        let mut v: Vec<u32> = match ins.name {
            Branch | Sb | Sh | Sw => vec![rs1, rs2],
            Lb | Lbu | Lh | Lhu | Lw => vec![rs1, rd],
            Jal | Auipc | ZicsrNonDeterminismRead => vec![rd],
            Jalr => vec![rs1, rd],
            ZicsrNonDeterminismWrite => vec![rs1],
            Nop | ZicsrDelegation => vec![],
            _ => {
                if rs2 != 0 {
                    vec![rs1, rs2, rd]
                } else {
                    vec![rs1, rd]
                }
            }
        };
        v.retain(|&r| xmm_resident(r));
        v
    };
    let is_boundary_name = |n: InstructionName| {
        use InstructionName::*;
        matches!(
            n,
            Jal | Jalr
                | Branch
                | Lb
                | Lbu
                | Lh
                | Lhu
                | Lw
                | Sb
                | Sh
                | Sw
                | ZicsrNonDeterminismRead
                | ZicsrNonDeterminismWrite
                | ZicsrDelegation
        )
    };
    let (mut total_xmm, mut reuse_w2, mut reuse_w4) = (0u64, 0u64, 0u64);
    let mut hist: Vec<Vec<u32>> = Vec::new(); // recent pure instrs' XMM touches
    for i in 0..instructions.len() {
        let ins = &instructions[i];
        if is_boundary_name(ins.name) {
            hist.clear();
            continue;
        }
        let w = exec[i];
        let t = touched(ins);
        if w > 0 {
            for &r in &t {
                total_xmm += w;
                if hist.last().map_or(false, |h| h.contains(&r)) {
                    reuse_w2 += w;
                }
                if hist.iter().rev().take(3).any(|h| h.contains(&r)) {
                    reuse_w4 += w;
                }
            }
        }
        hist.push(t);
        if hist.len() > 3 {
            hist.remove(0);
        }
    }
    println!("\n=== XMM-resident register reuse within pure-ALU runs ===");
    println!(
        "total XMM accesses (pure runs) = {} ({:.2}% of executed)",
        total_xmm,
        pct(total_xmm)
    );
    println!(
        "reuse window 2 (prev instr): {} ({:.2}% of XMM accesses, {:.2}% of executed)",
        reuse_w2,
        (reuse_w2 as f64) * 100.0 / (total_xmm.max(1) as f64),
        pct(reuse_w2)
    );
    println!(
        "reuse window 4 (prev 3):     {} ({:.2}% of XMM accesses, {:.2}% of executed)",
        reuse_w4,
        (reuse_w4 as f64) * 100.0 / (total_xmm.max(1) as f64),
        pct(reuse_w4)
    );

    println!("\n=== seq word LW/SW run-length distribution (execution-weighted) ===");
    println!(
        "run-executions={}  words-in-runs={} ({:.2}% of executed)  avg run len={:.2}",
        run_execs,
        words_in_runs,
        pct(words_in_runs),
        if run_execs > 0 {
            words_in_runs as f64 / run_execs as f64
        } else {
            0.0
        }
    );
    for (l, w) in &by_len {
        println!(
            "  len {:>2}: {:>12} run-execs ({:>5.2}% of run-execs, {:>5.2}% of all words)",
            l,
            w,
            (*w as f64) * 100.0 / (run_execs.max(1) as f64),
            pct(*w * (*l as u64))
        );
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
    let stats = analyze_dynamic_execution(&instructions, &binary, &mut source, u64::MAX / 2);
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

    let artifact = build_control_flow_artifact(&instructions, &binary, nd_sources, u64::MAX / 2);
    println!("{}", artifact);

    // Serialize to disk and verify the round-trip.
    let path = std::env::temp_dir().join("zksync_os_cfg_artifact.txt");
    artifact.save_to_file(&path).expect("save artifact");
    println!("artifact written to {}", path.display());
    let reloaded = ControlFlowArtifact::load_from_file(&path).expect("load artifact");
    assert_eq!(
        artifact, reloaded,
        "artifact serialization round-trip mismatch"
    );
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

/// Measure the distribution of register-timestamp "staleness" over the full block,
/// to decide whether register timestamps can be stored as a u32 (relative/delta)
/// instead of u64.
///
/// Key quantity: `staleness = global_ts - register_last_touch_ts`. If the max
/// staleness over the whole run is < 2^32, then every register's timestamp is always
/// within a u32 of the running timestamp, so a delta-from-base encoding is always
/// safe (absolute timestamps are 38-bit and do overflow u32 over a long run).
///
/// Run with: cargo test --features jit --release --lib measure_register_timestamp_deltas -- --ignored --nocapture
#[test]
#[ignore]
#[serial_test::serial]
fn measure_register_timestamp_deltas() {
    use common_constants::TIMESTAMP_STEP;

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

    let cycles_bound = 1usize << 31;
    let mut state = State::initial_with_counters(DelegationsAndFamiliesCounters::default());
    let mut snapshotter = SimpleSnapshotter::<_, { common_constants::rom::ROM_SECOND_WORD_BITS }>::new_with_cycle_limit(cycles_bound, state);

    // Per-register measurement state.
    let mut prev_ts = [0u64; 32]; // last observed (nonzero) timestamp
    let mut max_gap = [0u64; 32]; // max gap between consecutive touches
    let mut touch_count = [0u64; 32];
    let mut max_live_staleness = 0u64; // max over cycles of (global - oldest touched reg ts)
    let mut staleness_hist = [0u64; 40]; // bucket by bit-width of live staleness
    let mut total_cycles = 0u64;

    for _cycle in 0..cycles_bound {
        let pc = state.pc;
        VM::<DelegationsAndFamiliesCounters>::run_step::<_, _, _, Mersenne31Field>(
            &mut state,
            &mut ram,
            &mut snapshotter,
            &tape,
            &mut source,
        );
        state.timestamp += TIMESTAMP_STEP;
        total_cycles += 1;

        let mut min_touched = u64::MAX;
        for r in 1..32 {
            let ts = state.registers[r].timestamp;
            if ts != prev_ts[r] {
                if prev_ts[r] != 0 {
                    let gap = ts - prev_ts[r];
                    if gap > max_gap[r] {
                        max_gap[r] = gap;
                    }
                }
                prev_ts[r] = ts;
                touch_count[r] += 1;
            }
            if ts != 0 && ts < min_touched {
                min_touched = ts;
            }
        }
        if min_touched != u64::MAX {
            let stale = state.timestamp - min_touched;
            if stale > max_live_staleness {
                max_live_staleness = stale;
            }
            let bits = (64 - stale.max(1).leading_zeros()) as usize;
            staleness_hist[bits.min(39)] += 1;
        }

        if state.pc == pc {
            snapshotter.take_final_snapshot(&state);
            break;
        }
        if snapshotter.take_snapshot_if_needed(&state) {
            break;
        }
    }

    let bits = |v: u64| 64 - v.max(1).leading_zeros();
    let global_max_gap = max_gap.iter().copied().max().unwrap();
    // final staleness (touched-once-then-read-at-end case)
    let mut max_final_staleness = 0u64;
    for r in 1..32 {
        if prev_ts[r] != 0 {
            max_final_staleness = max_final_staleness.max(state.timestamp - prev_ts[r]);
        }
    }

    println!("\n===== REGISTER TIMESTAMP DELTA ANALYSIS (full block) =====");
    println!("total cycles                 : {}", total_cycles);
    println!(
        "final global ts              : {} ({} bits)",
        state.timestamp,
        bits(state.timestamp)
    );
    println!(
        "max consecutive-touch gap    : {} ({} bits)",
        global_max_gap,
        bits(global_max_gap)
    );
    println!(
        "max LIVE staleness           : {} ({} bits)  <-- the binding number",
        max_live_staleness,
        bits(max_live_staleness)
    );
    println!(
        "max FINAL staleness          : {} ({} bits)",
        max_final_staleness,
        bits(max_final_staleness)
    );
    let key = max_live_staleness.max(max_final_staleness);
    println!(
        "=> register ts as u32 delta SAFE: {}  (key={} < 2^32={})",
        key < (1u64 << 32),
        key,
        1u64 << 32
    );
    println!(
        "   would fit u16 ({}), u24 ({}), 19-bit col ({})",
        key < (1 << 16),
        key < (1 << 24),
        key < (1 << 19)
    );
    println!("\nlive-staleness histogram (by bit-width, cycle count):");
    for (b, c) in staleness_hist.iter().enumerate() {
        if *c > 0 {
            println!("  {:2} bits: {}", b, c);
        }
    }
    println!("\nper-register (skipping x0):");
    for r in 1..32 {
        if touch_count[r] > 0 {
            println!(
                "  x{:02}: touches={:>10}, max_gap={:>12} ({} bits), final_staleness={}",
                r,
                touch_count[r],
                max_gap[r],
                bits(max_gap[r]),
                state.timestamp - prev_ts[r]
            );
        }
    }
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
            jit_state.counters[CounterType::ShiftBinary as u8 as usize]
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
        let jit_reg_ts = jit_state.register_timestamps_array();
        for (reg_idx, ((reference, jit_value), jit_ts)) in reference_state
            .registers
            .iter()
            .zip(jit_regs.iter())
            .zip(jit_reg_ts.iter())
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
            jit_state.counters[CounterType::ShiftBinary as u8 as usize]
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
        let jit_reg_ts = jit_state.register_timestamps_array();
        for (reg_idx, ((reference, jit_value), jit_ts)) in reference_state
            .registers
            .iter()
            .zip(jit_regs.iter())
            .zip(jit_reg_ts.iter())
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
    let simulator = JittedCode::<_>::preprocess_bytecode(&instructions, None, mop_field());

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

// Reconstructs register timestamps from INTERMEDIATE per-chunk snapshots via
// `as_replayer_state`. That requires the per-snapshot register-timestamp data that only the
// `xmm_ts` mechanism writes into each snapshot's MachineState; the default packed scheme
// would need a per-snapshot copy of the packed array (deferred). (Has a known pre-existing
// divergence at snapshot 321 even under xmm_ts — not gated on.)
#[cfg(feature = "xmm_ts")]
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
    let simulator = JittedCode::<_>::preprocess_bytecode(&jit_instructions, None, mop_field());

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
