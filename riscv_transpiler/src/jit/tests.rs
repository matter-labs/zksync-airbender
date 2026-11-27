use crate::abstractions::non_determinism::QuasiUARTSource;

use super::*;
use crate::ir::{
    simple_instruction_set::{preprocess_bytecode, Instruction, InstructionName},
    FullUnsignedMachineDecoderConfig, ReducedMachineDecoderConfig,
};
use crate::vm::test::*;
use field::baby_bear::base::BabyBearField;
use std::alloc::Global;

fn assemble_single_instruction(instruction: &str) -> u32 {
    let mut labels = std::collections::HashMap::new();
    lib_rv32_asm::assemble_ir(instruction, &mut labels, 0)
        .expect("single-instruction assembly should succeed")
        .expect("single-instruction assembly should emit one opcode")
}

#[test]
fn vm_word_group_widths_match_jit_cycle_boundaries() {
    for (program, _) in super::vm_state_tests::word_group_programs() {
        let widths = SimpleTape::new(&program).word_group_widths(JitRunnerRam::Tiny);
        let halt = program
            .iter()
            .position(|instr| instr.name == InstructionName::Jal && instr.imm == 0)
            .unwrap();
        for cap in 0..=halt {
            let mut stop = 0;
            while stop < cap {
                stop += usize::from(widths[stop]);
            }
            let (state, _) = JittedCode::<_>::run_alternative_simulator_from_instructions(
                &program,
                &mut (),
                &[],
                Some(cap as u32),
                MopField::BabyBear,
                JitRunnerRam::Tiny,
            );
            assert_eq!(state.pc, 4 * stop as u32, "cap {cap}, {program:?}");
            assert_eq!(
                state.timestamp,
                INITIAL_TIMESTAMP + TIMESTAMP_STEP * stop as u64
            );
        }
    }
}

#[test]
#[serial_test::serial]
fn test_jit_preserves_counters_across_nondeterminism_callbacks() {
    struct ClobberingSource;

    impl NonDeterminismCSRSource for ClobberingSource {
        fn read(&mut self) -> u32 {
            // SysV permits callbacks to overwrite all these registers.
            unsafe {
                core::arch::asm!(
                    "pcmpeqd xmm8, xmm8",
                    "psrlq xmm8, 63",
                    "movdqa xmm9, xmm8",
                    "movdqa xmm10, xmm8",
                    "movdqa xmm11, xmm8",
                    "movdqa xmm12, xmm8",
                    out("xmm8") _, out("xmm9") _, out("xmm10") _,
                    out("xmm11") _, out("xmm12") _,
                    options(nostack, nomem),
                );
            }
            0
        }

        fn write_with_memory_access<R: crate::vm::RamPeek + ?Sized>(&mut self, _: &R, _: u32) {
            self.read();
        }

        fn write_with_memory_access_raw(&mut self, ram: &[u32], value: u32) {
            self.write_with_memory_access(ram, value);
        }

        fn write_with_memory_access_dyn(&mut self, ram: &dyn crate::vm::RamPeek, value: u32) {
            self.write_with_memory_access(ram, value);
        }
    }

    for callback in ["csrrw x5, 0x7c0, x0", "csrrw x0, 0x7c0, x1"] {
        let program = ["addi x1, x0, 7", callback, "jal x0, 0"].map(assemble_single_instruction);
        let (expected, _) = JittedCode::<_>::run_alternative_simulator(
            &program,
            &mut (),
            &[],
            None,
            MopField::BabyBear,
            JitRunnerRam::Tiny,
        );
        let (actual, _) = JittedCode::<_>::run_alternative_simulator(
            &program,
            &mut ClobberingSource,
            &[],
            None,
            MopField::BabyBear,
            JitRunnerRam::Tiny,
        );
        assert_eq!(actual.counters, expected.counters, "{callback}");
    }
}

fn run_jit_program(program: &[u32]) {
    JittedCode::<_>::run_alternative_simulator(
        program,
        &mut (),
        &[],
        None,
        MopField::BabyBear,
        JitRunnerRam::Medium,
    );
}

/// Assert that an unsupported instruction aborts the process (with `expected`
/// somewhere in its output) by re-running the current test in a subprocess.
///
/// We can not use `#[should_panic]` or `catch_unwind` here because the JIT-runtime
/// panic is raised from an `extern "sysv64"` callback reached from JIT-generated
/// code. Rust treats that path as non-unwinding, so the process aborts instead of
/// producing a catchable unwind.
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
        "ecall",
        "ebreak",
    ];

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

    let (binary, text) = load_dumps(
        "examples/keccak_f1600/app.bin",
        "examples/keccak_f1600/app.text",
    );

    JittedCode::<_>::run_alternative_simulator(
        &text,
        &mut (),
        &binary,
        None,
        MopField::BabyBear,
        JitRunnerRam::Medium,
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

    JittedCode::<_>::run_alternative_simulator(
        &text,
        &mut (),
        &[],
        None,
        MopField::BabyBear,
        JitRunnerRam::Medium,
    );
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

        // rs2 aliases rd, mirroring the decoder (`preprocess_bytecode` sets rs2 := rd so the
        // second XOR operand flows through the rs2 read port).
        prog.push(Instruction::new(ZimopIXorRot, rs1, rd, rd, rot));
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

        let (state, _mem) = JittedCode::<_>::run_alternative_simulator_from_instructions(
            &prog,
            &mut (),
            &[],
            None,
            MopField::BabyBear,
            JitRunnerRam::Medium,
        );
        let got = state.materialized_registers()[rd as usize];
        assert_eq!(
            got, expected,
            "ZimopIXorRot mismatch: rs1=x{rs1} rd=x{rd} v1={v1:#010x} v2={v2:#010x} rot={rot} -> got {got:#010x}, expected {expected:#010x}"
        );
    }
}

/// `Rev8` (Zbb byte swap) computes `rd = rs1.swap_bytes()` — the formula of the
/// reference `binary_shifts_family::shifts::rev8`. Covers GPR-mapped vs
/// XMM-resident rd/rs1, rs1 == rd, and rs1 == x0.
#[test]
#[serial_test::serial]
fn test_jit_rev8() {
    use InstructionName::{Add, Jal, Rev8};

    // (rs1, rd, v1). GPR-mapped regs are {10,11,12,13,14,15,16,28}; the rest are XMM-resident.
    let cases: &[(u8, u8, u32)] = &[
        (10, 11, 0xDDCC_BBAA), // both GPR-mapped
        (5, 11, 0x0102_0304),  // rs1 XMM-resident, rd GPR-mapped
        (11, 6, 0x8000_0001),  // rs1 GPR-mapped, rd XMM-resident
        (7, 9, 0xCAFE_BABE),   // both XMM-resident
        (12, 12, 0x00AA_0000), // rs1 == rd
        (0, 13, 0),            // rs1 == x0
    ];

    for &(rs1, rd, v1) in cases {
        let mut prog: Vec<Instruction> = Vec::new();
        if rs1 != 0 {
            prog.push(Instruction::new(Add, 0, 0, rs1, v1)); // rs1 = v1
        }
        if rd != rs1 {
            prog.push(Instruction::new(Add, 0, 0, rd, 0x5555_5555)); // rd's old value
        }
        // Formal rs2 = x0 and imm = 0, mirroring the decoder.
        prog.push(Instruction::new(Rev8, rs1, 0, rd, 0));
        prog.push(Instruction::new(Jal, 0, 0, 0, 0)); // jal x0, 0 = self-loop = exit

        let rs1_value = if rs1 == 0 { 0 } else { v1 };
        let expected = rs1_value.swap_bytes();

        let (state, _mem) = JittedCode::<_>::run_alternative_simulator_from_instructions(
            &prog,
            &mut (),
            &[],
            None,
            MopField::BabyBear,
            JitRunnerRam::Medium,
        );
        let got = state.materialized_registers()[rd as usize];
        assert_eq!(
            got, expected,
            "Rev8 mismatch: rs1=x{rs1} rd=x{rd} v1={v1:#010x} -> got {got:#010x}, expected {expected:#010x}"
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
        let set = |prog: &mut Vec<Instruction>, reg: u8, val: u32| {
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

        let (state, _mem) = JittedCode::<_>::run_alternative_simulator_from_instructions(
            &prog,
            &mut (),
            &[],
            None,
            MopField::BabyBear,
            JitRunnerRam::Medium,
        );
        let got = state.materialized_registers()[rd as usize];
        assert_eq!(
            got, expected,
            "ZimopTriAdd mismatch: rs1=x{rs1} rs2=x{rs2} rd=x{rd} v1={v1:#010x} v2={v2:#010x} v_rd={v_rd:#010x} -> got {got:#010x}, expected {expected:#010x}"
        );
    }
}

/// Both BabyBear emitters for ZimopAdd/Sub/Mul/FMA must match the reference
/// `field` crate. Build instruction streams directly and compare to
/// `from_raw_repr_with_reduction` + the field op + `as_u32_raw_repr_reduced`.
/// Covers GPR-mapped / XMM-resident placements, rs2 == x0, and inputs above the modulus.
#[test]
#[serial_test::serial]
fn test_jit_zimop_field_ops() {
    use InstructionName::{Add, Jal, ZimopAdd, ZimopFMA, ZimopMul, ZimopSub};

    fn field_expected<F: field::PrimeField>(op: InstructionName, a: u32, b: u32, c: u32) -> u32 {
        let fa = F::from_raw_repr_with_reduction(a);
        let fb = F::from_raw_repr_with_reduction(b);
        let res = match op {
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
    // rs2 == x0. (Each case rebuilds a JIT — keep the matrix modest.)
    let placements: &[(u8, u8, u8)] = &[(10, 11, 12), (5, 6, 7), (5, 11, 6), (11, 0, 12)];
    // (v1 -> rs1, v2 -> rs2, v_rd -> rd's old value); above the modulus to force reduction, plus 0.
    let values: &[(u32, u32, u32)] = &[
        (0x7fff_fffe, 0x7fff_ffff, 0x8000_0000),
        (0x7800_0000, 0x7800_0001, 0xffff_ffff),
        (0xdead_beef, 0x1234_5678, 0xcafe_babe),
        (0, 0, 0),
    ];
    let ops = [ZimopAdd, ZimopSub, ZimopMul, ZimopFMA];

    for mop_field in [MopField::BabyBear, MopField::BabyBearAssumeCanonical] {
        for &op in &ops {
            for &(rs1, rs2, rd) in placements {
                for &(v1, v2, v_rd) in values {
                    // this mode is only defined over canonical inputs
                    let (v1, v2, v_rd) = if mop_field == MopField::BabyBearAssumeCanonical {
                        const P: u32 = BabyBearField::ORDER;
                        (v1 % P, v2 % P, v_rd % P)
                    } else {
                        (v1, v2, v_rd)
                    };
                    let mut prog: Vec<Instruction> = Vec::new();
                    let set = |p: &mut Vec<Instruction>, reg: u8, val: u32| {
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
                    let expected = field_expected::<BabyBearField>(op, a, b, c);

                    let (state, _mem) =
                        JittedCode::<_>::run_alternative_simulator_from_instructions(
                            &prog,
                            &mut (),
                            &[],
                            None,
                            mop_field,
                            JitRunnerRam::Medium,
                        );
                    if mop_field == MopField::BabyBearAssumeCanonical {
                        // Even when the value computation degenerates (e.g. addition of x0 is
                        // just a move), all the bookkeeping must be the same as with the
                        // reducing implementation: register timestamps, machine timestamp,
                        // PC and family counters
                        let (reference_state, _mem) =
                            JittedCode::<_>::run_alternative_simulator_from_instructions(
                                &prog,
                                &mut (),
                                &[],
                                None,
                                MopField::BabyBear,
                                JitRunnerRam::Medium,
                            );
                        assert_eq!(
                            state.as_replayer_state(),
                            reference_state.as_replayer_state(),
                            "{op:?}: rs1=x{rs1} rs2=x{rs2} rd=x{rd} machine state diverged"
                        );
                    }
                    let got = state.materialized_registers()[rd as usize];
                    assert_eq!(
                        got, expected,
                        "{mop_field:?} {op:?}: rs1=x{rs1}({a:#010x}) rs2=x{rs2}({b:#010x}) rd=x{rd}({c:#010x}) -> got {got:#010x}, expected {expected:#010x}"
                    );
                }
            }
        }
    }
}

#[test]
#[serial_test::serial]
fn test_jit_full_block() {
    let path = std::env::current_dir().unwrap();
    println!("The current directory is {}", path.display());

    let (binary, text) = load_dumps("examples/zksync_os/app.bin", "examples/zksync_os/app.text");

    let witness = std::fs::read("examples/zksync_os/23620012_witness").unwrap();
    let witness = hex::decode(core::str::from_utf8(&witness).unwrap()).unwrap();
    let witness: Vec<_> = witness
        .as_chunks::<4>()
        .0
        .iter()
        .map(|el| u32::from_be_bytes(*el))
        .collect();
    let mut source = QuasiUARTSource::new_with_reads(witness);
    let (state, _) = JittedCode::<_>::run_alternative_simulator(
        &text,
        &mut source,
        &binary,
        None,
        MopField::BabyBear,
        JitRunnerRam::Full,
    );
    println!("PC = 0x{:08x}", state.pc);
    dbg!(state.materialized_registers());
}

#[test]
#[serial_test::serial]
fn test_jit_full_block_with_flattened_responder() {
    let path = std::env::current_dir().unwrap();
    println!("The current directory is {}", path.display());

    let (binary, text) = load_dumps("examples/zksync_os/app.bin", "examples/zksync_os/app.text");

    let witness = std::fs::read("examples/zksync_os/23620012_witness").unwrap();
    let witness = hex::decode(core::str::from_utf8(&witness).unwrap()).unwrap();
    let witness: Vec<_> = witness
        .as_chunks::<4>()
        .0
        .iter()
        .map(|el| u32::from_be_bytes(*el))
        .collect();
    let (state, _) = JittedCode::run_with_flattened_context(
        &text,
        &witness[..],
        &binary,
        None,
        MopField::BabyBear,
        JitRunnerRam::Medium,
    );
    println!("PC = 0x{:08x}", state.pc);
    dbg!(state.materialized_registers());
}

fn assert_jit_matches_reference(
    jit_state: &MachineState,
    jit_memory: &MemoryHolder,
    reference_state: &State<DelegationsAndFamiliesCounters>,
    reference_ram: &RamWithRomRegion<{ common_constants::rom::ROM_SECOND_WORD_BITS }>,
) {
    let reconstructed = jit_state.as_replayer_state();
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
    assert_eq!(reference_ram.backing.len(), jit_memory.memory().len());
    for (word_idx, ((reference_value, jit_value), jit_ts)) in reference_ram
        .backing
        .iter()
        .zip(jit_memory.memory().iter())
        .zip(jit_memory.timestamps().iter())
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
}

// Compare reconstructed register and memory timestamps against the reference VM.
#[test]
#[serial_test::serial]
fn packed_ts_vs_reference() {
    let (binary, text) = load_dumps("examples/zksync_os/app.bin", "examples/zksync_os/app.text");
    let witness = std::fs::read("examples/zksync_os/23620012_witness").unwrap();
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
        MopField::BabyBear,
        JitRunnerRam::Medium,
    );
    let (reference_state, reference_ram, _snap) = run_reference_for_num_cycles_with_snapshots(
        &binary,
        &text,
        source.clone(),
        jit_state.timestamp,
        false,
        JitRunnerRam::Medium.ram_size(),
    );

    assert_jit_matches_reference(&jit_state, &jit_memory, &reference_state, &reference_ram);
    println!(
        "packed_ts_vs_reference: reconstructed state MATCHES reference (32 regs + {} mem words) at cycle ts={}",
        jit_memory.memory().len(),
        jit_state.timestamp
    );
}

#[allow(dead_code)]
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
            binary,
            1 << 30,
        );

    let mut state = State::initial_with_counters(DelegationsAndFamiliesCounters::default());

    VM::<DelegationsAndFamiliesCounters>::run_by_timestamp_bound::<_, _, _, BabyBearField>(
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
    ram_bound: usize,
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
            binary, ram_bound,
        );

    let mut state = State::initial_with_counters(DelegationsAndFamiliesCounters::default());
    let mut snapshotter = SimpleSnapshotter::<_, {common_constants::rom::ROM_SECOND_WORD_BITS }>::new_with_cycle_limit(1 << 31, state);

    VM::<DelegationsAndFamiliesCounters>::run_by_timestamp_bound::<_, _, _, BabyBearField>(
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
    let (binary, text) = load_dumps("examples/zksync_os/app.bin", "examples/zksync_os/app.text");

    let witness = std::fs::read("examples/zksync_os/23620012_witness").unwrap();
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
    VM::<DelegationsAndFamiliesCounters>::run_basic_unrolled::<_, _, _, BabyBearField>(
        &mut state,
        &mut ram,
        &mut snapshotter,
        &tape,
        cycles_bound,
        &mut source,
    );
    let _elapsed = now.elapsed();

    println!("PC = 0x{:08x}", state.pc);
    dbg!(state.registers.map(|el| el.value));
}

#[test]
#[ignore = "full-block JIT/VM comparison, run on demand"]
#[serial_test::serial]
fn run_and_compare() {
    const CHECKPOINT_STEP: u32 = 1 << 22;

    let (binary, text) = load_dumps("examples/zksync_os/app.bin", "examples/zksync_os/app.text");
    let ram_config = JitRunnerRam::Full;

    let witness = std::fs::read("examples/zksync_os/23620012_witness").unwrap();
    let witness = hex::decode(core::str::from_utf8(&witness).unwrap()).unwrap();
    let witness: Vec<_> = witness
        .as_chunks::<4>()
        .0
        .iter()
        .map(|el| u32::from_be_bytes(*el))
        .collect();
    let source = QuasiUARTSource::new_with_reads(witness);

    let (cycles_taken, result) = compare_full_block(&binary, &text, &source, ram_config);
    let Err(mut divergence) = result else {
        println!("Passed for {cycles_taken} cycles");
        return;
    };

    let compare_checkpoint = |cycles_bound| {
        let (jit_state, jit_memory, jit_last_trace_chunk) =
            JittedCode::run_alternative_simulator_with_last_snapshot(
                &text,
                &mut source.clone(),
                &binary,
                Some(cycles_bound),
                MopField::BabyBear,
                ram_config,
            );
        let (reference_state, reference_ram, reference_snapshotter) =
            run_reference_for_num_cycles_with_snapshots(
                &binary,
                &text,
                source.clone(),
                jit_state.timestamp,
                false,
                ram_config.ram_size(),
            );
        compare_block_state(
            u64::from(cycles_bound),
            &reference_state,
            &jit_state,
            &reference_ram.backing,
            &jit_memory,
        )?;
        let reference_reads = &reference_snapshotter.reads_buffer;
        let tail_len = jit_last_trace_chunk.len as usize;
        let offset = reference_reads.len().checked_sub(tail_len).ok_or_else(|| {
            format!(
                "Snapshot length diverged after {cycles_bound} steps: reference has {} reads, JIT tail has {tail_len}",
                reference_reads.len()
            )
        })?;
        compare_block_trace_chunk(reference_reads, offset, &jit_last_trace_chunk)
    };

    let mut matching = 0;
    let final_checkpoint = u32::try_from(cycles_taken.div_ceil(u64::from(CHECKPOINT_STEP)))
        .unwrap()
        .max(1);
    let mut divergent = final_checkpoint;
    while divergent - matching > 1 {
        let checkpoint = matching + (divergent - matching) / 2;
        match compare_checkpoint(checkpoint * CHECKPOINT_STEP) {
            Ok(()) => matching = checkpoint,
            Err(mismatch) => {
                divergent = checkpoint;
                divergence = mismatch;
            }
        }
    }

    if divergent == final_checkpoint {
        let last_matching = u64::from(matching) * u64::from(CHECKPOINT_STEP);
        panic!(
            "No bounded checkpoint up to {last_matching} cycles diverges; the full run diverges after {cycles_taken} cycles: {divergence}"
        );
    }
    let steps = u64::from(divergent) * u64::from(CHECKPOINT_STEP);
    panic!(
        "Divergent checkpoint at {steps} cycles (bisection assumes the divergence persists): {divergence}"
    );
}

fn compare_full_block(
    binary: &[u32],
    text: &[u32],
    source: &QuasiUARTSource,
    ram_config: JitRunnerRam,
) -> (u64, Result<(), String>) {
    let final_timestamp = JittedCode::run_alternative_simulator_with_last_snapshot(
        text,
        &mut source.clone(),
        binary,
        None,
        MopField::BabyBear,
        ram_config,
    )
    .0
    .timestamp;
    let cycles_taken = (final_timestamp - INITIAL_TIMESTAMP) / TIMESTAMP_STEP;
    let (reference_state, reference_ram, reference_snapshotter) =
        run_reference_for_num_cycles_with_snapshots(
            binary,
            text,
            source.clone(),
            final_timestamp,
            false,
            ram_config.ram_size(),
        );

    let mut source = source.clone();
    let reference_reads = &reference_snapshotter.reads_buffer;
    let mut context = Context::new(
        BlockTraceContext {
            inner: DefaultContextImpl::new(&mut source),
            reference_reads,
            mismatch: None,
        },
        ram_config,
    );
    let instructions = preprocess_bytecode::<FullUnsignedMachineDecoderConfig, false>(text);
    let jit = JittedCode::preprocess_bytecode(&instructions, None, MopField::BabyBear, ram_config);
    let mut jit_memory = MemoryHolder::allocate_zeroed(ram_config, Global);
    let mut trace = unsafe { Box::<TraceChunk>::new_zeroed().assume_init() };
    jit.run(
        &mut context,
        &mut jit_memory,
        NonNull::from(trace.as_mut()),
        binary,
    );

    let mut comparison = context.into_implementation();
    if let Some(mismatch) = comparison.mismatch {
        panic!("{mismatch}");
    }
    let trace_len = comparison.inner.trace_len;
    assert_eq!(
        trace_len,
        reference_reads.len(),
        "Total trace length diverged"
    );
    println!("Compared {trace_len} trace entries");

    let jit_state = comparison
        .take_final_state()
        .expect("must finish execution");
    let result = compare_block_state(
        cycles_taken,
        &reference_state,
        &jit_state,
        &reference_ram.backing,
        &jit_memory,
    );
    (cycles_taken, result)
}

struct BlockTraceContext<'source, 'trace> {
    inner: DefaultContextImpl<'source, QuasiUARTSource>,
    reference_reads: &'trace [(u32, (u32, u32))],
    mismatch: Option<String>,
}

impl BlockTraceContext<'_, '_> {
    fn compare_chunk(&mut self, trace: NonNull<TraceChunk>) {
        if self.mismatch.is_none() {
            self.mismatch =
                compare_block_trace_chunk(self.reference_reads, self.inner.trace_len, unsafe {
                    trace.as_ref()
                })
                .err();
        }
    }
}

impl ContextImpl for BlockTraceContext<'_, '_> {
    fn read_nondeterminism(&mut self) -> u32 {
        self.inner.read_nondeterminism()
    }

    fn write_nondeterminism(&mut self, value: u32, memory: &[u32]) {
        self.inner.write_nondeterminism(value, memory);
    }

    fn receive_trace(
        &mut self,
        trace: NonNull<TraceChunk>,
        machine_state: &MachineState,
    ) -> NonNull<TraceChunk> {
        self.compare_chunk(trace);
        self.inner.receive_trace(trace, machine_state)
    }

    fn receive_final_trace_piece(
        &mut self,
        trace: NonNull<TraceChunk>,
        machine_state: &MachineState,
    ) {
        self.compare_chunk(trace);
        self.inner.receive_final_trace_piece(trace, machine_state);
    }

    fn take_final_state(&mut self) -> Option<MachineState> {
        self.inner.take_final_state()
    }

    fn final_state_ref(&self) -> Option<&MachineState> {
        self.inner.final_state_ref()
    }
}

fn compare_block_state(
    steps: u64,
    reference: &State<DelegationsAndFamiliesCounters>,
    jit: &MachineState,
    reference_ram: &[Register],
    jit_memory: &MemoryHolder,
) -> Result<(), String> {
    if reference.timestamp != jit.timestamp {
        return Err(format!(
            "TIMESTAMP diverged after {steps} steps: reference is {}, JIT is {}",
            reference.timestamp, jit.timestamp
        ));
    }
    if reference.pc != jit.pc {
        return Err(format!(
            "PC diverged after {steps} steps: expected {:#010x}, got {:#010x}",
            reference.pc, jit.pc
        ));
    }

    let jit = jit.as_replayer_state();
    if reference.counters != jit.counters {
        return Err(format!(
            "COUNTERS diverged after {steps} steps: reference is {:?}, JIT is {:?}",
            reference.counters, jit.counters
        ));
    }
    for (reg_idx, (reference, jit)) in reference.registers.iter().zip(&jit.registers).enumerate() {
        if reference.value != jit.value {
            return Err(format!(
                "VALUE diverged for x{reg_idx} after {steps} steps:\nreference\n{}\njitted\n{}",
                reference.value, jit.value
            ));
        }
        if reference.timestamp != jit.timestamp {
            return Err(format!(
                "TIMESTAMP diverged for x{reg_idx} after {steps} steps:\nreference\n{}\njitted\n{}",
                reference.timestamp, jit.timestamp
            ));
        }
    }

    if reference_ram.len() != jit_memory.memory().len() {
        return Err(format!(
            "RAM length diverged after {steps} steps: reference is {}, JIT is {}",
            reference_ram.len(),
            jit_memory.memory().len()
        ));
    }
    for (word_idx, (reference, (&jit_value, &jit_ts))) in reference_ram
        .iter()
        .zip(jit_memory.memory().iter().zip(jit_memory.timestamps()))
        .enumerate()
    {
        if reference.value != jit_value {
            return Err(format!(
                "VALUE diverged for word {word_idx} after {steps} steps: reference is {}, JIT is {jit_value}",
                reference.value
            ));
        }
        if reference.timestamp != jit_ts {
            return Err(format!(
                "TIMESTAMP diverged for word {word_idx} after {steps} steps: reference is {}, JIT is {jit_ts}",
                reference.timestamp
            ));
        }
    }

    Ok(())
}

fn compare_block_trace_chunk(
    reference_reads: &[(u32, (u32, u32))],
    offset: usize,
    jit_trace: &TraceChunk,
) -> Result<(), String> {
    let (values, timestamps) = jit_trace.data();
    let end = offset + values.len();
    let reference = reference_reads.get(offset..end).ok_or_else(|| {
        format!(
            "Snapshot length diverged at index {offset}: JIT chunk ends at {end}, reference has {} reads",
            reference_reads.len()
        )
    })?;
    for (idx, ((&(reference_value, (low, high)), &jit_value), &jit_ts)) in
        (offset..end).zip(reference.iter().zip(values).zip(timestamps))
    {
        if reference_value != jit_value {
            return Err(format!(
                "VALUE diverged at snapshot index {idx}: expected {reference_value}, got {jit_value}"
            ));
        }
        let reference_ts = (u64::from(high) << 32) | u64::from(low);
        if reference_ts != jit_ts {
            return Err(format!(
                "TIMESTAMP diverged at snapshot index {idx}: expected {reference_ts}, got {jit_ts}"
            ));
        }
    }
    Ok(())
}

#[test]
fn test_memory_holder_drop() {
    let boxed_holder: Box<MemoryHolder> =
        MemoryHolder::allocate_zeroed(JitRunnerRam::Small, Default::default());
    drop(boxed_holder);
}

#[test]
#[serial_test::serial]
fn test_jit_keccak_f1600_matches_vm() {
    let (binary, text) = load_dumps("../examples/keccak/app.bin", "../examples/keccak/app.text");

    let (jit_state, jit_memory, jit_trace) =
        JittedCode::<_>::run_alternative_simulator_with_last_snapshot(
            &text,
            &mut (),
            &binary,
            None,
            MopField::BabyBear,
            JitRunnerRam::Medium,
        );
    let (state, ram, snapshotter) = run_reference_for_num_cycles_with_snapshots(
        &binary,
        &text,
        (),
        jit_state.timestamp,
        false,
        JitRunnerRam::Medium.ram_size(),
    );
    assert_jit_matches_reference(&jit_state, &jit_memory, &state, &ram);
    // the guest reads every slot after each permutation, so the slot write timestamps survive only
    // in the timestamps of those reads
    let (values, timestamps) = jit_trace.data();
    assert!(!values.is_empty());
    let reads = &snapshotter.reads_buffer[snapshotter.reads_buffer.len() - values.len()..];
    for (i, (&(value, (ts_low, ts_high)), (jit_value, jit_ts))) in
        reads.iter().zip(values.iter().zip(timestamps)).enumerate()
    {
        let ts = (ts_high as TimestampScalar) << 32 | ts_low as TimestampScalar;
        assert_eq!((value, ts), (*jit_value, *jit_ts), "read {i}");
    }
    let keccak_calls = jit_state.counters.values[CounterType::KeccakF1600Delegation as u8 as usize];
    assert_eq!(keccak_calls as usize, state.counters.keccak_f1600_calls);
    assert!(keccak_calls > 0);
}
