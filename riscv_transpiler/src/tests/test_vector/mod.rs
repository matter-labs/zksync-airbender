use std::alloc::Global;
use std::panic::{catch_unwind, AssertUnwindSafe};

use common_constants::rom::{ROM_BYTE_SIZE, ROM_SECOND_WORD_BITS};
use field::Mersenne31Field;
use worker::Worker;

use crate::ir::{self, FullMachineDecoderConfig, FullUnsignedMachineDecoderConfig};
use crate::replayer::{ReplayerRam, ReplayerVM};
use crate::vm::{
    DelegationsAndFamiliesCounters, RamWithRomRegion, ReplayBuffer, SimpleSnapshotter, SimpleTape,
    Snapshotter, State, VM,
};

use self::parser::{
    instruction_tokens, parse_immediate_token, parse_memory_operand, parse_register,
    parse_value_token, split_macro_fields, RAM_TEST_BASE,
};

mod parser;

mod auipc;
mod beq;
mod csrrw;
mod jalr;
mod lb;
mod lbu;
mod lh;
mod lhu;
mod lui;
mod lw;
mod sb;
mod sh;
mod sw;

const SINGLE_STEP_CYCLE_BOUND: usize = 1;
const RAM_BOUND_BYTES: usize = 1 << 23;

type TouchedWords = Vec<Vec<(u32, (u64, u32)), Global>>;

#[derive(Clone, Copy)]
struct TestVectorSpec {
    test_vectors: &'static str,
    match_prefix: &'static str,
    patch_match: Option<&'static str>,
    opfields: &'static [usize],
    patch_immediate: Option<usize>,
    patch_immediate_with_register: bool,
    initial_registers_index: &'static [(usize, usize)],
    patch_initial_register: Option<&'static str>,
    final_register_index: Option<(usize, usize)>,
    selected_test_vectors: &'static [usize],
}

#[derive(Clone, Copy)]
enum MachineTarget {
    FullUnsigned,
    FullSigned,
}

#[derive(Clone, Copy)]
enum RejectStage {
    Decode,
    Execute,
}

struct ExpectedOutcome {
    final_pc: u32,
    register_checks: Vec<(usize, u32)>,
    memory_checks: Vec<(u32, u32)>,
}

enum OpcodePlan {
    Reject {
        target: MachineTarget,
        stage: RejectStage,
    },
    Execute {
        target: MachineTarget,
        expected: ExpectedOutcome,
    },
}

fn run_test_vector_cases(spec: TestVectorSpec) {
    let mut executed = 0usize;

    for (case_idx, line) in spec
        .test_vectors
        .lines()
        .filter(|line| line.starts_with(spec.match_prefix))
        .enumerate()
    {
        if !spec.selected_test_vectors.is_empty() && !spec.selected_test_vectors.contains(&case_idx)
        {
            continue;
        }

        executed += 1;

        let mut fields = split_macro_fields(line, spec.match_prefix)
            .into_iter()
            .map(str::to_owned)
            .collect::<Vec<_>>();
        if let Some(opinsert) = spec.patch_match {
            fields.insert(0, opinsert.to_owned());
        }

        if let Some(immediate_idx) = spec.patch_immediate {
            let (patched_imm, _) = parse_immediate_token(&fields[immediate_idx]);
            fields[immediate_idx] = patched_imm;
        }

        let mut instruction_fields = Vec::with_capacity(spec.opfields.len());
        for src_idx in spec.opfields.iter().copied() {
            instruction_fields.push(fields[src_idx].clone());
        }
        if spec.patch_immediate_with_register {
            let imm = instruction_fields.pop().unwrap();
            let reg = instruction_fields.pop().unwrap();
            instruction_fields.push(format!("{imm}({reg})"));
        }
        let instruction = instruction_fields.join(", ");

        let final_register = spec.final_register_index.map(|(reg_idx, value_idx)| {
            (
                parse_register(&fields[reg_idx]),
                parse_value_token(&fields[value_idx]),
            )
        });

        let mut owned_fields = fields.clone();
        if let Some(default_value) = spec.patch_initial_register {
            let patched_value = if matches!(spec.match_prefix, "TEST_LOAD" | "TEST_STORE") {
                RAM_TEST_BASE.to_string()
            } else {
                default_value.to_owned()
            };
            owned_fields.push(patched_value);
        }

        let mut initial_registers = [0u32; 32];
        for &(reg_idx, value_idx) in spec.initial_registers_index {
            let register = parse_register(&owned_fields[reg_idx]);
            initial_registers[register] = parse_value_token(&owned_fields[value_idx]);
        }

        run_test_vector_opcode(&instruction, None, initial_registers, final_register);
    }

    assert!(
        executed > 0,
        "expected at least one test vector for `{}`",
        spec.match_prefix,
    );
    if !spec.selected_test_vectors.is_empty() {
        assert_eq!(
            executed,
            spec.selected_test_vectors.len(),
            "not all requested test vectors were executed for `{}`",
            spec.match_prefix,
        );
    }
}

fn run_test_vector_opcode(
    instruction: &str,
    alternative_instruction_bytecode: Option<u32>,
    mut initial_registers: [u32; 32],
    final_register: Option<(usize, u32)>,
) {
    initial_registers[0] = 0;
    let program = build_program(instruction, alternative_instruction_bytecode);

    match plan_test_vector_opcode(instruction, &program, &initial_registers, final_register) {
        OpcodePlan::Reject { target, stage } => match (target, stage) {
            (MachineTarget::FullUnsigned, RejectStage::Decode) => {
                run_decode_rejection::<FullUnsignedMachineDecoderConfig>(&program, instruction);
            }
            (MachineTarget::FullSigned, RejectStage::Decode) => {
                run_decode_rejection::<FullMachineDecoderConfig>(&program, instruction);
            }
            (MachineTarget::FullUnsigned, RejectStage::Execute) => {
                run_rejection::<FullUnsignedMachineDecoderConfig>(
                    &program,
                    initial_registers,
                    instruction,
                );
            }
            (MachineTarget::FullSigned, RejectStage::Execute) => {
                run_rejection::<FullMachineDecoderConfig>(&program, initial_registers, instruction);
            }
        },
        OpcodePlan::Execute { target, expected } => match target {
            MachineTarget::FullUnsigned => {
                execute_case::<FullUnsignedMachineDecoderConfig>(
                    &program,
                    initial_registers,
                    &expected,
                );
            }
            MachineTarget::FullSigned => {
                execute_case::<FullMachineDecoderConfig>(&program, initial_registers, &expected);
            }
        },
    }
}

fn worker() -> Worker {
    Worker::new()
}

fn build_program(instruction: &str, alternative_instruction_bytecode: Option<u32>) -> Vec<u32> {
    let program = if let Some(bytecode) = alternative_instruction_bytecode {
        vec![bytecode]
    } else {
        lib_rv32_asm::assemble_program(instruction).unwrap()
    };

    assert_eq!(
        program.len(),
        1,
        "expected a single instruction in `{instruction}`",
    );

    program
}

fn initial_word(program: &[u32], address: u32) -> u32 {
    program.get((address / 4) as usize).copied().unwrap_or(0)
}

fn initial_state(initial_registers: [u32; 32]) -> State<DelegationsAndFamiliesCounters> {
    let mut state = State::initial_with_counters(DelegationsAndFamiliesCounters::default());
    for (slot, value) in state.registers.iter_mut().zip(initial_registers) {
        slot.value = value;
        slot.timestamp = 0;
    }
    state.registers[0].value = 0;

    state
}

fn assert_registers(
    state: &State<DelegationsAndFamiliesCounters>,
    expected_registers: &[(usize, u32)],
) {
    for &(register_idx, expected_value) in expected_registers {
        assert_eq!(
            state.registers[register_idx].value, expected_value,
            "unexpected value in x{register_idx}",
        );
    }
}

fn assert_replay_matches(
    vm_state: &State<DelegationsAndFamiliesCounters>,
    replay_state: &State<DelegationsAndFamiliesCounters>,
) {
    assert_eq!(vm_state.pc, replay_state.pc);
    assert_eq!(vm_state.timestamp, replay_state.timestamp);
    assert_eq!(vm_state.registers, replay_state.registers);
}

fn assert_touched_words(touched_words: &TouchedWords, expected_words: &[(u32, u32)]) {
    for &(address, expected_value) in expected_words {
        let (_, (_, actual_value)) = touched_words
            .iter()
            .flat_map(|chunk| chunk.iter())
            .find(|(candidate_address, _)| *candidate_address == address)
            .unwrap_or_else(|| panic!("missing touched word at address 0x{address:08x}"));
        assert_eq!(
            *actual_value, expected_value,
            "unexpected final word at address 0x{address:08x}",
        );
    }
}

fn finalize_state_with_snapshot(
    program: &[u32],
    tape: &SimpleTape,
    initial_registers: [u32; 32],
    collect_memory_checks: bool,
) -> (
    State<DelegationsAndFamiliesCounters>,
    SimpleSnapshotter<DelegationsAndFamiliesCounters, { ROM_SECOND_WORD_BITS }>,
    Option<TouchedWords>,
) {
    let mut state = initial_state(initial_registers);
    let mut snapshotter: SimpleSnapshotter<_, { ROM_SECOND_WORD_BITS }> =
        SimpleSnapshotter::new_with_cycle_limit(SINGLE_STEP_CYCLE_BOUND, state);
    let mut ram =
        RamWithRomRegion::<{ ROM_SECOND_WORD_BITS }>::from_rom_content(program, RAM_BOUND_BYTES);

    let finished =
        VM::<DelegationsAndFamiliesCounters>::run_basic_unrolled::<_, _, _, Mersenne31Field>(
            &mut state,
            &mut ram,
            &mut snapshotter,
            tape,
            SINGLE_STEP_CYCLE_BOUND,
            &mut (),
        );
    if !finished {
        snapshotter.take_final_snapshot(&state);
    }

    let touched_words = collect_memory_checks.then(|| {
        let worker = worker();
        ram.collect_inits_and_teardowns(&worker, Global)
    });

    (state, snapshotter, touched_words)
}

fn execute_case<D: ir::DecodingOptions>(
    program: &[u32],
    initial_registers: [u32; 32],
    expected: &ExpectedOutcome,
) {
    let instructions = crate::ir::simple_instruction_set::preprocess_bytecode::<D, true>(program);
    let tape = SimpleTape::new(&instructions);
    let (state, snapshotter, touched_words) = finalize_state_with_snapshot(
        program,
        &tape,
        initial_registers,
        !expected.memory_checks.is_empty(),
    );

    assert_eq!(state.pc, expected.final_pc);
    assert_registers(&state, &expected.register_checks);
    if let Some(touched_words) = touched_words.as_ref() {
        assert_touched_words(touched_words, &expected.memory_checks);
    }

    let mut replay_state = snapshotter.initial_snapshot.state;
    let mut ram_log_buffers = snapshotter
        .reads_buffer
        .make_range(0..snapshotter.reads_buffer.len());
    let mut ram = ReplayerRam::<{ ROM_SECOND_WORD_BITS }> {
        ram_log: &mut ram_log_buffers,
    };

    ReplayerVM::<DelegationsAndFamiliesCounters>::replay_basic_unrolled::<_, _, Mersenne31Field>(
        &mut replay_state,
        &mut ram,
        &tape,
        &mut (),
        SINGLE_STEP_CYCLE_BOUND,
        &mut (),
    );

    assert_replay_matches(&state, &replay_state);
}

fn run_decode_rejection<D: ir::DecodingOptions>(program: &[u32], instruction: &str) {
    let result = catch_unwind(AssertUnwindSafe(|| {
        crate::ir::simple_instruction_set::preprocess_bytecode::<D, true>(program)
    }));
    assert!(
        result.is_err(),
        "expected `{instruction}` to be rejected during transpiler preprocessing",
    );
}

fn run_rejection<D: ir::DecodingOptions>(
    program: &[u32],
    initial_registers: [u32; 32],
    instruction: &str,
) {
    let instructions = crate::ir::simple_instruction_set::preprocess_bytecode::<D, true>(program);
    let tape = SimpleTape::new(&instructions);
    let mut state = initial_state(initial_registers);
    let mut ram =
        RamWithRomRegion::<{ ROM_SECOND_WORD_BITS }>::from_rom_content(program, RAM_BOUND_BYTES);

    let result = catch_unwind(AssertUnwindSafe(|| {
        let _ = VM::<DelegationsAndFamiliesCounters>::run_basic_unrolled::<_, _, _, Mersenne31Field>(
            &mut state,
            &mut ram,
            &mut (),
            &tape,
            SINGLE_STEP_CYCLE_BOUND,
            &mut (),
        );
    }));
    assert!(
        result.is_err(),
        "expected `{instruction}` to be rejected during VM execution",
    );
}

fn plan_test_vector_opcode(
    instruction: &str,
    program: &[u32],
    initial_registers: &[u32; 32],
    final_register: Option<(usize, u32)>,
) -> OpcodePlan {
    let tokens = instruction_tokens(instruction);
    let mnemonic = tokens
        .first()
        .unwrap_or_else(|| panic!("empty instruction `{instruction}`"));

    let mut expected = ExpectedOutcome {
        final_pc: 4,
        register_checks: final_register.into_iter().collect(),
        memory_checks: Vec::new(),
    };

    let reject = match mnemonic.as_str() {
        "jal" => {
            let rd = parse_register(&tokens[1]);
            let target = parse_value_token(&tokens[2]);
            expected.final_pc = target;
            if rd != 0 {
                expected.register_checks.push((rd, 4));
            }
            target & 0b11 != 0
        }
        "jalr" => {
            let rd = parse_register(&tokens[1]);
            let (imm, rs1) = parse_memory_operand(&tokens[2]);
            let target = initial_registers[rs1].wrapping_add(imm) & !1;
            expected.final_pc = target;
            if rd != 0 {
                expected.register_checks.push((rd, 4));
            }
            target & 0b11 != 0
        }
        "beq" | "bne" | "blt" | "bltu" | "bge" | "bgeu" => {
            let rs1 = parse_register(&tokens[1]);
            let rs2 = parse_register(&tokens[2]);
            let target = parse_value_token(&tokens[3]);
            let lhs = initial_registers[rs1];
            let rhs = initial_registers[rs2];
            let should_jump = match mnemonic.as_str() {
                "beq" => lhs == rhs,
                "bne" => lhs != rhs,
                "blt" => (lhs as i32) < (rhs as i32),
                "bltu" => lhs < rhs,
                "bge" => (lhs as i32) >= (rhs as i32),
                "bgeu" => lhs >= rhs,
                _ => unreachable!(),
            };
            if should_jump {
                expected.final_pc = target;
                target & 0b11 != 0
            } else {
                false
            }
        }
        "lw" => {
            let rd = parse_register(&tokens[1]);
            let (imm, rs1) = parse_memory_operand(&tokens[2]);
            let address = initial_registers[rs1].wrapping_add(imm);
            let aligned_address = address & !3;
            let value = initial_word(program, aligned_address);
            if rd != 0 {
                expected.register_checks.push((rd, value));
            }
            address & 0b11 != 0
        }
        "lh" | "lhu" => {
            let rd = parse_register(&tokens[1]);
            let (imm, rs1) = parse_memory_operand(&tokens[2]);
            let address = initial_registers[rs1].wrapping_add(imm);
            let aligned_address = address & !3;
            let mut value = initial_word(program, aligned_address) >> ((address & 0b11) * 8);
            value = if mnemonic == "lh" {
                (((value as u16) as i16) as i32) as u32
            } else {
                (value as u16) as u32
            };
            if rd != 0 {
                expected.register_checks.push((rd, value));
            }
            address & 0b1 != 0
        }
        "lb" | "lbu" => {
            let rd = parse_register(&tokens[1]);
            let (imm, rs1) = parse_memory_operand(&tokens[2]);
            let address = initial_registers[rs1].wrapping_add(imm);
            let aligned_address = address & !3;
            let mut value = initial_word(program, aligned_address) >> ((address & 0b11) * 8);
            value = if mnemonic == "lb" {
                (((value as u8) as i8) as i32) as u32
            } else {
                (value as u8) as u32
            };
            if rd != 0 {
                expected.register_checks.push((rd, value));
            }
            false
        }
        "sw" => {
            let rs2 = parse_register(&tokens[1]);
            let (imm, rs1) = parse_memory_operand(&tokens[2]);
            let address = initial_registers[rs1].wrapping_add(imm);
            expected
                .memory_checks
                .push((address, initial_registers[rs2]));
            address < ROM_BYTE_SIZE as u32 || address & 0b11 != 0
        }
        "sh" => {
            let rs2 = parse_register(&tokens[1]);
            let (imm, rs1) = parse_memory_operand(&tokens[2]);
            let address = initial_registers[rs1].wrapping_add(imm);
            let aligned_address = address & !3;
            let existing_value = initial_word(program, aligned_address);
            let mask = match address & 0b11 {
                0 => 0xffff_0000,
                2 => 0x0000_ffff,
                _ => 0,
            };
            let new_value = ((initial_registers[rs2] & 0xffff) << ((address & 0b11) * 8))
                | (existing_value & mask);
            expected.memory_checks.push((aligned_address, new_value));
            address < ROM_BYTE_SIZE as u32 || address & 0b1 != 0
        }
        "sb" => {
            let rs2 = parse_register(&tokens[1]);
            let (imm, rs1) = parse_memory_operand(&tokens[2]);
            let address = initial_registers[rs1].wrapping_add(imm);
            let aligned_address = address & !3;
            let existing_value = initial_word(program, aligned_address);
            let mask = match address & 0b11 {
                0 => 0xffff_ff00,
                1 => 0xffff_00ff,
                2 => 0xff00_ffff,
                3 => 0x00ff_ffff,
                _ => unreachable!(),
            };
            let new_value = ((initial_registers[rs2] & 0xff) << ((address & 0b11) * 8))
                | (existing_value & mask);
            expected.memory_checks.push((aligned_address, new_value));
            address < ROM_BYTE_SIZE as u32
        }
        "csrrw" | "csrrs" | "csrrc" | "csrrwi" | "csrrsi" | "csrrci" | "fence" | "ecall"
        | "ebreak" | "fadd.s" => {
            return OpcodePlan::Reject {
                target: MachineTarget::FullUnsigned,
                stage: RejectStage::Decode,
            };
        }
        _ => false,
    };

    if reject {
        return OpcodePlan::Reject {
            target: match mnemonic.as_str() {
                "div" | "rem" | "mulh" | "mulhsu" => MachineTarget::FullSigned,
                _ => MachineTarget::FullUnsigned,
            },
            stage: RejectStage::Execute,
        };
    }

    match mnemonic.as_str() {
        "add" | "addi" | "auipc" | "lui" | "sub" | "beq" | "bne" | "blt" | "bltu" | "bge"
        | "bgeu" | "jal" | "jalr" | "slt" | "slti" | "sltiu" | "sltu" | "and" | "andi" | "or"
        | "ori" | "sll" | "slli" | "sra" | "srai" | "srl" | "srli" | "xor" | "xori" | "mul"
        | "mulhu" | "divu" | "remu" | "lw" | "sw" | "lb" | "lbu" | "lh" | "lhu" | "sb" | "sh" => {
            OpcodePlan::Execute {
                target: MachineTarget::FullUnsigned,
                expected,
            }
        }
        "div" | "rem" | "mulh" | "mulhsu" => OpcodePlan::Execute {
            target: MachineTarget::FullSigned,
            expected,
        },
        other => panic!("unsupported opcode `{other}`"),
    }
}
