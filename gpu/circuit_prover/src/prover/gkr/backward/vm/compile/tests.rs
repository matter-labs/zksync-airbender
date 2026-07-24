use std::collections::BTreeMap;

use cs::gkr_compiler::dag_ir::{BwdRegime, ReadPlace};
use gkr_eval_isa::bwd::batch::{BATCH_COEFFICIENT_ONE, unpack_batch_dst};
use gkr_eval_isa::bwd::compile::BwdCompiledLayer;
use gkr_eval_isa::bwd::disasm::disassemble_bwd_layer;
use gkr_eval_isa::bwd::source::BwdSpecial;
use gkr_eval_isa::fwd::encode::decode;
use gkr_eval_isa::fwd::isa::{DstLine, Instr, MovDir, OperandLine, Program};

use super::{AddSubBwdVmCase, load_add_sub_l0_case};
use crate::prover::gkr::forward::vm::desc::PROGRAM_CAP;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct BatchProgramSummary {
    batch_sinks: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FragmentAccState {
    NeedsInit,
    Active,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum BatchProgramInvariantError {
    BatchingSpecialOperand { instruction: usize, desc: u16 },
    InvalidBatchSinkDescriptor { instruction: usize, desc: u16 },
    BatchSinkBeforeInit { instruction: usize },
    AccumulatorUseBeforeInit { instruction: usize },
    AccumulatorInitWithoutSource { instruction: usize },
    FinalInstructionNotBatchSink,
    BatchSinkCount { expected: usize, actual: usize },
}

fn validate_raw_batch_sink_program(
    compiled: &BwdCompiledLayer,
    expected_fragments: usize,
) -> Result<BatchProgramSummary, BatchProgramInvariantError> {
    let mut acc_state = FragmentAccState::NeedsInit;
    let mut batch_sinks = 0;

    for (instruction_index, instruction) in compiled.program.instrs.iter().enumerate() {
        let mut batching_special = None;
        visit_instruction_operands(instruction, |operand| {
            let OperandLine::Special { desc } = operand else {
                return;
            };
            if matches!(
                compiled.specials.get(*desc),
                Some(BwdSpecial::Coefficient { .. } | BwdSpecial::AccInit)
            ) {
                batching_special.get_or_insert(*desc);
            }
        });
        if let Some(desc) = batching_special {
            return Err(BatchProgramInvariantError::BatchingSpecialOperand {
                instruction: instruction_index,
                desc,
            });
        }

        if let Some(desc) = batch_sink_desc(instruction) {
            if acc_state == FragmentAccState::NeedsInit {
                return Err(BatchProgramInvariantError::BatchSinkBeforeInit {
                    instruction: instruction_index,
                });
            }
            if desc != BATCH_COEFFICIENT_ONE
                && !matches!(
                    compiled.specials.get(desc),
                    Some(BwdSpecial::Coefficient { .. })
                )
            {
                return Err(BatchProgramInvariantError::InvalidBatchSinkDescriptor {
                    instruction: instruction_index,
                    desc,
                });
            }
            batch_sinks += 1;
            continue;
        }

        match instruction {
            Instr::Mov {
                dir: MovDir::AccFromSrc,
                src: Some(_),
                ..
            } => acc_state = FragmentAccState::Active,
            Instr::Mov {
                dir: MovDir::AccFromSrc,
                src: None,
                ..
            } => {
                return Err(BatchProgramInvariantError::AccumulatorInitWithoutSource {
                    instruction: instruction_index,
                });
            }
            Instr::Add { .. }
            | Instr::Mul { .. }
            | Instr::Fma { .. }
            | Instr::Mov {
                dir: MovDir::DstFromAcc,
                ..
            } if acc_state == FragmentAccState::NeedsInit => {
                return Err(BatchProgramInvariantError::AccumulatorUseBeforeInit {
                    instruction: instruction_index,
                });
            }
            Instr::Add { .. }
            | Instr::Mul { .. }
            | Instr::Fma { .. }
            | Instr::Mov {
                dir: MovDir::DstFromAcc,
                ..
            }
            | Instr::Mov {
                dir: MovDir::DstFromSrc,
                ..
            } => {}
        }
    }

    if compiled
        .program
        .instrs
        .last()
        .and_then(batch_sink_desc)
        .is_none()
    {
        return Err(BatchProgramInvariantError::FinalInstructionNotBatchSink);
    }
    if batch_sinks != expected_fragments {
        return Err(BatchProgramInvariantError::BatchSinkCount {
            expected: expected_fragments,
            actual: batch_sinks,
        });
    }

    Ok(BatchProgramSummary { batch_sinks })
}

fn batch_sink_desc(instruction: &Instr) -> Option<u16> {
    let Instr::Mov {
        dir: MovDir::DstFromAcc,
        dst: Some(dst),
        src: None,
        ..
    } = instruction
    else {
        return None;
    };
    unpack_batch_dst(dst)
}

#[test]
fn raw_batch_sink_gate_rejects_coefficient_source_operand() {
    let case = load_add_sub_l0_case(BwdRegime::R0, 2);
    let mut compiled = case.compiled.compiled.clone();
    let desc = (0..compiled.specials.len())
        .map(|desc| u16::try_from(desc).expect("backward descriptor fits u16"))
        .find(|desc| {
            matches!(
                compiled.specials.get(*desc),
                Some(BwdSpecial::Coefficient { .. })
            )
        })
        .expect("add/sub batching program must carry a coefficient descriptor");
    let instruction = compiled
        .program
        .instrs
        .iter()
        .position(|instruction| {
            matches!(
                instruction,
                Instr::Mov {
                    dir: MovDir::AccFromSrc,
                    src: Some(_),
                    ..
                }
            )
        })
        .expect("add/sub batching program must initialize a fragment accumulator");
    let Instr::Mov { src, .. } = &mut compiled.program.instrs[instruction] else {
        unreachable!("located instruction is Mov");
    };
    *src = Some(OperandLine::Special { desc });

    assert_eq!(
        validate_raw_batch_sink_program(&compiled, case.fragment_order_len),
        Err(BatchProgramInvariantError::BatchingSpecialOperand { instruction, desc })
    );
}

#[test]
fn raw_batch_sink_gate_rejects_accumulator_use_without_initialization() {
    let case = load_add_sub_l0_case(BwdRegime::R0, 2);
    let mut compiled = case.compiled.compiled.clone();
    let instruction = compiled
        .program
        .instrs
        .iter()
        .position(|instruction| {
            matches!(
                instruction,
                Instr::Mov {
                    dir: MovDir::AccFromSrc,
                    src: Some(_),
                    ..
                }
            )
        })
        .expect("add/sub batching program must initialize acc");
    let Instr::Mov { field, .. } = &compiled.program.instrs[instruction] else {
        unreachable!("located instruction is Mov");
    };
    compiled.program.instrs[instruction] = Instr::Mul {
        field: *field,
        promote: false,
        negate_acc: true,
        operands: vec![],
    };

    assert_eq!(
        validate_raw_batch_sink_program(&compiled, case.fragment_order_len),
        Err(BatchProgramInvariantError::AccumulatorUseBeforeInit { instruction })
    );
}

#[test]
fn batching_sink_does_not_force_reloading_the_preserved_accumulator() {
    let case = load_add_sub_l0_case(BwdRegime::R0, 2);
    let instructions = &case.compiled.compiled.program.instrs;

    for (instruction, window) in instructions.windows(3).enumerate() {
        let sink = batch_sink_desc(&window[1]).is_some();
        let reloads_same_source = matches!(
            (&window[0], &window[2]),
            (
                Instr::Mov {
                    dir: MovDir::AccFromSrc,
                    field: before_field,
                    src: Some(before_src),
                    ..
                },
                Instr::Mov {
                    dir: MovDir::AccFromSrc,
                    field: after_field,
                    src: Some(after_src),
                    ..
                },
            ) if before_field == after_field && before_src == after_src
        );
        let reloads_just_stored_acc = matches!(
            (&window[0], &window[2]),
            (
                Instr::Mov {
                    dir: MovDir::DstFromAcc,
                    field: before_field,
                    dst: Some(DstLine::Smem { cell: before_cell }),
                    ..
                },
                Instr::Mov {
                    dir: MovDir::AccFromSrc,
                    field: after_field,
                    src: Some(OperandLine::Smem { cell: after_cell }),
                    ..
                },
            ) if before_field == after_field && before_cell == after_cell
        );

        assert!(
            !(sink && (reloads_same_source || reloads_just_stored_acc)),
            "instruction {} redundantly reloads the accumulator preserved by batching sink {}",
            instruction + 2,
            instruction + 1,
        );
    }
}

#[test]
#[ignore = "inspection tool: prints the add/sub L0 R0 c2 backward VM decompile"]
fn dump_add_sub_l0_r0_c2_backward_vm() {
    let case = load_add_sub_l0_case(BwdRegime::R0, 2);
    let text = disassemble_bwd_layer("add_sub layer-0 R0 c2 backward VM", &case.compiled.compiled);
    let program = text
        .split_once("--- PROGRAM (single-accumulator VM; `acc` is implicit) ---")
        .expect("backward VM program heading")
        .1
        .split_once("--- backings (slot -> storage region) ---")
        .expect("backward VM backings heading")
        .0;
    let batch_sinks = program
        .lines()
        .filter(|line| line.contains("] batch +="))
        .count();
    let raw_summary =
        validate_raw_batch_sink_program(&case.compiled.compiled, case.fragment_order_len)
            .expect("raw add/sub program must have independent batching-sink fragments");

    println!("\n{text}");
    assert!(text.contains("budget = c2 (8 BF lanes)"));
    assert!(text.contains("batch_init = coeff[2]"));
    assert_eq!(
        case.fragment_order_len,
        case.distilled.fragments.fragments.len()
    );
    assert_eq!(raw_summary.batch_sinks, case.fragment_order_len);
    assert_eq!(raw_summary.batch_sinks, 144);
    assert_eq!(batch_sinks, raw_summary.batch_sinks);
    assert!(text.contains("terminal = ReturnBatch"));
}

#[test]
fn add_sub_l0_c2_c16_program_census_matches_published_artifacts() {
    let expected_r0 = [
        921, 911, 905, 901, 901, 901, 901, 901, 901, 901, 901, 901, 901, 901, 901,
    ];
    let expected_ext = [
        946, 910, 913, 906, 922, 918, 916, 913, 911, 911, 911, 911, 911, 911, 911,
    ];
    for (regime, expected) in [(BwdRegime::R0, expected_r0), (BwdRegime::Ext, expected_ext)] {
        let got = (2..=16)
            .map(|budget| {
                let case = load_add_sub_l0_case(regime, budget);
                assert_case_program_bindings(&case);
                case.compiled.encoded.len()
            })
            .collect::<Vec<_>>();
        assert_eq!(got, expected);
    }
}

fn assert_case_program_bindings(case: &AddSubBwdVmCase) {
    assert_eq!(
        decode(&case.compiled.encoded).unwrap(),
        case.compiled.compiled.program
    );
    assert!(case.compiled.encoded.len() <= PROGRAM_CAP);
    assert_no_logical_sources(&case.compiled.compiled.program);
    assert_source_windows_are_bound(case);
}

fn assert_no_logical_sources(program: &Program) {
    visit_operands(program, |operand| match operand {
        OperandLine::LogicalGlobal { .. } | OperandLine::LogicalFold { .. } => {
            panic!("backward program has unbound logical source: {operand:?}")
        }
        OperandLine::Source { .. }
        | OperandLine::Smem { .. }
        | OperandLine::Ldc { .. }
        | OperandLine::Special { .. } => {}
    });
}

fn assert_source_windows_are_bound(case: &AddSubBwdVmCase) {
    let windows = &case.compiled.compiled.source_windows;
    let mut referenced = BTreeMap::<(u8, u8), ReadPlace>::new();
    for (window_index, window) in windows.windows().iter().enumerate() {
        let window_index = u8::try_from(window_index).expect("source window index fits u8");
        for absolute_column in window.referenced_columns() {
            let column = absolute_column
                .checked_sub(window.first_column)
                .and_then(|column| u8::try_from(column).ok())
                .expect("referenced source column fits its source window");
            let place = windows
                .resolve_read_place(window_index, column)
                .expect("source window must reverse to a read place");
            assert_eq!(referenced.insert((window_index, column), place), None);
        }
    }

    let mut first_accesses = BTreeMap::<(u8, u8), usize>::new();
    let mut uses = BTreeMap::<(u8, u8), usize>::new();
    visit_operands(&case.compiled.compiled.program, |operand| {
        if let OperandLine::Source {
            window,
            column,
            first_access,
        } = operand
        {
            assert!(
                referenced.contains_key(&(*window, *column)),
                "program source must reverse through source_windows"
            );
            *uses.entry((*window, *column)).or_default() += 1;
            if *first_access {
                *first_accesses.entry((*window, *column)).or_default() += 1;
            }
        }
    });

    for source in referenced.keys() {
        assert!(
            uses.contains_key(source),
            "source-window entry is not read by the program"
        );
        assert_eq!(
            first_accesses.get(source).copied().unwrap_or_default(),
            1,
            "each backward read source must have one first_access"
        );
    }
}

fn visit_operands(program: &Program, mut visit: impl FnMut(&OperandLine)) {
    for instruction in &program.instrs {
        visit_instruction_operands(instruction, &mut visit);
    }
}

fn visit_instruction_operands(instruction: &Instr, mut visit: impl FnMut(&OperandLine)) {
    match instruction {
        Instr::Add { operands, .. } | Instr::Mul { operands, .. } => {
            for operand in operands {
                visit(operand);
            }
        }
        Instr::Fma { pairs, .. } => {
            for (lhs, rhs) in pairs {
                visit(lhs);
                visit(rhs);
            }
        }
        Instr::Mov { src, .. } => {
            if let Some(source) = src {
                visit(source);
            }
        }
    }
}
