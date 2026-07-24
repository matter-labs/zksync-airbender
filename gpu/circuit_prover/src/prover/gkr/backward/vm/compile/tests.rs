use std::collections::BTreeMap;

use cs::gkr_compiler::dag_ir::{BwdRegime, ReadPlace};
use gkr_eval_isa::bwd::disasm::disassemble_bwd_layer;
use gkr_eval_isa::fwd::encode::decode;
use gkr_eval_isa::fwd::isa::{Instr, OperandLine, Program};

use super::{load_add_sub_l0_case, AddSubBwdVmCase};
use crate::prover::gkr::forward::vm::desc::PROGRAM_CAP;

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

    println!("\n{text}");
    assert!(text.contains("budget = c2 (8 BF lanes)"));
    assert!(text.contains("batch_init = coeff[2]"));
    assert_eq!(batch_sinks, case.distilled.fragments.fragments.len());
    assert_eq!(batch_sinks, 144);
    assert!(!program.contains("AccInit"));
    assert!(program
        .lines()
        .filter(|line| line.contains("coeff["))
        .all(|line| line.contains("] batch +=")));
    assert!(text.contains("terminal = ReturnBatch"));
}

#[test]
fn add_sub_l0_c2_c16_program_census_matches_published_artifacts() {
    let expected_r0 = [
        977, 957, 951, 957, 957, 957, 957, 957, 957, 957, 957, 957, 957, 957, 957,
    ];
    let expected_ext = [
        992, 954, 957, 950, 968, 964, 962, 959, 957, 957, 957, 957, 957, 957, 957,
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
}
