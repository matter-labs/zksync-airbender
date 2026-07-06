//! Shape gates asserting the codegen-quality pass removed the F1-F5 waste from the
//! compiled add_sub L0 program (value-preserving; these assert the SHAPE win a
//! value-only gate cannot catch).
mod common;

use common::load_dag_sched;
use gkr_eval_isa::fwd::compile::compile_circuit;
use gkr_eval_isa::fwd::isa::{DstLine, Instr, MovDir, OperandLine};

const ADD_SUB: &str = "add_sub_lui_auipc_mop_layout_gkr.json";

fn add_sub_l0_instrs() -> Vec<Instr> {
    let (dag, sched, artifact) = load_dag_sched(ADD_SUB);
    let compiled = compile_circuit(&dag, &sched, &artifact).expect("compile add_sub");
    compiled
        .layers
        .into_iter()
        .next()
        .expect("layer 0")
        .program
        .instrs
}

/// F1: no `AccFromSrc(leaf); DstFromAcc` adjacent pair — every leaf that lands in a cell
/// is a single direct `DstFromSrc`. Covers ALL leaf source forms the rule handles
/// (codex-R4): Global (DRAM), Special (PEEK), Ldc (const/challenge) — not just Global,
/// since the original dump deferred PEEK leaves too.
#[test]
fn no_leaf_load_through_acc() {
    let instrs = add_sub_l0_instrs();
    for w in instrs.windows(2) {
        let load_leaf = matches!(&w[0], Instr::Mov { dir: MovDir::AccFromSrc, src: Some(s), .. }
            if matches!(s, OperandLine::Global { .. } | OperandLine::Special { .. } | OperandLine::Ldc { .. }));
        let store = matches!(
            &w[1],
            Instr::Mov {
                dir: MovDir::DstFromAcc,
                ..
            }
        );
        assert!(
            !(load_leaf && store),
            "F1 violated: AccFromSrc(leaf) immediately followed by DstFromAcc:\n  {:?}\n  {:?}",
            w[0],
            w[1]
        );
    }
}

/// F4: no `DstFromAcc(Smem c); AccFromSrc(Smem c)` adjacency (a spill immediately
/// reloaded — acc already holds it).
#[test]
fn no_spill_immediate_reload() {
    let instrs = add_sub_l0_instrs();
    for w in instrs.windows(2) {
        if let (
            Instr::Mov {
                dir: MovDir::DstFromAcc,
                dst: Some(DstLine::Smem { cell: c0 }),
                ..
            },
            Instr::Mov {
                dir: MovDir::AccFromSrc,
                src: Some(OperandLine::Smem { cell: c1 }),
                ..
            },
        ) = (&w[0], &w[1])
        {
            assert_ne!(
                c0, c1,
                "F4 violated: spill to cell {c0} immediately reloaded"
            );
        }
    }
}
