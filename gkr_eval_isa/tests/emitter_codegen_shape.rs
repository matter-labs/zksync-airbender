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

/// F3-a (MED-5, the real gate): no cache-root output is written by re-reading a HELD
/// smem cell — the deferred-hold signature `DstFromSrc(GlobalMaterialize CacheOutput) <-
/// Smem`. After F3, a leaf cache root is written eagerly from acc (`DstFromAcc`) or
/// directly from its source (`DstFromSrc <- Global/Special/Ldc`); compound cache roots
/// go through the compound-path `materialize_if_root(from_acc=true)` = `DstFromAcc`. So a
/// cache output sourced from an Smem cell is exactly the final-sweep hold this fix removes.
#[test]
fn no_cache_output_from_held_cell() {
    for instr in add_sub_l0_instrs() {
        if let Instr::Mov {
            dir: MovDir::DstFromSrc,
            dst: Some(DstLine::GlobalMaterialize { .. }),
            src: Some(OperandLine::Smem { .. }),
            ..
        } = instr
        {
            panic!("F3 violated: cache/output materialized from a held smem cell (deferred hold): {instr:?}");
        }
    }
}

/// F3-b: instruction-count reduction, pinned to the exact post-pass count.
#[test]
fn f3_reduces_instruction_count_vs_pre_pass_baseline() {
    let n = add_sub_l0_instrs().len();
    // Pre-pass add_sub L0 was 204 instrs (post site-gate, pre codegen pass). The full
    // codegen-quality pass (F1/F2/F4/F5 optimizer + F3 eager materialize) brings it to 166
    // — the corpus regen (Task 7) confirmed this is traffic-neutral (schedules unchanged;
    // only the emitted program is leaner). Pinned as an upper bound so a regression trips it.
    assert!(n <= 166, "expected add_sub L0 instr count <= 166 after codegen pass, got {n}");
}
