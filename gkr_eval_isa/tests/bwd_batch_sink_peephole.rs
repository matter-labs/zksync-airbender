//! Regression guard for `eval_plan::concrete`'s batching-sink peepholes.
//!
//! `elide_reloads_of_acc_preserved_by_batch_sink` (`src/eval_plan/concrete.rs`)
//! exists because `BatchAccumulate` updates the separate batch accumulator and
//! leaves the VM `acc` intact, so a reload straight after a sink is dead work. The
//! peephole deletes those reloads. `hoist_raw_source_batch_sinks`, which runs just
//! before it, moves a sink earlier to collapse a repeated read — and hoisting is
//! what can re-create the very pattern the elision just removed, one instruction
//! away from where it was checked.
//!
//! So this asserts the POSTCONDITION of the pair on a real compiled program rather
//! than either transform in isolation: after `concrete` lowering, no batching sink
//! is immediately followed by an ELIDABLE reload of what it preserved.
//!
//! **"Elidable" is not "identical-looking".** The peephole only removes a reload
//! whose re-read is provably idempotent — a logical global or fold line, an smem
//! cell, an `Ldc`, or a `VirtualSetup` special, whose value is a pure function of
//! the row. It deliberately keeps a reload of a raw `Source` line or of any other
//! special, because there re-reading is not merely redundant. The guard has to
//! carry that same filter or it asserts something the transform never promised.
//!
//! **Provenance, and a correction.** This guard shipped with the peephole in
//! `6a0b809e`, but it lived in `gpu_circuit_prover`'s backward-VM test module,
//! which the coefficient-term ISA retired. It has nothing to do with the GPU crate
//! — it is a property of THIS crate's lowering — so it moved here rather than being
//! dropped. Two things changed in the move:
//!
//!   * it now covers both regimes, since the sink peepholes are regime-independent;
//!     and
//!   * it now carries the source-class filter, which the original omitted. That
//!     omission was latent: at R0 `c2` — the only coordinate the original checked —
//!     no sink is followed by a non-elidable reload, so the over-assertion never
//!     fired. At Ext `c2` it does, on a `Special` that is not a `VirtualSetup`. The
//!     original guard would have reported a peephole bug that is not one.

mod common;

use gkr_eval_ir::lower_dag;
use gkr_eval_isa::BwdRegime;
use gkr_eval_isa::bwd::batch::unpack_batch_dst;
use gkr_eval_isa::bwd::compile::BwdCompiledLayer;
use gkr_eval_isa::bwd::distill::distill;
use gkr_eval_isa::bwd::source::BwdSpecial;
use gkr_eval_isa::eval_plan::{
    compile_backward_plan_artifact, load_backward_evaluation_artifact, select_backward_plan,
};
use gkr_eval_isa::fwd::compile::build_cross_layer_field_map;
use gkr_eval_isa::fwd::isa::{DstLine, Instr, MovDir, OperandLine};

const FIXTURE: &str = "add_sub_lui_auipc_mop_layout_gkr.json";

/// The published, certified plan for `add_sub` layer 0 replayed into a concrete
/// program — the same path production takes, so the peepholes under test really
/// ran.
fn compiled_add_sub_l0(regime: BwdRegime, budget_cells: usize) -> BwdCompiledLayer {
    let source = common::load_fixture(FIXTURE);
    let dag = lower_dag(&source).unwrap_or_else(|e| panic!("lower add/sub DAG: {e}"));
    let cross = build_cross_layer_field_map(&dag);
    let canonical = dag
        .layers
        .first()
        .cloned()
        .expect("add/sub artifact must have canonical layer 0");
    let distilled = distill(&canonical, regime, &cross, None);
    let trace_len = dag.globals.trace_len;

    let path = common::backward_artifact_path(FIXTURE);
    let plans = load_backward_evaluation_artifact(&path)
        .unwrap_or_else(|e| panic!("load {}: {e:?}", path.display()));
    let plan = select_backward_plan(&plans, 0, regime, budget_cells)
        .unwrap_or_else(|e| panic!("select add/sub L0 {regime:?} c{budget_cells}: {e:?}"));
    compile_backward_plan_artifact(&plans.circuit, 0, &canonical, &distilled, trace_len, plan)
        .unwrap_or_else(|e| panic!("replay add/sub L0 {regime:?} c{budget_cells}: {e:?}"))
        .compiled
        .compiled
}

/// The batch descriptor a `DstFromAcc` move with no source writes, if it is a
/// batching sink at all.
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
fn batching_sink_does_not_force_reloading_the_preserved_accumulator() {
    // The kept-reload count is ASSERTED, not printed. Two reasons.
    //
    // First, an unasserted number is invisible: a regression that changed the
    // filter's scope would only move a line of output nobody reads.
    //
    // Second, it pins WHICH arm of the filter below is actually load-bearing.
    // `concrete` lowering runs the peepholes (`:642`-`:643`) and only then calls
    // `bind_final_sources` (`:651`), which rewrites every `LogicalGlobal` and
    // `LogicalFold` operand into an `OperandLine::Source`. This guard reads that
    // bound program, so those two arms are unreachable HERE even though the
    // peephole itself sees them — the count is decided by `Source` and by the
    // non-`VirtualSetup` `Special`. Pinning it keeps that asymmetry on the
    // record: R0 keeps nothing, Ext keeps exactly the one `Special`.
    for (regime, expected_kept) in [(BwdRegime::R0, 0usize), (BwdRegime::Ext, 1usize)] {
        let compiled = compiled_add_sub_l0(regime, 2);
        let instructions = &compiled.program.instrs;
        // The guard is only meaningful if the program actually contains sinks.
        assert!(
            instructions.iter().any(|i| batch_sink_desc(i).is_some()),
            "{regime:?}: no batching sink in the program, so this guard proves nothing"
        );

        // Reloads the peephole deliberately leaves alone. Counted rather than
        // ignored, so its SCOPE is part of the record: if this ever reaches zero
        // for BOTH regimes, the filter has become untested and the simpler
        // unconditional postcondition would be the one to assert.
        let mut kept_non_idempotent = 0usize;

        for (instruction, window) in instructions.windows(3).enumerate() {
            if batch_sink_desc(&window[1]).is_none() {
                continue;
            }
            // The sink left `acc` alone, so re-reading the same source into it is
            // dead work — provided the re-read has no effect of its own.
            let same_source = match (&window[0], &window[2]) {
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
                ) if before_field == after_field && before_src == after_src => Some(before_src),
                _ => None,
            };
            // ...and so is reading back the cell `acc` was just spilled to. That one
            // is always idempotent: the store is right there in the window.
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

            let reloads_same_source = match same_source {
                None => false,
                Some(src) => {
                    let idempotent = match src {
                        OperandLine::LogicalGlobal { .. } | OperandLine::LogicalFold { .. } => true,
                        OperandLine::Smem { .. } | OperandLine::Ldc { .. } => true,
                        // A virtual-setup value is a pure function of the row, so
                        // re-reading it cannot differ. Any other special is opaque
                        // here and stays.
                        OperandLine::Special { desc } => {
                            matches!(
                                compiled.specials.get(*desc),
                                Some(BwdSpecial::VirtualSetup { .. })
                            )
                        }
                        // A raw source read is not free to repeat.
                        OperandLine::Source { .. } => false,
                    };
                    if !idempotent {
                        kept_non_idempotent += 1;
                    }
                    idempotent
                }
            };

            assert!(
                !(reloads_same_source || reloads_just_stored_acc),
                "{regime:?}: instruction {} redundantly reloads the accumulator \
                 preserved by batching sink {}",
                instruction + 2,
                instruction + 1,
            );
        }

        assert_eq!(
            kept_non_idempotent, expected_kept,
            "{regime:?} c2: expected the filter to keep {expected_kept} non-idempotent \
             sink-adjacent reload(s), found {kept_non_idempotent}"
        );
    }
}
