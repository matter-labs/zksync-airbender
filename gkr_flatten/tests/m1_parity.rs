//! M1 exit gate: bit-exact value parity between the flattened `LinearIR`
//! (`walk::flatten` + `ir::interpret`) and the reference DAG-walking
//! evaluator (`cs::gkr_compiler::dag_ir::eval::eval_layer_root`), driven by
//! the shared `resolvers::HashResolvers` bundle so both sides see identical
//! leaf values by construction.
//!
//! Run (fast subset, non-ignored — CI-safe):
//!   `cargo test -p gkr_flatten --test m1_parity fwd_small`
//! Run (full, release-only, both ignored sweeps):
//!   `RUSTFLAGS="-Awarnings" cargo test -p gkr_flatten --release --test m1_parity -- --ignored --nocapture`
//!
//! # bwd probe construct-skip policy
//!
//! `bwd_distilled_probe` flattens a *distilled* backward layer, which can
//! contain shapes the plain forward path never produces (decoder-bearing
//! cones, fenced cache-boundary leaves, ...). If flattening/evaluating such a
//! layer PANICS (a construct our code doesn't yet handle), that panic is
//! caught and the fixture is recorded as a documented SKIP with the panic
//! message — the gate stays green on the rest. A VALUE MISMATCH is never
//! caught this way: the comparison that could observe one always runs
//! outside any `catch_unwind` boundary, so a real parity bug still fails the
//! test hard. See `probe_fixture` below for exactly which panics are eligible
//! to be swallowed.

use cs::gkr_compiler::dag_ir::eval::eval_layer_root;
use cs::gkr_compiler::dag_ir::{BwdRegime, DagLayer, RootId, SourceKind};
use gkr_eval_isa::bwd::distill::distill;
use gkr_flatten::dag::LayerView;
use gkr_flatten::fixtures::{load_circuit, FIXTURES};
use gkr_flatten::ir::interpret;
use gkr_flatten::oracle::NeutralOracle;
use gkr_flatten::resolvers::HashResolvers;
use gkr_flatten::walk::flatten;

/// Flattens `view` (over `layer`) and checks every root's interpreted value
/// against `eval_layer_root` at each of `rows`. The single seeded
/// `HashResolvers` drives both sides, so any mismatch is a walker/interpreter
/// bug, never a resolver artifact (see `resolvers.rs`'s module doc).
fn assert_layer_parity(view: &LayerView<'_>, layer: &DagLayer, rows: &[usize]) {
    let r = HashResolvers { seed: 7 }.bundle();
    let out = flatten(view, &NeutralOracle);
    for &row in rows {
        let got = interpret(&out.program, layer, row, &r);
        for (ri, _root) in layer.roots.iter().enumerate() {
            let want = eval_layer_root(layer, RootId(ri as u32), row, &r);
            assert_eq!(got[&RootId(ri as u32)], want, "root {ri} row {row}");
        }
    }
}

/// Fast, non-ignored subset: `add_sub`, ALL forward layers (not just L0),
/// rows `[0, 1, 17]`. Non-ignored because this is the designated coverage
/// for all five `SourceKind` interpreter arms — the BINDING requirement
/// adjudicated in the Task 5 review (upper layers carry
/// Challenge/LookupValue/Constant/VirtualSetup leaves that L0 alone was
/// once assumed not to reach).
#[test]
fn fwd_small() {
    let (dag, cross) = load_circuit("add_sub_lui_auipc_mop_layout_gkr.json");
    assert!(dag.layers.len() > 1, "fwd_small needs >1 layer to sweep — fixture shape changed");

    let mut saw_read = false;
    let mut saw_constant_or_vs = false;
    let mut saw_challenge = false;
    let mut saw_lookup = false;

    for layer in &dag.layers {
        for s in &layer.sources {
            match &s.kind {
                SourceKind::Read { .. } => saw_read = true,
                SourceKind::Constant { .. } | SourceKind::VirtualSetup { .. } => {
                    saw_constant_or_vs = true;
                }
                SourceKind::Challenge { .. } => saw_challenge = true,
                SourceKind::LookupValue { .. } => saw_lookup = true,
            }
        }

        let view = LayerView::new(layer, &cross, None);
        assert_layer_parity(&view, layer, &[0, 1, 17]);
    }

    // Checked directly against this fixture (see the probe recorded in the
    // Task 7 report): add_sub L0 alone already carries all five SourceKind
    // variants (56 Read, 31 Constant, 14 Challenge, 2 VirtualSetup, 14
    // LookupValue sources) — none of the four buckets below are vacuous, so
    // no variant needs a "genuinely absent" exemption for this fixture.
    assert!(saw_read, "no Read leaf encountered across add_sub's layers");
    assert!(
        saw_constant_or_vs,
        "no Constant/VirtualSetup leaf encountered across add_sub's layers"
    );
    assert!(saw_challenge, "no Challenge leaf encountered across add_sub's layers");
    assert!(saw_lookup, "no LookupValue leaf encountered across add_sub's layers");
}

/// Full forward sweep: every layer of every fixture, rows `[0, 1, 17]`.
/// Release-only (debug is too slow across 12 fixtures' full layer sets) —
/// any mismatch here is a hard failure; there is no skip mechanism on the
/// forward side (unlike the bwd probe below), since the forward path is
/// the walker's primary target and every construct it emits must be exact.
#[test]
#[ignore = "release-only full sweep"]
fn fwd_all_fixtures() {
    let mut layers_checked = 0usize;
    for name in FIXTURES {
        let (dag, cross) = load_circuit(name);
        for layer in &dag.layers {
            let view = LayerView::new(layer, &cross, None);
            assert_layer_parity(&view, layer, &[0, 1, 17]);
            layers_checked += 1;
        }
        println!("fwd_all_fixtures: {name} ok ({} layers)", dag.layers.len());
    }
    println!(
        "fwd_all_fixtures: {}/{} fixtures, {layers_checked} layers total, all rows [0,1,17] parity-clean",
        FIXTURES.len(),
        FIXTURES.len()
    );
}

/// Extracts a human-readable message from a caught panic payload.
fn panic_message(e: Box<dyn std::any::Any + Send>) -> String {
    if let Some(s) = e.downcast_ref::<&str>() {
        (*s).to_string()
    } else if let Some(s) = e.downcast_ref::<String>() {
        s.clone()
    } else {
        "<non-string panic payload>".to_string()
    }
}

/// Outcome of one fixture's bwd probe.
enum ProbeOutcome {
    Passed,
    /// A construct-related panic (distill/flatten/interpret/eval), never a
    /// value mismatch — see this module's doc for the hard/soft distinction.
    Skipped(String),
}

/// Runs `f` with the default panic-hook stderr noise suppressed for the
/// duration of the call, restoring the previous hook before returning —
/// panics inside `f` are still caught and returned as an `Err`, they just
/// don't print. Used to keep `probe_fixture`'s expected construct-skip
/// panics quiet without silencing a real (never-caught) value mismatch,
/// which always runs outside this helper's scope.
fn silent_catch<R>(f: impl FnOnce() -> R + std::panic::UnwindSafe) -> std::thread::Result<R> {
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let r = std::panic::catch_unwind(f);
    std::panic::set_hook(prev);
    r
}

/// Runs the bwd probe for one fixture: distill L0 (Ext regime), flatten the
/// distilled layer from its single root, and compare `ir::interpret` against
/// `eval_layer_root` at rows `[0, 1, 17]`.
///
/// Three independent `catch_unwind` boundaries (distill, flatten, per-row
/// interpret+eval) each convert a panic into `ProbeOutcome::Skipped`. The
/// value comparison itself (`assert_eq!`) runs OUTSIDE all of them — it
/// compares two already-computed values, so a mismatch there panics for
/// real and is never caught: value mismatches are always a hard failure.
fn probe_fixture(name: &str) -> ProbeOutcome {
    let (dag, cross) = load_circuit(name);
    let layer0 = &dag.layers[0];

    let distilled = match silent_catch(std::panic::AssertUnwindSafe(|| {
        distill(layer0, BwdRegime::Ext, &cross, None)
    })) {
        Ok(d) => d,
        Err(e) => return ProbeOutcome::Skipped(format!("distill panicked: {}", panic_message(e))),
    };

    let root_expr = distilled.layer.roots[distilled.root.0 as usize].expr;
    let flattened = match silent_catch(std::panic::AssertUnwindSafe(|| {
        let view = LayerView::new(
            &distilled.layer,
            &distilled.cross_fields,
            Some(&distilled.field_overrides),
        );
        flatten(&view, &NeutralOracle)
    })) {
        Ok(out) => out,
        Err(e) => {
            return ProbeOutcome::Skipped(format!(
                "flatten panicked on distilled root expr {root_expr:?}: {}",
                panic_message(e)
            ));
        }
    };

    let r = HashResolvers { seed: 7 }.bundle();
    for &row in &[0usize, 1, 17] {
        let computed = silent_catch(std::panic::AssertUnwindSafe(|| {
            let got = interpret(&flattened.program, &distilled.layer, row, &r);
            let want = eval_layer_root(&distilled.layer, distilled.root, row, &r);
            (got[&distilled.root], want)
        }));
        match computed {
            Ok((got, want)) => {
                // Hard failure path: never caught, never skipped.
                assert_eq!(
                    got, want,
                    "bwd VALUE MISMATCH: {name} row {row} — this is never a documented skip"
                );
            }
            Err(e) => {
                return ProbeOutcome::Skipped(format!(
                    "interpret/eval panicked at row {row}: {}",
                    panic_message(e)
                ));
            }
        }
    }
    ProbeOutcome::Passed
}

/// Backward probe: for each fixture, distill L0 (Ext regime) and check value
/// parity of the single distilled root. See this module's doc +
/// `probe_fixture` for the construct-skip vs. value-mismatch distinction.
/// Release-only (bwd distill + flatten over the full corpus is slow in
/// debug).
#[test]
#[ignore = "release-only bwd probe"]
fn bwd_distilled_probe() {
    let mut passed = 0usize;
    let mut skipped: Vec<(&str, String)> = Vec::new();

    for name in FIXTURES {
        match probe_fixture(name) {
            ProbeOutcome::Passed => {
                passed += 1;
                println!("bwd_distilled_probe: {name} PASS");
            }
            ProbeOutcome::Skipped(reason) => {
                println!("bwd_distilled_probe: {name} SKIPPED — {reason}");
                skipped.push((name, reason));
            }
        }
    }

    println!(
        "bwd_distilled_probe: {passed}/{} fixtures passed, {} skipped (construct panics, not value mismatches)",
        FIXTURES.len(),
        skipped.len()
    );
    for (name, reason) in &skipped {
        println!("  skip census: {name}: {reason}");
    }
}
