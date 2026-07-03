//! THE PARITY GATE (spec §14 oracle, §15 SP1 gate) — schedule-driven (post-T3b flip).
//!
//! For every committed b16 schedule this integration test:
//!   1. `lower_dag(&artifact)` + `validate(&dag)`,
//!   2. loads + `validate_circuit_schedule`s the committed b16 schedule, then
//!      `compile_circuit`,
//!   3. per layer: `validate_compiled` → `encode`/`decode` roundtrip (decoded
//!      `Program` must equal the original),
//!   4. for every exposed root at sampled rows, asserts the CPU interpreter
//!      (`interpret_layer_row`) equals the authoritative `eval_layer_root`
//!      bit-for-bit.
//!
//! The interpreter and `eval_layer_root` consume the SAME `SyntheticResolvers`
//! instance, so parity (not numeric correctness) is what this proves — exactly the
//! SP1 expressive-completeness gate. This adds `validate_compiled` + encode/decode
//! roundtrip coverage on top of the corpus value+oracle parity in
//! `stage3_schedule_driven.rs`.
//!
//! ─ T3b RETIREMENT NOTE ─ The old residency/budget-sweep tests were retired with the
//! self-scheduling residency engine they exercised (see
//! `.superpowers/sdd/task-3b-report.md`). The schedule-driven world compiles committed
//! b16 schedules only; there is no self-scheduling at arbitrary budgets, and the 11
//! `_no_caches` fixtures have no committed schedule so their parity is out of scope
//! (consistent with the no_caches deferral).

mod common;
use common::{load_fixture, resolvers, sample_rows, schedule_path, SyntheticResolvers};

use std::collections::BTreeMap;

use cs::gkr_compiler::dag_ir::{
    eval_layer_root, lower_dag, validate, validate_circuit_schedule, CircuitSchedule, RootId,
};

use gkr_eval_isa::fwd::compile::compile_circuit;
use gkr_eval_isa::fwd::context::RootOutput;
use gkr_eval_isa::fwd::encode::{decode, encode};
use gkr_eval_isa::fwd::interp::interpret_layer_row;
use gkr_eval_isa::fwd::validate::validate_compiled;

// ── corpus: (fixture file, committed-schedule stem) ─────────────────────────────
//
// The 11 `_layout_gkr.json` fixtures with a committed b16 schedule. The schedule stem
// differs from the fixture stem only for `inits_and_teardowns` (fixture:
// `..._preprocessed_layout_gkr.json`, schedule stem: `inits_and_teardowns`).

const CORPUS: &[(&str, &str)] = &[
    ("add_sub_lui_auipc_mop_layout_gkr.json", "add_sub_lui_auipc_mop"),
    ("bigint_with_extended_control_layout_gkr.json", "bigint_with_extended_control"),
    ("blake2_g_function_layout_gkr.json", "blake2_g_function"),
    ("blake2_with_extended_control_layout_gkr.json", "blake2_with_extended_control"),
    ("inits_and_teardowns_preprocessed_layout_gkr.json", "inits_and_teardowns"),
    ("jump_branch_slt_layout_gkr.json", "jump_branch_slt"),
    ("keccak_special5_layout_gkr.json", "keccak_special5"),
    ("mem_subword_only_layout_gkr.json", "mem_subword_only"),
    ("mem_word_only_layout_gkr.json", "mem_word_only"),
    ("shift_binop_layout_gkr.json", "shift_binop"),
    ("unsigned_mul_div_layout_gkr.json", "unsigned_mul_div"),
];

const ADD_SUB: &[(&str, &str)] = &[CORPUS[0]];

/// Compile one fixture from its committed b16 schedule and, per layer,
/// `validate_compiled` + encode/decode-roundtrip + value-parity at sampled rows.
/// Returns the number of (root, row) comparisons made.
fn check_fixture(name: &str, stem: &str) -> usize {
    let artifact = load_fixture(name);
    let dag = lower_dag(&artifact).unwrap_or_else(|e| panic!("[{name}] lower_dag: {e}"));
    validate(&dag).unwrap_or_else(|e| panic!("[{name}] validate(dag): {e}"));

    let sp = schedule_path(stem);
    let sched: CircuitSchedule = serde_json::from_reader(
        std::fs::File::open(&sp).unwrap_or_else(|e| panic!("open {sp:?}: {e}")),
    )
    .unwrap_or_else(|e| panic!("parse {sp:?}: {e}"));
    validate_circuit_schedule(&dag, &sched)
        .unwrap_or_else(|e| panic!("[{name}] validate_circuit_schedule: {e}"));

    let compiled = compile_circuit(&dag, &sched, &artifact)
        .unwrap_or_else(|e| panic!("[{name}] compile_circuit: {e:?}"));
    assert_eq!(
        compiled.layers.len(),
        dag.layers.len(),
        "[{name}] compiled/dag layer count mismatch"
    );

    let n = dag.globals.trace_len;
    let rows = sample_rows(n);
    let s = SyntheticResolvers;
    let r = resolvers(&s);

    let mut comparisons = 0usize;
    for (l, dag_layer) in dag.layers.iter().enumerate() {
        let cl = &compiled.layers[l];

        validate_compiled(cl, dag_layer)
            .unwrap_or_else(|e| panic!("[{name}] layer {l}: validate_compiled: {e:?}"));

        // Encode → decode roundtrip must reproduce the program exactly.
        let lanes =
            encode(&cl.program).unwrap_or_else(|e| panic!("[{name}] layer {l}: encode: {e:?}"));
        let decoded =
            decode(&lanes).unwrap_or_else(|e| panic!("[{name}] layer {l}: decode: {e:?}"));
        assert_eq!(decoded, cl.program, "[{name}] layer {l}: encode/decode roundtrip mismatch");

        // Parity at sampled rows for every exposed root.
        let by_root: BTreeMap<RootId, RootOutput> = cl.root_outputs.iter().cloned().collect();
        for &row in &rows {
            let got = interpret_layer_row(cl, dag_layer, &r, row)
                .unwrap_or_else(|e| panic!("[{name}] layer {l} row {row}: interp: {e:?}"));
            for (rid, _out) in &cl.root_outputs {
                let want = eval_layer_root(dag_layer, *rid, row, &r);
                let have = got.by_root[rid];
                assert_eq!(
                    have, want,
                    "[{name}] layer {l} root {rid:?} row {row}: interp != eval_layer_root oracle"
                );
                comparisons += 1;
            }
        }

        // Skipped roots must not appear in root_outputs, and their underlying Root must be
        // a materialized (Output/Cache) root.
        for skipped in &cl.skipped {
            assert!(
                !by_root.contains_key(skipped),
                "[{name}] layer {l}: skipped root {skipped:?} also in root_outputs"
            );
            assert!(
                dag_layer.roots[skipped.0 as usize].materialize.is_some(),
                "[{name}] layer {l}: skipped root {skipped:?} is not a materialized (Output) root"
            );
        }
    }
    comparisons
}

fn run_corpus(fixtures: &[(&str, &str)]) {
    let mut total = 0usize;
    for &(name, stem) in fixtures {
        let t0 = std::time::Instant::now();
        let comparisons = check_fixture(name, stem);
        eprintln!("[fwd_parity] {name} OK in {:?} ({comparisons} root comparisons)", t0.elapsed());
        total += comparisons;
    }
    assert!(total > 0, "parity gate compared 0 roots — vacuous pass");
}

// ── add_sub (Commit 1) ──────────────────────────────────────────────────────────

#[test]
fn parity_add_sub() {
    run_corpus(ADD_SUB);
}

// ── full gate over all 11 committed-schedule fixtures ───────────────────────────
//
// The SP1 forward-value gate: every fixture layer compiles from its committed b16
// schedule, validates, encode/decode-roundtrips, and the CPU interpreter matches
// `eval_layer_root` bit-for-bit at the sampled rows.

#[test]
fn parity_all_layout_gkr() {
    run_corpus(CORPUS);
}
