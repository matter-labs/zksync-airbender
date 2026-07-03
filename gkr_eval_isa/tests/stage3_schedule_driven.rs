//! Stage-3 target tests (plan Task 3, Step 1): the schedule-driven
//! `compile_circuit` loads + validates a committed schedule and produces a
//! value-correct forward program for every layer (spec §6.1 cone-value gate).
//!
//! Tests/ binary: lib items via `gkr_eval_isa::`, shared fixture helpers via
//! `mod common`.

mod common;
use common::{load_dag_sched, resolvers, sample_rows, schedule_path, SyntheticResolvers};

use gkr_eval_isa::fwd::compile::compile_circuit;
use gkr_eval_isa::fwd::interp::interpret_layer_row;

#[test]
fn compile_circuit_loads_validates_and_compiles_all_layers() {
    let name = "add_sub_lui_auipc_mop_layout_gkr.json";
    let artifact = common::load_fixture(name);
    let dag = cs::gkr_compiler::dag_ir::lower_dag(&artifact).unwrap();
    cs::gkr_compiler::dag_ir::validate(&dag).unwrap();
    let sched: cs::gkr_compiler::dag_ir::CircuitSchedule = serde_json::from_reader(
        std::fs::File::open(schedule_path("add_sub_lui_auipc_mop")).unwrap(),
    )
    .unwrap();
    cs::gkr_compiler::dag_ir::validate_circuit_schedule(&dag, &sched).unwrap();
    let compiled = compile_circuit(&dag, &sched, &artifact).unwrap();
    assert_eq!(compiled.layers.len(), dag.layers.len());
    assert_eq!(compiled.budget, 16);
}

// Cone-value gate (spec §6.1): every root's interpreted value == the eval.rs oracle.
#[test]
fn schedule_driven_compile_matches_eval_oracle_add_sub() {
    let name = "add_sub_lui_auipc_mop_layout_gkr.json";
    let (dag, sched, artifact) = load_dag_sched(name);
    let compiled = compile_circuit(&dag, &sched, &artifact).unwrap();
    let sr = SyntheticResolvers; // unit struct
    let n = dag.globals.trace_len;
    let mut checks = 0usize;
    for (li, layer) in dag.layers.iter().enumerate() {
        for &row in &sample_rows(n) {
            let outs =
                interpret_layer_row(&compiled.layers[li], layer, &resolvers(&sr), row).unwrap();
            for (rid, _) in &compiled.layers[li].root_outputs {
                let got = outs.by_root[rid];
                let want =
                    cs::gkr_compiler::dag_ir::eval_layer_root(layer, *rid, row, &resolvers(&sr));
                assert_eq!(got, want, "{name} L{li} root {rid:?} row {row}");
                checks += 1;
            }
        }
    }
    assert!(checks > 0, "vacuous");
}

// Corpus-wide value parity over all 11 committed b16 schedules (report evidence). The
// schedule stem differs from the fixture stem only for `inits_and_teardowns`
// (fixture: `..._preprocessed_layout_gkr.json`, schedule: `inits_and_teardowns`), so we
// map explicitly. Each fixture: lower → validate → load+validate committed schedule →
// compile_circuit → every exposed root's interp value == eval oracle at sampled rows.
#[test]
fn all_committed_schedules_compile_and_match_oracle() {
    // (fixture file, committed schedule stem)
    let corpus: &[(&str, &str)] = &[
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

    let sr = SyntheticResolvers;
    let mut passed = 0usize;
    let mut total_checks = 0usize;
    for (name, stem) in corpus {
        let artifact = common::load_fixture(name);
        let dag = cs::gkr_compiler::dag_ir::lower_dag(&artifact)
            .unwrap_or_else(|e| panic!("[{name}] lower_dag: {e}"));
        cs::gkr_compiler::dag_ir::validate(&dag)
            .unwrap_or_else(|e| panic!("[{name}] validate: {e}"));
        let sched: cs::gkr_compiler::dag_ir::CircuitSchedule = serde_json::from_reader(
            std::fs::File::open(schedule_path(stem))
                .unwrap_or_else(|e| panic!("[{name}] open schedule {stem}: {e}")),
        )
        .unwrap_or_else(|e| panic!("[{name}] parse schedule {stem}: {e}"));
        cs::gkr_compiler::dag_ir::validate_circuit_schedule(&dag, &sched)
            .unwrap_or_else(|e| panic!("[{name}] validate_circuit_schedule: {e}"));

        let compiled = compile_circuit(&dag, &sched, &artifact)
            .unwrap_or_else(|e| panic!("[{name}] compile_circuit: {e:?}"));
        assert_eq!(compiled.layers.len(), dag.layers.len(), "{name} layer count");

        let n = dag.globals.trace_len;
        for (li, layer) in dag.layers.iter().enumerate() {
            for &row in &sample_rows(n) {
                let outs = interpret_layer_row(&compiled.layers[li], layer, &resolvers(&sr), row)
                    .unwrap_or_else(|e| panic!("[{name}] L{li} row {row} interp: {e:?}"));
                for (rid, _) in &compiled.layers[li].root_outputs {
                    let got = outs.by_root[rid];
                    let want =
                        cs::gkr_compiler::dag_ir::eval_layer_root(layer, *rid, row, &resolvers(&sr));
                    assert_eq!(got, want, "{name} L{li} root {rid:?} row {row}");
                    total_checks += 1;
                }
            }
        }
        passed += 1;
        eprintln!("[stage3-parity] {name}: OK ({} layers)", compiled.layers.len());
    }
    assert_eq!(passed, corpus.len(), "all committed schedules must compile + match");
    assert!(total_checks > 0, "vacuous");
    eprintln!("[stage3-parity] {passed}/{} fixtures, {total_checks} root checks", corpus.len());
}
