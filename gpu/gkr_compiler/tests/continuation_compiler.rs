use std::path::PathBuf;

use cs::gkr_compiler::GKRCircuitArtifact;
use field::baby_bear::base::BabyBearField;
use gkr_eval_ir::{DagCircuit, lower_dag, validate};
use gpu_gkr_compiler::{ContinuationCompileError, GpuResourceProfile, compile_continuations};

fn add_sub_dag() -> DagCircuit {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_gkr.json");
    let artifact: GKRCircuitArtifact<BabyBearField> =
        serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap();
    let dag = lower_dag(&artifact).unwrap();
    validate(&dag).unwrap();
    dag
}

#[test]
fn continuations_compile_every_layer_of_a_retained_circuit() {
    let dag = add_sub_dag();
    let bundle = compile_continuations(&dag, &GpuResourceProfile::production()).unwrap();
    assert_eq!(bundle.layers.len(), dag.layers.len());
    assert!(
        bundle
            .layers
            .iter()
            .all(|program| program.publication_depth() == 3)
    );
}

#[test]
fn continuation_compilation_is_deterministic() {
    let dag = add_sub_dag();
    let profile = GpuResourceProfile::production();
    assert_eq!(
        compile_continuations(&dag, &profile).unwrap(),
        compile_continuations(&dag, &profile).unwrap()
    );
}

#[test]
fn continuation_rejects_its_own_record_capacity() {
    let dag = add_sub_dag();
    let mut profile = GpuResourceProfile::production();
    profile.continuations.max_records = 1;
    profile.continuations.max_program_words = 4;
    assert!(matches!(
        compile_continuations(&dag, &profile),
        Err(ContinuationCompileError::Capacity {
            resource: "records",
            ..
        })
    ));
}
