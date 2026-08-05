use std::path::PathBuf;

use cs::gkr_compiler::GKRCircuitArtifact;
use field::baby_bear::base::BabyBearField;
use gkr_eval_ir::{DagCircuit, lower_dag, validate};
use gpu_gkr_compiler::{GpuResourceProfile, R0CompileError, compile_r0};

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
fn r0_compiles_every_layer_of_a_retained_circuit() {
    let dag = add_sub_dag();
    let bundle = compile_r0(&dag, &GpuResourceProfile::production()).unwrap();
    assert_eq!(bundle.layers.len(), dag.layers.len());
    assert!(
        bundle
            .layers
            .iter()
            .all(|program| program.target_depth() == 0)
    );
}

#[test]
fn r0_compilation_is_deterministic() {
    let dag = add_sub_dag();
    let profile = GpuResourceProfile::production();
    assert_eq!(
        compile_r0(&dag, &profile).unwrap(),
        compile_r0(&dag, &profile).unwrap()
    );
}

#[test]
fn r0_rejects_its_own_record_capacity() {
    let dag = add_sub_dag();
    let mut profile = GpuResourceProfile::production();
    profile.r0.max_records = 1;
    profile.r0.max_program_words = 4;
    assert!(matches!(
        compile_r0(&dag, &profile),
        Err(R0CompileError::Capacity {
            resource: "records",
            ..
        })
    ));
}
