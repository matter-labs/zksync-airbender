use std::path::PathBuf;

use cs::gkr_compiler::GKRCircuitArtifact;
use field::proth120::Proth120;
use gpu_gkr_compiler::{
    compile_forward_with_model, geometry::validate_forward_proth120, parse_forward_artifact,
    ElementModel, FieldTag,
};

#[test]
fn proth120_unified_forward_native_caps() {
    let directory = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../cs/compiled_circuits");
    let layout: GKRCircuitArtifact<Proth120> = serde_json::from_slice(
        &std::fs::read(directory.join("unified_reduced_machine_layout_gkr_proth120.json")).unwrap(),
    )
    .unwrap();
    let dag = gkr_eval_ir::lower_dag(&layout).unwrap();
    let artifact_path = std::env::var_os("M6_FORWARD_ARTIFACT")
        .map(PathBuf::from)
        .unwrap_or_else(|| directory.join("unified_reduced_machine_schedule_b4_gkr_proth120.json"));
    let artifact = parse_forward_artifact(
        &std::fs::read(&artifact_path).unwrap(),
        artifact_path.to_str().unwrap(),
    )
    .unwrap();
    let expected_budget = std::env::var("M6_FORWARD_BUDGET")
        .map(|value| value.parse().unwrap())
        .unwrap_or(4);
    assert_eq!(artifact.budget_buckets, expected_budget);
    assert_eq!(artifact.field, Some(FieldTag::Proth120));
    let forward = compile_forward_with_model(&dag, &artifact, ElementModel::PROTH120).unwrap();
    match validate_forward_proth120(&dag, &forward, &layout) {
        Ok(report) => {
            println!(
                "M6_FORWARD_GEOMETRY {}",
                serde_json::to_string(&report).unwrap()
            );
            assert_eq!(report.layers, 5);
            assert_eq!(report.stride_bytes, (1 << 22) * 16);
            assert_eq!(report.canonical_dynamic_columns, 89);
            assert_eq!(report.aliases, 31);
            for pair in report.backings.windows(2) {
                let end = pair[0].base + pair[0].columns * pair[0].stride_bytes as usize;
                assert!(end < pair[1].base);
            }
            assert_eq!(report.backings[0].matrix, "Raw");
            assert_eq!(report.backings[0].columns, 104);
        }
        Err(failure) => {
            if let Some(report) = &failure.report {
                println!(
                    "M6_FORWARD_GEOMETRY {}",
                    serde_json::to_string(report).unwrap()
                );
            }
            panic!("{failure}");
        }
    }
    let mut oversized = forward.clone();
    let instruction = oversized.layers[0].program.instrs[0].clone();
    oversized.layers[0]
        .program
        .instrs
        .extend(std::iter::repeat_n(instruction, 12_288));
    let failure = validate_forward_proth120(&dag, &oversized, &layout).unwrap_err();
    assert!(failure.message.contains("program lanes") && failure.message.contains("cap 12288"));
    let report = failure.report.unwrap();
    assert!(report.program_lanes > 12_288);
    assert_eq!(report.constants, 3);
    let mut bad_stride = layout.clone();
    bad_stride.trace_len = 1 << 28;
    assert!(validate_forward_proth120(&dag, &forward, &bad_stride)
        .unwrap_err()
        .message
        .contains("stride_bytes exceeds u32"));
}
