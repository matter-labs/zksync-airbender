mod common;

use std::collections::BTreeMap;
use std::io::Write;
use std::ops::RangeInclusive;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex, OnceLock};
use std::time::{Duration, Instant};

use cs::gkr_compiler::dag_ir::{BwdRegime, DagLayer, ReadPlace, VirtualSetupKind};
use gkr_eval_isa::bwd::distill::{DistilledLayer, distill};
use gkr_eval_isa::bwd::source::{BwdSpecial, BwdSpecialTable, OriginLeaf};
use gkr_eval_isa::eval_plan::backward_search::problem::build_backward_search_problem;
use gkr_eval_isa::eval_plan::backward_search::{
    ProductionPagingSolver, ProductionSearchIdentity, search_production_backward,
    solve_production_paging,
};
use gkr_eval_isa::eval_plan::{
    BackwardArtifactCoordinate, BackwardArtifactError, BackwardEvaluationCircuitArtifact,
    BackwardLayerArtifact, BackwardPlanArtifact, BackwardRegimeArtifact,
    BackwardRegimeChainProgress, BackwardScoreArtifact, CanonicalU128, DomainCertificate,
    SourceCostArtifact, capture_backward_plan_artifact, compile_backward_plan_artifact,
    load_backward_evaluation_artifact, produce_backward_regime_chain_with_progress,
    publish_backward_evaluation_artifact, select_backward_plan,
};
use gkr_eval_isa::fwd::encode::encode;
use gkr_eval_isa::fwd::source::virtual_setup_kind_code;
use rayon::prelude::*;

const R0_FEASIBILITY_FIXTURES: &[&str] = &[
    "bigint_with_extended_control_layout_gkr.json",
    "blake2_with_extended_control_layout_gkr.json",
    "keccak_special5_layout_gkr.json",
    "unified_reduced_machine_layout_gkr.json",
];

fn sample_plan(budget_cells: usize) -> BackwardPlanArtifact {
    BackwardPlanArtifact {
        budget_cells,
        problem: DomainCertificate {
            count: 0,
            digest: [0; 4],
        },
        fragment_order: vec![],
        retained_demands: vec![],
        expected_score: BackwardScoreArtifact {
            infeasible: false,
            whole_pass_dram_bytes: 0.into(),
            primitive_source_ops: 0.into(),
            instructions: 0,
            encoded_lanes: 0,
            arithmetic_ops: 0,
        },
        expected_paging: gkr_eval_isa::eval_plan::BackwardPagingCertificateArtifact {
            actions_consumed: 0,
            diverged: None,
            refused_retains: 0,
            predicted_source_reads: 0,
            realized_source_reads: 0,
            predicted_read_cost: SourceCostArtifact::default(),
            realized_read_cost: SourceCostArtifact::default(),
            fixed_write_cost: SourceCostArtifact::default(),
            peak_live_lanes: 0,
            placement_relocations: 0,
        },
        instruction_digest: [0; 4],
        encoded_digest: [0; 4],
    }
}

fn sample_regime() -> BackwardRegimeArtifact {
    BackwardRegimeArtifact {
        plans: (2..=16).map(sample_plan).collect(),
    }
}

fn sample_artifact(layers: Vec<BackwardLayerArtifact>) -> BackwardEvaluationCircuitArtifact {
    BackwardEvaluationCircuitArtifact {
        circuit: "fixture".to_owned(),
        layout_fixture: "fixture_layout".to_owned(),
        layers,
    }
}

struct CapturedRealPlan {
    artifact: BackwardPlanArtifact,
    encoded: Vec<u16>,
    oracle_instruction_digest: [u64; 4],
    oracle_encoded_digest: [u64; 4],
}

fn captured_real_plan() -> &'static CapturedRealPlan {
    static CAPTURED: OnceLock<CapturedRealPlan> = OnceLock::new();
    CAPTURED.get_or_init(|| {
        let fixture = common::FIXTURES[0];
        let source = common::load_fixture(fixture);
        let dag = cs::gkr_compiler::dag_ir::lower_dag(&source).unwrap();
        let (layer_index, layer, cross) = common::layers_with_bwd_roots(fixture)
            .next()
            .expect("fixture has a backward-bearing layer");
        let distilled = distill(&layer, BwdRegime::Ext, &cross, None);
        let searched = search_production_backward(
            &ProductionSearchIdentity {
                circuit: "add_sub_lui_auipc_mop".to_owned(),
                layout_fixture: fixture.to_owned(),
                layer: layer_index,
                regime: BwdRegime::Ext,
            },
            &layer,
            &distilled,
            dag.globals.trace_len,
            4,
            None,
        )
        .unwrap();
        let encoded = searched.candidate.compiled.encoded.clone();
        let instruction_lanes = encode(&searched.candidate.compiled.compiled.program).unwrap();
        let instruction_bytes = oracle_instruction_bytes(
            &instruction_lanes,
            &searched.candidate.compiled.compiled.specials,
        );
        let artifact = capture_backward_plan_artifact(&searched).unwrap();
        CapturedRealPlan {
            artifact,
            oracle_instruction_digest: oracle_four_lane_digest(&instruction_bytes),
            oracle_encoded_digest: oracle_four_lane_digest(&oracle_encoded_bytes(&encoded)),
            encoded,
        }
    })
}

fn oracle_encoded_bytes(encoded: &[u16]) -> Vec<u8> {
    encoded.iter().flat_map(|lane| lane.to_le_bytes()).collect()
}

fn oracle_instruction_bytes(encoded: &[u16], specials: &BwdSpecialTable) -> Vec<u8> {
    let mut bytes = oracle_encoded_bytes(encoded);
    bytes.extend_from_slice(&(specials.len() as u64).to_le_bytes());
    for index in 0..specials.len() {
        oracle_serialize_bwd_special(
            &mut bytes,
            specials
                .get(index as u16)
                .expect("oracle descriptor index must resolve"),
        );
    }
    bytes
}

fn oracle_serialize_bwd_special(bytes: &mut Vec<u8>, special: &BwdSpecial) {
    match special {
        BwdSpecial::FoldSource { origin } => {
            bytes.push(0);
            match origin {
                OriginLeaf::Read(place) => {
                    bytes.push(0);
                    oracle_serialize_read_place(bytes, place);
                }
                OriginLeaf::VirtualSetup { kind } => {
                    bytes.push(1);
                    bytes.extend_from_slice(&virtual_setup_kind_code(kind).to_le_bytes());
                }
            }
        }
        BwdSpecial::VirtualSetup { kind } => {
            bytes.push(1);
            bytes.extend_from_slice(&virtual_setup_kind_code(kind).to_le_bytes());
        }
        BwdSpecial::Coefficient { fragment } => {
            bytes.push(2);
            bytes.extend_from_slice(&fragment.to_le_bytes());
        }
        BwdSpecial::AccInit => bytes.push(3),
    }
}

fn oracle_serialize_read_place(bytes: &mut Vec<u8>, place: &ReadPlace) {
    match place {
        ReadPlace::BaseLayerMemory { column } => {
            bytes.push(0);
            bytes.extend_from_slice(&(*column as u64).to_le_bytes());
        }
        ReadPlace::BaseLayerWitness { column } => {
            bytes.push(1);
            bytes.extend_from_slice(&(*column as u64).to_le_bytes());
        }
        ReadPlace::Setup { column } => {
            bytes.push(2);
            bytes.extend_from_slice(&(*column as u64).to_le_bytes());
        }
        ReadPlace::Scratch { slot } => {
            bytes.push(3);
            bytes.extend_from_slice(&(*slot as u64).to_le_bytes());
        }
        ReadPlace::LayerOutput { layer, offset } => {
            bytes.push(4);
            bytes.extend_from_slice(&(*layer as u64).to_le_bytes());
            bytes.extend_from_slice(&(*offset as u64).to_le_bytes());
        }
        ReadPlace::CacheOutput { layer, offset } => {
            bytes.push(5);
            bytes.extend_from_slice(&(*layer as u64).to_le_bytes());
            bytes.extend_from_slice(&(*offset as u64).to_le_bytes());
        }
    }
}

fn oracle_four_lane_digest(bytes: &[u8]) -> [u64; 4] {
    let bytes = serde_json::to_vec(bytes).unwrap();
    let mut digest = [
        0xcbf2_9ce4_8422_2325u64,
        0x8422_2325_cbf2_9ce4,
        0x6a09_e667_f3bc_c909,
        0xbb67_ae85_84ca_a73b,
    ];
    let primes = [
        0x0000_0100_0000_01b3u64,
        0x9e37_79b1_85eb_ca87,
        0xc2b2_ae3d_27d4_eb4f,
        0x1656_67b1_9e37_79f9,
    ];
    for byte in bytes {
        for lane in 0..digest.len() {
            digest[lane] ^= u64::from(byte).wrapping_add((lane as u64) << 8);
            digest[lane] = digest[lane].wrapping_mul(primes[lane]);
        }
    }
    digest
}

fn replay_real_plan(
    artifact: &BackwardPlanArtifact,
) -> Result<
    gkr_eval_isa::eval_plan::backward_search::CertifiedBackwardCandidate,
    BackwardArtifactError,
> {
    let fixture = common::FIXTURES[0];
    let source = common::load_fixture(fixture);
    let dag = cs::gkr_compiler::dag_ir::lower_dag(&source).unwrap();
    let (layer_index, layer, cross) = common::layers_with_bwd_roots(fixture)
        .next()
        .expect("fixture has a backward-bearing layer");
    let distilled = distill(&layer, BwdRegime::Ext, &cross, None);
    compile_backward_plan_artifact(
        "add_sub_lui_auipc_mop",
        layer_index,
        &layer,
        &distilled,
        dag.globals.trace_len,
        artifact,
    )
}

#[test]
fn captured_plan_replays_without_search_or_pager() {
    let captured = captured_real_plan();
    let replayed = replay_real_plan(&captured.artifact).unwrap();
    assert_eq!(
        BackwardScoreArtifact::from_score(&replayed.score),
        captured.artifact.expected_score
    );
    assert_eq!(replayed.compiled.encoded, captured.encoded);
}

#[test]
fn captured_plan_digests_match_an_independent_backend_neutrality_oracle() {
    let captured = captured_real_plan();
    assert_eq!(
        captured.artifact.instruction_digest,
        captured.oracle_instruction_digest
    );
    assert_eq!(
        captured.artifact.encoded_digest,
        captured.oracle_encoded_digest
    );
}

#[test]
fn backend_neutrality_oracle_pins_special_lengths_tags_fields_and_endianness() {
    let mut specials = BwdSpecialTable::default();
    specials.intern(BwdSpecial::FoldSource {
        origin: OriginLeaf::Read(ReadPlace::BaseLayerMemory { column: 0x0102 }),
    });
    specials.intern(BwdSpecial::FoldSource {
        origin: OriginLeaf::Read(ReadPlace::BaseLayerWitness { column: 0x0304 }),
    });
    specials.intern(BwdSpecial::FoldSource {
        origin: OriginLeaf::Read(ReadPlace::Setup { column: 0x0506 }),
    });
    specials.intern(BwdSpecial::FoldSource {
        origin: OriginLeaf::Read(ReadPlace::Scratch { slot: 0x0708 }),
    });
    specials.intern(BwdSpecial::FoldSource {
        origin: OriginLeaf::Read(ReadPlace::LayerOutput {
            layer: 0x090a,
            offset: 0x0b0c,
        }),
    });
    specials.intern(BwdSpecial::FoldSource {
        origin: OriginLeaf::Read(ReadPlace::CacheOutput {
            layer: 0x0d0e,
            offset: 0x0f10,
        }),
    });
    specials.intern(BwdSpecial::FoldSource {
        origin: OriginLeaf::VirtualSetup {
            kind: VirtualSetupKind::RangeCheckTimestamp,
        },
    });
    specials.intern(BwdSpecial::VirtualSetup {
        kind: VirtualSetupKind::InitsAndTeardownsHigh,
    });
    specials.intern(BwdSpecial::Coefficient {
        fragment: 0x1413_1211,
    });
    specials.intern(BwdSpecial::AccInit);

    let bytes = oracle_instruction_bytes(&[0x0201, 0x0403], &specials);
    let mut cursor = 0usize;
    let mut take = |expected: &[u8]| {
        assert_eq!(&bytes[cursor..cursor + expected.len()], expected);
        cursor += expected.len();
    };
    take(&[0x01, 0x02, 0x03, 0x04]);
    take(&10u64.to_le_bytes());
    take(&[0, 0, 0]);
    take(&0x0102u64.to_le_bytes());
    take(&[0, 0, 1]);
    take(&0x0304u64.to_le_bytes());
    take(&[0, 0, 2]);
    take(&0x0506u64.to_le_bytes());
    take(&[0, 0, 3]);
    take(&0x0708u64.to_le_bytes());
    take(&[0, 0, 4]);
    take(&0x090au64.to_le_bytes());
    take(&0x0b0cu64.to_le_bytes());
    take(&[0, 0, 5]);
    take(&0x0d0eu64.to_le_bytes());
    take(&0x0f10u64.to_le_bytes());
    take(&[0, 1]);
    take(&1u32.to_le_bytes());
    take(&[1]);
    take(&3u32.to_le_bytes());
    take(&[2]);
    take(&0x1413_1211u32.to_le_bytes());
    take(&[3]);
    assert_eq!(cursor, bytes.len());
}

#[test]
fn artifact_replay_rejects_stale_problem_score_paging_and_output_certificates() {
    let captured = &captured_real_plan().artifact;

    let mut artifact = captured.clone();
    artifact.problem.digest[0] ^= 1;
    assert!(matches!(
        replay_real_plan(&artifact),
        Err(BackwardArtifactError::ProblemCertificateMismatch {
            circuit,
            layer: 0,
            regime: BwdRegime::Ext,
            budget_cells: 4,
        }) if circuit == "add_sub_lui_auipc_mop"
    ));

    let mut artifact = captured.clone();
    artifact.expected_score.instructions += 1;
    assert!(matches!(
        replay_real_plan(&artifact),
        Err(BackwardArtifactError::ScoreCertificateMismatch {
            circuit,
            layer: 0,
            regime: BwdRegime::Ext,
            budget_cells: 4,
        }) if circuit == "add_sub_lui_auipc_mop"
    ));

    let mut artifact = captured.clone();
    artifact.expected_paging.actions_consumed += 1;
    assert!(matches!(
        replay_real_plan(&artifact),
        Err(BackwardArtifactError::PagingCertificateMismatch {
            circuit,
            layer: 0,
            regime: BwdRegime::Ext,
            budget_cells: 4,
        }) if circuit == "add_sub_lui_auipc_mop"
    ));

    let mut artifact = captured.clone();
    artifact.instruction_digest[0] ^= 1;
    assert!(matches!(
        replay_real_plan(&artifact),
        Err(BackwardArtifactError::InstructionDigestMismatch {
            circuit,
            layer: 0,
            regime: BwdRegime::Ext,
            budget_cells: 4,
        }) if circuit == "add_sub_lui_auipc_mop"
    ));

    let mut artifact = captured.clone();
    artifact.encoded_digest[0] ^= 1;
    assert!(matches!(
        replay_real_plan(&artifact),
        Err(BackwardArtifactError::EncodedDigestMismatch {
            circuit,
            layer: 0,
            regime: BwdRegime::Ext,
            budget_cells: 4,
        }) if circuit == "add_sub_lui_auipc_mop"
    ));
}

#[test]
fn artifact_replay_rejects_malformed_fragment_order_and_retained_positions() {
    let captured = &captured_real_plan().artifact;

    let mut artifact = captured.clone();
    artifact.fragment_order[1] = artifact.fragment_order[0];
    assert!(matches!(
        replay_real_plan(&artifact),
        Err(BackwardArtifactError::InvalidFragmentPermutation {
            circuit,
            layer: 0,
            regime: BwdRegime::Ext,
            budget_cells: 4,
        }) if circuit == "add_sub_lui_auipc_mop"
    ));

    let mut artifact = captured.clone();
    artifact.fragment_order.pop();
    assert!(matches!(
        replay_real_plan(&artifact),
        Err(BackwardArtifactError::InvalidFragmentPermutation {
            circuit,
            layer: 0,
            regime: BwdRegime::Ext,
            budget_cells: 4,
        }) if circuit == "add_sub_lui_auipc_mop"
    ));

    let mut artifact = captured.clone();
    artifact.retained_demands.push(u32::MAX);
    assert!(matches!(
        replay_real_plan(&artifact),
        Err(BackwardArtifactError::InvalidRetainedDemand {
            circuit,
            layer: 0,
            regime: BwdRegime::Ext,
            budget_cells: 4,
            position,
        }) if circuit == "add_sub_lui_auipc_mop" && position == u32::MAX as usize
    ));
}

#[test]
fn backward_artifact_selection_is_exact_and_rejects_c17() {
    let regime = sample_regime();
    let artifact = sample_artifact(vec![BackwardLayerArtifact {
        layer: 5,
        r0: regime.clone(),
        ext: regime,
    }]);
    assert_eq!(
        select_backward_plan(&artifact, 5, BwdRegime::Ext, 4)
            .unwrap()
            .budget_cells,
        4
    );
    assert!(matches!(
        select_backward_plan(&artifact, 5, BwdRegime::Ext, 17),
        Err(BackwardArtifactError::BudgetOutOfRange {
            circuit,
            layer: 5,
            regime: BwdRegime::Ext,
            budget_cells: 17,
        }) if circuit == "fixture"
    ));
}

#[test]
fn backward_artifact_selection_reports_the_full_requested_coordinate() {
    let regime = sample_regime();
    let artifact = sample_artifact(vec![BackwardLayerArtifact {
        layer: 5,
        r0: regime.clone(),
        ext: regime,
    }]);
    assert!(matches!(
        select_backward_plan(&artifact, 6, BwdRegime::R0, 3),
        Err(BackwardArtifactError::MissingLayer {
            coordinate: BackwardArtifactCoordinate {
                circuit,
                layer: 6,
                regime: BwdRegime::R0,
                budget_cells: 3,
            },
        }) if circuit == "fixture"
    ));

    let mut malformed = artifact.clone();
    malformed.layers[0].ext.plans.remove(2);
    assert!(matches!(
        select_backward_plan(&malformed, 5, BwdRegime::Ext, 4),
        Err(BackwardArtifactError::InvalidBudgetCoverage {
            coordinate: BackwardArtifactCoordinate {
                circuit,
                layer: 5,
                regime: BwdRegime::Ext,
                budget_cells: 4,
            },
        }) if circuit == "fixture"
    ));

    let mut missing = artifact;
    missing.layers[0].r0.plans.pop();
    assert!(matches!(
        select_backward_plan(&missing, 5, BwdRegime::R0, 16),
        Err(BackwardArtifactError::InvalidBudgetCoverage {
            coordinate: BackwardArtifactCoordinate {
                circuit,
                layer: 5,
                regime: BwdRegime::R0,
                budget_cells: 16,
            },
        }) if circuit == "fixture"
    ));
}

#[test]
fn canonical_u128_json_is_a_decimal_string_and_round_trips_the_maximum() {
    let maximum = CanonicalU128::from(u128::MAX);
    assert_eq!(
        serde_json::to_string(&maximum).unwrap(),
        format!("\"{}\"", u128::MAX)
    );
    assert_eq!(
        serde_json::from_str::<CanonicalU128>(&serde_json::to_string(&maximum).unwrap()).unwrap(),
        maximum
    );
}

#[test]
fn canonical_u128_rejects_noncanonical_decimal_spellings() {
    for spelling in ["-1", "+1", "01", "", " 1"] {
        assert!(serde_json::from_str::<CanonicalU128>(&format!("\"{spelling}\"")).is_err());
    }
}

#[test]
fn backward_artifact_requires_strictly_increasing_layers() {
    let regime = sample_regime();
    let artifact = sample_artifact(vec![
        BackwardLayerArtifact {
            layer: 1,
            r0: regime.clone(),
            ext: regime.clone(),
        },
        BackwardLayerArtifact {
            layer: 1,
            r0: regime.clone(),
            ext: regime,
        },
    ]);
    assert!(matches!(
        artifact.validate_self_consistency(),
        Err(gkr_eval_isa::eval_plan::BackwardArtifactError::DuplicateOrUnorderedLayer { layer: 1 })
    ));
}

#[test]
fn backward_artifact_requires_every_budget_from_two_through_sixteen() {
    let mut regime = sample_regime();
    regime.plans.pop();
    let artifact = sample_artifact(vec![BackwardLayerArtifact {
        layer: 0,
        r0: regime.clone(),
        ext: regime,
    }]);
    assert!(matches!(
        artifact.validate_self_consistency(),
        Err(
            gkr_eval_isa::eval_plan::BackwardArtifactError::InvalidBudgetCoverage {
                coordinate: BackwardArtifactCoordinate {
                    circuit,
                    layer: 0,
                    regime: BwdRegime::R0,
                    budget_cells: 16,
                },
            }
        ) if circuit == "fixture"
    ));
}

#[test]
fn backward_artifact_reports_the_first_overlong_budget_coordinate() {
    let mut regime = sample_regime();
    regime.plans.push(sample_plan(16));
    let artifact = sample_artifact(vec![BackwardLayerArtifact {
        layer: 0,
        r0: regime.clone(),
        ext: regime,
    }]);
    assert!(matches!(
        artifact.validate_self_consistency(),
        Err(
            gkr_eval_isa::eval_plan::BackwardArtifactError::InvalidBudgetCoverage {
                coordinate: BackwardArtifactCoordinate {
                    circuit,
                    layer: 0,
                    regime: BwdRegime::R0,
                    budget_cells: 17,
                },
            }
        ) if circuit == "fixture"
    ));
}

#[test]
fn backward_artifact_requires_nonempty_identity_fields() {
    let regime = sample_regime();
    let mut artifact = sample_artifact(vec![BackwardLayerArtifact {
        layer: 0,
        r0: regime.clone(),
        ext: regime,
    }]);
    artifact.circuit.clear();
    assert!(matches!(
        artifact.validate_self_consistency(),
        Err(gkr_eval_isa::eval_plan::BackwardArtifactError::CircuitMismatch { .. })
    ));

    artifact.circuit = "fixture".to_owned();
    artifact.layout_fixture.clear();
    assert!(matches!(
        artifact.validate_self_consistency(),
        Err(gkr_eval_isa::eval_plan::BackwardArtifactError::LayoutFixtureMismatch { .. })
    ));
}

#[test]
fn backward_artifact_requires_strictly_increasing_retained_demand_indices() {
    let mut regime = sample_regime();
    regime.plans[0].retained_demands = vec![3, 3];
    let artifact = sample_artifact(vec![BackwardLayerArtifact {
        layer: 0,
        r0: regime.clone(),
        ext: regime,
    }]);
    assert!(matches!(
        artifact.validate_self_consistency(),
        Err(
            gkr_eval_isa::eval_plan::BackwardArtifactError::InvalidRetainedDemand {
                circuit,
                layer: 0,
                regime: BwdRegime::R0,
                budget_cells: 2,
                position: 3,
            }
        ) if circuit == "fixture"
    ));
}

#[test]
fn backward_artifact_reports_out_of_range_r0_budget() {
    let mut regime = sample_regime();
    regime.plans[0].budget_cells = 1;
    let artifact = sample_artifact(vec![BackwardLayerArtifact {
        layer: 7,
        r0: regime.clone(),
        ext: regime,
    }]);
    assert!(matches!(
        artifact.validate_self_consistency(),
        Err(gkr_eval_isa::eval_plan::BackwardArtifactError::BudgetOutOfRange {
            circuit,
            layer: 7,
            regime: BwdRegime::R0,
            budget_cells: 1,
        }) if circuit == "fixture"
    ));
}

#[test]
fn backward_artifact_reports_out_of_range_ext_budget() {
    let regime = sample_regime();
    let mut ext = regime.clone();
    ext.plans[14].budget_cells = 17;
    let artifact = sample_artifact(vec![BackwardLayerArtifact {
        layer: 9,
        r0: regime,
        ext,
    }]);
    assert!(matches!(
        artifact.validate_self_consistency(),
        Err(gkr_eval_isa::eval_plan::BackwardArtifactError::BudgetOutOfRange {
            circuit,
            layer: 9,
            regime: BwdRegime::Ext,
            budget_cells: 17,
        }) if circuit == "fixture"
    ));
}

#[test]
fn backward_artifact_rejects_unknown_schema_fields() {
    let regime = sample_regime();
    let artifact = sample_artifact(vec![BackwardLayerArtifact {
        layer: 0,
        r0: regime.clone(),
        ext: regime,
    }]);
    let mut json = serde_json::to_value(artifact).unwrap();
    json.as_object_mut()
        .unwrap()
        .insert("version".to_owned(), serde_json::json!(1));
    assert!(serde_json::from_value::<BackwardEvaluationCircuitArtifact>(json).is_err());
}

#[test]
fn backward_artifact_loader_rejects_unknown_problem_certificate_fields() {
    let regime = sample_regime();
    let artifact = sample_artifact(vec![BackwardLayerArtifact {
        layer: 0,
        r0: regime.clone(),
        ext: regime,
    }]);
    for field in ["version", "unknown"] {
        let mut json = serde_json::to_value(artifact.clone()).unwrap();
        let problem = json["layers"][0]["r0"]["plans"][0]["problem"]
            .as_object_mut()
            .unwrap();
        problem.insert(field.to_owned(), serde_json::json!(1));
        let path = std::env::temp_dir().join(format!(
            "gkr-eval-plan-artifact-problem-{field}-{}.json",
            std::process::id()
        ));
        std::fs::write(&path, serde_json::to_vec(&json).unwrap()).unwrap();
        assert!(matches!(
            load_backward_evaluation_artifact(&path),
            Err(gkr_eval_isa::eval_plan::BackwardArtifactError::Load(_))
        ));
        std::fs::remove_file(path).unwrap();
    }
}

#[test]
fn backward_artifact_loader_rejects_malformed_json() {
    let path = std::env::temp_dir().join(format!(
        "gkr-eval-plan-artifact-malformed-{}.json",
        std::process::id()
    ));
    std::fs::write(&path, b"{").unwrap();
    assert!(matches!(
        load_backward_evaluation_artifact(&path),
        Err(gkr_eval_isa::eval_plan::BackwardArtifactError::Load(_))
    ));
    std::fs::remove_file(path).unwrap();
}

#[test]
#[ignore = "Plan 4 R0 exact-solver feasibility gate"]
fn plan4_r0_exact_solver_feasibility_2_to_16() {
    let mut solved = 0usize;
    for fixture in R0_FEASIBILITY_FIXTURES {
        let artifact = common::load_fixture(fixture);
        let dag = cs::gkr_compiler::dag_ir::lower_dag(&artifact).unwrap();
        let trace_len = dag.globals.trace_len;
        let (layer_index, layer, cross) = common::layers_with_bwd_roots(fixture)
            .find(|(layer, _, _)| *layer == 0)
            .expect("review-pinned layer zero exists");
        let distilled = distill(&layer, BwdRegime::R0, &cross, None);
        for budget_cells in 2..=16 {
            let (_, problem) =
                build_backward_search_problem(&layer, &distilled, trace_len, budget_cells).unwrap();
            let result = solve_production_paging(&problem.unwrap().demands).unwrap();
            assert!(matches!(
                result.solver,
                ProductionPagingSolver::UniformIntervals | ProductionPagingSolver::RetainAll
            ));
            solved += 1;
            eprintln!("PLAN4-FEASIBLE {fixture} L{layer_index} R0 c{budget_cells} {solved}/60");
        }
    }
    assert_eq!(solved, 60);
}

#[test]
fn production_order_searches_a_representative_real_layer() {
    let fixture = common::FIXTURES[0];
    let artifact = common::load_fixture(fixture);
    let dag = cs::gkr_compiler::dag_ir::lower_dag(&artifact).unwrap();
    let trace_len = dag.globals.trace_len;
    let (layer_index, layer, cross) = common::layers_with_bwd_roots(fixture)
        .next()
        .expect("fixture has a backward-bearing layer");
    let distilled = distill(&layer, BwdRegime::R0, &cross, None);
    let result = search_production_backward(
        &ProductionSearchIdentity {
            circuit: "add_sub_lui_auipc_mop".to_owned(),
            layout_fixture: fixture.to_owned(),
            layer: layer_index,
            regime: BwdRegime::R0,
        },
        &layer,
        &distilled,
        trace_len,
        4,
        None,
    )
    .unwrap();
    assert_eq!(result.order.len(), result.problem.fragment_domain.len());
    assert_eq!(result.telemetry.completed_tiers[0], 128);
    assert_eq!(
        result.telemetry.exact_solver_calls,
        result.telemetry.evaluations
    );
    assert!(!result.telemetry.solver_kinds.is_empty());
}

#[test]
fn generation_chain_is_ascending_and_reports_each_completed_budget() {
    let fixture = common::FIXTURES[0];
    let source = common::load_fixture(fixture);
    let dag = cs::gkr_compiler::dag_ir::lower_dag(&source).unwrap();
    let (layer_index, layer, cross) = common::layers_with_bwd_roots(fixture).next().unwrap();
    let distilled = distill(&layer, BwdRegime::R0, &cross, None);
    let identity = ProductionSearchIdentity {
        circuit: common::schedule_stem(fixture).to_owned(),
        layout_fixture: fixture.to_owned(),
        layer: layer_index,
        regime: BwdRegime::R0,
    };

    let events = std::sync::Mutex::new(Vec::new());
    let chain = produce_backward_regime_chain_with_progress(
        &identity,
        &layer,
        &distilled,
        dag.globals.trace_len,
        2..=3,
        &|event| events.lock().unwrap().push(event),
    )
    .unwrap();
    assert_eq!(
        chain
            .plans
            .iter()
            .map(|plan| plan.budget_cells)
            .collect::<Vec<_>>(),
        vec![2, 3]
    );
    assert_eq!(
        events
            .into_inner()
            .unwrap()
            .into_iter()
            .filter_map(|event| match event {
                BackwardRegimeChainProgress::Completed { budget_cells } => Some(budget_cells),
                BackwardRegimeChainProgress::Search { .. } => None,
            })
            .collect::<Vec<_>>(),
        vec![2, 3],
    );
}

#[test]
fn generation_constructor_validates_before_returning() {
    let regime = sample_regime();
    let artifact = BackwardEvaluationCircuitArtifact::new(
        "fixture",
        "fixture_layout",
        vec![BackwardLayerArtifact {
            layer: 0,
            r0: regime.clone(),
            ext: regime,
        }],
    )
    .unwrap();
    assert_eq!(artifact.circuit, "fixture");

    assert!(matches!(
        BackwardEvaluationCircuitArtifact::new("", "fixture_layout", Vec::new()),
        Err(BackwardArtifactError::CircuitMismatch { .. })
    ));
}

#[test]
fn generation_atomic_publication_preserves_destination_on_validator_failure() {
    let directory = std::env::temp_dir().join(format!(
        "plan4-atomic-publication-{}-{:?}",
        std::process::id(),
        std::thread::current().id(),
    ));
    std::fs::create_dir_all(&directory).unwrap();
    let destination = directory.join("artifact.json");
    let sentinel = b"existing-certified-artifact\n";
    std::fs::write(&destination, sentinel).unwrap();
    let regime = sample_regime();
    let artifact = BackwardEvaluationCircuitArtifact::new(
        "fixture",
        "fixture_layout",
        vec![BackwardLayerArtifact {
            layer: 0,
            r0: regime.clone(),
            ext: regime,
        }],
    )
    .unwrap();

    let result = publish_backward_evaluation_artifact(&destination, &artifact, |_| {
        Err(BackwardArtifactError::Publish(
            "injected validator failure".to_owned(),
        ))
    });
    assert!(matches!(result, Err(BackwardArtifactError::Publish(_))));
    assert_eq!(std::fs::read(&destination).unwrap(), sentinel);
    assert_eq!(std::fs::read_dir(&directory).unwrap().count(), 1);
    std::fs::remove_dir_all(directory).unwrap();
}

#[test]
fn generation_backward_artifact_path_is_exact() {
    assert_eq!(
        common::backward_artifact_path("add_sub_lui_auipc_mop_layout_gkr.json"),
        common::compiled_circuit_dir().join("add_sub_lui_auipc_mop_bwd_eval_plan_c2-c16_gkr.json"),
    );
}

#[test]
fn generation_filters_force_diagnostic_tmp_output() {
    let config = Plan4RunConfig::from_values(
        Some("add_sub_lui_auipc_mop_layout_gkr.json"),
        Some("3"),
        Some("4"),
        None,
    )
    .unwrap();
    assert!(!config.may_publish_production);
    assert!(config.diagnostic_dir.as_ref().unwrap().starts_with("/tmp"));
    assert_eq!(config.budgets, 3..=4);
    assert!(Plan4RunConfig::from_values(None, Some("2"), None, Some("1")).is_err());
}

#[test]
fn generation_chain_queue_is_canonical_and_complete() {
    let inputs = build_plan4_chain_inputs(common::FIXTURES);
    assert_eq!(inputs.len(), 114);
    assert!(
        inputs
            .iter()
            .enumerate()
            .all(|(ordinal, input)| input.ordinal == ordinal)
    );
    for pair in inputs.chunks_exact(2) {
        assert_eq!(pair[0].fixture, pair[1].fixture);
        assert_eq!(pair[0].layer_index, pair[1].layer_index);
        assert_eq!(pair[0].regime, BwdRegime::R0);
        assert_eq!(pair[1].regime, BwdRegime::Ext);
    }
}

#[test]
fn generation_rejects_production_publication_for_a_partial_corpus() {
    let matrix = Plan4Matrix {
        inputs: build_plan4_chain_inputs(&common::FIXTURES[..1]),
        outputs: Vec::new(),
        budgets: 2..=16,
    };
    assert!(matches!(
        matrix.validate_production_scope(),
        Err(BackwardArtifactError::Publish(_))
    ));
}

#[test]
#[ignore = "Plan 4 small shared-pool worker-invariance probe"]
fn plan4_small_parallel_digest() {
    let matrix = run_plan4_matrix(&common::FIXTURES[..1], 2..=2).unwrap();
    println!("PLAN4-SMALL-DIGEST {:016x}", matrix.digest());
}

#[test]
#[ignore = "Plan 4 full backward artifact generator"]
fn plan4_generate_backward_artifacts() {
    let config = Plan4RunConfig::from_env().unwrap();
    let matrix = run_plan4_matrix(&config.fixtures, config.budgets.clone()).unwrap();
    let digest = matrix.digest();
    if let Some(directory) = &config.diagnostic_dir {
        matrix.write_diagnostic(directory).unwrap();
    } else if config.may_publish_production {
        matrix.publish().unwrap();
    }
    println!("PLAN4-BWD-DIGEST {digest:016x}");
}

struct Plan4RunConfig {
    fixtures: Vec<&'static str>,
    budgets: RangeInclusive<usize>,
    diagnostic_dir: Option<PathBuf>,
    may_publish_production: bool,
}

impl Plan4RunConfig {
    fn from_env() -> Result<Self, String> {
        let fixture = std::env::var("GKR_PLAN4_FIXTURE").ok();
        let budget_min = std::env::var("GKR_PLAN4_BUDGET_MIN").ok();
        let budget_max = std::env::var("GKR_PLAN4_BUDGET_MAX").ok();
        let digest_only = std::env::var("GKR_PLAN4_DIGEST_ONLY").ok();
        Self::from_values(
            fixture.as_deref(),
            budget_min.as_deref(),
            budget_max.as_deref(),
            digest_only.as_deref(),
        )
    }

    fn from_values(
        fixture: Option<&str>,
        budget_min: Option<&str>,
        budget_max: Option<&str>,
        digest_only: Option<&str>,
    ) -> Result<Self, String> {
        let filtered = fixture.is_some() || budget_min.is_some() || budget_max.is_some();
        let digest_only = digest_only == Some("1");
        if digest_only && filtered {
            return Err("GKR_PLAN4_DIGEST_ONLY=1 requires the complete unfiltered matrix".into());
        }
        let parse_budget = |name: &str, value: Option<&str>, default| {
            let value = value.map_or(Ok(default), |value| {
                value
                    .parse::<usize>()
                    .map_err(|error| format!("invalid {name}={value}: {error}"))
            })?;
            (2..=16)
                .contains(&value)
                .then_some(value)
                .ok_or_else(|| format!("{name} must be in 2..=16"))
        };
        let min = parse_budget("GKR_PLAN4_BUDGET_MIN", budget_min, 2)?;
        let max = parse_budget("GKR_PLAN4_BUDGET_MAX", budget_max, 16)?;
        if min > max {
            return Err("GKR_PLAN4_BUDGET_MIN exceeds GKR_PLAN4_BUDGET_MAX".into());
        }
        let fixtures = match fixture {
            Some(fixture) => vec![
                *common::FIXTURES
                    .iter()
                    .find(|candidate| **candidate == fixture)
                    .ok_or_else(|| format!("unknown GKR_PLAN4_FIXTURE={fixture}"))?,
            ],
            None => common::FIXTURES.to_vec(),
        };
        Ok(Self {
            fixtures,
            budgets: min..=max,
            diagnostic_dir: filtered.then(|| {
                std::env::temp_dir().join(format!("gkr-plan4-diagnostic-{}", std::process::id()))
            }),
            may_publish_production: !filtered && !digest_only,
        })
    }
}

struct Plan4ChainInput {
    ordinal: usize,
    fixture: &'static str,
    circuit: String,
    layer_index: usize,
    trace_len: usize,
    regime: BwdRegime,
    canonical: DagLayer,
    distilled: DistilledLayer,
}

struct Plan4ChainOutput {
    ordinal: usize,
    fixture: &'static str,
    circuit: String,
    layer_index: usize,
    regime: BwdRegime,
    artifact: BackwardRegimeArtifact,
}

fn build_plan4_chain_inputs(fixtures: &[&'static str]) -> Vec<Plan4ChainInput> {
    let mut inputs = Vec::new();
    for &fixture in fixtures {
        let source = common::load_fixture(fixture);
        let trace_len = cs::gkr_compiler::dag_ir::lower_dag(&source)
            .expect("lower Plan 4 fixture")
            .globals
            .trace_len;
        for (layer_index, canonical, cross) in common::layers_with_bwd_roots(fixture) {
            for regime in [BwdRegime::R0, BwdRegime::Ext] {
                let distilled = distill(&canonical, regime, &cross, None);
                inputs.push(Plan4ChainInput {
                    ordinal: inputs.len(),
                    fixture,
                    circuit: common::schedule_stem(fixture).to_owned(),
                    layer_index,
                    trace_len,
                    regime,
                    canonical: canonical.clone(),
                    distilled,
                });
            }
        }
    }
    inputs
}

#[derive(Clone)]
struct ActiveChain {
    fixture: &'static str,
    layer: usize,
    regime: BwdRegime,
    budget_cells: usize,
    search: gkr_eval_isa::eval_plan::backward_search::production::ProductionSearchProgress,
}

struct Plan4ProgressState {
    active: BTreeMap<usize, ActiveChain>,
    remaining_chains: BTreeMap<&'static str, usize>,
    stopped: bool,
}

struct Plan4Progress {
    started: Instant,
    total_entries: usize,
    total_circuits: usize,
    completed: AtomicUsize,
    completed_circuits: AtomicUsize,
    state: Mutex<Plan4ProgressState>,
    wake: Condvar,
}

impl Plan4Progress {
    fn new(inputs: &[Plan4ChainInput], entries_per_chain: usize) -> Arc<Self> {
        let mut remaining_chains = BTreeMap::new();
        for input in inputs {
            *remaining_chains.entry(input.fixture).or_insert(0) += 1;
        }
        Arc::new(Self {
            started: Instant::now(),
            total_entries: inputs.len() * entries_per_chain,
            total_circuits: remaining_chains.len(),
            completed: AtomicUsize::new(0),
            completed_circuits: AtomicUsize::new(0),
            state: Mutex::new(Plan4ProgressState {
                active: BTreeMap::new(),
                remaining_chains,
                stopped: false,
            }),
            wake: Condvar::new(),
        })
    }

    fn record(&self, input: &Plan4ChainInput, event: BackwardRegimeChainProgress) {
        let mut state = self.state.lock().expect("lock Plan 4 progress");
        match event {
            BackwardRegimeChainProgress::Search {
                budget_cells,
                search,
            } => {
                state.active.insert(
                    input.ordinal,
                    ActiveChain {
                        fixture: input.fixture,
                        layer: input.layer_index,
                        regime: input.regime,
                        budget_cells,
                        search,
                    },
                );
            }
            BackwardRegimeChainProgress::Completed { .. } => {
                self.completed.fetch_add(1, Ordering::Relaxed);
                state.active.remove(&input.ordinal);
            }
        }
    }

    fn chain_done(&self, input: &Plan4ChainInput) {
        let mut state = self.state.lock().expect("lock Plan 4 progress");
        state.active.remove(&input.ordinal);
        let remaining = state
            .remaining_chains
            .get_mut(input.fixture)
            .expect("fixture chain count exists");
        *remaining -= 1;
        if *remaining == 0 {
            self.completed_circuits.fetch_add(1, Ordering::Relaxed);
        }
    }

    fn monitor(self: Arc<Self>) {
        let mut state = self.state.lock().expect("lock Plan 4 progress monitor");
        loop {
            let (next, timeout) = self
                .wake
                .wait_timeout(state, Duration::from_secs(30))
                .expect("wait for Plan 4 progress");
            state = next;
            if state.stopped {
                break;
            }
            if timeout.timed_out() {
                drop(state);
                self.emit();
                state = self.state.lock().expect("relock Plan 4 progress monitor");
            }
        }
    }

    fn finish(&self) {
        {
            let mut state = self.state.lock().expect("lock Plan 4 final progress");
            state.stopped = true;
        }
        self.emit();
        self.wake.notify_all();
    }

    fn emit(&self) {
        let state = self.state.lock().expect("lock Plan 4 progress snapshot");
        let elapsed = self.started.elapsed();
        let completed = self.completed.load(Ordering::Relaxed);
        let completed_circuits = self.completed_circuits.load(Ordering::Relaxed);
        let eta = if completed == 0 {
            "unavailable".to_owned()
        } else {
            let remaining = self.total_entries.saturating_sub(completed) as u128;
            let width = rayon::current_num_threads().max(1) as u128;
            let nanos = elapsed
                .as_nanos()
                .saturating_mul(remaining)
                .saturating_div(completed as u128)
                .saturating_div(width);
            format!(
                "{:?}-estimate",
                Duration::from_nanos(nanos.min(u64::MAX as u128) as u64)
            )
        };
        let active = state.active.values().cloned().collect::<Vec<_>>();
        let mut stderr = std::io::stderr().lock();
        writeln!(
            stderr,
            "PLAN4 progress completed={}/{} circuits={}/{} active={} elapsed={elapsed:?} eta={eta}",
            completed,
            self.total_entries,
            completed_circuits,
            self.total_circuits,
            active.len(),
        )
        .expect("write Plan 4 progress");
        for active in active {
            writeln!(
                stderr,
                "  {} L{} {:?} c{} eval={}/{} solver={:?} dp={}/{}",
                active.fixture,
                active.layer,
                active.regime,
                active.budget_cells,
                active.search.tier_completed,
                active.search.tier_evaluations,
                active.search.solver,
                active.search.dp_states,
                active.search.peak_dp_states,
            )
            .expect("write Plan 4 active coordinate");
        }
        stderr.flush().expect("flush Plan 4 progress");
    }
}

struct Plan4Matrix {
    inputs: Vec<Plan4ChainInput>,
    outputs: Vec<Plan4ChainOutput>,
    budgets: RangeInclusive<usize>,
}

fn run_plan4_matrix(
    fixtures: &[&'static str],
    budgets: RangeInclusive<usize>,
) -> Result<Plan4Matrix, BackwardArtifactError> {
    let inputs = build_plan4_chain_inputs(fixtures);
    let entries_per_chain = budgets.clone().count();
    let progress = Plan4Progress::new(&inputs, entries_per_chain);
    let monitor_progress = Arc::clone(&progress);
    let monitor = std::thread::spawn(move || monitor_progress.monitor());
    let results = inputs
        .par_iter()
        .map(|input| {
            let identity = ProductionSearchIdentity {
                circuit: input.circuit.clone(),
                layout_fixture: input.fixture.to_owned(),
                layer: input.layer_index,
                regime: input.regime,
            };
            let result = produce_backward_regime_chain_with_progress(
                &identity,
                &input.canonical,
                &input.distilled,
                input.trace_len,
                budgets.clone(),
                &|event| progress.record(input, event),
            )
            .map(|artifact| Plan4ChainOutput {
                ordinal: input.ordinal,
                fixture: input.fixture,
                circuit: input.circuit.clone(),
                layer_index: input.layer_index,
                regime: input.regime,
                artifact,
            });
            progress.chain_done(input);
            result
        })
        .collect::<Vec<_>>();
    progress.finish();
    monitor.join().expect("join Plan 4 progress monitor");

    let mut outputs = Vec::with_capacity(results.len());
    let mut failures = Vec::new();
    for result in results {
        match result {
            Ok(output) => outputs.push(output),
            Err(BackwardArtifactError::IncompleteGeneration {
                failures: chain_failures,
            }) => failures.extend(chain_failures),
            Err(error) => return Err(error),
        }
    }
    if !failures.is_empty() {
        return Err(BackwardArtifactError::IncompleteGeneration { failures });
    }
    outputs.sort_by_key(|output| output.ordinal);
    Ok(Plan4Matrix {
        inputs,
        outputs,
        budgets,
    })
}

impl Plan4Matrix {
    fn validate_production_scope(&self) -> Result<(), BackwardArtifactError> {
        let fixtures = self.inputs.iter().map(|input| input.fixture).fold(
            Vec::new(),
            |mut fixtures, fixture| {
                if fixtures.last().copied() != Some(fixture) {
                    fixtures.push(fixture);
                }
                fixtures
            },
        );
        if self.budgets != (2..=16)
            || self.inputs.len() != 114
            || self.outputs.len() != 114
            || fixtures != common::FIXTURES
            || !self
                .outputs
                .iter()
                .enumerate()
                .all(|(ordinal, output)| output.ordinal == ordinal)
        {
            return Err(BackwardArtifactError::Publish(
                "only the complete canonical 12-fixture, 114-chain c2-c16 matrix may publish"
                    .to_owned(),
            ));
        }
        Ok(())
    }

    fn digest(&self) -> u64 {
        let mut digest = 0xcbf2_9ce4_8422_2325u64;
        for output in &self.outputs {
            let regime = match output.regime {
                BwdRegime::R0 => 0u8,
                BwdRegime::Ext => 1u8,
            };
            let bytes = serde_json::to_vec(&(
                output.ordinal,
                output.fixture,
                &output.circuit,
                output.layer_index,
                regime,
                &output.artifact,
            ))
            .expect("serialize deterministic Plan 4 digest input");
            for byte in bytes {
                digest ^= u64::from(byte);
                digest = digest.wrapping_mul(0x0000_0100_0000_01b3);
            }
        }
        digest
    }

    fn artifacts(&self) -> Result<Vec<BackwardEvaluationCircuitArtifact>, BackwardArtifactError> {
        self.validate_production_scope()?;
        let mut artifacts = Vec::new();
        for fixture in self
            .inputs
            .iter()
            .map(|input| input.fixture)
            .collect::<Vec<_>>()
        {
            if artifacts
                .iter()
                .any(|artifact: &BackwardEvaluationCircuitArtifact| {
                    artifact.layout_fixture == fixture
                })
            {
                continue;
            }
            let chains = self
                .outputs
                .iter()
                .filter(|output| output.fixture == fixture)
                .collect::<Vec<_>>();
            let mut layers = Vec::new();
            for pair in chains.chunks_exact(2) {
                assert_eq!(pair[0].regime, BwdRegime::R0);
                assert_eq!(pair[1].regime, BwdRegime::Ext);
                layers.push(BackwardLayerArtifact {
                    layer: pair[0].layer_index,
                    r0: pair[0].artifact.clone(),
                    ext: pair[1].artifact.clone(),
                });
            }
            artifacts.push(BackwardEvaluationCircuitArtifact::new(
                common::schedule_stem(fixture),
                fixture,
                layers,
            )?);
        }
        Ok(artifacts)
    }

    fn publish(&self) -> Result<(), BackwardArtifactError> {
        self.validate_production_scope()?;
        for artifact in self.artifacts()? {
            let path = common::backward_artifact_path(&artifact.layout_fixture);
            publish_backward_evaluation_artifact(&path, &artifact, |reloaded| {
                for layer in &reloaded.layers {
                    for regime in [BwdRegime::R0, BwdRegime::Ext] {
                        let input = self
                            .inputs
                            .iter()
                            .find(|input| {
                                input.fixture == reloaded.layout_fixture
                                    && input.layer_index == layer.layer
                                    && input.regime == regime
                            })
                            .expect("generated Plan 4 input exists for publication validation");
                        let plans = match regime {
                            BwdRegime::R0 => &layer.r0.plans,
                            BwdRegime::Ext => &layer.ext.plans,
                        };
                        for plan in plans {
                            compile_backward_plan_artifact(
                                &reloaded.circuit,
                                layer.layer,
                                &input.canonical,
                                &input.distilled,
                                input.trace_len,
                                plan,
                            )?;
                        }
                    }
                }
                Ok(())
            })?;
        }
        Ok(())
    }

    fn write_diagnostic(&self, directory: &Path) -> Result<(), BackwardArtifactError> {
        std::fs::create_dir_all(directory).map_err(|error| {
            BackwardArtifactError::Publish(format!("create {}: {error}", directory.display()))
        })?;
        let values = self
            .outputs
            .iter()
            .map(|output| {
                serde_json::json!({
                    "ordinal": output.ordinal,
                    "fixture": output.fixture,
                    "circuit": output.circuit,
                    "layer": output.layer_index,
                    "regime": match output.regime { BwdRegime::R0 => "R0", BwdRegime::Ext => "Ext" },
                    "plans": output.artifact.plans,
                })
            })
            .collect::<Vec<_>>();
        let path = directory.join("backward-generation-diagnostic.json");
        let bytes = serde_json::to_vec_pretty(&values).map_err(|error| {
            BackwardArtifactError::Publish(format!("serialize {}: {error}", path.display()))
        })?;
        std::fs::write(&path, bytes).map_err(|error| {
            BackwardArtifactError::Publish(format!("write {}: {error}", path.display()))
        })
    }
}
