mod common;

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::io::Write;
use std::ops::RangeInclusive;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex, OnceLock};
use std::time::{Duration, Instant};

use cs::gkr_compiler::dag_ir::{BwdRegime, DagLayer, ReadPlace, VirtualSetupKind};
use gkr_eval_isa::bwd::distill::{distill, DistilledLayer};
use gkr_eval_isa::bwd::source::{BwdSpecial, BwdSpecialTable, OriginLeaf};
use gkr_eval_isa::eval_plan::backward_search::problem::build_backward_search_problem;
use gkr_eval_isa::eval_plan::backward_search::{
    compulsory_read_floor, search_production_backward, solve_production_paging,
    ProductionPagingSolver, ProductionSearchIdentity,
};
use gkr_eval_isa::eval_plan::{
    capture_backward_plan_artifact, compile_backward_plan_artifact,
    load_backward_evaluation_artifact, produce_backward_regime_chain_with_progress,
    publish_backward_evaluation_artifact, select_backward_plan, BackwardArtifactCoordinate,
    BackwardArtifactError, BackwardEvaluationCircuitArtifact, BackwardLayerArtifact,
    BackwardPlanArtifact, BackwardRegimeArtifact, BackwardRegimeChainProgress,
    BackwardScoreArtifact, CanonicalU128, DomainCertificate, SourceCostArtifact,
};
use gkr_eval_isa::fwd::encode::encode;
use gkr_eval_isa::fwd::source::virtual_setup_kind_code;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};

const R0_FEASIBILITY_FIXTURES: &[&str] = &[
    "bigint_with_extended_control_layout_gkr.json",
    "blake2_with_extended_control_layout_gkr.json",
    "keccak_special5_layout_gkr.json",
    "unified_reduced_machine_layout_gkr.json",
];

const PLAN4_PRODUCTION_CHECKPOINT_ROOT: &str = ".agents/checkpoints/gkr-plan4-bwd-c2-c16";
static PLAN4_CHECKPOINT_NONCE: AtomicUsize = AtomicUsize::new(0);

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
    assert!(config.checkpoint_root().starts_with("/tmp"));
    assert!(
        config
            .checkpoint_root()
            .ends_with("gkr-plan4-chain-checkpoints")
    );
    assert_eq!(config.budgets, 3..=4);
    assert!(Plan4RunConfig::from_values(None, Some("2"), None, Some("1")).is_err());

    let production = Plan4RunConfig::from_values(None, None, None, None).unwrap();
    assert_eq!(
        production.checkpoint_root(),
        PathBuf::from(".agents/checkpoints/gkr-plan4-bwd-c2-c16"),
    );
}

#[test]
fn generation_hostile_tmpdir_cannot_redirect_filtered_diagnostics() {
    const CHILD: &str = "GKR_PLAN4_HOSTILE_TMPDIR_CHILD";
    const HOSTILE: &str = "/cs/compiled_circuits/hostile-tmp";
    if std::env::var_os(CHILD).is_some() {
        let config = Plan4RunConfig::from_values(
            Some("add_sub_lui_auipc_mop_layout_gkr.json"),
            None,
            None,
            None,
        )
        .unwrap();
        let directory = config.diagnostic_dir.unwrap();
        assert!(directory.starts_with("/tmp"));
        assert!(!directory.starts_with(HOSTILE));
        return;
    }

    let status = std::process::Command::new(std::env::current_exe().unwrap())
        .arg("generation_hostile_tmpdir_cannot_redirect_filtered_diagnostics")
        .arg("--exact")
        .env(CHILD, "1")
        .env("TMPDIR", HOSTILE)
        .status()
        .unwrap();
    assert!(status.success());
}

#[test]
fn generation_eta_uses_observed_parallel_throughput_without_width_division() {
    assert_eq!(
        plan4_estimated_remaining(Duration::from_secs(12), 3, 9),
        Some(Duration::from_secs(24)),
    );
    assert_eq!(
        plan4_estimated_remaining(Duration::from_secs(12), 0, 9),
        None
    );
}

#[test]
fn generation_chain_queue_is_canonical_and_complete() {
    let inputs = build_plan4_chain_inputs(common::FIXTURES);
    assert_eq!(inputs.len(), 114);
    assert!(inputs
        .iter()
        .enumerate()
        .all(|(ordinal, input)| input.ordinal == ordinal));
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
        summary: Plan4GenerationSummary::default(),
    };
    assert!(matches!(
        matrix.validate_production_scope(),
        Err(BackwardArtifactError::Publish(_))
    ));
}

#[test]
fn generation_failed_fixture_never_counts_as_a_completed_circuit() {
    let inputs = build_plan4_chain_inputs(&common::FIXTURES[..1]);
    let progress = Plan4Progress::new(&inputs, 1);
    for (index, input) in inputs.iter().enumerate() {
        progress.chain_done(input, index != 0);
    }
    assert_eq!(progress.snapshot().completed_circuits, 0);
}

#[test]
fn generation_progress_snapshot_releases_state_before_formatting() {
    let inputs = build_plan4_chain_inputs(&common::FIXTURES[..1]);
    let progress = Plan4Progress::new(&inputs, 1);
    let snapshot = progress.snapshot();
    let state = progress
        .state
        .try_lock()
        .expect("snapshot must not retain the active-map mutex");
    let mut rendered = Vec::new();
    Plan4Progress::write_snapshot(&snapshot, &mut rendered).unwrap();
    drop(state);
    assert!(String::from_utf8(rendered)
        .unwrap()
        .contains("PLAN4 progress"));
}

fn checkpoint_test_root(label: &str) -> PathBuf {
    let root = PathBuf::from("/tmp").join(format!(
        "gkr-plan4-{label}-{}-{:?}",
        std::process::id(),
        std::thread::current().id(),
    ));
    let _ = std::fs::remove_dir_all(&root);
    std::fs::create_dir_all(&root).unwrap();
    root
}

fn checkpoint_test_inputs(count: usize) -> Vec<Plan4ChainInput> {
    let mut inputs = build_plan4_chain_inputs(&common::FIXTURES[..1]);
    inputs.truncate(count);
    inputs
}

fn checkpoint_inventory(root: &Path) -> usize {
    std::fs::read_dir(root)
        .unwrap()
        .filter_map(Result::ok)
        .filter(|entry| {
            entry
                .path()
                .extension()
                .is_some_and(|extension| extension == "json")
        })
        .count()
}

#[test]
fn checkpoint_resume_skips_certified_chains_and_preserves_digest() {
    let root = checkpoint_test_root("resume");
    let calls = AtomicUsize::new(0);
    let producer = |input: &Plan4ChainInput,
                    budgets: RangeInclusive<usize>,
                    progress: &(dyn Fn(BackwardRegimeChainProgress) + Sync)| {
        calls.fetch_add(1, Ordering::Relaxed);
        produce_backward_regime_chain_with_progress(
            &input.identity(),
            &input.canonical,
            &input.distilled,
            input.trace_len,
            budgets,
            progress,
        )
    };

    let first = run_plan4_matrix_with_checkpoints_and_producer(
        checkpoint_test_inputs(2),
        2..=2,
        &root,
        &producer,
    )
    .unwrap();
    assert_eq!(calls.load(Ordering::Relaxed), 2);
    assert_eq!(first.summary.new_entries, 2);
    assert_eq!(first.summary.resumed_entries, 0);
    assert_eq!(first.summary.exact_solver_calls, 2);

    let second = run_plan4_matrix_with_checkpoints_and_producer(
        checkpoint_test_inputs(2),
        2..=2,
        &root,
        &producer,
    )
    .unwrap();
    assert_eq!(calls.load(Ordering::Relaxed), 2);
    assert_eq!(second.summary.new_entries, 0);
    assert_eq!(second.summary.resumed_entries, 2);
    assert_eq!(second.summary.exact_solver_calls, 0);
    assert_eq!(first.digest(), second.digest());
    std::fs::remove_dir_all(root).unwrap();
}

#[test]
fn checkpoint_stale_or_corrupt_fails_closed_without_producer_calls() {
    let inputs = checkpoint_test_inputs(1);
    let input = &inputs[0];
    let budgets = 2..=2;
    let producer_calls = AtomicUsize::new(0);
    let producer = |_: &Plan4ChainInput,
                    _: RangeInclusive<usize>,
                    _: &(dyn Fn(BackwardRegimeChainProgress) + Sync)| {
        producer_calls.fetch_add(1, Ordering::Relaxed);
        Ok(BackwardRegimeArtifact {
            plans: vec![sample_plan(2)],
        })
    };

    let stale_root = checkpoint_test_root("stale");
    let stale_path = plan4_checkpoint_path(&stale_root, input, &budgets).unwrap();
    let stale = Plan4ChainCheckpoint {
        circuit: "stale-circuit".to_owned(),
        layout_fixture: input.fixture.to_owned(),
        layer: input.layer_index,
        regime: plan4_regime_code(input.regime),
        budget_min: 2,
        budget_max: 2,
        artifact: BackwardRegimeArtifact {
            plans: vec![sample_plan(2)],
        },
    };
    std::fs::write(&stale_path, serde_json::to_vec_pretty(&stale).unwrap()).unwrap();
    assert!(matches!(
        run_plan4_matrix_with_checkpoints_and_producer(
            checkpoint_test_inputs(1),
            budgets.clone(),
            &stale_root,
            &producer,
        ),
        Err(BackwardArtifactError::Publish(_))
    ));

    let corrupt_root = checkpoint_test_root("corrupt");
    let corrupt_path = plan4_checkpoint_path(&corrupt_root, input, &budgets).unwrap();
    std::fs::write(&corrupt_path, b"{not-json\n").unwrap();
    assert!(matches!(
        run_plan4_matrix_with_checkpoints_and_producer(
            checkpoint_test_inputs(1),
            budgets,
            &corrupt_root,
            &producer,
        ),
        Err(BackwardArtifactError::Publish(_))
    ));
    assert_eq!(producer_calls.load(Ordering::Relaxed), 0);
    std::fs::remove_dir_all(stale_root).unwrap();
    std::fs::remove_dir_all(corrupt_root).unwrap();
}

#[test]
fn checkpoint_interrupted_matrix_keeps_completed_inventory() {
    let root = checkpoint_test_root("interrupted");
    let producer = |input: &Plan4ChainInput,
                    _: RangeInclusive<usize>,
                    _: &(dyn Fn(BackwardRegimeChainProgress) + Sync)| {
        if input.ordinal < 3 {
            Ok(BackwardRegimeArtifact {
                plans: vec![sample_plan(2)],
            })
        } else {
            Err(BackwardArtifactError::Publish(
                "injected chain failure".to_owned(),
            ))
        }
    };
    let result = run_plan4_matrix_with_checkpoints_and_producer(
        checkpoint_test_inputs(4),
        2..=2,
        &root,
        &producer,
    );
    assert!(result.is_err());
    assert_eq!(checkpoint_inventory(&root), 3);
    std::fs::remove_dir_all(root).unwrap();
}

#[test]
fn checkpoint_requires_exact_identity_and_budget_coverage() {
    let root = checkpoint_test_root("exact-identity");
    let inputs = checkpoint_test_inputs(1);
    let input = &inputs[0];
    let budgets = 2..=2;
    let path = plan4_checkpoint_path(&root, input, &budgets).unwrap();
    let checkpoint = Plan4ChainCheckpoint {
        circuit: input.circuit.clone(),
        layout_fixture: input.fixture.to_owned(),
        layer: input.layer_index,
        regime: plan4_regime_code(input.regime),
        budget_min: 2,
        budget_max: 2,
        artifact: BackwardRegimeArtifact {
            plans: vec![sample_plan(3)],
        },
    };
    std::fs::write(path, serde_json::to_vec_pretty(&checkpoint).unwrap()).unwrap();
    assert!(matches!(
        load_plan4_chain_checkpoint(&root, input, &budgets),
        Err(BackwardArtifactError::Publish(_))
    ));
    std::fs::remove_dir_all(root).unwrap();
}

#[test]
fn checkpoint_atomic_collisions_preserve_unowned_files() {
    let root = checkpoint_test_root("atomic-collision");
    let inputs = checkpoint_test_inputs(1);
    let input = &inputs[0];
    let budgets = 2..=2;
    let destination = plan4_checkpoint_path(&root, input, &budgets).unwrap();
    let sentinel = b"foreign checkpoint\n";
    std::fs::write(&destination, sentinel).unwrap();
    let artifact = BackwardRegimeArtifact {
        plans: vec![sample_plan(2)],
    };
    assert!(matches!(
        publish_plan4_chain_checkpoint(&root, input, &budgets, &artifact),
        Err(BackwardArtifactError::Publish(_))
    ));
    assert_eq!(std::fs::read(&destination).unwrap(), sentinel);
    assert_eq!(
        std::fs::read_dir(&root).unwrap().count(),
        1,
        "failed publication must clean up only its owned temporary and lock",
    );

    std::fs::remove_file(&destination).unwrap();
    let temporary = root.join("foreign-temporary");
    std::fs::write(&temporary, sentinel).unwrap();
    let checkpoint = Plan4ChainCheckpoint {
        circuit: input.circuit.clone(),
        layout_fixture: input.fixture.to_owned(),
        layer: input.layer_index,
        regime: plan4_regime_code(input.regime),
        budget_min: 2,
        budget_max: 2,
        artifact,
    };
    assert!(matches!(
        publish_plan4_chain_checkpoint_to_temporary(&destination, &temporary, &checkpoint,),
        Err(BackwardArtifactError::Publish(_))
    ));
    assert_eq!(std::fs::read(&temporary).unwrap(), sentinel);
    assert!(!destination.exists());
    std::fs::remove_dir_all(root).unwrap();
}

#[test]
fn chain_census_reports_dram_floor_percentages_and_attainment() {
    let above_floor = Plan4CensusScore {
        dram_bytes: 150,
        source_ops: 5,
        instructions: 4,
        encoded_lanes: 3,
        arithmetic_ops: 2,
    };
    let at_floor = Plan4CensusScore {
        dram_bytes: 100,
        ..above_floor.clone()
    };
    let scores = (0..15)
        .map(|index| {
            if index == 0 {
                above_floor.clone()
            } else {
                at_floor.clone()
            }
        })
        .collect::<Vec<_>>();
    let mut output = String::new();
    render_plan4_chain_census(&mut output, "fixture", 0, BwdRegime::R0, 100, 5, &scores);
    assert!(output.contains("DRAM above compulsory floor: c2=50.00% c3=0.00%"));

    let mut totals = Plan4CorpusTotals {
        chains: 1,
        ..Default::default()
    };
    for (index, score) in scores.iter().enumerate() {
        totals.record(index + 2, 100, score);
    }
    totals.render_aggregates(&mut output);
    assert!(output.contains("floor attainment: c2=0/1 (0.00%) c3=1/1 (100.00%)"));

    let zero_scores = vec![
        Plan4CensusScore {
            dram_bytes: 0,
            ..above_floor
        };
        15
    ];
    render_plan4_chain_census(
        &mut output,
        "zero-floor-fixture",
        0,
        BwdRegime::R0,
        0,
        0,
        &zero_scores,
    );
    assert!(output.contains("DRAM above compulsory floor: c2=n/a (zero floor)"));
}

#[test]
fn artifact_consumer_is_reconstruction_only() {
    assert_plan4_artifact_consumer_is_reconstruction_only();
}

#[test]
fn generation_uses_seed_only_selector() {
    let artifact_source = include_str!("../src/eval_plan/backward_artifact.rs");
    let production_source = include_str!("../src/eval_plan/backward_search/production.rs");
    let production_chain = source_function_body(
        artifact_source,
        "pub fn produce_backward_regime_chain_with_progress(",
    );
    assert!(production_chain.contains("select_production_backward_seeds_with_progress"));
    let seed_selector = source_function_body(
        production_source,
        "pub fn select_production_backward_seeds_with_progress(",
    );
    for forbidden in [
        "search_production_backward",
        "run_search_driver",
        "mutate_production_order",
        "production_identity_seed",
        "StableRng",
        ".mutate(",
    ] {
        assert!(
            !production_chain.contains(forbidden) && !seed_selector.contains(forbidden),
            "production generation must not invoke {forbidden}",
        );
    }

    let exact_evaluation = source_function_body(production_source, "fn evaluate_rebuilt_problem(");
    let permit = exact_evaluation
        .find("production_evaluation_gate().acquire()")
        .expect("exact production evaluation acquires the global permit");
    let paging = exact_evaluation
        .find("solve_production_paging_observed")
        .expect("exact production evaluation pages exactly");
    let certification = exact_evaluation
        .find("compile_and_certify_paging")
        .expect("exact production evaluation compiles and certifies");
    assert!(permit < paging && paging < certification);
    assert!(!exact_evaluation.contains("drop(_permit)"));
}

#[test]
#[ignore = "Plan 4 small shared-pool worker-invariance probe"]
fn plan4_small_parallel_digest() {
    let matrix = run_plan4_matrix(&common::FIXTURES[..1], 2..=2).unwrap();
    println!("PLAN4-SMALL-DIGEST {:016x}", matrix.digest());
}

#[test]
#[ignore = "Plan 4 small checkpoint/resume worker-invariance probe"]
fn plan4_small_checkpoint_digest() {
    let root = checkpoint_test_root("small-checkpoint-digest");
    let first = run_plan4_matrix_with_checkpoints_and_producer(
        checkpoint_test_inputs(2),
        2..=2,
        &root,
        &produce_plan4_chain,
    )
    .unwrap();
    let resumed = run_plan4_matrix_with_checkpoints_and_producer(
        checkpoint_test_inputs(2),
        2..=2,
        &root,
        &produce_plan4_chain,
    )
    .unwrap();
    assert_eq!(first.digest(), resumed.digest());
    assert_eq!(first.summary.new_entries, 2);
    assert_eq!(resumed.summary.resumed_entries, 2);
    assert_eq!(resumed.summary.exact_solver_calls, 0);
    println!("PLAN4-SMALL-CHECKPOINT-DIGEST {:016x}", first.digest());
    std::fs::remove_dir_all(root).unwrap();
}

#[test]
#[ignore = "Plan 4 full backward artifact generator"]
fn plan4_generate_backward_artifacts() {
    let config = Plan4RunConfig::from_env().unwrap();
    let matrix = run_plan4_matrix_with_checkpoints(
        &config.fixtures,
        config.budgets.clone(),
        &config.checkpoint_root(),
    )
    .unwrap();
    let digest = matrix.digest();
    if let Some(directory) = &config.diagnostic_dir {
        matrix.write_diagnostic(directory).unwrap();
    } else if config.may_publish_production {
        matrix.publish().unwrap();
    }
    matrix.write_generation_summary(std::io::stdout()).unwrap();
    println!("PLAN4-BWD-DIGEST {digest:016x}");
}

#[test]
#[ignore = "Plan 4 full backward artifact replay and budget-floor census"]
fn plan4_backward_artifact_corpus_gate() {
    assert_plan4_artifact_consumer_is_reconstruction_only();

    let expected_paths = common::FIXTURES
        .iter()
        .map(|fixture| common::backward_artifact_path(fixture))
        .collect::<Vec<_>>();
    assert_eq!(expected_paths.len(), 12, "Plan 4 fixture count drifted");
    assert_eq!(
        expected_paths.iter().collect::<BTreeSet<_>>().len(),
        12,
        "Plan 4 artifact paths must be unique",
    );
    let expected_names = expected_paths
        .iter()
        .map(|path| path.file_name().unwrap().to_owned())
        .collect::<BTreeSet<_>>();
    let actual_names = std::fs::read_dir(common::compiled_circuit_dir())
        .unwrap()
        .filter_map(|entry| {
            let name = entry.unwrap().file_name();
            name.to_string_lossy()
                .ends_with("_bwd_eval_plan_c2-c16_gkr.json")
                .then_some(name)
        })
        .collect::<BTreeSet<_>>();
    assert_eq!(
        actual_names, expected_names,
        "the complete exact 12-file Plan 4 artifact corpus must be installed",
    );

    let started = Instant::now();
    let mut totals = Plan4CorpusTotals::default();
    let mut digest = 0xcbf2_9ce4_8422_2325u64;
    let mut chain_ordinal = 0usize;
    let mut census = String::new();
    writeln!(
        census,
        "fixture | layer | regime | floor bytes | first floor budget | c2 ... c16 DRAM"
    )
    .unwrap();

    for (&fixture, path) in common::FIXTURES.iter().zip(&expected_paths) {
        let artifact = load_backward_evaluation_artifact(path).unwrap_or_else(|error| {
            panic!("load exact Plan 4 artifact {}: {error:?}", path.display())
        });
        assert_eq!(artifact.layout_fixture, fixture);
        assert_eq!(artifact.circuit, common::schedule_stem(fixture));
        totals.files += 1;
        totals.layers += artifact.layers.len();

        let inputs = build_plan4_chain_inputs(&[fixture]);
        assert_eq!(inputs.len(), artifact.layers.len() * 2);
        for input in inputs {
            let layer = artifact
                .layers
                .binary_search_by_key(&input.layer_index, |layer| layer.layer)
                .ok()
                .map(|index| &artifact.layers[index])
                .expect("every canonical backward-bearing layer must be present");
            let regime_artifact = match input.regime {
                BwdRegime::R0 => &layer.r0,
                BwdRegime::Ext => &layer.ext,
            };
            assert_eq!(regime_artifact.plans.len(), 15);
            totals.chains += 1;

            let digest_regime = match input.regime {
                BwdRegime::R0 => 0u8,
                BwdRegime::Ext => 1u8,
            };
            let digest_bytes = serde_json::to_vec(&(
                chain_ordinal,
                fixture,
                &artifact.circuit,
                input.layer_index,
                digest_regime,
                regime_artifact,
            ))
            .unwrap();
            for byte in digest_bytes {
                digest ^= u64::from(byte);
                digest = digest.wrapping_mul(0x0000_0100_0000_01b3);
            }
            chain_ordinal += 1;

            let (_, floor_problem) = build_backward_search_problem(
                &input.canonical,
                &input.distilled,
                input.trace_len,
                2,
            )
            .unwrap();
            let floor = compulsory_read_floor(
                floor_problem
                    .as_ref()
                    .expect("production artifact chains must have feasible problems"),
            )
            .unwrap();
            let floor_bytes = floor.dram_bytes().unwrap();
            let floor_ops = floor.ops.primitive_equivalents().unwrap();
            let mut scores = Vec::with_capacity(15);

            for budget_cells in 2..=16 {
                let plan =
                    select_backward_plan(&artifact, input.layer_index, input.regime, budget_cells)
                        .unwrap();
                assert_eq!(plan.budget_cells, budget_cells);
                assert!(!plan.expected_score.infeasible);
                assert_eq!(plan.expected_paging.diverged, None);
                assert_eq!(plan.expected_paging.refused_retains, 0);

                let replayed = compile_backward_plan_artifact(
                    &artifact.circuit,
                    input.layer_index,
                    &input.canonical,
                    &input.distilled,
                    input.trace_len,
                    plan,
                )
                .unwrap_or_else(|error| {
                    panic!(
                        "certify {} L{} {:?} c{}: {error:?}",
                        fixture, input.layer_index, input.regime, budget_cells,
                    )
                });
                assert!(!replayed.score.infeasible);
                assert_eq!(replayed.certificate.diverged, None);
                assert_eq!(replayed.certificate.refused_retains, 0);
                common::assert_bwd_value_parity(
                    &replayed.compiled.compiled,
                    &input.distilled,
                    &input.canonical,
                );

                let score = Plan4CensusScore::from_artifact(plan);
                assert!(score.dram_bytes >= floor_bytes);
                assert!(score.source_ops >= floor_ops);
                totals.record(budget_cells, floor_bytes, &score);
                scores.push(score);
                totals.entries += 1;
                totals.certified += 1;
                totals.semantic_parity += 1;
            }
            render_plan4_chain_census(
                &mut census,
                fixture,
                input.layer_index,
                input.regime,
                floor_bytes,
                floor_ops,
                &scores,
            );
        }
    }

    assert_eq!(chain_ordinal, 114);
    assert_eq!(totals.files, 12);
    assert_eq!(totals.layers, 57);
    assert_eq!(totals.chains, 114);
    assert_eq!(totals.entries, 1_710);
    assert_eq!(totals.certified, 1_710);
    assert_eq!(totals.semantic_parity, 1_710);
    totals.render_aggregates(&mut census);
    print!("{census}");
    println!(
        "PLAN4-CORPUS files={} layers={} chains={} entries={} certified={} parity={} resource_limited=0 fallback=0 replay_diverged=0 replay_refused=0 certificate_failed=0 elapsed={:?}",
        totals.files,
        totals.layers,
        totals.chains,
        totals.entries,
        totals.certified,
        totals.semantic_parity,
        started.elapsed(),
    );
    println!("PLAN4-BWD-DIGEST {digest:016x}");
}

#[derive(Clone, Debug)]
struct Plan4CensusScore {
    dram_bytes: u128,
    source_ops: u128,
    instructions: usize,
    encoded_lanes: usize,
    arithmetic_ops: usize,
}

impl Plan4CensusScore {
    fn from_artifact(plan: &BackwardPlanArtifact) -> Self {
        Self {
            dram_bytes: plan.expected_score.whole_pass_dram_bytes.value(),
            source_ops: plan.expected_score.primitive_source_ops.value(),
            instructions: plan.expected_score.instructions,
            encoded_lanes: plan.expected_score.encoded_lanes,
            arithmetic_ops: plan.expected_score.arithmetic_ops,
        }
    }

    fn secondary_key(&self) -> (u128, usize, usize, usize) {
        (
            self.source_ops,
            self.instructions,
            self.encoded_lanes,
            self.arithmetic_ops,
        )
    }
}

#[derive(Default)]
struct Plan4CorpusTotals {
    files: usize,
    layers: usize,
    chains: usize,
    entries: usize,
    certified: usize,
    semantic_parity: usize,
    compulsory_dram_floor_bytes: u128,
    dram_bytes: [u128; 15],
    floor_attained: [usize; 15],
    source_ops: [u128; 15],
    instructions: [u128; 15],
    encoded_lanes: [u128; 15],
    arithmetic_ops: [u128; 15],
}

impl Plan4CorpusTotals {
    fn record(&mut self, budget_cells: usize, floor_bytes: u128, score: &Plan4CensusScore) {
        let index = budget_cells - 2;
        if budget_cells == 2 {
            self.compulsory_dram_floor_bytes += floor_bytes;
        }
        self.dram_bytes[index] += score.dram_bytes;
        self.floor_attained[index] += usize::from(score.dram_bytes == floor_bytes);
        self.source_ops[index] += score.source_ops;
        self.instructions[index] += score.instructions as u128;
        self.encoded_lanes[index] += score.encoded_lanes as u128;
        self.arithmetic_ops[index] += score.arithmetic_ops as u128;
    }

    fn render_aggregates(&self, output: &mut String) {
        writeln!(output, "PLAN4-CENSUS-AGGREGATE chains={}", self.chains).unwrap();
        writeln!(
            output,
            "row/round-weighted DRAM totals: {}",
            render_u128_budget_values(&self.dram_bytes),
        )
        .unwrap();
        writeln!(
            output,
            "aggregate DRAM above compulsory floor: {}",
            self.dram_bytes
                .iter()
                .enumerate()
                .map(|(index, dram_bytes)| format!(
                    "c{}={}",
                    index + 2,
                    format_percentage_above_floor(*dram_bytes, self.compulsory_dram_floor_bytes),
                ))
                .collect::<Vec<_>>()
                .join(" "),
        )
        .unwrap();
        writeln!(
            output,
            "floor attainment: {}",
            self.floor_attained
                .iter()
                .enumerate()
                .map(|(index, attained)| format!(
                    "c{}={}/{} ({})",
                    index + 2,
                    attained,
                    self.chains,
                    format_percentage(*attained as u128, self.chains as u128),
                ))
                .collect::<Vec<_>>()
                .join(" "),
        )
        .unwrap();
        writeln!(
            output,
            "row/round-weighted source-op totals: {}",
            render_u128_budget_values(&self.source_ops),
        )
        .unwrap();
        writeln!(
            output,
            "equal-chain instruction totals: {}",
            render_u128_budget_values(&self.instructions),
        )
        .unwrap();
        writeln!(
            output,
            "equal-chain encoded-lane totals: {}",
            render_u128_budget_values(&self.encoded_lanes),
        )
        .unwrap();
        writeln!(
            output,
            "equal-chain arithmetic-op totals: {}",
            render_u128_budget_values(&self.arithmetic_ops),
        )
        .unwrap();
    }
}

fn render_plan4_chain_census(
    output: &mut String,
    fixture: &str,
    layer: usize,
    regime: BwdRegime,
    floor_bytes: u128,
    floor_ops: u128,
    scores: &[Plan4CensusScore],
) {
    assert_eq!(scores.len(), 15);
    let first_floor = scores
        .iter()
        .position(|score| score.dram_bytes == floor_bytes)
        .map_or_else(|| ">16".to_owned(), |index| (index + 2).to_string());
    let values = |select: fn(&Plan4CensusScore) -> u128| {
        scores
            .iter()
            .enumerate()
            .map(|(index, score)| format!("c{}={}", index + 2, select(score)))
            .collect::<Vec<_>>()
            .join(" ")
    };
    writeln!(
        output,
        "{fixture} | L{layer} | {regime:?} | {floor_bytes} | {first_floor} | {}",
        values(|score| score.dram_bytes),
    )
    .unwrap();
    writeln!(
        output,
        "  source ops floor={floor_ops}: {}",
        values(|score| score.source_ops),
    )
    .unwrap();
    writeln!(
        output,
        "  instructions: {}",
        values(|score| score.instructions as u128),
    )
    .unwrap();
    writeln!(
        output,
        "  encoded lanes: {}",
        values(|score| score.encoded_lanes as u128),
    )
    .unwrap();
    writeln!(
        output,
        "  arithmetic ops: {}",
        values(|score| score.arithmetic_ops as u128),
    )
    .unwrap();
    writeln!(
        output,
        "  DRAM above compulsory floor: {}",
        scores
            .iter()
            .enumerate()
            .map(|(index, score)| format!(
                "c{}={}",
                index + 2,
                format_percentage_above_floor(score.dram_bytes, floor_bytes),
            ))
            .collect::<Vec<_>>()
            .join(" "),
    )
    .unwrap();

    let mut improvements = Vec::new();
    if let Some(floor_index) = scores
        .iter()
        .position(|score| score.dram_bytes == floor_bytes)
    {
        let mut best = scores[floor_index].secondary_key();
        for (index, score) in scores.iter().enumerate().skip(floor_index + 1) {
            if score.dram_bytes == floor_bytes && score.secondary_key() < best {
                best = score.secondary_key();
                improvements.push(format!("c{}={best:?}", index + 2));
            }
        }
    }
    writeln!(
        output,
        "  post-floor secondary improvements: {}",
        if improvements.is_empty() {
            "none".to_owned()
        } else {
            improvements.join(", ")
        },
    )
    .unwrap();
}

fn render_u128_budget_values(values: &[u128; 15]) -> String {
    values
        .iter()
        .enumerate()
        .map(|(index, value)| format!("c{}={value}", index + 2))
        .collect::<Vec<_>>()
        .join(" ")
}

fn format_percentage_above_floor(value: u128, floor: u128) -> String {
    if floor == 0 {
        "n/a (zero floor)".to_owned()
    } else {
        format_percentage(
            value
                .checked_sub(floor)
                .expect("DRAM must not be below floor"),
            floor,
        )
    }
}

fn format_percentage(numerator: u128, denominator: u128) -> String {
    if denominator == 0 {
        return "n/a (zero denominator)".to_owned();
    }
    let basis_points = numerator
        .checked_mul(10_000)
        .expect("census percentage overflow")
        / denominator;
    format!("{}.{:02}%", basis_points / 100, basis_points % 100)
}

fn assert_plan4_artifact_consumer_is_reconstruction_only() {
    let artifact_consumer = source_function_body(
        include_str!("../src/eval_plan/backward_artifact.rs"),
        "pub fn compile_backward_plan_artifact(",
    );
    assert!(artifact_consumer.contains("reconstruct_paging_plan"));
    for (name, body) in [
        ("artifact consumer", artifact_consumer),
        (
            "paging certification",
            source_function_body(
                include_str!("../src/eval_plan/backward_search/replay.rs"),
                "pub fn compile_and_certify_paging(",
            ),
        ),
        (
            "paging reconstruction",
            source_function_body(
                include_str!("../src/eval_plan/backward_search/pager.rs"),
                "pub fn reconstruct_paging_plan(",
            ),
        ),
    ] {
        for forbidden in [
            "solve_production_paging",
            "solve_exact_paging",
            "run_search_driver",
            "search_production",
        ] {
            assert!(
                !body.contains(forbidden),
                "{name} must not invoke {forbidden}",
            );
        }
    }
}

fn source_function_body<'a>(source: &'a str, signature: &str) -> &'a str {
    let function_start = source.find(signature).expect("function exists");
    let body_start = source[function_start..]
        .find('{')
        .map(|offset| function_start + offset)
        .expect("function body exists");
    let mut depth = 0usize;
    for (offset, byte) in source[body_start..].bytes().enumerate() {
        match byte {
            b'{' => depth += 1,
            b'}' => {
                depth -= 1;
                if depth == 0 {
                    return &source[body_start..=body_start + offset];
                }
            }
            _ => {}
        }
    }
    panic!("function body is balanced")
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
                PathBuf::from("/tmp").join(format!("gkr-plan4-diagnostic-{}", std::process::id()))
            }),
            may_publish_production: !filtered && !digest_only,
        })
    }

    fn checkpoint_root(&self) -> PathBuf {
        self.diagnostic_dir.as_ref().map_or_else(
            || PathBuf::from(PLAN4_PRODUCTION_CHECKPOINT_ROOT),
            |directory| directory.join("gkr-plan4-chain-checkpoints"),
        )
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

impl Plan4ChainInput {
    fn identity(&self) -> ProductionSearchIdentity {
        ProductionSearchIdentity {
            circuit: self.circuit.clone(),
            layout_fixture: self.fixture.to_owned(),
            layer: self.layer_index,
            regime: self.regime,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Plan4ChainCheckpoint {
    circuit: String,
    layout_fixture: String,
    layer: usize,
    regime: u8,
    budget_min: usize,
    budget_max: usize,
    artifact: BackwardRegimeArtifact,
}

fn plan4_regime_code(regime: BwdRegime) -> u8 {
    match regime {
        BwdRegime::R0 => 0,
        BwdRegime::Ext => 1,
    }
}

fn plan4_budget_endpoints(
    budgets: &RangeInclusive<usize>,
) -> Result<(usize, usize), BackwardArtifactError> {
    let mut values = budgets.clone();
    let budget_min = values.next().ok_or_else(|| {
        BackwardArtifactError::Publish("Plan 4 checkpoint budget range is empty".to_owned())
    })?;
    let budget_max = values.next_back().unwrap_or(budget_min);
    Ok((budget_min, budget_max))
}

fn plan4_checkpoint_record(
    input: &Plan4ChainInput,
    budgets: &RangeInclusive<usize>,
    artifact: BackwardRegimeArtifact,
) -> Result<Plan4ChainCheckpoint, BackwardArtifactError> {
    let (budget_min, budget_max) = plan4_budget_endpoints(budgets)?;
    Ok(Plan4ChainCheckpoint {
        circuit: input.circuit.clone(),
        layout_fixture: input.fixture.to_owned(),
        layer: input.layer_index,
        regime: plan4_regime_code(input.regime),
        budget_min,
        budget_max,
        artifact,
    })
}

fn plan4_checkpoint_path(
    root: &Path,
    input: &Plan4ChainInput,
    budgets: &RangeInclusive<usize>,
) -> Result<PathBuf, BackwardArtifactError> {
    let (budget_min, budget_max) = plan4_budget_endpoints(budgets)?;
    if input.circuit.is_empty()
        || !input
            .circuit
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'-'))
    {
        return Err(BackwardArtifactError::Publish(format!(
            "invalid Plan 4 checkpoint schedule stem {:?}",
            input.circuit,
        )));
    }
    Ok(root.join(format!(
        "{}-l{}-r{}-c{}-c{}.json",
        input.circuit,
        input.layer_index,
        plan4_regime_code(input.regime),
        budget_min,
        budget_max,
    )))
}

fn plan4_checkpoint_error(
    path: &Path,
    input: &Plan4ChainInput,
    detail: impl std::fmt::Display,
) -> BackwardArtifactError {
    BackwardArtifactError::Publish(format!(
        "checkpoint {} for {}/{} L{} {:?}: {detail}",
        path.display(),
        input.circuit,
        input.fixture,
        input.layer_index,
        input.regime,
    ))
}

fn load_plan4_chain_checkpoint(
    root: &Path,
    input: &Plan4ChainInput,
    budgets: &RangeInclusive<usize>,
) -> Result<Option<Plan4ChainCheckpoint>, BackwardArtifactError> {
    let path = plan4_checkpoint_path(root, input, budgets)?;
    let bytes = match std::fs::read(&path) {
        Ok(bytes) => bytes,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(None),
        Err(error) => return Err(plan4_checkpoint_error(&path, input, error)),
    };
    let checkpoint: Plan4ChainCheckpoint = serde_json::from_slice(&bytes)
        .map_err(|error| plan4_checkpoint_error(&path, input, format!("parse: {error}")))?;
    let expected =
        plan4_checkpoint_record(input, budgets, BackwardRegimeArtifact { plans: Vec::new() })?;
    if checkpoint.circuit != expected.circuit
        || checkpoint.layout_fixture != expected.layout_fixture
        || checkpoint.layer != expected.layer
        || checkpoint.regime != expected.regime
        || checkpoint.budget_min != expected.budget_min
        || checkpoint.budget_max != expected.budget_max
    {
        return Err(plan4_checkpoint_error(
            &path,
            input,
            "identity or budget range mismatch",
        ));
    }
    let expected_budgets = budgets.clone().collect::<Vec<_>>();
    if checkpoint.artifact.plans.len() != expected_budgets.len()
        || checkpoint
            .artifact
            .plans
            .iter()
            .zip(&expected_budgets)
            .any(|(plan, expected_budget)| plan.budget_cells != *expected_budget)
    {
        return Err(plan4_checkpoint_error(
            &path,
            input,
            "plan count or budget order mismatch",
        ));
    }
    for plan in &checkpoint.artifact.plans {
        compile_backward_plan_artifact(
            &input.circuit,
            input.layer_index,
            &input.canonical,
            &input.distilled,
            input.trace_len,
            plan,
        )
        .map_err(|error| {
            plan4_checkpoint_error(
                &path,
                input,
                format!("replay c{} failed: {error:?}", plan.budget_cells),
            )
        })?;
    }
    Ok(Some(checkpoint))
}

fn publish_plan4_chain_checkpoint(
    root: &Path,
    input: &Plan4ChainInput,
    budgets: &RangeInclusive<usize>,
    artifact: &BackwardRegimeArtifact,
) -> Result<(), BackwardArtifactError> {
    std::fs::create_dir_all(root).map_err(|error| {
        BackwardArtifactError::Publish(format!(
            "create checkpoint root {}: {error}",
            root.display(),
        ))
    })?;
    let destination = plan4_checkpoint_path(root, input, budgets)?;
    let file_name = destination
        .file_name()
        .and_then(|name| name.to_str())
        .ok_or_else(|| {
            BackwardArtifactError::Publish(format!(
                "invalid checkpoint destination {}",
                destination.display(),
            ))
        })?;
    let nonce = PLAN4_CHECKPOINT_NONCE.fetch_add(1, Ordering::Relaxed);
    let temporary = root.join(format!(".{file_name}.tmp-{}-{nonce}", std::process::id(),));
    let checkpoint = plan4_checkpoint_record(input, budgets, artifact.clone())?;
    publish_plan4_chain_checkpoint_to_temporary(&destination, &temporary, &checkpoint)
}

fn publish_plan4_chain_checkpoint_to_temporary(
    destination: &Path,
    temporary: &Path,
    checkpoint: &Plan4ChainCheckpoint,
) -> Result<(), BackwardArtifactError> {
    let parent = destination
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    let lock = destination.with_extension("json.publish-lock");
    let mut created_temporary = false;
    let mut created_lock = false;
    let publication = (|| {
        let mut file = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(temporary)
            .map_err(|error| {
                BackwardArtifactError::Publish(format!(
                    "create checkpoint temporary {}: {error}",
                    temporary.display(),
                ))
            })?;
        created_temporary = true;
        serde_json::to_writer_pretty(&mut file, checkpoint).map_err(|error| {
            BackwardArtifactError::Publish(format!(
                "serialize checkpoint temporary {}: {error}",
                temporary.display(),
            ))
        })?;
        file.write_all(b"\n")
            .and_then(|()| file.sync_all())
            .map_err(|error| {
                BackwardArtifactError::Publish(format!(
                    "sync checkpoint temporary {}: {error}",
                    temporary.display(),
                ))
            })?;
        drop(file);

        let reloaded: Plan4ChainCheckpoint =
            serde_json::from_slice(&std::fs::read(temporary).map_err(|error| {
                BackwardArtifactError::Publish(format!(
                    "reload checkpoint temporary {}: {error}",
                    temporary.display(),
                ))
            })?)
            .map_err(|error| {
                BackwardArtifactError::Publish(format!(
                    "parse checkpoint temporary {}: {error}",
                    temporary.display(),
                ))
            })?;
        if reloaded != *checkpoint {
            return Err(BackwardArtifactError::Publish(format!(
                "checkpoint temporary {} changed across serialization",
                temporary.display(),
            )));
        }

        let _lock_file = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&lock)
            .map_err(|error| {
                BackwardArtifactError::Publish(format!(
                    "claim checkpoint destination {}: {error}",
                    destination.display(),
                ))
            })?;
        created_lock = true;
        match std::fs::read(destination) {
            Ok(bytes) => {
                let existing: Plan4ChainCheckpoint =
                    serde_json::from_slice(&bytes).map_err(|error| {
                        BackwardArtifactError::Publish(format!(
                            "existing checkpoint {} is not replaceable: {error}",
                            destination.display(),
                        ))
                    })?;
                if existing != *checkpoint {
                    return Err(BackwardArtifactError::Publish(format!(
                        "existing checkpoint {} has different identity, range, or artifact",
                        destination.display(),
                    )));
                }
                return Ok(());
            }
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => {
                return Err(BackwardArtifactError::Publish(format!(
                    "inspect checkpoint destination {}: {error}",
                    destination.display(),
                )));
            }
        }
        std::fs::rename(temporary, destination).map_err(|error| {
            BackwardArtifactError::Publish(format!(
                "rename checkpoint {} to {}: {error}",
                temporary.display(),
                destination.display(),
            ))
        })?;
        std::fs::File::open(parent)
            .and_then(|directory| directory.sync_all())
            .map_err(|error| {
                BackwardArtifactError::Publish(format!(
                    "sync checkpoint directory {}: {error}",
                    parent.display(),
                ))
            })?;
        Ok(())
    })();
    if created_lock {
        let _ = std::fs::remove_file(&lock);
    }
    if created_temporary && temporary.exists() {
        let _ = std::fs::remove_file(temporary);
    }
    publication
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
    remaining_chains: BTreeMap<&'static str, FixtureProgress>,
    stopped: bool,
}

struct FixtureProgress {
    remaining: usize,
    failed: bool,
}

struct Plan4ProgressSnapshot {
    completed: usize,
    new_entries: usize,
    resumed_entries: usize,
    total_entries: usize,
    completed_circuits: usize,
    total_circuits: usize,
    active: Vec<ActiveChain>,
    elapsed: Duration,
    eta: Option<Duration>,
}

fn plan4_estimated_remaining(
    elapsed: Duration,
    completed: usize,
    total: usize,
) -> Option<Duration> {
    if completed == 0 {
        return None;
    }
    let remaining = total.saturating_sub(completed) as u128;
    let nanos = elapsed
        .as_nanos()
        .checked_mul(remaining)?
        .checked_div(completed as u128)?;
    Some(Duration::from_nanos(nanos.min(u64::MAX as u128) as u64))
}

struct Plan4Progress {
    started: Instant,
    total_entries: usize,
    total_circuits: usize,
    completed: AtomicUsize,
    new_entries: AtomicUsize,
    resumed_entries: AtomicUsize,
    completed_circuits: AtomicUsize,
    state: Mutex<Plan4ProgressState>,
    wake: Condvar,
}

impl Plan4Progress {
    fn new(inputs: &[Plan4ChainInput], entries_per_chain: usize) -> Arc<Self> {
        let mut remaining_chains = BTreeMap::new();
        for input in inputs {
            remaining_chains
                .entry(input.fixture)
                .or_insert(FixtureProgress {
                    remaining: 0,
                    failed: false,
                })
                .remaining += 1;
        }
        Arc::new(Self {
            started: Instant::now(),
            total_entries: inputs.len() * entries_per_chain,
            total_circuits: remaining_chains.len(),
            completed: AtomicUsize::new(0),
            new_entries: AtomicUsize::new(0),
            resumed_entries: AtomicUsize::new(0),
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
            BackwardRegimeChainProgress::Completed { .. } => {}
        }
    }

    fn checkpointed_chain(&self, input: &Plan4ChainInput, entries: usize, resumed: bool) {
        let mut state = self.state.lock().expect("lock Plan 4 checkpoint progress");
        state.active.remove(&input.ordinal);
        self.completed.fetch_add(entries, Ordering::Relaxed);
        if resumed {
            self.resumed_entries.fetch_add(entries, Ordering::Relaxed);
        } else {
            self.new_entries.fetch_add(entries, Ordering::Relaxed);
        }
    }

    fn chain_done(&self, input: &Plan4ChainInput, succeeded: bool) {
        let mut state = self.state.lock().expect("lock Plan 4 progress");
        state.active.remove(&input.ordinal);
        let fixture = state
            .remaining_chains
            .get_mut(input.fixture)
            .expect("fixture chain count exists");
        fixture.failed |= !succeeded;
        fixture.remaining -= 1;
        if fixture.remaining == 0 && !fixture.failed {
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
        let snapshot = self.snapshot();
        let mut stderr = std::io::stderr().lock();
        Self::write_snapshot(&snapshot, &mut stderr).expect("write Plan 4 progress snapshot");
        stderr.flush().expect("flush Plan 4 progress");
    }

    fn snapshot(&self) -> Plan4ProgressSnapshot {
        let elapsed = self.started.elapsed();
        let completed = self.completed.load(Ordering::Relaxed);
        let new_entries = self.new_entries.load(Ordering::Relaxed);
        let resumed_entries = self.resumed_entries.load(Ordering::Relaxed);
        let completed_circuits = self.completed_circuits.load(Ordering::Relaxed);
        let active = {
            let state = self.state.lock().expect("lock Plan 4 progress snapshot");
            state.active.values().cloned().collect::<Vec<_>>()
        };
        Plan4ProgressSnapshot {
            completed,
            new_entries,
            resumed_entries,
            total_entries: self.total_entries,
            completed_circuits,
            total_circuits: self.total_circuits,
            active,
            elapsed,
            eta: plan4_estimated_remaining(elapsed, completed, self.total_entries),
        }
    }

    fn write_snapshot(
        snapshot: &Plan4ProgressSnapshot,
        mut output: impl Write,
    ) -> std::io::Result<()> {
        let eta = snapshot.eta.map_or_else(
            || "unavailable".to_owned(),
            |eta| format!("{eta:?}-estimate"),
        );
        writeln!(
            output,
            "PLAN4 progress completed={}/{} new={} resumed={} circuits={}/{} active={} elapsed={:?} eta={eta}",
            snapshot.completed,
            snapshot.total_entries,
            snapshot.new_entries,
            snapshot.resumed_entries,
            snapshot.completed_circuits,
            snapshot.total_circuits,
            snapshot.active.len(),
            snapshot.elapsed,
        )?;
        for active in &snapshot.active {
            writeln!(
                output,
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
            )?;
        }
        Ok(())
    }
}

struct Plan4Matrix {
    inputs: Vec<Plan4ChainInput>,
    outputs: Vec<Plan4ChainOutput>,
    budgets: RangeInclusive<usize>,
    summary: Plan4GenerationSummary,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Plan4GenerationSummary {
    new_entries: usize,
    resumed_entries: usize,
    exact_solver_calls: usize,
}

#[derive(Default)]
struct Plan4ChainGenerationTelemetry {
    latest: BTreeMap<
        usize,
        gkr_eval_isa::eval_plan::backward_search::production::ProductionSearchProgress,
    >,
    exact_solver_calls: usize,
}

impl Plan4ChainGenerationTelemetry {
    fn record(&mut self, event: BackwardRegimeChainProgress) {
        match event {
            BackwardRegimeChainProgress::Search {
                budget_cells,
                search,
            } => {
                self.latest.insert(budget_cells, search);
            }
            BackwardRegimeChainProgress::Completed { budget_cells } => {
                if let Some(search) = self.latest.remove(&budget_cells) {
                    self.exact_solver_calls = self
                        .exact_solver_calls
                        .checked_add(search.evaluations)
                        .expect("Plan 4 exact solver call count overflow");
                }
            }
        }
    }
}

struct Plan4ChainRun {
    output: Plan4ChainOutput,
    resumed: bool,
    exact_solver_calls: usize,
}

fn produce_plan4_chain(
    input: &Plan4ChainInput,
    budgets: RangeInclusive<usize>,
    progress: &(dyn Fn(BackwardRegimeChainProgress) + Sync),
) -> Result<BackwardRegimeArtifact, BackwardArtifactError> {
    produce_backward_regime_chain_with_progress(
        &input.identity(),
        &input.canonical,
        &input.distilled,
        input.trace_len,
        budgets,
        progress,
    )
}

fn run_plan4_matrix(
    fixtures: &[&'static str],
    budgets: RangeInclusive<usize>,
) -> Result<Plan4Matrix, BackwardArtifactError> {
    let checkpoint_root = PathBuf::from("/tmp")
        .join(format!("gkr-plan4-diagnostic-{}", std::process::id()))
        .join("gkr-plan4-chain-checkpoints");
    run_plan4_matrix_with_checkpoints(fixtures, budgets, &checkpoint_root)
}

fn run_plan4_matrix_with_checkpoints(
    fixtures: &[&'static str],
    budgets: RangeInclusive<usize>,
    checkpoint_root: &Path,
) -> Result<Plan4Matrix, BackwardArtifactError> {
    run_plan4_matrix_with_checkpoints_and_producer(
        build_plan4_chain_inputs(fixtures),
        budgets,
        checkpoint_root,
        &produce_plan4_chain,
    )
}

fn run_plan4_matrix_with_checkpoints_and_producer<P>(
    inputs: Vec<Plan4ChainInput>,
    budgets: RangeInclusive<usize>,
    checkpoint_root: &Path,
    producer: &P,
) -> Result<Plan4Matrix, BackwardArtifactError>
where
    P: Fn(
            &Plan4ChainInput,
            RangeInclusive<usize>,
            &(dyn Fn(BackwardRegimeChainProgress) + Sync),
        ) -> Result<BackwardRegimeArtifact, BackwardArtifactError>
        + Sync,
{
    let entries_per_chain = budgets.clone().count();
    let progress = Plan4Progress::new(&inputs, entries_per_chain);
    let monitor_progress = Arc::clone(&progress);
    let monitor = std::thread::spawn(move || monitor_progress.monitor());
    let results = inputs
        .par_iter()
        .map(|input| {
            let result = (|| {
                if let Some(checkpoint) =
                    load_plan4_chain_checkpoint(checkpoint_root, input, &budgets)?
                {
                    let entries = checkpoint.artifact.plans.len();
                    let output = Plan4ChainOutput {
                        ordinal: input.ordinal,
                        fixture: input.fixture,
                        circuit: input.circuit.clone(),
                        layer_index: input.layer_index,
                        regime: input.regime,
                        artifact: checkpoint.artifact,
                    };
                    progress.checkpointed_chain(input, entries, true);
                    return Ok(Plan4ChainRun {
                        output,
                        resumed: true,
                        exact_solver_calls: 0,
                    });
                }

                let telemetry = Mutex::new(Plan4ChainGenerationTelemetry::default());
                let artifact = producer(input, budgets.clone(), &|event| {
                    if matches!(event, BackwardRegimeChainProgress::Search { .. }) {
                        progress.record(input, event);
                    }
                    telemetry
                        .lock()
                        .expect("lock Plan 4 chain telemetry")
                        .record(event);
                })?;
                publish_plan4_chain_checkpoint(checkpoint_root, input, &budgets, &artifact)?;
                let exact_solver_calls = telemetry
                    .into_inner()
                    .expect("unlock Plan 4 chain telemetry")
                    .exact_solver_calls;
                let entries = artifact.plans.len();
                let output = Plan4ChainOutput {
                    ordinal: input.ordinal,
                    fixture: input.fixture,
                    circuit: input.circuit.clone(),
                    layer_index: input.layer_index,
                    regime: input.regime,
                    artifact,
                };
                progress.checkpointed_chain(input, entries, false);
                Ok(Plan4ChainRun {
                    output,
                    resumed: false,
                    exact_solver_calls,
                })
            })();
            progress.chain_done(input, result.is_ok());
            result
        })
        .collect::<Vec<_>>();
    progress.finish();
    monitor.join().expect("join Plan 4 progress monitor");

    let mut outputs = Vec::with_capacity(results.len());
    let mut summary = Plan4GenerationSummary::default();
    let mut failures = Vec::new();
    for result in results {
        match result {
            Ok(chain) => {
                let entries = chain.output.artifact.plans.len();
                if chain.resumed {
                    summary.resumed_entries += entries;
                } else {
                    summary.new_entries += entries;
                    summary.exact_solver_calls += chain.exact_solver_calls;
                }
                outputs.push(chain.output);
            }
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
        summary,
    })
}

impl Plan4Matrix {
    fn write_generation_summary(&self, mut output: impl Write) -> std::io::Result<()> {
        writeln!(
            output,
            "PLAN4 generation new={} resumed={} exact_solver_calls={}",
            self.summary.new_entries, self.summary.resumed_entries, self.summary.exact_solver_calls,
        )
    }

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
