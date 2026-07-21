mod common;

use std::sync::OnceLock;

use cs::gkr_compiler::dag_ir::{BwdRegime, ReadPlace, VirtualSetupKind};
use gkr_eval_isa::bwd::distill::distill;
use gkr_eval_isa::bwd::source::{BwdSpecial, BwdSpecialTable, OriginLeaf};
use gkr_eval_isa::eval_plan::backward_search::problem::build_backward_search_problem;
use gkr_eval_isa::eval_plan::backward_search::{
    ProductionPagingSolver, ProductionSearchIdentity, search_production_backward,
    solve_production_paging,
};
use gkr_eval_isa::eval_plan::{
    BackwardArtifactCoordinate, BackwardArtifactError, BackwardEvaluationCircuitArtifact,
    BackwardLayerArtifact, BackwardPlanArtifact, BackwardRegimeArtifact, BackwardScoreArtifact,
    CanonicalU128, DomainCertificate, SourceCostArtifact, capture_backward_plan_artifact,
    compile_backward_plan_artifact, load_backward_evaluation_artifact, select_backward_plan,
};
use gkr_eval_isa::fwd::encode::encode;
use gkr_eval_isa::fwd::source::virtual_setup_kind_code;

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
