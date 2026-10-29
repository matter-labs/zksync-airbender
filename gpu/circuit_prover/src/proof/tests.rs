use super::*;
use crate::upstream::{BaseColumns, CommitmentMode, SecurityLevel};
use gpu_trace::witness::circuit_type::{CircuitType, DelegationCircuitType as D};

fn physical_config(n: usize, k: usize) -> ProverConfig {
    prover::gkr::prover_config::example_configs::packed_config_for_security_level_under_pessimistic_conjecture(n, k, SecurityLevel::Sec100)
}

fn geometry(config: &ProverConfig) -> BaseCommitmentGeometry {
    let columns = if config.trace_len_log2 == 23 {
        BaseColumns {
            memory: 38,
            witness: 58,
            setup: 10,
        }
    } else {
        BaseColumns {
            memory: 225,
            witness: 538,
            setup: 6,
        }
    };
    BaseCommitmentGeometry::from_config(config, columns).unwrap()
}

#[test]
fn cpu_merged_proof_admission_is_physical_blake_only() {
    let mut config = physical_config(20, 4);
    config.commitment_mode = CommitmentMode::MergedMemoryAndWitness;
    let shape = geometry(&config);
    validate_base_proof_geometry_policy(&shape, ProofMemoryPolicy::default(), 4);
    assert_eq!(shape.total_physical_columns(), 49);
    super::merged_commitment::validate_merged_circuit_type(
        CircuitType::Delegation(D::Blake2WithCompression),
        &shape,
    );
    assert!(
        std::panic::catch_unwind(|| super::merged_commitment::validate_merged_circuit_type(
            CircuitType::Delegation(D::Blake2GFunction),
            &shape,
        ))
        .is_err()
    );
    for (n, k) in [(20, 0), (20, 2), (23, 1)] {
        let mut config = physical_config(n, k);
        config.commitment_mode = CommitmentMode::MergedMemoryAndWitness;
        assert!(
            std::panic::catch_unwind(|| validate_base_proof_geometry_policy(
                &geometry(&config),
                ProofMemoryPolicy::default(),
                4,
            ))
            .is_err()
        );
    }
    let mut virtual_config =
        CircuitType::Delegation(D::Blake2WithCompression).prover_config(SecurityLevel::Sec100);
    virtual_config.commitment_mode = CommitmentMode::MergedMemoryAndWitness;
    assert!(
        std::panic::catch_unwind(|| validate_base_proof_geometry_policy(
            &geometry(&virtual_config),
            ProofMemoryPolicy::default(),
            4,
        ))
        .is_err()
    );
    let nondefault = ProofMemoryPolicy {
        memory: memory_policy::OpeningStrategy::PerCoset,
        ..Default::default()
    };
    validate_base_proof_geometry_policy(&shape, nondefault, 4);
    validate_baby_bear_base_proof_policy(&shape, nondefault, 27);
    assert!(std::panic::catch_unwind(|| {
        gpu_trace::trace::memory::validate_separate_base_commitment_geometry(&shape)
    })
    .is_err());
}

#[test]
fn cpu_physical_proof_admission_checks_full_schedule_and_policy() {
    let policy = ProofMemoryPolicy::default();
    for (n, k) in [(20, 4), (20, 2), (23, 1)] {
        let config = physical_config(n, k);
        let geometry = geometry(&config);
        validate_base_proof_geometry_policy(&geometry, policy, 4);
        validate_baby_bear_base_proof_policy(&geometry, policy, 27);
        gpu_whir::validate_baby_bear_recursive_schedule((n + k) as u32, &config.whir_schedule, 27);
        for case in 0..4 {
            let mut bad = config.whir_schedule.clone();
            match case {
                0 => bad.base_round.folding_pow_bits = 1,
                1 => bad.internal_rounds[0].num_ood_samples = 2,
                2 => bad.internal_rounds[0].ood_pow_bits = 1,
                _ => bad.internal_rounds[0].folding_pow_bits = 1,
            }
            assert!(
                std::panic::catch_unwind(|| gpu_whir::validate_baby_bear_recursive_schedule(
                    (n + k) as u32,
                    &bad,
                    27,
                ))
                .is_err()
            );
        }
        let nondefault = ProofMemoryPolicy {
            setup: memory_policy::OpeningStrategy::PerCoset,
            ..policy
        };
        validate_base_proof_geometry_policy(&geometry, nondefault, 4);
        validate_baby_bear_base_proof_policy(&geometry, nondefault, 27);
        assert!(std::panic::catch_unwind(|| {
            gpu_trace::trace::holder::validate_baby_bear_base_geometry(&geometry, (n + k) as u32)
        })
        .is_err());
    }
    let unqualified = geometry(&physical_config(21, 3));
    assert!(
        std::panic::catch_unwind(|| validate_base_proof_geometry_policy(&unqualified, policy, 4))
            .is_err()
    );
}

#[test]
fn cpu_virtual_admission_checks_shape_policy_and_merged_mode() {
    for circuit in [D::BigIntWithControl, D::Blake2WithCompression] {
        let config = CircuitType::Delegation(circuit).prover_config(SecurityLevel::Sec100);
        let geometry = geometry(&config);
        assert!(geometry.is_virtual_packing());
        let policy = ProofMemoryPolicy {
            memory: memory_policy::OpeningStrategy::InPlace,
            ..Default::default()
        };
        validate_base_proof_geometry_policy(&geometry, policy, 4);
        validate_baby_bear_base_proof_policy(&geometry, policy, 27);
    }
    for (n, k) in [(20, 0), (21, 1), (20, 4)] {
        let mut config = physical_config(n, k);
        config.whir_schedule.base_round.fold_log2 = 0;
        assert!(
            std::panic::catch_unwind(|| validate_base_proof_geometry_policy(
                &geometry(&config),
                ProofMemoryPolicy::default(),
                4,
            ))
            .is_err()
        );
    }
    let mut config =
        CircuitType::Delegation(D::Blake2WithCompression).prover_config(SecurityLevel::Sec100);
    config.commitment_mode = CommitmentMode::MergedMemoryAndWitness;
    assert!(
        std::panic::catch_unwind(|| validate_base_proof_geometry_policy(
            &geometry(&config),
            ProofMemoryPolicy::default(),
            4,
        ))
        .is_err()
    );
}

#[test]
fn cpu_valid_memory_policies_admit_all_supported_base_geometries() {
    let mut configs: Vec<_> = [(20, 2), (20, 4), (23, 1)]
        .map(|(n, k)| physical_config(n, k))
        .into();
    for circuit in [D::BigIntWithControl, D::Blake2WithCompression] {
        configs.push(CircuitType::Delegation(circuit).prover_config(SecurityLevel::Sec100));
    }
    let mut merged = physical_config(20, 4);
    merged.commitment_mode = CommitmentMode::MergedMemoryAndWitness;
    configs.push(merged);
    let mut admitted = 0;
    for config in configs {
        let geometry = geometry(&config);
        for policy in ProofMemoryPolicy::candidates() {
            validate_base_proof_geometry_policy(&geometry, policy, 4);
            validate_baby_bear_base_proof_policy(&geometry, policy, 27);
            admitted += 1;
        }
        for gkr in memory_policy::GkrMemoryPolicy::candidates() {
            let policy = ProofMemoryPolicy {
                gkr,
                ..Default::default()
            };
            validate_base_proof_geometry_policy(&geometry, policy, 4);
            validate_baby_bear_base_proof_policy(&geometry, policy, 27);
        }
    }
    assert_eq!(admitted, 6 * 144);
}

#[test]
fn cpu_virtual_proof_admission_accepts_production_preset_policies() {
    for (delegation, stem) in [
        (D::BigIntWithControl, "bigint_with_extended_control"),
        (D::Blake2WithCompression, "blake2_with_extended_control"),
        (D::Blake2GFunction, "blake2_g_function"),
        (D::KeccakSpecial5, "keccak_special5"),
        (D::KeccakChi5, "keccak_chi5"),
        (D::KeccakColumnParity, "keccak_column_parity"),
        (D::KeccakThetaRho, "keccak_theta_rho"),
    ] {
        let circuit = CircuitType::Delegation(delegation);
        let config = circuit.prover_config(SecurityLevel::Sec100);
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../cs/compiled_circuits")
            .join(format!("{stem}_layout_gkr.json"));
        let artifact: GKRCircuitArtifact<BF> =
            serde_json::from_reader(std::fs::File::open(path).unwrap()).unwrap();
        let geometry =
            BaseCommitmentGeometry::from_config(&config, BaseColumns::of(&artifact)).unwrap();
        let main_layers = artifact.layers.len();
        for arena in [21usize << 30, 30usize << 30] {
            let policy = memory_policy::presets::policy(circuit, arena);
            validate_base_proof_geometry_policy(&geometry, policy, main_layers);
            validate_baby_bear_base_proof_policy(&geometry, policy, 27);
        }
        let nonpreset = ProofMemoryPolicy {
            gkr: memory_policy::GkrMemoryPolicy::Recompute {
                value_layers: 1,
                cache_layers: 1,
            },
            setup: memory_policy::OpeningStrategy::InPlace,
            memory: memory_policy::OpeningStrategy::PerCoset,
            ..Default::default()
        };
        validate_base_proof_geometry_policy(&geometry, nonpreset, main_layers);
        validate_baby_bear_base_proof_policy(&geometry, nonpreset, 27);
        let invalid = ProofMemoryPolicy {
            gkr: memory_policy::GkrMemoryPolicy::Recompute {
                value_layers: 0,
                cache_layers: 0,
            },
            ..Default::default()
        };
        assert!(
            std::panic::catch_unwind(|| validate_base_proof_geometry_policy(
                &geometry,
                invalid,
                main_layers
            ))
            .is_err()
        );
    }
}

#[test]
fn cpu_semantic_policy_failures_precede_transfer_construction() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../cs/compiled_circuits/blake2_with_extended_control_layout_gkr.json");
    let artifact: GKRCircuitArtifact<BF> =
        serde_json::from_reader(std::fs::File::open(path).unwrap()).unwrap();
    let circuit = CircuitType::Delegation(D::Blake2WithCompression);
    let config = circuit.prover_config(SecurityLevel::Sec100);
    let final_trace_log = artifact.trace_len.trailing_zeros();
    let programs = GkrPrograms::compile(circuit, Arc::new(artifact)).unwrap();
    let layers = programs.main_layers_count();
    let mut invalid: Vec<_> = [
        (0, 0, "recomputation must omit a nonempty prefix"),
        (layers, 0, "value omission must retain"),
        (0, layers + 1, "cache omission exceeds"),
    ]
    .into_iter()
    .map(|(value_layers, cache_layers, expected)| {
        (
            ProofMemoryPolicy {
                gkr: memory_policy::GkrMemoryPolicy::Recompute {
                    value_layers,
                    cache_layers,
                },
                ..Default::default()
            },
            expected,
        )
    })
    .collect();
    let mut unavailable_cosets = ProofMemoryPolicy::default();
    unavailable_cosets.witness.post_commitment =
        memory_policy::WitnessPostCommitStorage::RawEvaluations;
    invalid.push((unavailable_cosets, "invalid witness memory policy"));
    for (policy, expected) in invalid {
        let constructed = std::cell::Cell::new(false);
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            admit_dr_tail_before_transfers(
                Some(DrTailPreflightRequest {
                    gkr_programs: &programs,
                    prover_config: &config,
                    final_trace_size_log_2: final_trace_log,
                    device_id: 0,
                    memory_policy: policy,
                    twiddle_domain_log2: 27,
                }),
                |_| constructed.set(true),
            )
            .unwrap();
        }));
        let error = result.expect_err("invalid policy must fail before device admission");
        let message = error
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| error.downcast_ref::<&str>().copied())
            .unwrap();
        assert!(message.contains(expected), "unexpected failure: {message}");
        assert!(!constructed.get());
    }
}
