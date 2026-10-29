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
    use gpu_trace::witness::circuit_type::{CircuitType, DelegationCircuitType};
    let mut config = physical_config(20, 4);
    config.commitment_mode = CommitmentMode::MergedMemoryAndWitness;
    let shape = geometry(&config);
    validate_base_proof_geometry_policy(
        CircuitType::Delegation(D::Blake2WithCompression),
        &shape,
        ProofMemoryPolicy::default(),
    );
    assert_eq!(shape.total_physical_columns(), 49);
    super::merged_commitment::validate_merged_circuit_type(
        CircuitType::Delegation(DelegationCircuitType::Blake2WithCompression),
        &shape,
    );
    assert!(
        std::panic::catch_unwind(|| super::merged_commitment::validate_merged_circuit_type(
            CircuitType::Delegation(DelegationCircuitType::Blake2GFunction),
            &shape,
        ))
        .is_err()
    );
    for (n, k) in [(20, 0), (20, 2), (23, 1)] {
        let mut config = physical_config(n, k);
        config.commitment_mode = CommitmentMode::MergedMemoryAndWitness;
        assert!(
            std::panic::catch_unwind(|| validate_base_proof_geometry_policy(
                gpu_trace::witness::circuit_type::CircuitType::Delegation(
                    gpu_trace::witness::circuit_type::DelegationCircuitType::Blake2WithCompression
                ),
                &geometry(&config),
                ProofMemoryPolicy::default(),
            ))
            .is_err()
        );
    }
    let mut virtual_config = CircuitType::Delegation(DelegationCircuitType::Blake2WithCompression)
        .prover_config(SecurityLevel::Sec100);
    virtual_config.commitment_mode = CommitmentMode::MergedMemoryAndWitness;
    assert!(
        std::panic::catch_unwind(|| validate_base_proof_geometry_policy(
            gpu_trace::witness::circuit_type::CircuitType::Delegation(
                gpu_trace::witness::circuit_type::DelegationCircuitType::Blake2WithCompression
            ),
            &geometry(&virtual_config),
            ProofMemoryPolicy::default(),
        ))
        .is_err()
    );
    let mut nondefault = ProofMemoryPolicy::default();
    nondefault.memory = gpu_trace::trace::holder::OpeningStrategy::PerCoset;
    assert!(
        std::panic::catch_unwind(|| validate_base_proof_geometry_policy(
            gpu_trace::witness::circuit_type::CircuitType::Delegation(
                gpu_trace::witness::circuit_type::DelegationCircuitType::Blake2WithCompression
            ),
            &shape,
            nondefault
        ))
        .is_err()
    );
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
        validate_base_proof_geometry_policy(
            CircuitType::Delegation(D::Blake2WithCompression),
            &geometry,
            policy,
        );
        gpu_trace::trace::holder::validate_baby_bear_base_opening(
            &geometry,
            gpu_trace::trace::holder::OpeningStrategy::AllCosets,
            gpu_trace::trace::holder::TreesCacheMode::CachePartial,
            27,
        );
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
                    27
                ))
                .is_err()
            );
        }
        let mut wrong_policy = policy;
        wrong_policy.setup = gpu_trace::trace::holder::OpeningStrategy::PerCoset;
        assert!(
            std::panic::catch_unwind(|| validate_base_proof_geometry_policy(
                gpu_trace::witness::circuit_type::CircuitType::Delegation(
                    gpu_trace::witness::circuit_type::DelegationCircuitType::Blake2WithCompression
                ),
                &geometry,
                wrong_policy
            ))
            .is_err()
        );
        assert!(std::panic::catch_unwind(|| {
            gpu_trace::trace::holder::validate_baby_bear_base_geometry(&geometry, (n + k) as u32)
        })
        .is_err());
    }
    let unqualified = geometry(&physical_config(21, 3));
    assert!(
        std::panic::catch_unwind(|| validate_base_proof_geometry_policy(
            gpu_trace::witness::circuit_type::CircuitType::Delegation(
                gpu_trace::witness::circuit_type::DelegationCircuitType::Blake2WithCompression
            ),
            &unqualified,
            policy
        ))
        .is_err()
    );
}

#[test]
fn cpu_virtual_admission_checks_shape_policy_and_merged_mode() {
    use gpu_trace::witness::circuit_type::{CircuitType, DelegationCircuitType as D};
    for circuit in [D::BigIntWithControl, D::Blake2WithCompression] {
        let config = CircuitType::Delegation(circuit).prover_config(SecurityLevel::Sec100);
        let geometry = geometry(&config);
        assert!(geometry.is_virtual_packing());
        validate_base_proof_geometry_policy(
            CircuitType::Delegation(D::Blake2WithCompression),
            &geometry,
            ProofMemoryPolicy::default(),
        );
        let mut wrong_policy = ProofMemoryPolicy::default();
        wrong_policy.memory = gpu_trace::trace::holder::OpeningStrategy::PerCoset;
        assert!(
            std::panic::catch_unwind(|| validate_base_proof_geometry_policy(
                gpu_trace::witness::circuit_type::CircuitType::Delegation(
                    gpu_trace::witness::circuit_type::DelegationCircuitType::Blake2WithCompression
                ),
                &geometry,
                wrong_policy
            ))
            .is_err()
        );
    }
    for (n, k) in [(20, 0), (21, 1), (20, 4)] {
        let mut config = physical_config(n, k);
        config.whir_schedule.base_round.fold_log2 = 0;
        assert!(
            std::panic::catch_unwind(|| validate_base_proof_geometry_policy(
                gpu_trace::witness::circuit_type::CircuitType::Delegation(
                    gpu_trace::witness::circuit_type::DelegationCircuitType::Blake2WithCompression
                ),
                &geometry(&config),
                ProofMemoryPolicy::default()
            ))
            .is_err()
        );
    }
    let mut config =
        CircuitType::Delegation(D::Blake2WithCompression).prover_config(SecurityLevel::Sec100);
    config.commitment_mode = CommitmentMode::MergedMemoryAndWitness;
    assert!(
        std::panic::catch_unwind(|| validate_base_proof_geometry_policy(
            gpu_trace::witness::circuit_type::CircuitType::Delegation(
                gpu_trace::witness::circuit_type::DelegationCircuitType::Blake2WithCompression
            ),
            &geometry(&config),
            ProofMemoryPolicy::default()
        ))
        .is_err()
    );
}

#[test]
fn cpu_virtual_proof_admission_accepts_production_preset_policies() {
    use gpu_trace::witness::circuit_type::{CircuitType, DelegationCircuitType as D};
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
        for arena in [21usize << 30, 30usize << 30] {
            let policy = memory_policy::presets::policy(circuit, arena);
            validate_base_proof_geometry_policy(circuit, &geometry, policy);
            assert_eq!(policy.setup, memory_policy::OpeningStrategy::AllCosets);
            assert_eq!(policy.memory, memory_policy::OpeningStrategy::AllCosets);
            assert_eq!(
                policy.witness.commitment,
                memory_policy::WitnessCommitmentStrategy::AllCosets
            );
        }
        let unqualified = ProofMemoryPolicy {
            gkr: memory_policy::GkrMemoryPolicy::Recompute {
                value_layers: 0,
                cache_layers: 0,
            },
            ..Default::default()
        };
        assert!(
            std::panic::catch_unwind(|| validate_base_proof_geometry_policy(
                circuit,
                &geometry,
                unqualified
            ))
            .is_err()
        );
    }
}
