use super::*;
use prover::definitions::SecurityLevel;
use prover::gkr::prover_config::example_configs::packed_config_for_security_level_under_pessimistic_conjecture as packed_config;

fn geometry(config: &ProverConfig) -> BaseCommitmentGeometry {
    BaseCommitmentGeometry::from_config(
        config,
        BaseColumns {
            memory: 5,
            witness: 9,
            setup: 3,
        },
    )
    .unwrap()
}

#[test]
fn cpu_merged_identity_storage_cannot_take_the_separate_legacy_route() {
    let mut config = packed_config(20, 0, SecurityLevel::Sec100);
    assert!(!uses_base_commitment_geometry(&geometry(&config)));
    config.commitment_mode = CommitmentMode::MergedMemoryAndWitness;
    let merged = geometry(&config);
    assert!(uses_base_commitment_geometry(&merged));
    assert_eq!(merged.oracle(BaseOracleRole::Memory).logical_columns(), 14);
    assert_eq!(merged.oracle(BaseOracleRole::Witness).logical_columns(), 0);
    TraceHolder::<BF>::validate_base_layout(&merged, TreesCacheMode::CachePartial);
    assert!(
        std::panic::catch_unwind(|| validate_separate_base_commitment_geometry(&merged)).is_err()
    );
}

#[test]
fn cpu_separate_commitment_admits_only_qualified_physical_shapes() {
    for (n, k) in [(20, 0), (20, 2), (20, 4), (23, 1)] {
        let config = packed_config(n, k, SecurityLevel::Sec100);
        validate_separate_base_commitment_geometry(&geometry(&config));
    }
    for (n, k) in [(20, 1), (21, 3)] {
        let config = packed_config(n, k, SecurityLevel::Sec100);
        assert!(
            std::panic::catch_unwind(|| validate_separate_base_commitment_geometry(&geometry(
                &config
            )))
            .is_err()
        );
    }
}

#[test]
fn cpu_virtual_commitment_shapes_and_merged_reject_before_construction() {
    use crate::witness::circuit_type::DelegationCircuitType as D;
    for circuit in [D::BigIntWithControl, D::Blake2WithCompression] {
        let config = CircuitType::Delegation(circuit).prover_config(SecurityLevel::Sec100);
        validate_separate_base_commitment_geometry(&geometry(&config));
    }
    for (n, k) in [(20, 0), (21, 1), (20, 4)] {
        let mut config = packed_config(n, k, SecurityLevel::Sec100);
        config.whir_schedule.base_round.fold_log2 = 0;
        let shape = geometry(&config);
        let constructed = std::cell::Cell::new(false);
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            validate_separate_base_commitment_geometry(&shape);
            constructed.set(true);
        }))
        .is_err());
        assert!(!constructed.get());
    }
    let mut config = packed_config(20, 4, SecurityLevel::Sec100);
    config.commitment_mode = CommitmentMode::MergedMemoryAndWitness;
    assert!(
        std::panic::catch_unwind(|| validate_separate_base_commitment_geometry(&geometry(&config)))
            .is_err()
    );
    let mut config = packed_config(20, 0, SecurityLevel::Sec100);
    config.trace_len_log2 += 1;
    config.whir_schedule.base_round.fold_log2 = 2;
    let shape = geometry(&config);
    assert!(
        std::panic::catch_unwind(|| validate_separate_base_commitment_geometry(&shape)).is_err()
    );
}
