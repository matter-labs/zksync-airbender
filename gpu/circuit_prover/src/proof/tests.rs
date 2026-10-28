use super::*;
use crate::upstream::{BaseColumns, SecurityLevel};

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
fn cpu_physical_proof_admission_checks_full_schedule_and_policy() {
    let policy = ProofMemoryPolicy::default();
    for (n, k) in [(20, 4), (20, 2), (23, 1)] {
        let config = physical_config(n, k);
        let geometry = geometry(&config);
        validate_physical_proof_geometry_policy(&geometry, policy);
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
            std::panic::catch_unwind(|| validate_physical_proof_geometry_policy(
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
        std::panic::catch_unwind(|| validate_physical_proof_geometry_policy(&unqualified, policy))
            .is_err()
    );
}

#[test]
fn cpu_virtual_and_merged_reject_independently_of_physical_packing() {
    for k in [0, 2] {
        let mut config = physical_config(20, k);
        config.whir_schedule.base_round.fold_log2 = 0;
        let geometry = geometry(&config);
        assert!(geometry.is_virtual_packing());
        let failure = std::panic::catch_unwind(|| {
            validate_physical_proof_geometry_policy(&geometry, ProofMemoryPolicy::default())
        })
        .unwrap_err();
        let message = failure
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| failure.downcast_ref::<&str>().copied())
            .unwrap();
        assert!(message.contains("virtual base commitment proofs"));
    }
    let mut config = physical_config(20, 4);
    config.commitment_mode = CommitmentMode::MergedMemoryAndWitness;
    assert!(
        std::panic::catch_unwind(|| validate_physical_proof_geometry_policy(
            &geometry(&config),
            ProofMemoryPolicy::default()
        ))
        .is_err()
    );
}
