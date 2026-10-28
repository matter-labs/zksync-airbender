use super::*;
use field::Field;

fn config() -> ProverConfig {
    ProverConfig::whir_only(
        13,
        prover::gkr::prover_config::WhirSchedule::from_legacy_arrays(
            2,
            16,
            0,
            &[1, 5],
            &[1, 1],
            &[2],
            &[0, 0],
        ),
        SecurityLevel::Sec100,
    )
}

fn columns() -> BaseColumns {
    BaseColumns {
        memory: 5,
        witness: 9,
        setup: 3,
    }
}

fn setup() -> CpuGKRSetup<BF> {
    CpuGKRSetup {
        hypercube_evals: (0..3)
            .map(|_| {
                Arc::new(prover::allocation_pool::AllocationType::from(vec![
                    BF::ZERO;
                    1 << 13
                ]))
            })
            .collect(),
    }
}

#[test]
fn cpu_setup_cache_identity_binds_complete_base_geometry_before_initialization() {
    let cfg = config();
    let geometry = BaseCommitmentGeometry::from_config(&cfg, columns()).unwrap();
    let cache = LazyGpuGKRSetupHost::new(setup(), geometry);
    cache.validate_config(&cfg, columns());
    assert_eq!(cache.base_commitment_geometry(), geometry);
    for case in 0..5 {
        let mut wrong = cfg.clone();
        let mut counts = columns();
        match case {
            0 => wrong.whir_schedule.base_round.physical_packing_log2 = 1,
            1 => wrong.whir_schedule.base_round.fold_log2 = 0,
            2 => wrong.trace_len_log2 += 1,
            3 => {
                wrong.commitment_mode =
                    prover::gkr::prover_config::CommitmentMode::MergedMemoryAndWitness
            }
            _ => counts.memory += 1,
        }
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(
            || cache.validate_config(&wrong, counts)
        ))
        .is_err());
        assert!(
            cache.inner.get().is_none(),
            "rejected config must not initialize or pin setup"
        );
    }
}

#[test]
fn cpu_setup_cache_rejects_bad_logical_sources_before_gpu_or_pinning() {
    let geometry = BaseCommitmentGeometry::from_config(&config(), columns()).unwrap();
    for case in 0..2 {
        let mut bad = setup();
        if case == 0 {
            bad.hypercube_evals.pop();
        } else {
            bad.hypercube_evals[0] = Arc::new(prover::allocation_pool::AllocationType::from(vec![
                    BF::ZERO;
                    8
                ]));
        }
        assert!(std::panic::catch_unwind(|| LazyGpuGKRSetupHost::new(bad, geometry)).is_err());
    }
}
