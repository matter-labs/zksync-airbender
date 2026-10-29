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

fn artifact(name: &str) -> Arc<GKRCircuitArtifact<BF>> {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../cs/compiled_circuits")
        .join(format!("{name}_layout_gkr.json"));
    Arc::new(serde_json::from_reader(std::fs::File::open(path).unwrap()).unwrap())
}

#[test]
fn cpu_resolved_request_rejects_identity_and_mode_before_transfers() {
    use gpu_trace::witness::circuit_type::{DelegationCircuitType, UnrolledCircuitType};
    let kind = CircuitType::Delegation(DelegationCircuitType::Blake2WithCompression);
    let circuit = artifact("blake2_with_extended_control");
    let config = gpu_circuit_prover::config::prover_config(kind, SecurityLevel::Sec100).unwrap();
    let resolved = ResolvedProverConfig::new(kind, Arc::clone(&circuit), config.clone());
    resolved.validate_request(kind, SecurityLevel::Sec100, &circuit);
    assert_eq!(
        resolved.config(),
        &kind.prover_config(SecurityLevel::Sec100)
    );
    assert_eq!(
        resolved.geometry().logical_columns(),
        BaseColumns::of(&circuit)
    );
    // Primitive memory admission is qualified; execution requests retain their
    // separate fail-closed boundary in admit_inputs_before_transfers.
    assert!(resolved.geometry().is_virtual_packing());
    gpu_trace::trace::memory::validate_memory_commitment_config(
        resolved.config(),
        &resolved.geometry(),
        &circuit,
    );

    for (request_kind, request_artifact) in [
        (
            CircuitType::Unrolled(UnrolledCircuitType::Unified),
            Arc::clone(&circuit),
        ),
        (kind, Arc::new((*circuit).clone())),
    ] {
        let constructed = std::cell::Cell::new(false);
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            resolved.validate_request(request_kind, SecurityLevel::Sec100, &request_artifact);
            constructed.set(true);
        }))
        .is_err());
        assert!(!constructed.get());
    }
    let mut merged = config;
    merged.commitment_mode = CommitmentMode::MergedMemoryAndWitness;
    let merged = ResolvedProverConfig::new(kind, Arc::clone(&circuit), merged);
    assert!(std::panic::catch_unwind(|| merged.validate_request(
        kind,
        SecurityLevel::Sec100,
        &circuit
    ))
    .is_err());
}

#[test]
fn cpu_resolved_physical_request_uses_current_artifact_geometry() {
    use gpu_trace::witness::circuit_type::{DelegationCircuitType, UnrolledCircuitType};
    use prover::gkr::prover_config::example_configs::packed_config_for_security_level_under_pessimistic_conjecture as packed_config;
    for (kind, name, n, k) in [
        (
            CircuitType::Delegation(DelegationCircuitType::Blake2WithCompression),
            "blake2_with_extended_control",
            20,
            2,
        ),
        (
            CircuitType::Delegation(DelegationCircuitType::Blake2WithCompression),
            "blake2_with_extended_control",
            20,
            4,
        ),
        (
            CircuitType::Unrolled(UnrolledCircuitType::Unified),
            "unified_reduced_machine",
            23,
            1,
        ),
    ] {
        let circuit = artifact(name);
        let resolved = ResolvedProverConfig::new(
            kind,
            Arc::clone(&circuit),
            packed_config(n, k, SecurityLevel::Sec100),
        );
        let constructed = std::cell::Cell::new(false);
        resolved.validate_request(kind, SecurityLevel::Sec100, &circuit);
        gpu_trace::trace::memory::validate_memory_commitment_config(
            resolved.config(),
            &resolved.geometry(),
            &circuit,
        );
        constructed.set(true);
        assert!(constructed.get());
        assert_eq!(
            resolved.geometry().logical_columns(),
            BaseColumns::of(&circuit)
        );
        let mut wrong = resolved.config().clone();
        wrong.whir_schedule.base_round.fold_log2 = 0;
        assert!(std::panic::catch_unwind(|| {
            gpu_trace::trace::memory::validate_memory_commitment_config(
                &wrong,
                &resolved.geometry(),
                &circuit,
            )
        })
        .is_err());
    }
}

#[test]
fn cpu_worker_admission_rejects_metadata_before_transfer_construction() {
    use gpu_trace::witness::circuit_type::{DelegationCircuitType, UnrolledCircuitType};
    let kind = CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns);
    let circuit = artifact("inits_and_teardowns");
    let config = gpu_circuit_prover::config::prover_config(kind, SecurityLevel::Sec100).unwrap();
    let resolved = Arc::new(ResolvedProverConfig::new(
        kind,
        Arc::clone(&circuit),
        config.clone(),
    ));
    assert_eq!(resolved.geometry().logical_columns().setup, 0);
    let cache = Arc::new(LazyGpuGKRSetupHost::new(
        CpuGKRSetup {
            hypercube_evals: vec![],
        },
        resolved.geometry(),
    ));
    assert!(cache.inner.set(None).is_ok());
    let precomputations = CircuitPrecomputations {
        gkr_programs: Arc::new(GkrPrograms::compile(kind, Arc::clone(&circuit)).unwrap()),
        setup_host: cache,
        decoder_host: None,
        resolved_config: resolved,
    };
    assert_eq!(
        precomputations.setup_host.base_commitment_geometry(),
        precomputations.resolved_config.geometry()
    );
    let (setup, memory) =
        precomputations.admit_inputs_before_transfers(kind, SecurityLevel::Sec100, None, 27);
    assert!(setup.is_none() && memory.is_none());
    let caps = vec![
        MerkleTreeCapVarLength {
            cap: vec![[0; 8]; config.cap_size / config.lde_factor()]
        };
        config.lde_factor()
    ];
    let (_, memory) =
        precomputations.admit_inputs_before_transfers(kind, SecurityLevel::Sec100, Some(&caps), 27);
    memory
        .unwrap()
        .validate_for_geometry(&precomputations.resolved_config.geometry());

    for case in 0..6 {
        let mut wrong = precomputations.clone();
        let mut request_kind = kind;
        let mut supplied_caps = caps.clone();
        match case {
            0 => {
                request_kind = CircuitType::Delegation(DelegationCircuitType::Blake2WithCompression)
            }
            1 => {
                wrong.gkr_programs =
                    Arc::new(GkrPrograms::compile(kind, Arc::new((*circuit).clone())).unwrap())
            }
            2 => {
                let mut cfg = config.clone();
                cfg.commitment_mode = CommitmentMode::MergedMemoryAndWitness;
                wrong.resolved_config =
                    Arc::new(ResolvedProverConfig::new(kind, Arc::clone(&circuit), cfg));
            }
            3 => {
                let mut columns = BaseColumns::of(&circuit);
                columns.memory += 1;
                wrong.setup_host = Arc::new(LazyGpuGKRSetupHost::new(
                    CpuGKRSetup {
                        hypercube_evals: vec![],
                    },
                    BaseCommitmentGeometry::from_config(&config, columns).unwrap(),
                ));
            }
            4 => {
                supplied_caps[0].cap.pop();
            }
            _ => {
                let mut cfg = config.clone();
                cfg.whir_schedule.base_round.fold_log2 = 0;
                wrong.resolved_config =
                    Arc::new(ResolvedProverConfig::new(kind, Arc::clone(&circuit), cfg));
                wrong.setup_host = Arc::new(LazyGpuGKRSetupHost::new(
                    CpuGKRSetup {
                        hypercube_evals: vec![],
                    },
                    wrong.resolved_config.geometry(),
                ));
            }
        }
        let constructed = std::cell::Cell::new(false);
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                wrong.admit_inputs_before_transfers(
                    request_kind,
                    SecurityLevel::Sec100,
                    Some(&supplied_caps),
                    27,
                );
                constructed.set(true);
            }))
            .is_err(),
            "case {case} was admitted"
        );
        assert!(!constructed.get());
    }
}

#[test]
fn cpu_worker_virtual_setup_requests_reject_before_holder_construction() {
    use gpu_trace::witness::circuit_type::DelegationCircuitType;
    for (delegation, name) in [
        (
            DelegationCircuitType::Blake2WithCompression,
            "blake2_with_extended_control",
        ),
        (
            DelegationCircuitType::BigIntWithControl,
            "bigint_with_extended_control",
        ),
    ] {
        let kind = CircuitType::Delegation(delegation);
        let circuit = artifact(name);
        let config = kind.prover_config(SecurityLevel::Sec100);
        let resolved = Arc::new(ResolvedProverConfig::new(
            kind,
            Arc::clone(&circuit),
            config.clone(),
        ));
        let geometry = resolved.geometry();
        assert!(geometry.is_virtual_packing());
        let cpu_setup = CpuGKRSetup {
            hypercube_evals: (0..geometry.logical_columns().setup)
                .map(|_| {
                    Arc::new(prover::allocation_pool::AllocationType::from(
                        vec![BF::ZERO; circuit.trace_len],
                    ))
                })
                .collect(),
        };
        let precomputations = CircuitPrecomputations {
            gkr_programs: Arc::new(GkrPrograms::compile(kind, Arc::clone(&circuit)).unwrap()),
            setup_host: Arc::new(LazyGpuGKRSetupHost::new(cpu_setup, geometry)),
            decoder_host: None,
            resolved_config: resolved,
        };
        let caps = vec![
            MerkleTreeCapVarLength {
                cap: vec![[0; 8]; config.cap_size / config.lde_factor()]
            };
            config.lde_factor()
        ];
        for caps in [None, Some(caps.as_slice())] {
            let constructed = std::cell::Cell::new(false);
            let error = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                precomputations.admit_inputs_before_transfers(
                    kind,
                    SecurityLevel::Sec100,
                    caps,
                    27,
                );
                constructed.set(true);
            }))
            .unwrap_err();
            let message = error
                .downcast_ref::<String>()
                .map(String::as_str)
                .or_else(|| error.downcast_ref::<&str>().copied())
                .unwrap();
            assert!(message.contains("virtual execution requests"));
            assert!(!constructed.get());
        }
        assert!(precomputations.setup_host.inner.get().is_none());
    }
}

#[test]
fn cpu_resolved_merged_request_accepts_only_qualified_blake_geometry() {
    use gpu_trace::witness::circuit_type::DelegationCircuitType as D;
    use prover::gkr::prover_config::example_configs::packed_config_for_security_level_under_pessimistic_conjecture as packed_config;
    let kind = CircuitType::Delegation(D::Blake2WithCompression);
    let circuit = artifact("blake2_with_extended_control");
    let canonical = kind.prover_config(SecurityLevel::Sec100);
    let mut config = packed_config(20, 4, SecurityLevel::Sec100);
    config.commitment_mode = CommitmentMode::MergedMemoryAndWitness;
    let resolved = ResolvedProverConfig::new(kind, Arc::clone(&circuit), config.clone());
    resolved.validate_request(kind, SecurityLevel::Sec100, &circuit);
    assert_eq!(resolved.geometry().total_physical_columns(), 49);
    gpu_circuit_prover::proof::merged_commitment::validate_merged_commitment_geometry(
        resolved.config(),
        &resolved.geometry(),
        &circuit,
    );
    assert_eq!(kind.prover_config(SecurityLevel::Sec100), canonical);
    assert_ne!(config, canonical, "no canonical BF route is overridden");
    for (n, k, wrong_kind) in [
        (20, 0, kind),
        (20, 2, kind),
        (23, 1, kind),
        (20, 4, CircuitType::Delegation(D::Blake2GFunction)),
    ] {
        let mut wrong = packed_config(n, k, SecurityLevel::Sec100);
        wrong.commitment_mode = CommitmentMode::MergedMemoryAndWitness;
        let resolved = ResolvedProverConfig::new(wrong_kind, Arc::clone(&circuit), wrong);
        let constructed = std::cell::Cell::new(false);
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            resolved.validate_request(wrong_kind, SecurityLevel::Sec100, &circuit);
            constructed.set(true);
        }))
        .is_err());
        assert!(!constructed.get());
    }
}

#[test]
fn cpu_worker_merged_admission_rejects_before_transfer_construction() {
    use gpu_trace::witness::circuit_type::DelegationCircuitType as D;
    use prover::gkr::prover_config::example_configs::packed_config_for_security_level_under_pessimistic_conjecture as packed_config;
    let kind = CircuitType::Delegation(D::Blake2WithCompression);
    let circuit = artifact("blake2_with_extended_control");
    let mut config = packed_config(20, 4, SecurityLevel::Sec100);
    config.commitment_mode = CommitmentMode::MergedMemoryAndWitness;
    let resolved = Arc::new(ResolvedProverConfig::new(
        kind,
        Arc::clone(&circuit),
        config.clone(),
    ));
    let geometry = resolved.geometry();
    let setup_column = Arc::new(prover::allocation_pool::AllocationType::from(
        vec![BF::ZERO; circuit.trace_len],
    ));
    let cpu_setup = || CpuGKRSetup {
        hypercube_evals: vec![Arc::clone(&setup_column); geometry.logical_columns().setup],
    };
    let make_cache = |geometry| Arc::new(LazyGpuGKRSetupHost::new(cpu_setup(), geometry));
    let cache = make_cache(geometry);
    cache.validate_config(&config, BaseColumns::of(&circuit));
    let precomputations = CircuitPrecomputations {
        gkr_programs: Arc::new(GkrPrograms::compile(kind, Arc::clone(&circuit)).unwrap()),
        setup_host: cache,
        decoder_host: None,
        resolved_config: resolved,
    };
    assert_eq!(
        precomputations.setup_host.base_commitment_geometry(),
        geometry
    );
    let caps = vec![
        MerkleTreeCapVarLength {
            cap: vec![[0; 8]; 8]
        };
        2
    ];
    for case in 0..8 {
        let mut wrong = precomputations.clone();
        let mut request_kind = kind;
        let expected = match case {
            0 => {
                request_kind = CircuitType::Delegation(D::Blake2GFunction);
                "request circuit differs from resolved config"
            }
            1 => {
                request_kind = CircuitType::Delegation(D::Blake2GFunction);
                wrong.resolved_config = Arc::new(ResolvedProverConfig::new(
                    request_kind,
                    Arc::clone(&circuit),
                    config.clone(),
                ));
                "unqualified packed merged circuit"
            }
            2 => {
                wrong.gkr_programs =
                    Arc::new(GkrPrograms::compile(kind, Arc::new((*circuit).clone())).unwrap());
                "request artifact differs from resolved config"
            }
            3 => {
                let mut separate = config.clone();
                separate.commitment_mode = CommitmentMode::SeparateMemoryAndWitness;
                wrong.setup_host = make_cache(
                    BaseCommitmentGeometry::from_config(&separate, BaseColumns::of(&circuit))
                        .unwrap(),
                );
                "setup cache commitment geometry mismatch"
            }
            4 => {
                let mut virtual_config = kind.prover_config(SecurityLevel::Sec100);
                virtual_config.commitment_mode = CommitmentMode::MergedMemoryAndWitness;
                wrong.resolved_config = Arc::new(ResolvedProverConfig::new(
                    kind,
                    Arc::clone(&circuit),
                    virtual_config,
                ));
                "virtual merged commitment is not admitted"
            }
            5 => {
                let mut unqualified = packed_config(20, 2, SecurityLevel::Sec100);
                unqualified.commitment_mode = CommitmentMode::MergedMemoryAndWitness;
                wrong.resolved_config = Arc::new(ResolvedProverConfig::new(
                    kind,
                    Arc::clone(&circuit),
                    unqualified,
                ));
                "unqualified packed merged shape"
            }
            6 => {
                let mut separate = config.clone();
                separate.commitment_mode = CommitmentMode::SeparateMemoryAndWitness;
                wrong.resolved_config = Arc::new(ResolvedProverConfig::new(
                    kind,
                    Arc::clone(&circuit),
                    separate,
                ));
                "setup cache commitment geometry mismatch"
            }
            _ => {
                wrong.setup_host = make_cache(geometry);
                assert!(wrong.setup_host.inner.set(None).is_ok());
                "missing setup producer"
            }
        };
        // Exercise both request kinds through the same production helper. No
        // rejected request may reach cache pinning or a transfer constructor.
        for caps in [None, Some(caps.as_slice())] {
            let constructed = std::cell::Cell::new(false);
            let error = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                wrong.admit_inputs_before_transfers(request_kind, SecurityLevel::Sec100, caps, 27);
                constructed.set(true);
            }))
            .expect_err("invalid metadata was admitted");
            let message = error
                .downcast_ref::<String>()
                .map(String::as_str)
                .or_else(|| error.downcast_ref::<&str>().copied())
                .unwrap();
            assert!(message.contains(expected), "case {case}: {message}");
            assert!(
                !constructed.get(),
                "case {case} reached transfer construction"
            );
            assert!(
                wrong.setup_host.cpu_setup.lock().unwrap().is_some(),
                "rejection consumed the CPU setup"
            );
        }
    }
}
