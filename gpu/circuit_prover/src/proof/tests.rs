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

fn artifact(stem: &str) -> GKRCircuitArtifact<BF> {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../cs/compiled_circuits")
        .join(format!("{stem}_layout_gkr.json"));
    serde_json::from_reader(std::fs::File::open(path).unwrap()).unwrap()
}

fn blake_programs() -> GkrPrograms {
    GkrPrograms::compile(
        CircuitType::Delegation(D::Blake2WithCompression),
        Arc::new(artifact("blake2_with_extended_control")),
    )
    .unwrap()
}

fn panic_message(error: &(dyn std::any::Any + Send)) -> String {
    error
        .downcast_ref::<String>()
        .cloned()
        .or_else(|| error.downcast_ref::<&str>().map(|s| (*s).to_owned()))
        .unwrap()
}

#[test]
#[should_panic(expected = "GKR final trace size differs from configured explicit output size")]
fn cpu_preflight_rejects_explicit_output_identity_before_device_admission() {
    // An invalid device id would fail if admission reached any CUDA query.
    let _ = preflight_proof(
        &blake_programs(),
        &physical_config(20, 2),
        14,
        -1,
        ProofMemoryPolicy::default(),
        27,
    );
}

#[test]
#[should_panic(
    expected = "GPU forward transcript handoff requires at least one dimension-reduction layer"
)]
fn cpu_preflight_rejects_empty_reduction_before_device_admission() {
    let mut config = physical_config(20, 2);
    config.sumcheck_explicit_output_size_log_2 = 20;
    config.validate_for_whir_message_size(config.whir_message_size_log2());
    let _ = preflight_proof(
        &blake_programs(),
        &config,
        20,
        -1,
        ProofMemoryPolicy::default(),
        27,
    );
}

#[test]
#[should_panic(expected = "base partial tree exceeds the commitment domain")]
fn cpu_memory_only_proof_still_requires_partial_query_geometry() {
    let config = ProverConfig::whir_only(
        13,
        prover::gkr::prover_config::WhirSchedule::from_legacy_arrays(
            2,
            1024,
            0,
            &[0, 5],
            &[1, 1],
            &[128],
            &[0, 0],
        ),
        SecurityLevel::Sec100,
    );
    config.validate_for_whir_message_size(13);
    let shape = BaseCommitmentGeometry::from_config(
        &config,
        BaseColumns {
            memory: 1,
            witness: 0,
            setup: 0,
        },
    )
    .unwrap();
    validate_baby_bear_base_proof_policy(&shape, ProofMemoryPolicy::default(), 27);
}

#[test]
fn cpu_every_supported_geometry_admits_every_policy_candidate() {
    let mut configs: Vec<_> = [
        (20, 0),
        (20, 1),
        (20, 2),
        (20, 3),
        (20, 4),
        (21, 3),
        (23, 1),
    ]
    .map(|(n, k)| physical_config(n, k))
    .into();
    let mut unfolded = physical_config(20, 4);
    unfolded.whir_schedule.base_round.fold_log2 = 0;
    configs.push(unfolded);
    for circuit in [D::BigIntWithControl, D::Blake2WithCompression] {
        configs.push(CircuitType::Delegation(circuit).prover_config(SecurityLevel::Sec100));
    }
    for mut merged in [
        physical_config(20, 4),
        CircuitType::Delegation(D::Blake2WithCompression).prover_config(SecurityLevel::Sec100),
    ] {
        merged.commitment_mode = CommitmentMode::MergedMemoryAndWitness;
        configs.push(merged);
    }
    for config in configs {
        let geometry = geometry(&config);
        let gkr_only = memory_policy::GkrMemoryPolicy::candidates().map(|gkr| ProofMemoryPolicy {
            gkr,
            ..Default::default()
        });
        for policy in ProofMemoryPolicy::candidates().chain(gkr_only) {
            validate_base_proof_geometry_policy(&geometry, policy, 4);
            validate_baby_bear_base_proof_policy(&geometry, policy, 27);
        }
    }
}

#[test]
fn cpu_recursive_schedule_refuses_unimplemented_pow_and_ood_counts() {
    let config = physical_config(20, 2);
    gpu_whir::validate_baby_bear_recursive_schedule(22, &config.whir_schedule, 27);
    for case in 0..2 {
        let mut bad = config.whir_schedule.clone();
        let expected = if case == 0 {
            bad.base_round.folding_pow_bits = 1;
            "base-round folding PoW is not implemented"
        } else {
            bad.internal_rounds[0].num_ood_samples = 2;
            "exactly one OOD sample per oracle"
        };
        let error = std::panic::catch_unwind(|| {
            gpu_whir::validate_baby_bear_recursive_schedule(22, &bad, 27)
        })
        .expect_err(expected);
        let message = panic_message(&*error);
        assert!(message.contains(expected), "{message}");
    }
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
        let artifact = artifact(stem);
        let geometry =
            BaseCommitmentGeometry::from_config(&config, BaseColumns::of(&artifact)).unwrap();
        for arena in [21usize << 30, 30usize << 30] {
            let policy = memory_policy::presets::policy(circuit, arena);
            validate_base_proof_geometry_policy(&geometry, policy, artifact.layers.len());
            validate_baby_bear_base_proof_policy(&geometry, policy, 27);
        }
    }
}

#[test]
fn cpu_semantic_policy_failures_precede_transfer_construction() {
    let programs = blake_programs();
    let config =
        CircuitType::Delegation(D::Blake2WithCompression).prover_config(SecurityLevel::Sec100);
    let final_trace_log = u32::try_from(config.sumcheck_explicit_output_size_log_2).unwrap();
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
        let message =
            panic_message(&*result.expect_err("invalid policy must fail before device admission"));
        assert!(message.contains(expected), "unexpected failure: {message}");
        assert!(!constructed.get());
    }
}
