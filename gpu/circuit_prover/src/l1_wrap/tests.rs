use super::geometry::cpu_tests::wrap_geometry;
use super::inputs::ALLOCATOR_BLOCK_BYTES;
use super::*;
use crate::config::GPU_SUPPORTED_SECURITY_LEVELS;
use crate::proof::inputs::EXTERNAL_CHALLENGES_E4_LEN;
use crate::proof::memory_policy::presets::{self, compression};
use crate::proof::memory_policy::presets::{H2D_STAGING_BYTES, INPUTS_RESERVE_BYTES};
use crate::upstream::ProofProfile;
use crate::upstream::{FinalRegisterValue, GKRCircuitArtifact, SecurityLevel};
use gpu_core::primitives::field::E4;
use gpu_gkr::proth120::backward::max_coefficient_table_bytes;
use gpu_gkr::proth120::packed_challenges::BOUNDARY_PREFIX_U32_LEN;
use gpu_gkr::proth120::programs::GkrProgramsPr;
use gpu_hash::blake2s::Digest as Blake2sDigest;
use gpu_prover_context::{ProverContextConfig, DEFAULT_H2D_STAGING_BYTES};
use gpu_trace::trace::holder::resolve_partial_tree_reduction_layers;
use gpu_trace::trace::memory_cap::PartialTreesGeometry;
use gpu_trace::witness::circuit_type::{CircuitType, UnrolledCircuitType};
use prover::gkr::prover_config::example_configs::l1_wrap::EXTERNAL_CHALLENGES_POW_BITS;
use std::alloc::Global;
use std::panic::{catch_unwind, AssertUnwindSafe};

fn panic_message(f: impl FnOnce()) -> String {
    let payload = catch_unwind(AssertUnwindSafe(f)).expect_err("expected a named panic");
    payload
        .downcast_ref::<String>()
        .cloned()
        .or_else(|| {
            payload
                .downcast_ref::<&str>()
                .map(|message| message.to_string())
        })
        .expect("panic payload is a message")
}

fn production_mode() -> OperationMode {
    OperationMode::SingleChunk {
        external_challenges_pow_bits: EXTERNAL_CHALLENGES_POW_BITS,
        register_final_state: [FinalRegisterValue {
            value: 0,
            last_access_timestamp: 0,
        }; 32],
        final_pc: 0,
        final_timestamp: 0,
    }
}

#[test]
fn cpu_l1_inputs_fit_reserve() {
    assert_eq!(
        ALLOCATOR_BLOCK_BYTES,
        1 << ProverContextConfig::default().allocator_block_log_size
    );
    let (geometry, _) = wrap_geometry(CircuitType::L1Wrap);
    let bytes = L1WrapInputs::<'static, Global>::phase_one_capacity_bytes(
        &geometry,
        crate::proof::memory_policy::presets::l1_wrap::PARTIAL_TREES.setup,
    );
    let mib = 1 << 20;
    // Tracing data, I&T pages/values/timestamps, decoder, transcript prefix,
    // then the setup's raw evaluations, packed monomials and depth-10 trees.
    assert_eq!(bytes, (112 + 1 + 16 + 32 + 3 + 1 + 320 + 512 + 64) * mib);
    assert!(bytes <= INPUTS_RESERVE_BYTES);
}

/// Most bytes an L1 wrap phase one stages: the transcript prefix and the
/// coefficient tables without their zero-coefficient filtering.
fn l1_wrap_staged_bytes_bound() -> usize {
    let circuit: GKRCircuitArtifact<Proth120> = serde_json::from_str(include_str!(
        "../../../../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json"
    ))
    .expect("committed Proth120 layout");
    let num_sets = circuit.memory_layout.teardown_sets.len();
    let programs = GkrProgramsPr::compile(CircuitType::L1Wrap, std::sync::Arc::new(circuit))
        .expect("L1Wrap programs");
    (BOUNDARY_PREFIX_U32_LEN + num_sets) * size_of::<u32>() + max_coefficient_table_bytes(&programs)
}

/// Bytes an compression proof stages: the unified memory cap, the persisted memory
/// partial trees, the inits-and-teardowns top bits and the external challenges.
fn compression_proof_staged_bytes(
    circuit: CircuitType,
    profile: ProofProfile,
    security: SecurityLevel,
) -> usize {
    let config = profile.prover_config(
        circuit.get_domain_size_log2() as usize,
        prover::definitions::SoundnessMode::PessimisticConjecture,
    );
    let log_domain_size = circuit.get_domain_size().trailing_zeros();
    let log_lde_factor = config.lde_factor().trailing_zeros();
    let log_rows_per_leaf = config.base_oracles_values_per_leaf().trailing_zeros();
    let log_tree_cap_size = config.cap_size.trailing_zeros();
    let trees = PartialTreesGeometry {
        log_domain_size,
        log_lde_factor,
        log_rows_per_leaf,
        log_tree_cap_size,
        reduction_layers: resolve_partial_tree_reduction_layers(
            presets::partial_trees(circuit, profile).memory,
            log_domain_size,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
        ),
        columns_count: 0,
    };
    let trees_bytes = trees.cosets_count() * trees.coset_stride() * size_of::<Blake2sDigest>();
    let expected_trees = match profile {
        ProofProfile::CompressionFinal => 2 << 20,
        ProofProfile::Compression => 1 << 20,
        _ => panic!("{profile:?} is not a compression profile"),
    };
    assert_eq!(
        trees_bytes, expected_trees,
        "{security:?} {profile:?} partial trees"
    );
    (1 << log_tree_cap_size) * size_of::<Blake2sDigest>()
        + trees_bytes
        + circuit.get_num_inits_and_teardowns_sets() * size_of::<u32>()
        + EXTERNAL_CHALLENGES_E4_LEN * size_of::<E4>()
}

#[test]
fn cpu_h2d_staging_is_the_largest_bundle_rounded_up() {
    let wrap = l1_wrap_staged_bytes_bound();
    let compression = GPU_SUPPORTED_SECURITY_LEVELS
        .into_iter()
        .flat_map(|security| {
            [
                (
                    UnrolledCircuitType::Unified22,
                    ProofProfile::CompressionFinal,
                ),
                (UnrolledCircuitType::Unified, ProofProfile::Compression),
            ]
            .map(|(circuit, profile)| {
                compression_proof_staged_bytes(CircuitType::Unrolled(circuit), profile, security)
            })
        })
        .max()
        .unwrap();
    let unit = DEFAULT_H2D_STAGING_BYTES;
    assert_eq!(
        H2D_STAGING_BYTES,
        wrap.max(compression).div_ceil(unit) * unit,
        "staged bundles: L1 wrap {wrap} B, compression proof {compression} B"
    );
    println!(
        "L1 wrap stages up to {wrap} B; fits the {unit} B default staging buffer: {}",
        wrap <= unit
    );
}

#[test]
fn cpu_l1_preflight() {
    let circuit: GKRCircuitArtifact<Proth120> = serde_json::from_str(include_str!(
        "../../../../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json"
    ))
    .expect("committed Proth120 layout");
    let (geometry, config) = wrap_geometry(CircuitType::L1Wrap);
    assert_eq!(
        L1_WRAP_NTT_LOG_MAX_DOMAIN as usize,
        config.trace_len_log2 + config.pack_log2() + config.lde_factor().trailing_zeros() as usize
    );
    let cpu_batching_pow_bits = config.base_round().batching_pow_bits::<Proth120, Proth120>(
        config.security_level.security_bits(),
        config.whir_message_size_log2(),
        prover::gkr::prover_config::pow_bits::committed_base_oracle_columns(
            &circuit,
            config.pack_log2(),
            config.merged_memory_and_witness(),
        ),
    );
    assert_eq!(cpu_batching_pow_bits, 13);
    assert_eq!(
        l1_wrap_batching_pow_bits(&config, &circuit),
        cpu_batching_pow_bits
    );
    validate_l1_wrap_preconditions(
        &geometry,
        &config,
        &production_mode(),
        L1_WRAP_POLICY,
        L1_WRAP_NTT_LOG_MAX_DOMAIN,
    );
    let recompute = ProofMemoryPolicy {
        gkr: GkrMemoryPolicy::Recompute {
            value_layers: 1,
            cache_layers: 0,
        },
        ..L1_WRAP_POLICY
    };
    let standard =
        CircuitType::Unrolled(gpu_trace::witness::circuit_type::UnrolledCircuitType::Unified)
            .prover_config(SecurityLevel::Sec100);
    let mode_message = format!("L1Wrap requires OperationMode::SingleChunk with external_challenges_pow_bits {EXTERNAL_CHALLENGES_POW_BITS}");
    let mut other_pack = config.clone();
    other_pack.whir_schedule.base_round.physical_packing_log2 -= 1;
    let mut other_commitment = config.clone();
    other_commitment.commitment_mode = crate::upstream::CommitmentMode::SeparateMemoryAndWitness;
    let mut other_pow = production_mode();
    if let OperationMode::SingleChunk {
        external_challenges_pow_bits,
        ..
    } = &mut other_pow
    {
        *external_challenges_pow_bits -= 1;
    }
    let cases: [(&ProverConfig, OperationMode, ProofMemoryPolicy, u32, String); 8] = [
        (
            &config,
            production_mode(),
            recompute,
            L1_WRAP_NTT_LOG_MAX_DOMAIN,
            "L1Wrap does not support GkrMemoryPolicy::Recompute".to_string(),
        ),
        (
            &config,
            production_mode(),
            compression::POLICY,
            L1_WRAP_NTT_LOG_MAX_DOMAIN,
            format!(
                "L1Wrap requires presets::l1_wrap::L1_WRAP_POLICY, got {:?}",
                compression::POLICY
            ),
        ),
        (
            &standard,
            production_mode(),
            L1_WRAP_POLICY,
            L1_WRAP_NTT_LOG_MAX_DOMAIN,
            "L1Wrap requires the ProofProfile::L1Wrap prover config".to_string(),
        ),
        (
            &config,
            OperationMode::MultipleChunks,
            L1_WRAP_POLICY,
            L1_WRAP_NTT_LOG_MAX_DOMAIN,
            mode_message.clone(),
        ),
        (
            &other_pack,
            production_mode(),
            L1_WRAP_POLICY,
            L1_WRAP_NTT_LOG_MAX_DOMAIN,
            "L1Wrap requires the ProofProfile::L1Wrap prover config".to_string(),
        ),
        (
            &other_commitment,
            production_mode(),
            L1_WRAP_POLICY,
            L1_WRAP_NTT_LOG_MAX_DOMAIN,
            "L1Wrap requires the ProofProfile::L1Wrap prover config".to_string(),
        ),
        (
            &config,
            other_pow,
            L1_WRAP_POLICY,
            L1_WRAP_NTT_LOG_MAX_DOMAIN,
            mode_message,
        ),
        (
            &config,
            production_mode(),
            L1_WRAP_POLICY,
            L1_WRAP_NTT_LOG_MAX_DOMAIN - 1,
            format!(
                "L1Wrap requires a Proth120 NTT context with log_max_domain {L1_WRAP_NTT_LOG_MAX_DOMAIN}, got {}",
                L1_WRAP_NTT_LOG_MAX_DOMAIN - 1
            ),
        ),
    ];
    for (config, mode, policy, log_max_domain, expected) in cases {
        assert_eq!(
            panic_message(|| validate_l1_wrap_preconditions(
                &geometry,
                config,
                &mode,
                policy,
                log_max_domain
            )),
            expected
        );
    }
}
