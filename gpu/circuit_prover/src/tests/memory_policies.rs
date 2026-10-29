use super::*;
use crate::proof::memory_policy::{
    GkrMemoryPolicy, OpeningStrategy, WitnessCommitmentStrategy, WitnessMemoryPolicy,
    WitnessOpeningStrategy, WitnessPostCommitStorage,
};

fn check_policies(
    fixture: &BasicUnrolledProofFixture,
    policies: impl IntoIterator<Item = ProofMemoryPolicy>,
) {
    let baseline = fixture.base.context.get_used_mem_current();
    let cpu_bytes = serde_json::to_vec(&fixture.expected_cpu_proof).unwrap();
    let mut policies = policies.into_iter();
    while let Some(first_policy) = policies.next() {
        let second_policy = policies.next().unwrap_or(first_policy);
        fixture.base.context.reset_used_mem_peak();
        eprintln!("policy parity: circuit={:?} arena_bytes={} first={first_policy:?} second={second_policy:?}", fixture.base.circuit_type, fixture.base.context.get_mem_size());
        let first = fixture
            .base
            .schedule_prove_with_memory_policy(first_policy)
            .unwrap();
        let second = fixture
            .base
            .schedule_prove_with_memory_policy(second_policy)
            .unwrap();
        for job in [first, second] {
            let (proof, _) = job.finish().unwrap();
            assert_gkr_proof_eq_for_test(&proof, &fixture.expected_cpu_proof);
            assert!(
                serde_json::to_vec(&proof).unwrap() == cpu_bytes,
                "policy changed serialized proof bytes"
            );
        }
        assert_eq!(fixture.base.context.get_used_mem_current(), baseline);
        eprintln!(
            "policy parity passed: proofs=2 bytes={} peak_bytes={} baseline={baseline}",
            cpu_bytes.len(),
            fixture.base.context.get_used_mem_peak()
        );
    }
}

fn check_opening_policies(fixture: &BasicUnrolledProofFixture) {
    use crate::proof::memory_policy::OpeningStrategy::{AllCosets, InPlace, PerCoset};
    let policies = [InPlace, PerCoset, AllCosets];
    check_policies(
        fixture,
        policies.into_iter().flat_map(|setup| {
            policies.into_iter().map(move |memory| ProofMemoryPolicy {
                setup,
                memory,
                ..Default::default()
            })
        }),
    );
}

#[test]
#[ignore]
fn opening_policies_add_sub_parity_and_reuse() {
    check_opening_policies(&prepare_basic_unrolled_proof_fixture_sec100());
}

#[test]
#[ignore]
fn opening_policies_unified_parity_and_reuse() {
    check_opening_policies(&prepare_unified_proof_fixture());
}

#[test]
#[ignore]
fn opening_policies_setup_less_parity_and_reuse() {
    let (base, expected) =
        super::inits_and_teardowns::prepare_inits_and_teardowns_proof_fixture(true);
    use crate::proof::memory_policy::OpeningStrategy::{AllCosets, InPlace, PerCoset};
    let fixture = BasicUnrolledProofFixture {
        base,
        expected_cpu_proof: expected.unwrap(),
    };
    check_policies(
        &fixture,
        [InPlace, PerCoset, AllCosets].map(|memory| ProofMemoryPolicy {
            memory,
            ..Default::default()
        }),
    );
}

fn in_place_policy(gkr: GkrMemoryPolicy) -> ProofMemoryPolicy {
    ProofMemoryPolicy {
        gkr,
        setup: OpeningStrategy::InPlace,
        memory: OpeningStrategy::InPlace,
        witness: WitnessMemoryPolicy {
            commitment: WitnessCommitmentStrategy::InPlace,
            post_commitment: WitnessPostCommitStorage::RawEvaluations,
            opening: WitnessOpeningStrategy::Recompute(OpeningStrategy::InPlace),
        },
    }
}

fn check_witness_policies(fixture: &BasicUnrolledProofFixture) {
    let in_place = in_place_policy(GkrMemoryPolicy::Materialize);
    check_policies(
        fixture,
        std::iter::once(in_place).chain(WitnessMemoryPolicy::candidates().map(|witness| {
            ProofMemoryPolicy {
                witness,
                ..Default::default()
            }
        })),
    );
}

#[test]
#[ignore]
fn witness_policies_add_sub_parity_and_reuse() {
    check_witness_policies(&prepare_basic_unrolled_proof_fixture_sec100());
}

#[test]
#[ignore]
fn witness_policies_unified_parity_and_reuse() {
    check_witness_policies(&prepare_unified_proof_fixture());
}

fn check_gkr_recompute(
    fixture: &BasicUnrolledProofFixture,
    candidates: impl Iterator<Item = GkrMemoryPolicy>,
) {
    let policy = ProofMemoryPolicy {
        witness: WitnessMemoryPolicy {
            post_commitment: WitnessPostCommitStorage::RawEvaluations,
            opening: WitnessOpeningStrategy::Recompute(OpeningStrategy::AllCosets),
            ..Default::default()
        },
        ..Default::default()
    };
    let in_place = in_place_policy(GkrMemoryPolicy::Recompute {
        value_layers: 2,
        cache_layers: 3,
    });
    check_policies(
        fixture,
        candidates
            .map(|gkr| ProofMemoryPolicy { gkr, ..policy })
            .chain(std::iter::once(in_place)),
    );
}

macro_rules! gkr_recompute_test {
    ($name:ident, $fixture:path) => {
        gkr_recompute_test!($name, $fixture, GkrMemoryPolicy::candidates());
    };
    ($name:ident, $fixture:path, $candidates:expr) => {
        #[test]
        #[ignore]
        fn $name() {
            check_gkr_recompute(&$fixture(), $candidates);
        }
    };
}

gkr_recompute_test!(
    gkr_recompute_add_sub_parity_and_reuse,
    prepare_basic_unrolled_proof_fixture_sec100
);
gkr_recompute_test!(
    gkr_recompute_unified_parity_and_reuse,
    prepare_unified_proof_fixture
);
gkr_recompute_test!(
    gkr_recompute_shift_binop_parity_and_reuse,
    super::proof_matrix::prepare_shift_binop_proof_fixture
);
gkr_recompute_test!(
    gkr_recompute_jump_branch_slt_parity_and_reuse,
    super::proof_matrix::prepare_jump_branch_slt_proof_fixture
);
gkr_recompute_test!(
    gkr_recompute_mul_div_parity_and_reuse,
    super::proof_matrix::prepare_mul_div_proof_fixture
);
gkr_recompute_test!(
    gkr_recompute_load_store_word_parity_and_reuse,
    super::proof_matrix::prepare_load_store_word_only_proof_fixture
);
gkr_recompute_test!(
    gkr_recompute_load_store_subword_parity_and_reuse,
    super::proof_matrix::prepare_load_store_subword_only_proof_fixture
);
// Materialize peaks at 35 GiB for bigint, above the 30 GiB preset arena.
gkr_recompute_test!(
    gkr_recompute_bigint_parity_and_reuse,
    super::proof_matrix::prepare_bigint_proof_fixture,
    GkrMemoryPolicy::candidates().filter(|&gkr| gkr != GkrMemoryPolicy::Materialize)
);
gkr_recompute_test!(
    gkr_recompute_keccak_parity_and_reuse,
    super::proof_matrix::prepare_keccak_special5_proof_fixture
);
gkr_recompute_test!(
    gkr_recompute_blake2_compression_parity_and_reuse,
    super::proof_matrix::prepare_blake2_with_compression_proof_fixture
);
gkr_recompute_test!(
    gkr_recompute_blake2_g_parity_and_reuse,
    super::proof_matrix::prepare_blake2_g_function_proof_fixture
);
gkr_recompute_test!(
    gkr_recompute_inits_and_teardowns_parity_and_reuse,
    super::proof_matrix::prepare_inits_and_teardowns_matrix_proof_fixture
);

/// The existing production table is the policy authority. Regeneration of that
/// table must requalify these bytes; the fixture arena alone is not a fit claim.
fn check_production_presets(fixture: &BasicUnrolledProofFixture) {
    let policies = [21usize << 30, 30usize << 30].map(|arena| {
        let policy = presets::policy(
            fixture.base.circuit_type,
            crate::upstream::ProofProfile::Standard,
            arena,
        );
        eprintln!(
            "preset parity row: circuit={:?} preset_arena_bytes={arena} policy={policy:?}",
            fixture.base.circuit_type
        );
        policy
    });
    check_policies(fixture, policies);
}

macro_rules! production_presets_test {
    ($name:ident, $fixture:path) => {
        #[test]
        #[ignore = "both production preset policies against a fresh CPU proof"]
        fn $name() {
            check_production_presets(&$fixture());
        }
    };
}

production_presets_test!(
    production_presets_bigint_parity_and_reuse,
    super::proof_matrix::prepare_bigint_proof_fixture
);
production_presets_test!(
    production_presets_blake_compression_parity_and_reuse,
    super::proof_matrix::prepare_blake2_with_compression_proof_fixture
);
production_presets_test!(
    production_presets_blake_g_parity_and_reuse,
    super::proof_matrix::prepare_blake2_g_function_proof_fixture
);
production_presets_test!(
    production_presets_keccak_special5_parity_and_reuse,
    super::proof_matrix::prepare_keccak_special5_proof_fixture
);
production_presets_test!(
    production_presets_keccak_chi5_parity_and_reuse,
    super::proof_matrix::keccak_f1600::keccak_chi5
);
production_presets_test!(
    production_presets_keccak_column_parity_parity_and_reuse,
    super::proof_matrix::keccak_f1600::keccak_column_parity
);
production_presets_test!(
    production_presets_keccak_theta_rho_parity_and_reuse,
    super::proof_matrix::keccak_f1600::keccak_theta_rho
);

#[test]
#[ignore = "virtual BigInt opening/witness families against one fresh CPU proof"]
fn virtual_bigint_opening_witness_policies_parity_and_reuse() {
    let fixture = super::proof_matrix::prepare_bigint_proof_fixture();
    // Materialize pairs exceed this existing 30 GiB fixture arena. Keep the
    // production GKR baseline while varying every opening/witness candidate.
    let gkr = presets::policy(
        fixture.base.circuit_type,
        crate::upstream::ProofProfile::Standard,
        30usize << 30,
    )
    .gkr;
    let openings = [
        OpeningStrategy::InPlace,
        OpeningStrategy::PerCoset,
        OpeningStrategy::AllCosets,
    ];
    check_policies(
        &fixture,
        openings.into_iter().flat_map(|setup| {
            openings.into_iter().map(move |memory| ProofMemoryPolicy {
                gkr,
                setup,
                memory,
                ..Default::default()
            })
        }),
    );
    check_policies(
        &fixture,
        std::iter::once(in_place_policy(gkr)).chain(WitnessMemoryPolicy::candidates().map(
            |witness| ProofMemoryPolicy {
                gkr,
                witness,
                ..Default::default()
            },
        )),
    );
}

#[test]
#[ignore = "virtual Special5 opening/witness families against one fresh CPU proof"]
fn virtual_special5_opening_witness_policies_parity_and_reuse() {
    let fixture = super::proof_matrix::prepare_keccak_special5_proof_fixture();
    check_opening_policies(&fixture);
    check_witness_policies(&fixture);
}

#[test]
#[ignore = "virtual Blake compression opening/witness families against one fresh CPU proof"]
fn virtual_blake_compression_opening_witness_policies_parity_and_reuse() {
    let fixture = super::proof_matrix::prepare_blake2_with_compression_proof_fixture();
    check_opening_policies(&fixture);
    check_witness_policies(&fixture);
}

#[test]
#[ignore = "virtual Blake G opening/witness families against one fresh CPU proof"]
fn virtual_blake_g_opening_witness_policies_parity_and_reuse() {
    let fixture = super::proof_matrix::prepare_blake2_g_function_proof_fixture();
    check_opening_policies(&fixture);
    check_witness_policies(&fixture);
}

#[test]
#[ignore = "virtual Chi5 policy families against one fresh CPU proof"]
fn virtual_chi5_memory_policies_parity_and_reuse() {
    let fixture = super::proof_matrix::keccak_f1600::keccak_chi5();
    check_opening_policies(&fixture);
    check_witness_policies(&fixture);
    check_gkr_recompute(&fixture, GkrMemoryPolicy::candidates());
}

#[test]
#[ignore = "virtual ColumnParity policy families against one fresh CPU proof"]
fn virtual_column_parity_memory_policies_parity_and_reuse() {
    let fixture = super::proof_matrix::keccak_f1600::keccak_column_parity();
    check_opening_policies(&fixture);
    check_witness_policies(&fixture);
    check_gkr_recompute(&fixture, GkrMemoryPolicy::candidates());
}

#[test]
#[ignore = "virtual ThetaRho policy families against one fresh CPU proof"]
fn virtual_theta_rho_memory_policies_parity_and_reuse() {
    let fixture = super::proof_matrix::keccak_f1600::keccak_theta_rho();
    check_opening_policies(&fixture);
    check_witness_policies(&fixture);
    check_gkr_recompute(&fixture, GkrMemoryPolicy::candidates());
}

#[test]
#[ignore = "physical Blake20/k2 opening/witness families against one fresh CPU proof"]
fn physical_blake20_pack2_opening_witness_policies_parity_and_reuse() {
    let fixture =
        super::proof_matrix::prepare_blake2_with_compression_proof_fixture_with_packing(2);
    check_opening_policies(&fixture);
    check_witness_policies(&fixture);
}

#[test]
#[ignore = "physical Blake20/k4 policy families against one fresh CPU proof"]
fn physical_blake20_pack4_memory_policies_parity_and_reuse() {
    let fixture =
        super::proof_matrix::prepare_blake2_with_compression_proof_fixture_with_packing(4);
    check_opening_policies(&fixture);
    check_witness_policies(&fixture);
    check_gkr_recompute(&fixture, GkrMemoryPolicy::candidates());
}

#[test]
#[ignore = "physical unified23/k1 policy families against one fresh CPU proof"]
fn physical_unified23_pack1_memory_policies_parity_and_reuse() {
    let fixture = super::prepare_unified_proof_fixture_with_packing(1);
    check_opening_policies(&fixture);
    check_witness_policies(&fixture);
    check_gkr_recompute(&fixture, GkrMemoryPolicy::candidates());
}

#[test]
#[ignore = "merged Blake20/k4 policy families against one fresh CPU proof"]
fn merged_blake20_pack4_memory_policies_parity_and_reuse() {
    let mut config = prover::gkr::prover_config::example_configs::packed_config_for_security_level_under_pessimistic_conjecture(20, 4, SecurityLevel::Sec100);
    config.commitment_mode = CommitmentMode::MergedMemoryAndWitness;
    let fixture =
        super::proof_matrix::prepare_blake2_with_compression_proof_fixture_for_config(config);
    check_opening_policies(&fixture);
    check_witness_policies(&fixture);
    check_gkr_recompute(&fixture, GkrMemoryPolicy::candidates());
}

// Geometry-audit cases use the existing CPU oracle, GPU cap producer and
// two-queued-proof policy driver. They stay ignored until the combined gate.
fn geometry_guard_g_check_policies(
    mut fixture: BasicUnrolledProofFixture,
    first: ProofMemoryPolicy,
) {
    let geometry = BaseCommitmentGeometry::from_config(
        &fixture.base.prover_config,
        BaseColumns::of(&fixture.base.compiled_circuit),
    )
    .unwrap();
    fixture.base.memory_tree_caps = super::packed_proof::gpu_memory_caps(&fixture.base, geometry);
    let second = ProofMemoryPolicy {
        setup: OpeningStrategy::PerCoset,
        memory: OpeningStrategy::InPlace,
        ..first
    };
    assert_ne!(
        first, second,
        "the pair must exercise different opening handoffs"
    );
    for arena in [21usize << 30, 30usize << 30] {
        assert_ne!(
            second,
            presets::policy(
                fixture.base.circuit_type,
                crate::upstream::ProofProfile::Standard,
                arena
            ),
            "the second policy is an explicit nonpreset test tuple"
        );
    }
    assert!(first.witness.is_valid() && second.witness.is_valid());
    eprintln!(
        "geometry guard: config={:?} setup_memory_peak={} arena_bytes={}",
        fixture.base.prover_config,
        fixture.base.context.get_used_mem_peak(),
        fixture.base.context.get_mem_size()
    );
    check_policies(&fixture, [first, second]);
}

#[test]
#[ignore = "geometry audit F1: fresh CPU proof and two queued GPU proofs"]
fn geometry_guard_g_f01_blake_physical_k1() {
    let config = prover::gkr::prover_config::example_configs::packed_config_for_security_level_under_pessimistic_conjecture(20, 1, SecurityLevel::Sec100);
    config.validate_for_whir_message_size(config.whir_message_size_log2());
    let fixture =
        super::proof_matrix::prepare_blake2_with_compression_proof_fixture_for_config(config);
    let first = fixture.base.memory_policy();
    geometry_guard_g_check_policies(fixture, first);
}

#[test]
#[ignore = "geometry audit F2: fresh CPU proof and two queued GPU proofs"]
fn geometry_guard_g_f02_blake_physical_k3() {
    let config = prover::gkr::prover_config::example_configs::packed_config_for_security_level_under_pessimistic_conjecture(20, 3, SecurityLevel::Sec100);
    config.validate_for_whir_message_size(config.whir_message_size_log2());
    let fixture =
        super::proof_matrix::prepare_blake2_with_compression_proof_fixture_for_config(config);
    let first = fixture.base.memory_policy();
    geometry_guard_g_check_policies(fixture, first);
}

#[test]
#[ignore = "geometry audit F3: fresh CPU proof and two queued GPU proofs"]
fn geometry_guard_g_f03_blake_virtual_k0() {
    let config = prover::gkr::prover_config::example_configs::virtual_packed_config_for_security_level_under_pessimistic_conjecture(20, 0, SecurityLevel::Sec100);
    config.validate_for_whir_message_size(config.whir_message_size_log2());
    let fixture =
        super::proof_matrix::prepare_blake2_with_compression_proof_fixture_for_config(config);
    let first = fixture.base.memory_policy();
    geometry_guard_g_check_policies(fixture, first);
}

#[test]
#[ignore = "geometry audit F4: fresh CPU proof and two queued GPU proofs"]
fn geometry_guard_g_f04_blake_virtual_k1() {
    let config = prover::gkr::prover_config::example_configs::virtual_packed_config_for_security_level_under_pessimistic_conjecture(20, 1, SecurityLevel::Sec100);
    // Physical column packing and a virtual base round are independent:
    // this is the full-proof physical-k1/f0 case as well as virtual F4.
    assert_eq!(config.pack_log2(), 1);
    assert_eq!(config.base_round().fold_log2, 0);
    config.validate_for_whir_message_size(config.whir_message_size_log2());
    let fixture =
        super::proof_matrix::prepare_blake2_with_compression_proof_fixture_for_config(config);
    let first = fixture.base.memory_policy();
    geometry_guard_g_check_policies(fixture, first);
}

#[test]
#[ignore = "geometry audit F5: fresh CPU proof and two queued GPU proofs"]
fn geometry_guard_g_f05_blake_virtual_k3() {
    let config = prover::gkr::prover_config::example_configs::virtual_packed_config_for_security_level_under_pessimistic_conjecture(20, 3, SecurityLevel::Sec100);
    config.validate_for_whir_message_size(config.whir_message_size_log2());
    let fixture =
        super::proof_matrix::prepare_blake2_with_compression_proof_fixture_for_config(config);
    let first = fixture.base.memory_policy();
    geometry_guard_g_check_policies(fixture, first);
}

#[test]
#[ignore = "geometry audit F6: fresh CPU proof and two queued GPU proofs"]
fn geometry_guard_g_f06_blake_virtual_k4() {
    let config = prover::gkr::prover_config::example_configs::virtual_packed_config_for_security_level_under_pessimistic_conjecture(20, 4, SecurityLevel::Sec100);
    config.validate_for_whir_message_size(config.whir_message_size_log2());
    let fixture =
        super::proof_matrix::prepare_blake2_with_compression_proof_fixture_for_config(config);
    let first = fixture.base.memory_policy();
    geometry_guard_g_check_policies(fixture, first);
}

#[test]
#[ignore = "geometry audit F7: fresh CPU proof and two queued GPU proofs"]
fn geometry_guard_g_f07_blake_merged_virtual_k2() {
    let mut config = prover::gkr::prover_config::example_configs::virtual_packed_config_for_security_level_under_pessimistic_conjecture(20, 2, SecurityLevel::Sec100);
    config.commitment_mode = CommitmentMode::MergedMemoryAndWitness;
    config.validate_for_whir_message_size(config.whir_message_size_log2());
    let fixture =
        super::proof_matrix::prepare_blake2_with_compression_proof_fixture_for_config(config);
    let first = fixture.base.memory_policy();
    geometry_guard_g_check_policies(fixture, first);
}

#[test]
#[ignore = "geometry audit F8: fresh CPU proof and two queued GPU proofs"]
fn geometry_guard_g_f08_blake_merged_physical_k2() {
    let mut config = prover::gkr::prover_config::example_configs::packed_config_for_security_level_under_pessimistic_conjecture(20, 2, SecurityLevel::Sec100);
    config.commitment_mode = CommitmentMode::MergedMemoryAndWitness;
    config.validate_for_whir_message_size(config.whir_message_size_log2());
    let fixture =
        super::proof_matrix::prepare_blake2_with_compression_proof_fixture_for_config(config);
    let first = fixture.base.memory_policy();
    geometry_guard_g_check_policies(fixture, first);
}

#[test]
#[ignore = "geometry audit F9: fresh CPU proof and two queued GPU proofs"]
fn geometry_guard_g_f09_bigint_merged_virtual_k0() {
    let mut config = prover::gkr::prover_config::example_configs::virtual_packed_config_for_security_level_under_pessimistic_conjecture(22, 0, SecurityLevel::Sec100);
    config.commitment_mode = CommitmentMode::MergedMemoryAndWitness;
    config.validate_for_whir_message_size(config.whir_message_size_log2());
    let (buffer, table_driver) = super::proof_matrix::replay_bigint_delegation_buffer();
    let oracle = BigintDelegationOracle {
        cycle_data: &buffer,
        marker: core::marker::PhantomData,
    };
    let fixture = prepare_delegation_proof_fixture_for_config(
        DelegationCircuitType::BigIntWithControl,
        super::proof_matrix::BIGINT_DELEGATION_LAYOUT_PATH,
        &table_driver,
        buffer.clone(),
        &oracle,
        bigint_with_extended_control_mod::witness_eval_fn,
        CircuitType::Delegation(DelegationCircuitType::BigIntWithControl).get_domain_size(),
        config,
    );
    drop(buffer);
    let first = fixture.base.memory_policy();
    geometry_guard_g_check_policies(fixture, first);
}

#[test]
#[ignore = "geometry audit F10: fresh CPU proof and two queued GPU proofs"]
fn geometry_guard_g_f10_bigint_merged_physical_k1() {
    let mut config = prover::gkr::prover_config::example_configs::packed_config_for_security_level_under_pessimistic_conjecture(22, 1, SecurityLevel::Sec100);
    config.commitment_mode = CommitmentMode::MergedMemoryAndWitness;
    config.validate_for_whir_message_size(config.whir_message_size_log2());
    let (buffer, table_driver) = super::proof_matrix::replay_bigint_delegation_buffer();
    let oracle = BigintDelegationOracle {
        cycle_data: &buffer,
        marker: core::marker::PhantomData,
    };
    let fixture = prepare_delegation_proof_fixture_for_config(
        DelegationCircuitType::BigIntWithControl,
        super::proof_matrix::BIGINT_DELEGATION_LAYOUT_PATH,
        &table_driver,
        buffer.clone(),
        &oracle,
        bigint_with_extended_control_mod::witness_eval_fn,
        CircuitType::Delegation(DelegationCircuitType::BigIntWithControl).get_domain_size(),
        config,
    );
    drop(buffer);
    let first = fixture.base.memory_policy();
    // The approved F10 exception keeps the preset GKR level but avoids
    // materializing the combined memory/witness cosets for either proof.
    let first = ProofMemoryPolicy {
        memory: OpeningStrategy::InPlace,
        witness: WitnessMemoryPolicy {
            commitment: WitnessCommitmentStrategy::InPlace,
            post_commitment: WitnessPostCommitStorage::RawEvaluations,
            opening: WitnessOpeningStrategy::Recompute(OpeningStrategy::InPlace),
        },
        ..first
    };
    geometry_guard_g_check_policies(fixture, first);
}

#[test]
#[ignore = "geometry audit F11: fresh CPU proof and two queued GPU proofs"]
fn geometry_guard_g_f11_blake_virtual_lde4() {
    let mut config = prover::gkr::prover_config::example_configs::virtual_packed_config_for_security_level_under_pessimistic_conjecture(20, 2, SecurityLevel::Sec100);
    config.whir_schedule.base_round.lde_factor_log2 = 2;
    config.validate_for_whir_message_size(config.whir_message_size_log2());
    let fixture =
        super::proof_matrix::prepare_blake2_with_compression_proof_fixture_for_config(config);
    let first = fixture.base.memory_policy();
    geometry_guard_g_check_policies(fixture, first);
}

// F11 companions: per-coset memory caps are in natural coset order, which only
// LDE >= 4 distinguishes from the bit-reversed tree order.
// The all-cosets preset policy does not fit LDE8 in the 30 GiB fixture arena,
// so this companion checks the memory caps only; virtual_whir_k2_lde8_cpu_parity
// covers the LDE8 proof.
#[test]
#[ignore = "geometry audit F11 companion: fresh CPU proof and GPU memory caps"]
fn geometry_guard_g_f11_blake_virtual_lde8_memory_caps() {
    let mut config = prover::gkr::prover_config::example_configs::virtual_packed_config_for_security_level_under_pessimistic_conjecture(20, 2, SecurityLevel::Sec100);
    config.whir_schedule.base_round.lde_factor_log2 = 3;
    config.validate_for_whir_message_size(config.whir_message_size_log2());
    let fixture =
        super::proof_matrix::prepare_blake2_with_compression_proof_fixture_for_config(config);
    let geometry = BaseCommitmentGeometry::from_config(
        &fixture.base.prover_config,
        BaseColumns::of(&fixture.base.compiled_circuit),
    )
    .unwrap();
    super::packed_proof::gpu_memory_caps(&fixture.base, geometry);
}

#[test]
#[ignore = "geometry audit F11 companion: fresh CPU proof and two queued GPU proofs"]
fn geometry_guard_g_f11_blake_physical_k1_lde4() {
    let mut config = prover::gkr::prover_config::example_configs::packed_config_for_security_level_under_pessimistic_conjecture(20, 1, SecurityLevel::Sec100);
    config.whir_schedule.base_round.lde_factor_log2 = 2;
    config.validate_for_whir_message_size(config.whir_message_size_log2());
    let fixture =
        super::proof_matrix::prepare_blake2_with_compression_proof_fixture_for_config(config);
    let first = fixture.base.memory_policy();
    geometry_guard_g_check_policies(fixture, first);
}

#[test]
#[ignore = "geometry audit F11 companion: fresh CPU proof and two queued GPU proofs"]
fn geometry_guard_g_f11_blake_merged_virtual_k2_lde4() {
    let mut config = prover::gkr::prover_config::example_configs::virtual_packed_config_for_security_level_under_pessimistic_conjecture(20, 2, SecurityLevel::Sec100);
    config.commitment_mode = CommitmentMode::MergedMemoryAndWitness;
    config.whir_schedule.base_round.lde_factor_log2 = 2;
    config.validate_for_whir_message_size(config.whir_message_size_log2());
    let fixture =
        super::proof_matrix::prepare_blake2_with_compression_proof_fixture_for_config(config);
    let first = fixture.base.memory_policy();
    geometry_guard_g_check_policies(fixture, first);
}

#[test]
#[ignore = "geometry audit F11 companion: fresh CPU proof and two queued GPU proofs"]
fn geometry_guard_g_f11_blake_merged_physical_k2_lde4() {
    let mut config = prover::gkr::prover_config::example_configs::packed_config_for_security_level_under_pessimistic_conjecture(20, 2, SecurityLevel::Sec100);
    config.commitment_mode = CommitmentMode::MergedMemoryAndWitness;
    config.whir_schedule.base_round.lde_factor_log2 = 2;
    config.validate_for_whir_message_size(config.whir_message_size_log2());
    let fixture =
        super::proof_matrix::prepare_blake2_with_compression_proof_fixture_for_config(config);
    let first = fixture.base.memory_policy();
    geometry_guard_g_check_policies(fixture, first);
}

#[test]
#[ignore = "geometry audit F12: fresh CPU proof and two queued GPU proofs"]
fn geometry_guard_g_f12_blake_virtual_cap32() {
    let mut config = prover::gkr::prover_config::example_configs::virtual_packed_config_for_security_level_under_pessimistic_conjecture(20, 2, SecurityLevel::Sec100);
    config.cap_size = 32;
    config.whir_schedule.cap_size = 32;
    config.validate_for_whir_message_size(config.whir_message_size_log2());
    let fixture =
        super::proof_matrix::prepare_blake2_with_compression_proof_fixture_for_config(config);
    let first = fixture.base.memory_policy();
    geometry_guard_g_check_policies(fixture, first);
}

#[test]
#[ignore = "geometry audit F13: fresh CPU proof and two queued GPU proofs"]
fn geometry_guard_g_f13_blake_physical_naive() {
    let mut config = prover::gkr::prover_config::example_configs::packed_config_for_security_level_under_pessimistic_conjecture(20, 2, SecurityLevel::Sec100);
    config.same_size_sumcheck_schedule.clear();
    assert_eq!(
        crate::upstream::validate_sumcheck_schedule(&config.same_size_sumcheck_schedule, 20)
            .unwrap(),
        crate::upstream::SumcheckScheduleClass::Naive
    );
    config.validate_for_whir_message_size(config.whir_message_size_log2());
    let fixture =
        super::proof_matrix::prepare_blake2_with_compression_proof_fixture_for_config(config);
    let first = fixture.base.memory_policy();
    geometry_guard_g_check_policies(fixture, first);
}

#[test]
#[ignore = "direct-circuit short-DR wiring: fresh CPU proof and two queued GPU proofs"]
fn geometry_guard_g_short_dr_six_rounds_cpu_parity() {
    let mut config = prover::gkr::prover_config::example_configs::packed_config_for_security_level_under_pessimistic_conjecture(
        20, 2, SecurityLevel::Sec100,
    );
    config.sumcheck_explicit_output_size_log_2 = 14;
    config.validate_for_whir_message_size(config.whir_message_size_log2());
    let fixture =
        super::proof_matrix::prepare_blake2_with_compression_proof_fixture_for_config(config);
    assert_eq!(fixture.base.final_trace_size_log_2, 14);
    let first = fixture.base.memory_policy();
    geometry_guard_g_check_policies(fixture, first);
}
