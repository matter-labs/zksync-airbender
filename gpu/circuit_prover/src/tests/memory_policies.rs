use super::*;
use crate::proof::BaseLdeSchedule;

fn check_recycled_proofs(fixture: &BasicUnrolledProofFixture) {
    super::proof_matrix::run_multi_schedule(fixture);
}

#[test]
#[ignore]
fn jit_full_add_sub_parity_and_reuse() {
    check_recycled_proofs(&prepare_basic_unrolled_proof_fixture_sec100());
}

#[test]
#[ignore]
fn jit_full_unified_parity_and_reuse() {
    check_recycled_proofs(&prepare_unified_proof_fixture());
}

#[test]
#[ignore]
fn jit_full_setup_less_parity_and_reuse() {
    let (base, expected) =
        super::inits_and_teardowns::prepare_inits_and_teardowns_proof_fixture(true);
    check_recycled_proofs(&BasicUnrolledProofFixture {
        base,
        expected_cpu_proof: expected.unwrap(),
    });
}

#[test]
#[ignore]
fn jit_full_add_sub_profile() {
    super::proof_matrix::run_profile_with_schedule(
        &prepare_basic_unrolled_profiling_fixture(),
        BaseLdeSchedule::AtQueries,
    );
}

#[test]
#[ignore]
fn jit_full_unified_profile() {
    super::proof_matrix::run_profile_with_schedule(
        &prepare_unified_profiling_fixture(),
        BaseLdeSchedule::AtQueries,
    );
}

#[test]
#[ignore]
fn jit_full_blake2_compression_delegation_profile() {
    super::proof_matrix::run_profile_with_schedule(
        &super::proof_matrix::prepare_blake2_with_compression_profiling_fixture(),
        BaseLdeSchedule::AtQueries,
    );
}

// Offline regression controls. Production always defers setup and memory.
#[test]
#[ignore]
fn pre_whir_full_add_sub_profile() {
    super::proof_matrix::run_profile_with_schedule(
        &prepare_basic_unrolled_profiling_fixture(),
        BaseLdeSchedule::PreWhir,
    );
}

#[test]
#[ignore]
fn pre_whir_full_unified_profile() {
    super::proof_matrix::run_profile_with_schedule(
        &prepare_unified_profiling_fixture(),
        BaseLdeSchedule::PreWhir,
    );
}

#[test]
#[ignore]
fn pre_whir_full_blake2_compression_delegation_profile() {
    super::proof_matrix::run_profile_with_schedule(
        &super::proof_matrix::prepare_blake2_with_compression_profiling_fixture(),
        BaseLdeSchedule::PreWhir,
    );
}

fn check_retained_proofs(fixture: &BasicUnrolledProofFixture) {
    use crate::proof::memory_policy::OpeningPolicy::{FullMaterialization, RetainMonomials};
    let baseline = fixture.base.context.get_used_mem_current();
    for policy in [
        ProofMemoryPolicy {
            setup: RetainMonomials,
            memory: RetainMonomials,
            ..Default::default()
        },
        ProofMemoryPolicy {
            setup: FullMaterialization,
            memory: RetainMonomials,
            ..Default::default()
        },
        ProofMemoryPolicy {
            setup: RetainMonomials,
            memory: FullMaterialization,
            ..Default::default()
        },
    ] {
        let first = fixture
            .base
            .schedule_prove_with_memory_policy(policy)
            .unwrap();
        let second = fixture
            .base
            .schedule_prove_with_memory_policy(policy)
            .unwrap();
        for job in [first, second] {
            let (proof, _) = job.finish().unwrap();
            assert_gkr_proof_eq_for_test(&proof, &fixture.expected_cpu_proof);
        }
        assert_eq!(fixture.base.context.get_used_mem_current(), baseline);
    }
}

#[test]
#[ignore]
fn retained_openings_add_sub_parity_and_reuse() {
    check_retained_proofs(&prepare_basic_unrolled_proof_fixture_sec100());
}

#[test]
#[ignore]
fn retained_openings_unified_parity_and_reuse() {
    check_retained_proofs(&prepare_unified_proof_fixture());
}

#[test]
#[ignore]
fn retained_openings_setup_less_parity_and_reuse() {
    let (base, expected) =
        super::inits_and_teardowns::prepare_inits_and_teardowns_proof_fixture(true);
    check_retained_proofs(&BasicUnrolledProofFixture {
        base,
        expected_cpu_proof: expected.unwrap(),
    });
}

fn check_in_place_openings(fixture: &BasicUnrolledProofFixture) {
    use crate::proof::memory_policy::OpeningPolicy::{
        FullMaterialization, InPlace, RetainMonomials,
    };
    let baseline = fixture.base.context.get_used_mem_current();
    for (setup, memory) in [
        (InPlace, InPlace),
        (FullMaterialization, InPlace),
        (InPlace, FullMaterialization),
        (RetainMonomials, InPlace),
        (InPlace, RetainMonomials),
    ] {
        let policy = ProofMemoryPolicy {
            setup,
            memory,
            ..Default::default()
        };
        let first = fixture
            .base
            .schedule_prove_with_memory_policy(policy)
            .unwrap();
        let second = fixture
            .base
            .schedule_prove_with_memory_policy(policy)
            .unwrap();
        for job in [first, second] {
            let (proof, _) = job.finish().unwrap();
            assert_gkr_proof_eq_for_test(&proof, &fixture.expected_cpu_proof);
        }
        assert_eq!(fixture.base.context.get_used_mem_current(), baseline);
    }
}

#[test]
#[ignore]
fn in_place_openings_add_sub_parity_and_reuse() {
    check_in_place_openings(&prepare_basic_unrolled_proof_fixture_sec100());
}

#[test]
#[ignore]
fn in_place_openings_unified_parity_and_reuse() {
    check_in_place_openings(&prepare_unified_proof_fixture());
}

#[test]
#[ignore]
fn in_place_openings_setup_less_parity_and_reuse() {
    let (base, expected) =
        super::inits_and_teardowns::prepare_inits_and_teardowns_proof_fixture(true);
    check_in_place_openings(&BasicUnrolledProofFixture {
        base,
        expected_cpu_proof: expected.unwrap(),
    });
}

const RETAIN_MONOMIALS: ProofMemoryPolicy = ProofMemoryPolicy {
    setup: crate::proof::memory_policy::OpeningPolicy::RetainMonomials,
    memory: crate::proof::memory_policy::OpeningPolicy::RetainMonomials,
    witness: crate::proof::memory_policy::WitnessMemoryPolicy::FullMaterialization {
        whir: crate::proof::memory_policy::FullWitnessWhirPolicy::RetainCosets,
    },
};

#[test]
#[ignore]
fn retained_add_sub_profile() {
    super::proof_matrix::run_profile_with_memory_policy(
        &prepare_basic_unrolled_profiling_fixture(),
        RETAIN_MONOMIALS,
    );
}

#[test]
#[ignore]
fn retained_unified_profile() {
    super::proof_matrix::run_profile_with_memory_policy(
        &prepare_unified_profiling_fixture(),
        RETAIN_MONOMIALS,
    );
}

#[test]
#[ignore]
fn retained_blake2_compression_delegation_profile() {
    super::proof_matrix::run_profile_with_memory_policy(
        &super::proof_matrix::prepare_blake2_with_compression_profiling_fixture(),
        RETAIN_MONOMIALS,
    );
}

fn check_witness_policies(fixture: &BasicUnrolledProofFixture) {
    use crate::proof::memory_policy::{FullWitnessWhirPolicy, OpeningPolicy, WitnessMemoryPolicy};
    let baseline = fixture.base.context.get_used_mem_current();
    for opening in [
        OpeningPolicy::FullMaterialization,
        OpeningPolicy::RetainMonomials,
        OpeningPolicy::InPlace,
    ] {
        for witness in [
            WitnessMemoryPolicy::FullMaterialization {
                whir: FullWitnessWhirPolicy::Recompute(opening),
            },
            WitnessMemoryPolicy::RetainMonomials { whir: opening },
            WitnessMemoryPolicy::InPlace { whir: opening },
        ] {
            let policy = ProofMemoryPolicy {
                witness,
                ..Default::default()
            };
            let first = fixture
                .base
                .schedule_prove_with_memory_policy(policy)
                .unwrap();
            let second = fixture
                .base
                .schedule_prove_with_memory_policy(policy)
                .unwrap();
            for job in [first, second] {
                let (proof, _) = job.finish().unwrap();
                assert_gkr_proof_eq_for_test(&proof, &fixture.expected_cpu_proof);
            }
            assert_eq!(fixture.base.context.get_used_mem_current(), baseline);
        }
    }
    // Exercise all three in-place oracle openings together as well.
    let policy = ProofMemoryPolicy {
        setup: OpeningPolicy::InPlace,
        memory: OpeningPolicy::InPlace,
        witness: WitnessMemoryPolicy::InPlace {
            whir: OpeningPolicy::InPlace,
        },
    };
    let (proof, _) = fixture
        .base
        .schedule_prove_with_memory_policy(policy)
        .unwrap()
        .finish()
        .unwrap();
    assert_gkr_proof_eq_for_test(&proof, &fixture.expected_cpu_proof);
    assert_eq!(fixture.base.context.get_used_mem_current(), baseline);
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

#[test]
#[ignore]
fn witness_policies_setup_less_parity_and_reuse() {
    let (base, expected) =
        super::inits_and_teardowns::prepare_inits_and_teardowns_proof_fixture(true);
    check_witness_policies(&BasicUnrolledProofFixture {
        base,
        expected_cpu_proof: expected.unwrap(),
    });
}

// Explicit offline timing selection, confined to the test harness. Each run
// uses the normal production policy entry point and complete proof fixture.
fn witness_profile_policy() -> ProofMemoryPolicy {
    use crate::proof::memory_policy::{FullWitnessWhirPolicy, OpeningPolicy, WitnessMemoryPolicy};
    let selection = std::env::var("AB_WITNESS_PROFILE_POLICY")
        .expect("set AB_WITNESS_PROFILE_POLICY for witness policy measurements");
    let witness = match selection.as_str() {
        "full_keep" => WitnessMemoryPolicy::default(),
        "full_recompute_full" => WitnessMemoryPolicy::FullMaterialization {
            whir: FullWitnessWhirPolicy::Recompute(OpeningPolicy::FullMaterialization),
        },
        "full_recompute_monomials" => WitnessMemoryPolicy::FullMaterialization {
            whir: FullWitnessWhirPolicy::Recompute(OpeningPolicy::RetainMonomials),
        },
        "full_recompute_in_place" => WitnessMemoryPolicy::FullMaterialization {
            whir: FullWitnessWhirPolicy::Recompute(OpeningPolicy::InPlace),
        },
        "monomials_full" => WitnessMemoryPolicy::RetainMonomials {
            whir: OpeningPolicy::FullMaterialization,
        },
        "monomials_stream" => WitnessMemoryPolicy::RetainMonomials {
            whir: OpeningPolicy::RetainMonomials,
        },
        "monomials_in_place" => WitnessMemoryPolicy::RetainMonomials {
            whir: OpeningPolicy::InPlace,
        },
        "in_place_full" => WitnessMemoryPolicy::InPlace {
            whir: OpeningPolicy::FullMaterialization,
        },
        "in_place_monomials" => WitnessMemoryPolicy::InPlace {
            whir: OpeningPolicy::RetainMonomials,
        },
        "in_place_stream" => WitnessMemoryPolicy::InPlace {
            whir: OpeningPolicy::InPlace,
        },
        other => panic!("unknown witness profile policy: {other}"),
    };
    ProofMemoryPolicy {
        witness,
        ..Default::default()
    }
}

#[test]
#[ignore]
fn witness_add_sub_profile() {
    super::proof_matrix::run_profile_with_memory_policy(
        &prepare_basic_unrolled_profiling_fixture(),
        witness_profile_policy(),
    );
}

#[test]
#[ignore]
fn witness_unified_profile() {
    super::proof_matrix::run_profile_with_memory_policy(
        &prepare_unified_profiling_fixture(),
        witness_profile_policy(),
    );
}

#[test]
#[ignore]
fn witness_blake2_compression_delegation_profile() {
    super::proof_matrix::run_profile_with_memory_policy(
        &super::proof_matrix::prepare_blake2_with_compression_profiling_fixture(),
        witness_profile_policy(),
    );
}

#[test]
#[ignore]
fn memory_policy_paired_timing() {
    let fixture = match std::env::var("AB_MEMORY_PROFILE_CASE").unwrap().as_str() {
        "add_sub" => prepare_basic_unrolled_profiling_fixture(),
        "unified" => prepare_unified_profiling_fixture(),
        "blake2_with_compression" => {
            super::proof_matrix::prepare_blake2_with_compression_profiling_fixture()
        }
        other => panic!("unknown memory profile case: {other}"),
    };
    let candidate = match std::env::var("AB_WITNESS_PROFILE_POLICY").unwrap().as_str() {
        "setup_memory_monomials" => RETAIN_MONOMIALS,
        "setup_memory_in_place" => ProofMemoryPolicy {
            setup: crate::proof::memory_policy::OpeningPolicy::InPlace,
            memory: crate::proof::memory_policy::OpeningPolicy::InPlace,
            ..Default::default()
        },
        _ => witness_profile_policy(),
    };
    let baseline = fixture.context.get_used_mem_current();
    let plan = fixture.dr_tail_plan().unwrap();
    let run = |policy| {
        let transfers = fixture.schedule_transfers().unwrap();
        fixture.context.get_h2d_stream().synchronize().unwrap();
        fixture.context.reset_used_mem_peak();
        let (proof, ms) = crate::proof::prove_with_memory_policy::<Global>(
            &fixture.gkr_programs,
            &fixture.prover_config,
            fixture.final_trace_size_log_2,
            transfers,
            &plan,
            policy,
            &fixture.context,
        )
        .unwrap()
        .finish()
        .unwrap();
        assert_eq!(fixture.context.get_used_mem_current(), baseline);
        (proof, ms, fixture.context.get_used_mem_peak())
    };
    let (expected, _, _) = run(ProofMemoryPolicy::default());
    // Warm both policies twice, then retain every AB/BA sample. A fixture and
    // CUDA context are shared so process-to-process variation cannot separate
    // the comparison arms. Proof equality is checked outside the timed job.
    for _ in 0..2 {
        for policy in [ProofMemoryPolicy::default(), candidate] {
            let (proof, _, _) = run(policy);
            assert_gkr_proof_eq_for_test(&proof, &expected);
        }
    }
    for pair in 0..6 {
        let order = if pair % 2 == 0 { [0, 1] } else { [1, 0] };
        for arm in order {
            let policy = if arm == 0 {
                ProofMemoryPolicy::default()
            } else {
                candidate
            };
            let (proof, ms, peak) = run(policy);
            assert_gkr_proof_eq_for_test(&proof, &expected);
            eprintln!("memory_policy_sample pair={pair} arm={arm} ms={ms} peak_bytes={peak}");
        }
    }
}
