use super::*;

fn check_policies(
    fixture: &BasicUnrolledProofFixture,
    policies: impl IntoIterator<Item = ProofMemoryPolicy>,
) {
    let baseline = fixture.base.context.get_used_mem_current();
    for policy in policies {
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

fn check_opening_policies(fixture: &BasicUnrolledProofFixture) {
    use crate::proof::memory_policy::OpeningStrategy::{AllCosets, InPlace, PerCoset};
    let policies = [AllCosets, PerCoset, InPlace];
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
    check_opening_policies(&BasicUnrolledProofFixture {
        base,
        expected_cpu_proof: expected.unwrap(),
    });
}

fn check_witness_policies(fixture: &BasicUnrolledProofFixture) {
    use crate::proof::memory_policy::{OpeningStrategy, WitnessMemoryPolicy};
    check_policies(
        fixture,
        WitnessMemoryPolicy::candidates().map(|witness| ProofMemoryPolicy {
            witness,
            ..Default::default()
        }),
    );
    check_policies(
        fixture,
        [ProofMemoryPolicy {
            setup: OpeningStrategy::InPlace,
            memory: OpeningStrategy::InPlace,
            witness: WitnessMemoryPolicy {
                commitment: crate::proof::memory_policy::WitnessCommitmentStrategy::InPlace,
                post_commitment:
                    crate::proof::memory_policy::WitnessPostCommitStorage::RawEvaluations,
                opening: crate::proof::memory_policy::WitnessOpeningStrategy::Recompute(
                    OpeningStrategy::InPlace,
                ),
            },
        }],
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
