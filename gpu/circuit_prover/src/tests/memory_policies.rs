use super::*;

fn check_policies(
    fixture: &BasicUnrolledProofFixture,
    policies: impl IntoIterator<Item = ProofMemoryPolicy>,
) {
    let baseline = fixture.base.context.get_used_mem_current();
    let mut policies = policies.into_iter();
    while let Some(first_policy) = policies.next() {
        let second_policy = policies.next().unwrap_or(first_policy);
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
        }
        assert_eq!(fixture.base.context.get_used_mem_current(), baseline);
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

fn check_witness_policies(fixture: &BasicUnrolledProofFixture) {
    use crate::proof::memory_policy::{
        OpeningStrategy, WitnessCommitmentStrategy, WitnessMemoryPolicy, WitnessOpeningStrategy,
        WitnessPostCommitStorage,
    };
    let in_place = ProofMemoryPolicy {
        setup: OpeningStrategy::InPlace,
        memory: OpeningStrategy::InPlace,
        witness: WitnessMemoryPolicy {
            commitment: WitnessCommitmentStrategy::InPlace,
            post_commitment: WitnessPostCommitStorage::RawEvaluations,
            opening: WitnessOpeningStrategy::Recompute(OpeningStrategy::InPlace),
        },
    };
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
