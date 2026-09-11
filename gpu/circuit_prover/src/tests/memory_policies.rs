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
    use crate::proof::memory_policy::OpeningPolicy::{
        FullMaterialization, InPlace, RetainMonomials,
    };
    let policies = [FullMaterialization, RetainMonomials, InPlace];
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
    use crate::proof::memory_policy::{FullWitnessWhirPolicy, OpeningPolicy, WitnessMemoryPolicy};
    for opening in [
        OpeningPolicy::FullMaterialization,
        OpeningPolicy::RetainMonomials,
        OpeningPolicy::InPlace,
    ] {
        check_policies(
            fixture,
            [
                WitnessMemoryPolicy::FullMaterialization {
                    whir: FullWitnessWhirPolicy::Recompute(opening),
                },
                WitnessMemoryPolicy::RetainMonomials { whir: opening },
                WitnessMemoryPolicy::InPlace { whir: opening },
            ]
            .map(|witness| ProofMemoryPolicy {
                witness,
                ..Default::default()
            }),
        );
    }
    let policy = ProofMemoryPolicy {
        setup: OpeningPolicy::InPlace,
        memory: OpeningPolicy::InPlace,
        witness: WitnessMemoryPolicy::InPlace {
            whir: OpeningPolicy::InPlace,
        },
    };
    check_policies(fixture, [policy]);
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
