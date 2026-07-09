//! Shared host-side helpers the A/B bench harness (`tests::fwd_vm_ab_report` +
//! the ncu targets) and the Task 10 production v2 parity gate
//! (`vm::gpu_tests`) both reuse: `fixture_stage1` (stage1 lookup mappings from
//! a `CircuitFixture`) and `challenge_value` (the SAME `ChallengeRef` ->
//! concrete `Ext` mapping on both sides, spec §5).
//!
//! The Task 2 G-CPU gate this module used to host (`HostSnapshot` /
//! `HostStorageResolvers` / `sample_rows` / `validate_bindings_sampled`, plus
//! the `root_flat_addr`/D2H-column plumbing they depended on) is gone (Task
//! 12) — superseded by the Task 10 production v2 device-side parity gate.

use cs::gkr_compiler::dag_ir::{ChallengeKey, ChallengePower, ChallengeRef, Ext, PermutationSlot};
use field::Field;

use super::super::fixture::{CircuitFixture, CircuitKeepalive};
use crate::prover::gkr::stage1::GpuGKRStage1Output;

/// `base^power` per the DAG-IR convention (`One` = power 1, `Static(p)` = power
/// p, so `Static(0)` = 1). `alpha^j`, `rho^p`, etc. resolve through this.
fn pow_of(base: Ext, power: &ChallengePower) -> Ext {
    let p = match power {
        ChallengePower::One => 1u32,
        ChallengePower::Static(p) => *p,
    };
    base.pow(p)
}

/// Map a `PermutationSlot` to its linearization-challenge index
/// (`cs/src/definitions/constants.rs:15-20` `PERMUTATION_ARGUMENT_CHALLENGE_POWERS_*_IDX`).
fn perm_role(slot: &PermutationSlot) -> usize {
    match slot {
        PermutationSlot::AddressLow => 0,
        PermutationSlot::AddressHigh => 1,
        PermutationSlot::TimestampLow => 2,
        PermutationSlot::TimestampHigh => 3,
        PermutationSlot::ValueLow => 4,
        PermutationSlot::ValueHigh => 5,
    }
}

pub(crate) fn fixture_stage1(fixture: &CircuitFixture) -> &GpuGKRStage1Output {
    match &fixture.keepalive {
        CircuitKeepalive::Unrolled { stage1, .. } => stage1,
        CircuitKeepalive::Delegation(keepalive) => &keepalive.stage1,
    }
}

/// The SAME `ChallengeRef` -> concrete `Ext` mapping the production v2
/// lowering (`vm::lower`) sources challenge values from (spec §5: "the SAME
/// mapping"). Any change to how a challenge resolves must land here once, for
/// both call sites.
pub(crate) fn challenge_value(fixture: &CircuitFixture, r: &ChallengeRef) -> Ext {
    let base = match &r.key {
        ChallengeKey::LookupMultiplicative => fixture.lookup_alpha,
        ChallengeKey::LookupAdditive => fixture.lookup_additive_part,
        ChallengeKey::PermutationAdditive => {
            fixture.external_challenges.permutation_argument_additive_part
        }
        ChallengeKey::PermutationLinearization(slot) => {
            fixture.external_challenges.permutation_argument_linearization_challenges
                [perm_role(slot)]
        }
        ChallengeKey::ConstraintAggregation => panic!(
            "challenge_value: ConstraintAggregation is not sourced for these circuits' forward \
            programs (no materialized constraint roots): {r:?}"
        ),
    };
    pow_of(base, &r.power)
}
