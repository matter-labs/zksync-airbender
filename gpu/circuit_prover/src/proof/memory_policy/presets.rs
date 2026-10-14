use super::{PartialTreePolicy, ProofMemoryPolicy};
use crate::proof::merged_commitment::MergedCommitStrategy;
use crate::upstream::ProofProfile;
use gpu_trace::witness::circuit_type::{CircuitType, UnrolledCircuitType};

mod generated;
pub mod l1_feeder;
pub mod l1_wrap;

/// Arena bytes kept free for the next request's inputs while a proof runs:
/// the largest full-capacity input bundle of any supported circuit, rounded up.
pub const INPUTS_RESERVE_BYTES: usize = 1537 << 20;

pub const L1_ARENA_BYTES: usize = 64 << 30;

pub fn select_arena_bytes(available: usize) -> usize {
    generated::PRESET_ARENA_BYTES
        .iter()
        .rev()
        .copied()
        .find(|&bytes| bytes <= available)
        .unwrap_or_else(|| panic!("no memory preset fits in {available} available arena bytes"))
}

pub fn select_auto_arena_bytes(available: usize) -> usize {
    let generated = select_arena_bytes(available);
    if L1_ARENA_BYTES <= available {
        generated.max(L1_ARENA_BYTES)
    } else {
        generated
    }
}

/// `ProofProfile::L1Feeder` and `UnrolledCircuitType::Unified22` imply each other.
fn is_l1_feeder(circuit: CircuitType, profile: ProofProfile) -> bool {
    const UNIFIED22: CircuitType = CircuitType::Unrolled(UnrolledCircuitType::Unified22);
    assert!(
        profile != ProofProfile::L1Feeder || circuit == UNIFIED22,
        "ProofProfile::L1Feeder requires CircuitType::Unrolled(UnrolledCircuitType::Unified22), got {circuit:?}"
    );
    assert!(
        circuit != UNIFIED22 || profile == ProofProfile::L1Feeder,
        "CircuitType::Unrolled(UnrolledCircuitType::Unified22) requires ProofProfile::L1Feeder, got {profile:?}"
    );
    profile == ProofProfile::L1Feeder
}

pub fn policy(
    circuit: CircuitType,
    profile: ProofProfile,
    arena_bytes: usize,
) -> ProofMemoryPolicy {
    if is_l1_feeder(circuit, profile) {
        return l1_feeder::policy(arena_bytes);
    }
    match circuit {
        CircuitType::L1Wrap21 => l1_wrap::policy(arena_bytes),
        _ => generated::policy(circuit, select_arena_bytes(arena_bytes)),
    }
}

pub fn partial_trees(circuit: CircuitType, profile: ProofProfile) -> PartialTreePolicy {
    if is_l1_feeder(circuit, profile) {
        return l1_feeder::PARTIAL_TREES;
    }
    match circuit {
        CircuitType::L1Wrap21 => l1_wrap::PARTIAL_TREES,
        _ => PartialTreePolicy::DEFAULT,
    }
}

pub fn admit_l1_wrap(arena_bytes: usize) {
    use l1_wrap::{L1_WRAP_FLOOR_SOURCE, L1_WRAP_WHOLE_PROOF_FLOOR_BYTES};
    assert!(
        arena_bytes >= L1_WRAP_WHOLE_PROOF_FLOOR_BYTES,
        "L1Wrap requires an arena of at least {L1_WRAP_WHOLE_PROOF_FLOOR_BYTES} bytes ({L1_WRAP_FLOOR_SOURCE} whole-proof floor), got {arena_bytes}"
    );
}

pub fn admit_l1_feeder(arena_bytes: usize) {
    use l1_feeder::{L1_FEEDER_FLOOR_BYTES, L1_FEEDER_FLOOR_SOURCE};
    assert!(
        arena_bytes >= L1_FEEDER_FLOOR_BYTES,
        "ProofProfile::L1Feeder requires an arena of at least {L1_FEEDER_FLOOR_BYTES} bytes ({L1_FEEDER_FLOOR_SOURCE} floor), got {arena_bytes}"
    );
}

pub fn merged_commit_strategy(circuit: CircuitType, profile: ProofProfile) -> MergedCommitStrategy {
    if is_l1_feeder(circuit, profile) {
        MergedCommitStrategy::Monomials
    } else {
        MergedCommitStrategy::AllCosets
    }
}

#[cfg(test)]
mod cpu_tests {
    use super::*;
    use crate::proof::memory_policy::{
        GkrMemoryPolicy, OpeningStrategy, WitnessCommitmentStrategy, WitnessOpeningStrategy,
        WitnessPostCommitStorage,
    };
    use gpu_trace::witness::circuit_type::{
        DelegationCircuitType, UnrolledMemoryCircuitType, UnrolledNonMemoryCircuitType,
    };

    #[test]
    fn cpu_m8_feeder_policy() {
        let unified = CircuitType::Unrolled(UnrolledCircuitType::Unified);
        let unified22 = CircuitType::Unrolled(UnrolledCircuitType::Unified22);
        let selected = policy(unified22, ProofProfile::L1Feeder, 30 << 30);
        assert_eq!(selected, l1_feeder::POLICY);
        assert!(selected.witness.is_valid());
        assert_eq!(selected.gkr, GkrMemoryPolicy::Materialize);
        assert_eq!(selected.setup, OpeningStrategy::PerCoset);
        assert_eq!(selected.memory, OpeningStrategy::PerCoset);
        assert_eq!(
            selected.witness.commitment,
            WitnessCommitmentStrategy::PerCoset
        );
        assert_eq!(
            selected.witness.post_commitment,
            WitnessPostCommitStorage::RawAndMonomials
        );
        assert_eq!(
            selected.witness.opening,
            WitnessOpeningStrategy::Recompute(OpeningStrategy::PerCoset)
        );
        assert_eq!(
            merged_commit_strategy(unified22, ProofProfile::L1Feeder),
            MergedCommitStrategy::Monomials
        );
        assert_eq!(
            merged_commit_strategy(unified, ProofProfile::Standard),
            MergedCommitStrategy::AllCosets
        );
        let feeder_trees = partial_trees(unified22, ProofProfile::L1Feeder);
        assert_eq!(feeder_trees, l1_feeder::PARTIAL_TREES);
        assert_eq!((feeder_trees.setup, feeder_trees.memory), (10, 10));
        assert_eq!(
            partial_trees(unified, ProofProfile::Standard),
            PartialTreePolicy::DEFAULT
        );
        assert_eq!(
            policy(unified, ProofProfile::Standard, 21 << 30),
            generated::policy(unified, 21 << 30)
        );
        let delegations = [
            DelegationCircuitType::BigIntWithControl,
            DelegationCircuitType::Blake2WithCompression,
            DelegationCircuitType::Blake2GFunction,
            DelegationCircuitType::KeccakSpecial5,
            DelegationCircuitType::KeccakColumnParity,
            DelegationCircuitType::KeccakThetaRho,
            DelegationCircuitType::KeccakChi5,
        ];
        let unrolled = [
            UnrolledCircuitType::InitsAndTeardowns,
            UnrolledCircuitType::Memory(UnrolledMemoryCircuitType::LoadStoreSubwordOnly),
            UnrolledCircuitType::Memory(UnrolledMemoryCircuitType::LoadStoreWordOnly),
            UnrolledCircuitType::NonMemory(UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop),
            UnrolledCircuitType::NonMemory(UnrolledNonMemoryCircuitType::JumpBranchSlt),
            UnrolledCircuitType::NonMemory(UnrolledNonMemoryCircuitType::MulDivUnsigned),
            UnrolledCircuitType::NonMemory(UnrolledNonMemoryCircuitType::ShiftBinary),
        ];
        let named_panic = |select: &dyn Fn(), expected: String| {
            let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(select))
                .expect_err("a mismatched L1Feeder identity must panic");
            assert_eq!(
                panic
                    .downcast_ref::<String>()
                    .expect("named L1Feeder panic"),
                &expected
            );
        };
        for circuit in delegations
            .into_iter()
            .map(CircuitType::Delegation)
            .chain(unrolled.into_iter().map(CircuitType::Unrolled))
            .chain([unified, CircuitType::L1Wrap21])
        {
            let expected = format!("ProofProfile::L1Feeder requires CircuitType::Unrolled(UnrolledCircuitType::Unified22), got {circuit:?}");
            named_panic(
                &|| {
                    policy(circuit, ProofProfile::L1Feeder, 30 << 30);
                },
                expected.clone(),
            );
            named_panic(
                &|| {
                    partial_trees(circuit, ProofProfile::L1Feeder);
                },
                expected.clone(),
            );
            named_panic(
                &|| {
                    merged_commit_strategy(circuit, ProofProfile::L1Feeder);
                },
                expected,
            );
        }
        for profile in [ProofProfile::Standard, ProofProfile::L1Wrap] {
            let expected = format!("CircuitType::Unrolled(UnrolledCircuitType::Unified22) requires ProofProfile::L1Feeder, got {profile:?}");
            named_panic(
                &|| {
                    policy(unified22, profile, 30 << 30);
                },
                expected.clone(),
            );
            named_panic(
                &|| {
                    partial_trees(unified22, profile);
                },
                expected.clone(),
            );
            named_panic(
                &|| {
                    merged_commit_strategy(unified22, profile);
                },
                expected,
            );
        }
    }

    #[test]
    fn cpu_m8_admission() {
        use l1_feeder::{L1_FEEDER_FLOOR_BYTES, L1_FEEDER_FLOOR_SOURCE};
        use l1_wrap::{L1_WRAP_FLOOR_SOURCE, L1_WRAP_WHOLE_PROOF_FLOOR_BYTES};
        assert_eq!(L1_WRAP_FLOOR_SOURCE, "measured");
        assert_eq!(L1_FEEDER_FLOOR_SOURCE, "measured");
        admit_l1_wrap(L1_WRAP_WHOLE_PROOF_FLOOR_BYTES);
        admit_l1_feeder(L1_FEEDER_FLOOR_BYTES);
        let cases: [(fn(usize), usize, String); 2] = [
            (
                admit_l1_wrap,
                L1_WRAP_WHOLE_PROOF_FLOOR_BYTES - 1,
                format!(
                    "L1Wrap requires an arena of at least {L1_WRAP_WHOLE_PROOF_FLOOR_BYTES} bytes (measured whole-proof floor), got {}",
                    L1_WRAP_WHOLE_PROOF_FLOOR_BYTES - 1
                ),
            ),
            (
                admit_l1_feeder,
                L1_FEEDER_FLOOR_BYTES - 1,
                format!(
                    "ProofProfile::L1Feeder requires an arena of at least {L1_FEEDER_FLOOR_BYTES} bytes (measured floor), got {}",
                    L1_FEEDER_FLOOR_BYTES - 1
                ),
            ),
        ];
        for (admit, arena_bytes, expected) in cases {
            let panic = std::panic::catch_unwind(|| admit(arena_bytes))
                .expect_err("an arena below the floor must be rejected");
            assert_eq!(
                panic
                    .downcast_ref::<String>()
                    .expect("named admission panic"),
                &expected
            );
        }
    }

    #[test]
    fn cpu_m8_auto_arena() {
        let available = 20 << 30;
        let panic = std::panic::catch_unwind(|| select_auto_arena_bytes(available))
            .expect_err("an arena below every preset must be rejected");
        assert_eq!(
            panic.downcast_ref::<String>().expect("named preset panic"),
            &format!("no memory preset fits in {available} available arena bytes")
        );
        for (available, expected) in [(21, 21), (30, 30), (63, 30), (64, 64), (96, 64)] {
            assert_eq!(select_auto_arena_bytes(available << 30), expected << 30);
        }
        assert_eq!(select_arena_bytes(64 << 30), 30 << 30);
        const { assert!(L1_ARENA_BYTES >= l1_wrap::L1_WRAP_WHOLE_PROOF_FLOOR_BYTES) };
    }

    #[test]
    fn preset_budget_boundaries() {
        assert_eq!(generated::PRESET_ARENA_BYTES, &[21 << 30, 30 << 30]);
        assert!(std::panic::catch_unwind(|| select_arena_bytes((21 << 30) - 1)).is_err());
        for (available, expected) in [
            (21 << 30, 21 << 30),
            ((30 << 30) - 1, 21 << 30),
            (30 << 30, 30 << 30),
            (usize::MAX, 30 << 30),
        ] {
            assert_eq!(select_arena_bytes(available), expected);
        }
    }
}
