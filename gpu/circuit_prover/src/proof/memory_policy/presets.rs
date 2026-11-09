use super::{PartialTreePolicy, ProofMemoryPolicy};
use crate::upstream::ProofProfile;
use gpu_gkr::stage1::merged_commitment::MergedCommitStrategy;
use gpu_trace::witness::circuit_type::{CircuitType, UnrolledCircuitType};

pub mod compression;
mod generated;
pub mod l1_wrap;

/// Arena bytes kept free for the next request's inputs while a proof runs:
/// the largest full-capacity input bundle of any supported circuit, rounded up.
pub const INPUTS_RESERVE_BYTES: usize = 1537 << 20;

/// `ProverContextConfig::h2d_staging_bytes`: the largest total any request
/// bundle stages through `Transfer::stage`, an compression proof's persisted
/// memory partial trees (2 MiB) plus the default capacity for small values.
pub const H2D_STAGING_BYTES: usize = (2 << 20) + gpu_prover_context::DEFAULT_H2D_STAGING_BYTES;

pub fn select_arena_bytes(available: usize) -> usize {
    generated::PRESET_ARENA_BYTES
        .iter()
        .rev()
        .copied()
        .find(|&bytes| bytes <= available)
        .unwrap_or_else(|| panic!("no memory preset fits in {available} available arena bytes"))
}

/// `ProofProfile::CompressionFinal` and `UnrolledCircuitType::Unified22` imply each
/// other; `ProofProfile::Compression` requires `UnrolledCircuitType::Unified`,
/// which also proves `ProofProfile::Standard`.
fn is_compression(circuit: CircuitType, profile: ProofProfile) -> bool {
    const UNIFIED22: CircuitType = CircuitType::Unrolled(UnrolledCircuitType::Unified22);
    const UNIFIED: CircuitType = CircuitType::Unrolled(UnrolledCircuitType::Unified);
    assert!(
        profile != ProofProfile::CompressionFinal || circuit == UNIFIED22,
        "ProofProfile::CompressionFinal requires CircuitType::Unrolled(UnrolledCircuitType::Unified22), got {circuit:?}"
    );
    assert!(
        circuit != UNIFIED22 || profile == ProofProfile::CompressionFinal,
        "CircuitType::Unrolled(UnrolledCircuitType::Unified22) requires ProofProfile::CompressionFinal, got {profile:?}"
    );
    assert!(
        profile != ProofProfile::Compression || circuit == UNIFIED,
        "ProofProfile::Compression requires CircuitType::Unrolled(UnrolledCircuitType::Unified), got {circuit:?}"
    );
    profile.is_compression()
}

pub fn policy(
    circuit: CircuitType,
    profile: ProofProfile,
    arena_bytes: usize,
) -> ProofMemoryPolicy {
    if is_compression(circuit, profile) {
        return compression::POLICY;
    }
    match circuit {
        CircuitType::L1Wrap => l1_wrap::L1_WRAP_POLICY,
        _ => generated::policy(circuit, select_arena_bytes(arena_bytes)),
    }
}

pub fn partial_trees(circuit: CircuitType, profile: ProofProfile) -> PartialTreePolicy {
    if is_compression(circuit, profile) {
        return compression::PARTIAL_TREES;
    }
    match circuit {
        CircuitType::L1Wrap => l1_wrap::PARTIAL_TREES,
        _ => PartialTreePolicy::DEFAULT,
    }
}

/// Whether the commitment exports its memory partial trees for the proof to
/// open, and the proof requires them.
pub fn persists_memory_partial_trees(circuit: CircuitType, profile: ProofProfile) -> bool {
    is_compression(circuit, profile)
}

pub fn merged_commit_strategy(circuit: CircuitType, profile: ProofProfile) -> MergedCommitStrategy {
    if is_compression(circuit, profile) {
        MergedCommitStrategy::Monomials
    } else {
        MergedCommitStrategy::AllCosets
    }
}

#[cfg(test)]
mod cpu_tests {
    use super::*;
    use gpu_trace::witness::circuit_type::{
        DelegationCircuitType, UnrolledMemoryCircuitType, UnrolledNonMemoryCircuitType,
    };

    #[test]
    fn cpu_compression_profile_refusals() {
        let unified = CircuitType::Unrolled(UnrolledCircuitType::Unified);
        let unified22 = CircuitType::Unrolled(UnrolledCircuitType::Unified22);
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
                .expect_err("a mismatched Compression identity must panic");
            assert_eq!(
                panic
                    .downcast_ref::<String>()
                    .expect("named Compression panic"),
                &expected
            );
        };
        for circuit in delegations
            .into_iter()
            .map(CircuitType::Delegation)
            .chain(unrolled.into_iter().map(CircuitType::Unrolled))
            .chain([unified, CircuitType::L1Wrap])
        {
            assert!(!persists_memory_partial_trees(
                circuit,
                ProofProfile::Standard
            ));
            let expected = format!("ProofProfile::CompressionFinal requires CircuitType::Unrolled(UnrolledCircuitType::Unified22), got {circuit:?}");
            named_panic(
                &|| {
                    policy(circuit, ProofProfile::CompressionFinal, 30 << 30);
                },
                expected.clone(),
            );
            named_panic(
                &|| {
                    partial_trees(circuit, ProofProfile::CompressionFinal);
                },
                expected.clone(),
            );
            named_panic(
                &|| {
                    merged_commit_strategy(circuit, ProofProfile::CompressionFinal);
                },
                expected.clone(),
            );
            named_panic(
                &|| {
                    persists_memory_partial_trees(circuit, ProofProfile::CompressionFinal);
                },
                expected,
            );
        }
        for profile in [ProofProfile::Standard, ProofProfile::L1Wrap] {
            let expected = format!("CircuitType::Unrolled(UnrolledCircuitType::Unified22) requires ProofProfile::CompressionFinal, got {profile:?}");
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
                expected.clone(),
            );
            named_panic(
                &|| {
                    persists_memory_partial_trees(unified22, profile);
                },
                expected,
            );
        }
    }

    #[test]
    fn cpu_compression_a_profile_refusals() {
        let unified22 = CircuitType::Unrolled(UnrolledCircuitType::Unified22);
        let a = ProofProfile::Compression;
        let named_panic = |circuit: CircuitType, expected: String| {
            let panic = std::panic::catch_unwind(|| policy(circuit, a, 21 << 30))
                .expect_err("a mismatched Compression identity must panic");
            assert_eq!(
                panic
                    .downcast_ref::<String>()
                    .expect("named Compression panic"),
                &expected
            );
        };
        named_panic(
            unified22,
            format!("CircuitType::Unrolled(UnrolledCircuitType::Unified22) requires ProofProfile::CompressionFinal, got {a:?}"),
        );
        for circuit in [
            CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns),
            CircuitType::Delegation(DelegationCircuitType::BigIntWithControl),
            CircuitType::L1Wrap,
        ] {
            named_panic(
                circuit,
                format!("ProofProfile::Compression requires CircuitType::Unrolled(UnrolledCircuitType::Unified), got {circuit:?}"),
            );
        }
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
