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
    #[test]
    #[should_panic(expected = "ProofProfile::CompressionFinal requires")]
    fn cpu_compression_final_requires_unified22() {
        is_compression(
            CircuitType::Unrolled(UnrolledCircuitType::Unified),
            ProofProfile::CompressionFinal,
        );
    }

    #[test]
    #[should_panic(expected = "requires ProofProfile::CompressionFinal")]
    fn cpu_unified22_requires_compression_final() {
        is_compression(
            CircuitType::Unrolled(UnrolledCircuitType::Unified22),
            ProofProfile::Standard,
        );
    }

    #[test]
    #[should_panic(expected = "ProofProfile::Compression requires")]
    fn cpu_compression_requires_unified() {
        is_compression(
            CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns),
            ProofProfile::Compression,
        );
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
