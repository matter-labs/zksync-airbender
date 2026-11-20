use super::{PartialTreePolicy, ProofMemoryPolicy};
use crate::upstream::ProofProfile;
use gpu_trace::witness::circuit_type::{CircuitType, UnrolledCircuitType};

use crate::baby_bear::presets::{compression, generated};
use crate::proth120::presets as l1_wrap;

/// Arena bytes kept free for the next request's inputs while a proof runs:
/// the largest full-capacity input bundle of any supported circuit, rounded up.
pub const INPUTS_RESERVE_BYTES: usize = 1537 << 20;

pub(crate) const PRESET_ARENA_BYTES: &[usize] = &[22548578304, 32212254720];

pub fn select_arena_bytes(available: usize) -> usize {
    PRESET_ARENA_BYTES
        .iter()
        .rev()
        .copied()
        .find(|&bytes| bytes <= available)
        .unwrap_or_else(|| panic!("no memory preset fits in {available} available arena bytes"))
}

/// `ProofProfile::CompressionFinal` and `UnrolledCircuitType::Unified22` imply each
/// other; `ProofProfile::Compression` requires `UnrolledCircuitType::Unified`,
/// which also proves `ProofProfile::Standard`.
pub(crate) fn is_compression(circuit: CircuitType, profile: ProofProfile) -> bool {
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
        // Reuse the 2^22 witness prefix for the 21 GiB arena.
        CircuitType::L1Wrap22 if arena_bytes < PRESET_ARENA_BYTES[1] => {
            l1_wrap::L1_WRAP_REUSE_PREFIX_POLICY
        }
        CircuitType::L1Wrap21 | CircuitType::L1Wrap22 => l1_wrap::L1_WRAP_POLICY,
        _ => generated::policy(circuit, select_arena_bytes(arena_bytes)),
    }
}

pub fn partial_trees(circuit: CircuitType, profile: ProofProfile) -> PartialTreePolicy {
    if is_compression(circuit, profile) {
        return compression::PARTIAL_TREES;
    }
    match circuit {
        CircuitType::L1Wrap21 | CircuitType::L1Wrap22 => l1_wrap::PARTIAL_TREES,
        _ => PartialTreePolicy::DEFAULT,
    }
}

/// Whether the commitment exports its memory partial trees for the proof to
/// open, and the proof requires them.
pub fn persists_memory_partial_trees(circuit: CircuitType, profile: ProofProfile) -> bool {
    is_compression(circuit, profile)
}

#[cfg(test)]
mod cpu_tests {
    use super::*;
    use crate::proof::memory_policy::WitnessPostCommitStorage;

    #[test]
    fn cpu_l1_wrap_prefix_reuse_preset() {
        use WitnessPostCommitStorage::{RawAndMonomials, RawWithReusedPrefixScratch};

        let [tight, roomy] = PRESET_ARENA_BYTES else {
            panic!("L1 wrap memory schedule test requires both arena presets");
        };
        let config = ProofProfile::L1Wrap.prover_config(
            CircuitType::L1Wrap22.get_domain_size_log2() as usize,
            prover::definitions::SoundnessMode::EthproofsSoundnessCalc,
        );
        let shape = gpu_whir::proth120::L1WhirShape::from_config(&config);
        assert_eq!(
            (shape.log_message, shape.log_base_lde, shape.cap_log),
            (25, 7, 5)
        );
        let query_domains: Vec<_> = shape.rounds.iter().map(|r| r.query_domain_log2).collect();
        assert_eq!(query_domains, [31, 31, 28, 25, 23, 20]);

        for (circuit, arena, expected) in [
            (CircuitType::L1Wrap21, *tight, RawAndMonomials),
            (CircuitType::L1Wrap21, *roomy, RawAndMonomials),
            (CircuitType::L1Wrap22, *tight, RawWithReusedPrefixScratch),
            (CircuitType::L1Wrap22, *roomy, RawAndMonomials),
        ] {
            let selected = policy(circuit, ProofProfile::L1Wrap, arena);
            assert!(selected.witness.is_valid());
            assert_eq!(selected.witness.post_commitment, expected);
        }
    }
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
        assert_eq!(PRESET_ARENA_BYTES, &[21 << 30, 30 << 30]);
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
