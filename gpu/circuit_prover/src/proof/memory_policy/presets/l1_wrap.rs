use super::super::{
    GkrMemoryPolicy, OpeningStrategy, ProofMemoryPolicy, WitnessCommitmentStrategy,
    WitnessMemoryPolicy, WitnessOpeningStrategy, WitnessPostCommitStorage,
};

pub const MEASURED_M4_PEAK_BYTES: usize = 25_937_575_936;
pub const OVERLAP_BYTES: usize = 3_472_883_712;

pub const fn align_up(bytes: usize, unit: usize) -> usize {
    assert!(unit > 0, "L1Wrap arena alignment unit must be positive");
    let rounded = bytes
        .checked_add(unit - 1)
        .expect("L1Wrap arena alignment overflow");
    (rounded / unit)
        .checked_mul(unit)
        .expect("L1Wrap arena alignment overflow")
}

pub const L1_WRAP_ARENA_MIN_BYTES: usize =
    align_up(MEASURED_M4_PEAK_BYTES + OVERLAP_BYTES, 1 << 30);

/// Smallest sufficient arena of the bounded capacity matrix (`gpu/execution_prover/tests/l1_memory.rs`: 32/40/48/64 GiB candidates, both directions, three opposite followers) on the RTX PRO 6000 Blackwell (sm_120).
pub const L1_WRAP_WHOLE_PROOF_FLOOR_BYTES: usize = 32 << 30;
pub const L1_WRAP_FLOOR_SOURCE: &str = "measured";
const _: () = assert!(L1_WRAP_WHOLE_PROOF_FLOOR_BYTES >= L1_WRAP_ARENA_MIN_BYTES);

pub const L1_WRAP_POLICY: ProofMemoryPolicy = ProofMemoryPolicy {
    gkr: GkrMemoryPolicy::Materialize,
    setup: OpeningStrategy::PerCoset,
    memory: OpeningStrategy::PerCoset,
    witness: WitnessMemoryPolicy {
        commitment: WitnessCommitmentStrategy::PerCoset,
        post_commitment: WitnessPostCommitStorage::RawAndMonomials,
        opening: WitnessOpeningStrategy::PackedCosetRecompute,
    },
};

pub fn policy(arena_bytes: usize) -> ProofMemoryPolicy {
    assert!(
        arena_bytes >= L1_WRAP_ARENA_MIN_BYTES,
        "L1Wrap requires an arena of at least {L1_WRAP_ARENA_MIN_BYTES} bytes, got {arena_bytes}"
    );
    L1_WRAP_POLICY
}

#[cfg(test)]
mod cpu_tests {
    use super::*;
    use cs::gkr_compiler::GKRCircuitArtifact;
    use gpu_core::primitives::field::PR;
    use gpu_trace::witness::circuit_type::CircuitType;
    use riscv_transpiler::witness::UnifiedOpcodeTracingDataWithTimestamp;

    #[test]
    fn cpu_l1_wrap_preset_components() {
        const ROWS: usize = 1 << 22;
        const PACKED_ROWS: usize = 1 << 26;
        const RAW_BYTES: usize = (104 + 10) * ROWS * 16;
        const MONOMIAL_BYTES: usize = (7 + 1) * PACKED_ROWS * 16;
        const SCRATCH_BYTES: usize = 7 * PACKED_ROWS * 16;
        const RETAINED_BYTES: usize = 2 * 32 * ((1 << 20) - 1) * 32;
        const ROOTS_TOP_CAP_BYTES: usize = 2 * (32 + 24 + 8) * 32;
        const OFFSET_BYTES: usize = 2 * 32 * 16;
        const BLOCK_BYTES: usize = 1 << 20;
        const SMALL_POOL_BYTES: usize = 2 * 16 * BLOCK_BYTES;
        const RETAINED_BLOCK_ROUNDING: usize =
            2 * align_up(RETAINED_BYTES / 2, BLOCK_BYTES) - RETAINED_BYTES;
        assert_eq!(
            RAW_BYTES
                + MONOMIAL_BYTES
                + SCRATCH_BYTES
                + RETAINED_BYTES
                + ROOTS_TOP_CAP_BYTES
                + OFFSET_BYTES,
            25_904_024_576
        );
        assert_eq!(
            MEASURED_M4_PEAK_BYTES,
            RAW_BYTES
                + MONOMIAL_BYTES
                + SCRATCH_BYTES
                + RETAINED_BYTES
                + RETAINED_BLOCK_ROUNDING
                + SMALL_POOL_BYTES
        );
        let layout: GKRCircuitArtifact<PR> = serde_json::from_str(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json"
        )))
        .unwrap();
        assert_eq!(layout.trace_len, ROWS);
        let mapping_columns = layout.generic_lookups.len()
            + usize::from(layout.has_decoder_lookup)
            + layout.range_check_16_lookup_expressions.len()
            + layout.timestamp_range_check_lookup_expressions.len();
        assert_eq!(layout.scratch_space_size, 41);
        assert_eq!(mapping_columns, 29);
        assert_eq!(
            std::mem::size_of::<UnifiedOpcodeTracingDataWithTimestamp>(),
            56
        );
        assert_eq!(
            OVERLAP_BYTES,
            layout.scratch_space_size * ROWS * std::mem::size_of::<PR>()
                + mapping_columns * ROWS * std::mem::size_of::<u32>()
                + ROWS * std::mem::size_of::<UnifiedOpcodeTracingDataWithTimestamp>()
        );
        assert_eq!(
            L1_WRAP_ARENA_MIN_BYTES,
            align_up(MEASURED_M4_PEAK_BYTES + OVERLAP_BYTES, 1 << 30)
        );
        assert_eq!(L1_WRAP_ARENA_MIN_BYTES, 28 << 30);
        let panic = std::panic::catch_unwind(|| policy(L1_WRAP_ARENA_MIN_BYTES - 1)).unwrap_err();
        let message = panic.downcast_ref::<String>().unwrap();
        assert_eq!(
            message,
            &format!(
                "L1Wrap requires an arena of at least {L1_WRAP_ARENA_MIN_BYTES} bytes, got {}",
                L1_WRAP_ARENA_MIN_BYTES - 1
            )
        );
        assert_eq!(
            super::super::policy(
                CircuitType::L1Wrap,
                crate::upstream::ProofProfile::L1Wrap,
                80 << 30
            ),
            L1_WRAP_POLICY
        );
        assert_eq!(
            super::super::policy(
                CircuitType::L1Wrap,
                crate::upstream::ProofProfile::L1Wrap,
                L1_WRAP_ARENA_MIN_BYTES
            ),
            L1_WRAP_POLICY
        );
        assert!(L1_WRAP_POLICY.witness.is_valid());
        assert!(WitnessMemoryPolicy::candidates()
            .all(|p| p.opening != WitnessOpeningStrategy::PackedCosetRecompute));
        assert_eq!(ProofMemoryPolicy::candidates().count(), 144);
    }
}
