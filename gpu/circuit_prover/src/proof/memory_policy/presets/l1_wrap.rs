use super::super::{
    GkrMemoryPolicy, OpeningStrategy, PartialTreePolicy, ProofMemoryPolicy,
    WitnessCommitmentStrategy, WitnessMemoryPolicy, WitnessOpeningStrategy,
    WitnessPostCommitStorage,
};

pub const MEASURED_M4_PEAK_BYTES: usize = 25_937_575_936;
pub const OVERLAP_BYTES: usize = 1_736_441_856;

const ANALYTIC_COMMIT_PEAK_BYTES: usize = (104 + 10) * (1 << 21) * 16
    + (7 + 1 + 7) * (1 << 25) * 16
    + 2 * align_up(64 * ((1 << 14) - 1) * 32, 1 << 20)
    + 2 * 16 * (1 << 20);

pub const fn align_up(bytes: usize, unit: usize) -> usize {
    assert!(unit > 0, "L1Wrap arena alignment unit must be positive");
    let rounded = bytes
        .checked_add(unit - 1)
        .expect("L1Wrap arena alignment overflow");
    (rounded / unit)
        .checked_mul(unit)
        .expect("L1Wrap arena alignment overflow")
}

/// Analytic 2^21 bootstrap guard; capacity qualification supplies the measured floor.
pub const L1_WRAP_ARENA_MIN_BYTES: usize =
    align_up(ANALYTIC_COMMIT_PEAK_BYTES + OVERLAP_BYTES, 1 << 30);

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

pub const PARTIAL_TREES: PartialTreePolicy = PartialTreePolicy {
    setup: 10,
    memory: 10,
    ..PartialTreePolicy::DEFAULT
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
        const ROWS: usize = 1 << 21;
        const PACKED_ROWS: usize = 1 << 25;
        const COSETS: usize = 64;
        const RAW_BYTES: usize = (104 + 10) * ROWS * 16;
        const MONOMIAL_BYTES: usize = (7 + 1) * PACKED_ROWS * 16;
        const SCRATCH_BYTES: usize = 7 * PACKED_ROWS * 16;
        const RETAINED_BYTES: usize = 2 * COSETS * ((1 << 14) - 1) * 32;
        const ROOTS_TOP_CAP_BYTES: usize = 2 * (COSETS + (COSETS - 8) + 8) * 32;
        const OFFSET_BYTES: usize = 2 * COSETS * 16;
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
            11_945_383_936
        );
        assert_eq!(
            ANALYTIC_COMMIT_PEAK_BYTES,
            RAW_BYTES
                + MONOMIAL_BYTES
                + SCRATCH_BYTES
                + RETAINED_BYTES
                + RETAINED_BLOCK_ROUNDING
                + SMALL_POOL_BYTES
        );
        let layout: GKRCircuitArtifact<PR> = serde_json::from_str(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120_2p21.json"
        )))
        .unwrap();
        assert_eq!(layout.trace_len, ROWS);
        let memory_columns = layout.memory_layout.total_width + layout.witness_layout.total_width;
        let setup_columns = layout.generic_lookup_tables_width;
        assert_eq!(RAW_BYTES, (memory_columns + setup_columns) * ROWS * 16);
        assert_eq!(
            MONOMIAL_BYTES,
            (memory_columns.div_ceil(16) + setup_columns.div_ceil(16)) * PACKED_ROWS * 16
        );
        assert_eq!(
            SCRATCH_BYTES,
            memory_columns.div_ceil(16) * PACKED_ROWS * 16
        );
        let config = crate::upstream::ProofProfile::L1Wrap
            .prover_config(21, crate::upstream::SecurityLevel::Sec100);
        assert_eq!(config.lde_factor, COSETS);
        let log_leaves = (PACKED_ROWS / config.base_oracles_values_per_leaf).trailing_zeros();
        assert_eq!(PARTIAL_TREES.memory, 10);
        assert_eq!(PARTIAL_TREES.setup, 10);
        assert_eq!(
            RETAINED_BYTES,
            2 * COSETS
                * gpu_trace::trace::packed::retained_len(log_leaves, PARTIAL_TREES.memory)
                * 32
        );
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
            align_up(ANALYTIC_COMMIT_PEAK_BYTES + OVERLAP_BYTES, 1 << 30)
        );
        assert_eq!(L1_WRAP_ARENA_MIN_BYTES, 13 << 30);
        for arena in [21 << 30, 30 << 30] {
            assert_eq!(policy(arena), L1_WRAP_POLICY);
        }
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
