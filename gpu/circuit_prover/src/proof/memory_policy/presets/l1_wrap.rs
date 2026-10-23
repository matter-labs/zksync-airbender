use super::super::{
    GkrMemoryPolicy, OpeningStrategy, PartialTreePolicy, ProofMemoryPolicy,
    WitnessCommitmentStrategy, WitnessMemoryPolicy, WitnessOpeningStrategy,
    WitnessPostCommitStorage,
};

/// Historical tracker peak for the 104-column 2^21 wrap at pack 3 / 128 cosets and the preset's
/// depth-10 trees (`tests/l1_stage_parity.rs` `l1_wrap_m4_stages_match_reference`)
/// on the RTX PRO 6000 Blackwell (sm_120).
pub const MEASURED_M4_PEAK_BYTES: usize = 11_517_558_784;
pub const OVERLAP_BYTES: usize = 1_736_441_856;

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

/// Smallest sufficient arena of the bounded capacity matrix (`gpu/execution_prover/tests/l1_memory.rs`: 21/30 GiB candidates, both directions, three opposite followers, proof equal to the 2^21 reference) on the RTX PRO 6000 Blackwell (sm_120).
pub const L1_WRAP_WHOLE_PROOF_FLOOR_BYTES: usize = 21 << 30;
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

    /// The 104-column calibration model, without per-commit tree scratch.
    /// The current layout model must fit under this historical calibration.
    const HISTORICAL_ANALYTIC_COMMIT_PEAK_BYTES: usize = (104 + 10) * (1 << 21) * 16
        + (13 + 2 + 13) * (1 << 24) * 16
        + 2 * align_up(128 * ((1 << 14) - 1) * 32, 1 << 20)
        + 2 * 16 * (1 << 20);

    #[test]
    fn cpu_l1_wrap_preset_components() {
        const BLOCK_BYTES: usize = 1 << 20;
        let layout: GKRCircuitArtifact<PR> = serde_json::from_str(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120_2p21.json"
        )))
        .unwrap();
        let rows = layout.trace_len;
        assert_eq!(rows, 1 << 21);
        let config = crate::upstream::ProofProfile::L1Wrap.prover_config(
            rows.trailing_zeros() as usize,
            crate::upstream::SecurityLevel::Sec100,
        );
        let packed_rows = 1 << config.whir_message_size_log2();
        let cosets = config.lde_factor;
        assert_eq!(cosets, 128);
        let memory_columns = layout.memory_layout.total_width + layout.witness_layout.total_width;
        let setup_columns = layout.generic_lookup_tables_width;
        let packed_memory_columns = memory_columns.div_ceil(1 << config.pack_log2);
        let packed_setup_columns = setup_columns.div_ceil(1 << config.pack_log2);
        let field_bytes = std::mem::size_of::<PR>();
        let raw_bytes = (memory_columns + setup_columns) * rows * field_bytes;
        let monomial_bytes =
            (packed_memory_columns + packed_setup_columns) * packed_rows * field_bytes;
        let scratch_bytes = packed_memory_columns * packed_rows * field_bytes;
        let log_leaves = (packed_rows / config.base_oracles_values_per_leaf).trailing_zeros();
        assert_eq!(PARTIAL_TREES.memory, 10);
        assert_eq!(PARTIAL_TREES.setup, 10);
        let retained_bytes = 2
            * cosets
            * gpu_trace::trace::packed::retained_len(log_leaves, PARTIAL_TREES.memory)
            * 32;
        let retained_block_rounding =
            2 * align_up(retained_bytes / 2, BLOCK_BYTES) - retained_bytes;
        let small_pool_bytes = 2 * 16 * BLOCK_BYTES;
        let current_analytic_commit_peak = raw_bytes
            + monomial_bytes
            + scratch_bytes
            + retained_bytes
            + retained_block_rounding
            + small_pool_bytes;
        assert!(
            HISTORICAL_ANALYTIC_COMMIT_PEAK_BYTES >= current_analytic_commit_peak,
            "current layout exceeds the historical M4 calibration"
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
            layout.scratch_space_size * rows * std::mem::size_of::<PR>()
                + mapping_columns * rows * std::mem::size_of::<u32>()
                + rows * std::mem::size_of::<UnifiedOpcodeTracingDataWithTimestamp>()
        );
        let tree_scratch_bytes = gpu_hash::keccak256::partial_coset_tree_scratch_len(
            packed_rows.trailing_zeros(),
            config.base_oracles_values_per_leaf.trailing_zeros(),
            PARTIAL_TREES.memory,
        ) * 32;
        assert_eq!(tree_scratch_bytes, 8 * BLOCK_BYTES);
        assert_eq!(
            MEASURED_M4_PEAK_BYTES,
            HISTORICAL_ANALYTIC_COMMIT_PEAK_BYTES + tree_scratch_bytes
        );
        assert_eq!(
            L1_WRAP_ARENA_MIN_BYTES,
            align_up(MEASURED_M4_PEAK_BYTES + OVERLAP_BYTES, 1 << 30)
        );
        assert_eq!(L1_WRAP_ARENA_MIN_BYTES, 13 << 30);
        assert_eq!(L1_WRAP_WHOLE_PROOF_FLOOR_BYTES, 21 << 30);
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
                CircuitType::L1Wrap21,
                crate::upstream::ProofProfile::L1Wrap,
                80 << 30
            ),
            L1_WRAP_POLICY
        );
        assert_eq!(
            super::super::policy(
                CircuitType::L1Wrap21,
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
