//! The unified reduced-machine circuit at trace length 2^22: the circuit of
//! every L1 feeder layer (`ProofProfile::L1Feeder`).
//!
//! Same definition, tables and witness-eval fn as the 2^23
//! `unified_reduced_machine` crate; only the compiled artifact
//! (`generated/layout.json`) differs, because the GKR compiler sizes the
//! lookup capacity and the inits-and-teardowns windows from the trace length.

use prover::cs;
use prover::cs::tables::TableDriver;
use prover::field::baby_bear::base::BabyBearField;
use prover::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
use prover::gkr::witness_gen::oracles::UnifiedRiscvCircuitOracle;

pub use common_constants::circuit_families::REDUCED_MACHINE_CIRCUIT_FAMILY_IDX as FAMILY_IDX;

pub const TRACE_LEN_LOG2: u32 = 22;

pub type UnifiedReducedMachineCircuit2_22 =
    ::unified_reduced_machine::UnifiedReducedMachineCircuit<TRACE_LEN_LOG2>;

pub const MAX_ROM_SIZE: usize = ::unified_reduced_machine::MAX_ROM_SIZE;
pub const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize =
    ::unified_reduced_machine::ROM_ADDRESS_SPACE_SECOND_WORD_BITS;

/// Compile the 2^22 unified GKR circuit artifact (bytecode-independent, like
/// the 2^23 sibling).
pub fn get_circuit(use_caches: bool) -> cs::gkr_compiler::GKRCircuitArtifact<BabyBearField> {
    circuit_common::risc_v_with_mem_get_circuit::<BabyBearField, UnifiedReducedMachineCircuit2_22>(
        use_caches,
        &[],
    )
}

/// The table driver is trace-independent: identical to the 2^23 sibling's.
pub fn get_table_driver(binary: &[u32]) -> TableDriver<BabyBearField> {
    ::unified_reduced_machine::get_table_driver(binary)
}

/// The witness-eval fn is trace-independent: identical to the 2^23 sibling's
/// (`test::witness_eval_fn_matches_sibling` regenerates it and checks).
pub fn witness_eval_fn(
    proxy: &'_ mut ColumnMajorWitnessProxy<'_, UnifiedRiscvCircuitOracle<'_>, BabyBearField>,
) {
    ::unified_reduced_machine::witness_eval_fn(proxy)
}

#[cfg(test)]
mod test {
    use circuit_common::RiscVCycleCircuit;
    use test_utils::skip_if_ci;

    use super::*;

    #[test]
    fn coexisting_unified_shapes() {
        assert_eq!(
            <UnifiedReducedMachineCircuit2_22 as RiscVCycleCircuit<BabyBearField, true>>::DOMAIN_SIZE_LOG2,
            22
        );
        assert_eq!(
            <::unified_reduced_machine::UnifiedReducedMachineCircuit as RiscVCycleCircuit<
                BabyBearField,
                true,
            >>::DOMAIN_SIZE_LOG2,
            23
        );
        assert_eq!(::unified_reduced_machine::TRACE_LEN_LOG2, 23);
        assert_eq!(TRACE_LEN_LOG2, 22);
        assert_eq!(
            <UnifiedReducedMachineCircuit2_22 as RiscVCycleCircuit<BabyBearField, true>>::NUM_INIT_AND_TEARDOWN_PAIRS,
            <::unified_reduced_machine::UnifiedReducedMachineCircuit as RiscVCycleCircuit<
                BabyBearField,
                true,
            >>::NUM_INIT_AND_TEARDOWN_PAIRS,
        );
        assert_eq!(
            <UnifiedReducedMachineCircuit2_22 as RiscVCycleCircuit<BabyBearField, true>>::CIRCUIT_FAMILY,
            FAMILY_IDX
        );
    }

    /// Both committed layouts describe their own trace length and differ
    /// only through it.
    #[test]
    fn committed_layouts_are_distinct_shapes() {
        let layout_2_22: cs::gkr_compiler::GKRCircuitArtifact<BabyBearField> =
            serde_json::from_str(include_str!("../generated/layout.json")).unwrap();
        let layout_2_23: cs::gkr_compiler::GKRCircuitArtifact<BabyBearField> =
            serde_json::from_str(include_str!(
                "../../unified_reduced_machine/generated/layout.json"
            ))
            .unwrap();
        assert_eq!(layout_2_22.trace_len, 1 << 22);
        assert_eq!(layout_2_23.trace_len, 1 << 23);
        assert_eq!(
            layout_2_22.memory_layout.teardown_sets.len(),
            layout_2_23.memory_layout.teardown_sets.len()
        );
        assert_ne!(layout_2_22, layout_2_23);
    }

    #[test]
    fn generate() {
        skip_if_ci!();

        circuit_common::generate_default_risc_v_with_mem_cycles_artifacts::<
            UnifiedReducedMachineCircuit2_22,
        >(true);
    }

    /// The SSA-derived witness-eval fn must equal the 2^23 sibling's, which
    /// this crate re-exports instead of carrying a copy.
    #[test]
    fn witness_eval_fn_matches_sibling() {
        skip_if_ci!();

        let ssa = circuit_common::risc_v_with_mem_get_ssa_form::<
            BabyBearField,
            UnifiedReducedMachineCircuit2_22,
        >(&[]);
        let compiled_circuit: cs::gkr_compiler::GKRCircuitArtifact<BabyBearField> =
            serde_json::from_str(include_str!("../generated/layout.json")).unwrap();
        let generated = witness_eval_generator::derive_from_ssa::derive_from_gkr_ssa(
            &ssa,
            &compiled_circuit,
            false,
            "BabyBearField",
        )
        .to_string();
        let sibling =
            include_str!("../../unified_reduced_machine/generated/witness_generation_fn.rs");
        assert!(
            generated == sibling,
            "the 2^22 witness-eval fn differs from the 2^23 sibling's: keep a crate-local copy"
        );
    }
}
