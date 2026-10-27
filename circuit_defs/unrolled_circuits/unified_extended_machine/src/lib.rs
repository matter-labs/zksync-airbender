//! GKR wiring for the unified extended-machine circuit
//! (`cs::gkr_circuits::unified_extended_machine`: the reduced machine plus unsigned
//! `MUL`/`MULHU` and ROM-free sub-word loads/stores).
//!
//! Mirrors `unified_reduced_machine`: it exposes the compiled GKR artifact, the table driver
//! and the witness-eval fn so the `setups` crate can build a `CircuitSetup` for it. Unlike the
//! reduced machine the circuit has no bytecode-dependent (ROM) tables, so the table driver
//! takes no binary.

use cs::gkr_circuits::unified_extended_machine::*;
use prover::cs;
use prover::cs::tables::TableDriver;
use prover::cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;
use prover::field::baby_bear::base::BabyBearField;
use prover::field::PrimeField;
use prover::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
use prover::gkr::witness_gen::oracles::UnifiedRiscvCircuitOracle;

pub use common_constants::circuit_families::EXTENDED_MACHINE_CIRCUIT_FAMILY_IDX as FAMILY_IDX;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct UnifiedExtendedMachineCircuit;

impl<F: PrimeField> circuit_common::RiscVCycleCircuit<F, true> for UnifiedExtendedMachineCircuit {
    const CIRCUIT_FAMILY: u8 =
        common_constants::circuit_families::EXTENDED_MACHINE_CIRCUIT_FAMILY_IDX;
    const TRACE_LEN_LOG2: u32 = TRACE_LEN_LOG2;
    const NUM_INIT_AND_TEARDOWN_PAIRS: usize = 1;

    fn circuit_fn<CS: cs::cs::circuit_trait::Circuit<F>>(cs: &mut CS, _bytecode: &[u32]) {
        unified_extended_machine_circuit_with_preprocessed_bytecode_for_gkr(cs);
    }

    fn table_addition_fn<CS: cs::cs::circuit_trait::Circuit<F>>(cs: &mut CS, _bytecode: &[u32]) {
        unified_extended_machine_table_addition_fn(cs);
    }

    fn table_driver_fn(table_driver: &mut TableDriver<F>, _bytecode: &[u32]) {
        unified_extended_machine_table_driver_fn(table_driver);
    }
}

/// log2 of the trace length. The lookup tables of this circuit (decoder 2^20 plus the sub-word
/// memory tables) need the full 2^23 rows.
pub const TRACE_LEN_LOG2: u32 = 23;

/// Compile (or load from cache) the GKR circuit artifact; bytecode-independent.
pub fn get_circuit(use_caches: bool) -> cs::gkr_compiler::GKRCircuitArtifact<BabyBearField> {
    circuit_common::risc_v_with_mem_get_circuit::<BabyBearField, UnifiedExtendedMachineCircuit>(
        use_caches,
        &[],
    )
}

/// The table driver: base tables only (no bytecode-dependent content).
pub fn get_table_driver() -> TableDriver<BabyBearField> {
    let mut table_driver = TableDriver::new();
    <UnifiedExtendedMachineCircuit as circuit_common::RiscVCycleCircuit<BabyBearField, true>>::table_driver_fn(&mut table_driver, &[]);
    table_driver
}

mod sealed {
    use super::*;
    use prover::cs::oracle::Placeholder;
    use prover::cs::witness_placer::*;
    use prover::gkr::witness_gen::witness_proxy::*;

    include!("../generated/witness_generation_fn.rs");
}

/// Witness-eval fn specialized to the GKR `ColumnMajorWitnessProxy` /
/// `UnifiedRiscvCircuitOracle` over `BabyBearField`.
pub fn witness_eval_fn(
    proxy: &'_ mut ColumnMajorWitnessProxy<'_, UnifiedRiscvCircuitOracle<'_>, BabyBearField>,
) {
    let fn_ptr = sealed::evaluate_witness_fn::<
        ScalarWitnessTypeSet<BabyBearField, true>,
        ColumnMajorWitnessProxy<'_, UnifiedRiscvCircuitOracle<'_>, BabyBearField>,
    >;
    (fn_ptr)(proxy);
}

#[cfg(test)]
mod test {
    use test_utils::skip_if_ci;

    use super::*;

    #[test]
    fn generate() {
        skip_if_ci!();

        circuit_common::generate_default_risc_v_with_mem_cycles_artifacts::<
            UnifiedExtendedMachineCircuit,
        >(true);
    }
}
