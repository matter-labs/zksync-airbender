#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

use crate::cs::gkr_circuits::binary_shifts_family::*;
use crate::cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;
use prover::cs;
use prover::cs::tables::TableDriver;
use prover::field::baby_bear::base::BabyBearField;
use prover::field::PrimeField;
use prover::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
use prover::gkr::witness_gen::oracles::NonMemoryCircuitOracle;
use prover::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct ShiftBinaryCircuit;

impl<F: PrimeField> circuit_common::RiscVCycleCircuit<F, false> for ShiftBinaryCircuit {
    const CIRCUIT_FAMILY: u8 = common_constants::circuit_families::SHIFT_BINARY_CIRCUIT_FAMILY_IDX;
    const DOMAIN_SIZE_LOG2: u32 = 24;

    fn circuit_fn<CS: cs::cs::circuit_trait::Circuit<F>>(cs: &mut CS, _bytecode: &[u32]) {
        shift_binop_circuit_with_preprocessed_bytecode_for_gkr(cs);
    }

    fn table_addition_fn<CS: cs::cs::circuit_trait::Circuit<F>>(cs: &mut CS, _bytecode: &[u32]) {
        shift_binop_table_addition_fn(cs)
    }

    fn table_driver_fn(table_driver: &mut TableDriver<F>, _bytecode: &[u32]) {
        shift_binop_table_driver_fn(table_driver);
    }
}

mod sealed {
    use super::*;
    use crate::cs::oracle::Placeholder;
    use prover::cs::witness_placer::*;
    use prover::gkr::witness_gen::witness_proxy::*;

    include!("../generated/witness_generation_fn.rs");
}

// pub fn witness_eval_fn<'a, 'b>(
//     proxy: &'_ mut ColumnMajorWitnessProxy<'a, NonMemoryCircuitOracle<'b>, BabyBearField>,
// ) {
//     let fn_ptr = sealed::evaluate_witness_fn::<
//         ScalarWitnessTypeSet<BabyBearField, true>,
//         ColumnMajorWitnessProxy<'a, NonMemoryCircuitOracle<'b>, BabyBearField>,
//     >;
//     (fn_ptr)(proxy);
// }

pub fn witness_eval_fn(
    proxy: &'_ mut ColumnMajorWitnessProxy<'_, NonMemoryCircuitOracle<'_>, BabyBearField>,
) {
    let fn_ptr = sealed::evaluate_witness_fn::<
        ScalarWitnessTypeSet<BabyBearField, true>,
        ColumnMajorWitnessProxy<'_, NonMemoryCircuitOracle<'_>, BabyBearField>,
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
        circuit_common::generate_default_risc_v_non_mem_cycles_artifacts::<ShiftBinaryCircuit>(
            true,
        );
    }
}
