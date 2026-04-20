#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

use crate::cs::gkr_circuits::mem_subword_only::*;
use crate::cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;
use prover::cs;
use prover::cs::tables::TableDriver;
use prover::field::baby_bear::base::BabyBearField;
use prover::field::PrimeField;
use prover::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
use prover::gkr::witness_gen::oracles::MemoryCircuitOracle;
use prover::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct LoadStoreSubwordOnlyCircuit;

impl<F: PrimeField> circuit_common::RiscVCycleCircuit<F, true> for LoadStoreSubwordOnlyCircuit {
    const CIRCUIT_FAMILY: u8 =
        common_constants::circuit_families::LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX;
    const DOMAIN_SIZE_LOG2: u32 = 24;

    fn circuit_fn<CS: cs::cs::circuit_trait::Circuit<F>>(cs: &mut CS, _bytecode: &[u32]) {
        mem_subword_only_circuit_with_preprocessed_bytecode_for_gkr(cs);
    }

    fn table_addition_fn<CS: cs::cs::circuit_trait::Circuit<F>>(cs: &mut CS, bytecode: &[u32]) {
        mem_subword_only_table_addition_fn(cs);
        // ROM tables must be added here (with dummy bytecode) so that
        // offset_for_decoder_table in the compiled JSON reflects the correct
        // total_tables_len at prove time, when real ROM tables are present.
        for (table_type, table) in create_mem_subword_only_special_tables::<
            F,
            { common_constants::ROM_SECOND_WORD_BITS },
        >(bytecode)
        {
            cs.add_table_with_content(table_type, table);
        }
    }

    fn table_driver_fn(table_driver: &mut TableDriver<F>, bytecode: &[u32]) {
        mem_subword_only_table_driver_fn(table_driver);
        // ROM tables must be added here (with dummy bytecode) so that
        // offset_for_decoder_table in the compiled JSON reflects the correct
        // total_tables_len at prove time, when real ROM tables are present.
        for (table_type, table) in create_mem_subword_only_special_tables::<
            F,
            { common_constants::ROM_SECOND_WORD_BITS },
        >(bytecode)
        {
            table_driver.add_table_with_content(table_type, table);
        }
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
//     proxy: &'_ mut ColumnMajorWitnessProxy<'a, MemoryCircuitOracle<'b>, BabyBearField>,
// ) {
//     let fn_ptr = sealed::evaluate_witness_fn::<
//         ScalarWitnessTypeSet<BabyBearField, true>,
//         ColumnMajorWitnessProxy<'a, MemoryCircuitOracle<'b>, BabyBearField>,
//     >;
//     (fn_ptr)(proxy);
// }

pub fn witness_eval_fn(
    proxy: &'_ mut ColumnMajorWitnessProxy<'_, MemoryCircuitOracle<'_>, BabyBearField>,
) {
    let fn_ptr = sealed::evaluate_witness_fn::<
        ScalarWitnessTypeSet<BabyBearField, true>,
        ColumnMajorWitnessProxy<'_, MemoryCircuitOracle<'_>, BabyBearField>,
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
            LoadStoreSubwordOnlyCircuit,
        >(true);
    }
}
