#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

use crate::cs::gkr_circuits::delegation::keccak_special5::*;
use crate::cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;
use prover::cs;
use prover::cs::tables::TableDriver;
use prover::field::baby_bear::base::BabyBearField;
use prover::field::PrimeField;
use prover::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
use prover::tracers::oracles::transpiler_oracles::delegation::*;
use prover::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct KeccakSpecial5DelegationCircuit;

impl<F: PrimeField> circuit_common::DelegationCircuit<F> for KeccakSpecial5DelegationCircuit {
    const DELEGATION_TYPE_ID: u16 =
        common_constants::delegation_types::keccak_special5::KECCAK_SPECIAL5_CSR_REGISTER as u16;
    const DOMAIN_SIZE_LOG2: u32 = 22;

    fn circuit_fn<CS: cs::cs::circuit_trait::Circuit<F>>(cs: &mut CS) {
        define_keccak_special5_delegation_circuit::<_, _, false>(cs);
    }

    fn table_addition_fn<CS: cs::cs::circuit_trait::Circuit<F>>(cs: &mut CS) {
        keccak_special5_delegation_circuit_table_addition_fn(cs)
    }

    fn table_driver_fn(table_driver: &mut TableDriver<F>) {
        keccak_special5_delegation_circuit_table_driver_fn(table_driver);
    }
}

mod sealed {
    use super::*;
    use prover::cs::witness_placer::*;
    use prover::gkr::witness_gen::witness_proxy::*;

    include!("../generated/witness_generation_fn.rs");
}

pub fn witness_eval_fn<'a, 'b>(
    proxy: &'_ mut ColumnMajorWitnessProxy<'a, KeccakDelegationOracle<'b>, BabyBearField>,
) {
    let fn_ptr = sealed::evaluate_witness_fn::<
        ScalarWitnessTypeSet<BabyBearField, true>,
        ColumnMajorWitnessProxy<'a, KeccakDelegationOracle<'b>, BabyBearField>,
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
        circuit_common::generate_default_delegation_artifacts::<KeccakSpecial5DelegationCircuit>(
            true,
        );
    }
}
