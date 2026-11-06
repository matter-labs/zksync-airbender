use crate::cs::gkr_circuits::delegation::blake2_round_with_extended_control::*;
use crate::cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;
use prover::cs;
use prover::cs::tables::TableDriver;
use prover::field::baby_bear::base::BabyBearField;
use prover::field::PrimeField;
use prover::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
use prover::tracers::oracles::transpiler_oracles::delegation::*;
use prover::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Blake2sWithCompressionDelegationCircuit;

impl<F: PrimeField> circuit_common::DelegationCircuit<F>
    for Blake2sWithCompressionDelegationCircuit
{
    const DELEGATION_TYPE_ID: u16 =
        common_constants::delegation_types::blake2s_with_control::BLAKE2S_DELEGATION_CSR_REGISTER
            as u16;
    // the LOGICAL trace length for the purposes of GKR (rows of the circuit
    // trace); the polynomials WHIR commits may be larger when the base
    // commitment packs columns (`BASE_PACKING`)
    const TRACE_LEN_LOG2: u32 = 20;
    // packed by 2^2 columns into 2^22-variate committed polynomials, opened
    // with one value per packed column per base leaf (virtual packing)
    const BASE_PACKING: circuit_common::BasePacking =
        circuit_common::BasePacking::physical_and_virtual(2);

    fn circuit_fn<CS: cs::cs::circuit_trait::Circuit<F>>(cs: &mut CS) {
        define_blake2_with_extended_control_delegation_circuit(cs);
    }

    fn table_addition_fn<CS: cs::cs::circuit_trait::Circuit<F>>(cs: &mut CS) {
        blake2_with_extended_control_table_addition_fn(cs)
    }

    fn table_driver_fn(table_driver: &mut TableDriver<F>) {
        blake2_with_extended_control_table_driver_fn(table_driver);
    }
}

mod sealed {
    use super::*;

    use prover::cs::witness_placer::*;
    use prover::gkr::witness_gen::witness_proxy::*;

    include!("../generated/witness_generation_fn.rs");
}

pub fn witness_eval_fn(
    proxy: &'_ mut ColumnMajorWitnessProxy<'_, Blake2sDelegationOracle<'_>, BabyBearField>,
) {
    let fn_ptr = sealed::evaluate_witness_fn::<
        ScalarWitnessTypeSet<BabyBearField, true>,
        ColumnMajorWitnessProxy<'_, Blake2sDelegationOracle<'_>, BabyBearField>,
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
        circuit_common::generate_default_delegation_artifacts::<
            Blake2sWithCompressionDelegationCircuit,
        >(true);
    }
}
