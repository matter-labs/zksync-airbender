use prover::cs::cs::oracle::Oracle;
use prover::field::PrimeField;

#[allow(dead_code)]
pub struct NullOracle;

impl<F: PrimeField> Oracle<F> for NullOracle {
    fn get_witness_from_placeholder(
        &self,
        _placeholder: prover::cs::cs::placeholder::Placeholder,
        _subindex: usize,
        _trace_row: usize,
    ) -> F {
        F::ZERO
    }

    fn get_u32_witness_from_placeholder(
        &self,
        _placeholder: prover::cs::cs::placeholder::Placeholder,
        _trace_row: usize,
    ) -> u32 {
        0
    }

    fn get_timestamp_witness_from_placeholder(
        &self,
        _placeholder: prover::cs::cs::placeholder::Placeholder,
        _trace_row: usize,
    ) -> prover::common_constants::TimestampScalar {
        0
    }
}
