//! Checks made by the fuzzer to ensure correctness.

use clap::ValueEnum;
use prover::cs::cs::circuit::CircuitOutput;
use prover::field::PrimeField;

use crate::witgen::witness::Assignment;

mod linear_constraints;

#[derive(ValueEnum, Clone, Copy, PartialEq, Eq)]
pub enum Checks {
    /// Checks correctness of the [`optimize_out_linear_constraints`] function.
    LinearConstraints,
}

impl Checks {
    pub(crate) fn instantiate<F: PrimeField>(&self) -> Box<dyn Check<F>> {
        match self {
            Checks::LinearConstraints => Box::new(linear_constraints::LinearConstraintsCheck),
        }
    }
}

pub(crate) trait Check<F: PrimeField> {
    /// Performs the check on the given set of assignments that satisfy the given circuit
    /// constraints.
    fn check(
        &self,
        circuit_output: CircuitOutput<F>,
        assignments: &[Assignment<F>],
    ) -> Result<(), String>;
}
