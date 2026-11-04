use std::collections::BTreeSet;

use prover::cs::cs::circuit::CircuitOutput;
use prover::cs::definitions::Variable;
use prover::cs::one_row_compiler::optimize_out_linear_constraints;
use prover::field::PrimeField;

use crate::witgen::validator::check_constraints;
use crate::witgen::witness::Assignment;

pub(crate) struct LinearConstraintsCheck;

impl<F: PrimeField> super::Check<F> for LinearConstraintsCheck {
    fn check(
        &self,
        circuit_output: CircuitOutput<F>,
        assignments: &[Assignment<F>],
    ) -> Result<(), String> {
        let mut all_variables_to_place =
            BTreeSet::from_iter((0..circuit_output.num_of_variables as u64).map(Variable));
        let (eliminated_vars, new_constraints) = optimize_out_linear_constraints(
            &circuit_output.state_input,
            &circuit_output.state_output,
            &circuit_output.substitutions,
            circuit_output.constraints.clone(),
            &mut all_variables_to_place,
        );
        log::debug!("Eliminated {} variables", eliminated_vars.len());
        log::debug!(
            "Constraint count before: {}",
            circuit_output.constraints.len()
        );
        log::debug!("Constraint count after:  {}", new_constraints.len());

        // Check that the new constraints can be satisfied with the assignments.
        if !check_constraints(&new_constraints, assignments) {
            return Err(
                "Constraints after call to 'optimize_out_linear_constraints' failed".to_owned(),
            );
        }

        // TODO: If both constraint system pass with the assignments we then need to do the
        // check that ensures that they are equivalent.
        Ok(())
    }
}
