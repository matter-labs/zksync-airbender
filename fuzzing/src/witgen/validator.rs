use prover::cs::constraint::Constraint;
use prover::field::PrimeField;

use crate::witgen::witness::Assignment;

pub fn check_constraints<F: PrimeField>(
    constraints: &[(Constraint<F>, bool)],
    assignments: &[Assignment<F>],
) -> bool {
    constraints
        .iter()
        .all(|(constraint, _)| check_constraint(constraint.clone(), assignments))
}

/// Checks that the given constraint is equal to 0 with each of the given assignments.
///
/// Based on `BasicAssembly::try_check_constraint`.
pub fn check_constraint<F: PrimeField>(
    constraint: Constraint<F>,
    assignments: &[Assignment<F>],
) -> bool {
    let (quad, linear, constant) = constraint.split_max_quadratic();

    assignments.iter().all(|assignment| {
        let mut value = constant;
        for (coeff, a, b) in &quad {
            let mut t = *coeff;
            let a = assignment[a];
            let b = assignment[b];
            t.mul_assign(&a);
            t.mul_assign(&b);

            value.add_assign(&t);
        }
        for (coeff, a) in &linear {
            let mut t = *coeff;
            let a = assignment[a];
            t.mul_assign(&a);

            value.add_assign(&t);
        }

        value == F::ZERO
    })
}
