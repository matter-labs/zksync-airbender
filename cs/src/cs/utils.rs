use super::*;
use crate::constraint::{Constraint, Term};
use crate::cs::circuit_trait::*;
use crate::structured_expr::Expr;
use crate::types::*;
use crate::witness_placer::*;
use field::PrimeField;

#[track_caller]
pub fn mask_linear_term<F: PrimeField, C: Circuit<F>>(
    cs: &mut C,
    term: Term<F>,
    mask: Boolean,
) -> Variable {
    let expr = mask_linear_term_into_expr(&Constraint::from(term), &mask);
    add_variable_from_max_quadratic_expr(cs, expr)
}

#[track_caller]
fn add_variable_from_max_quadratic_expr<F: PrimeField, C: Circuit<F>>(
    cs: &mut C,
    expr: Expr<F>,
) -> Variable {
    match expr.degree() {
        0 => panic!("masked expression must contain at least one variable"),
        1 => cs.add_variable_from_expr_allow_explicit_linear(expr),
        2 => cs.add_variable_from_expr(expr),
        degree => panic!("masked expression degree {degree} exceeds max-quadratic lowering"),
    }
}

#[track_caller]
pub fn collapse_max_quadratic_constraint_into<F: PrimeField, C: Circuit<F>>(
    cs: &mut C,
    constraint: Constraint<F>,
    result: Variable,
) {
    return collapse_max_quadratic_constraint_into_fixed(cs, constraint, result);
}

/// Assigns a preallocated result variable from an expression.
///
/// Delegation circuits often get output variables from register or memory
/// access plumbing before the expression for that output is known. This helper
/// keeps witness assignment on the expression path, while callers can record
/// the structured definition separately with `define_variable_from_expr`.
#[track_caller]
pub fn collapse_max_quadratic_expr_into<F: PrimeField, C: Circuit<F>>(
    cs: &mut C,
    expr: Expr<F>,
    result: Variable,
) {
    let constraint = expr.to_max_quadratic_constraint();
    collapse_max_quadratic_constraint_into_fixed(cs, constraint, result);
}

pub fn mask_by_boolean_into_accumulator_constraint<F: PrimeField>(
    boolean: &Boolean,
    variable: &Num<F>,
    accumulator: Constraint<F>,
) -> Constraint<F> {
    mask_by_boolean_into_accumulator_expr(boolean, variable, Expr::from(accumulator))
        .to_max_quadratic_constraint()
}

pub fn mask_by_boolean_into_accumulator_expr<F: PrimeField>(
    boolean: &Boolean,
    variable: &Num<F>,
    accumulator: Expr<F>,
) -> Expr<F> {
    accumulator + mask_into_expr(variable, boolean)
}

pub fn mask_by_boolean_into_accumulator_constraint_with_shift<F: PrimeField>(
    boolean: &Boolean,
    variable: &Num<F>,
    accumulator: Constraint<F>,
    shift: F,
) -> Constraint<F> {
    mask_by_boolean_into_accumulator_expr_with_shift(
        boolean,
        variable,
        Expr::from(accumulator),
        shift,
    )
    .to_max_quadratic_constraint()
}

pub fn mask_by_boolean_into_accumulator_expr_with_shift<F: PrimeField>(
    boolean: &Boolean,
    variable: &Num<F>,
    accumulator: Expr<F>,
    shift: F,
) -> Expr<F> {
    accumulator + mask_into_expr(variable, boolean) * shift
}

/// returns 0 if condition == `false` and `a` if condition == `true`
pub fn mask_into_constraint<F: PrimeField>(a: &Num<F>, condition: &Boolean) -> Constraint<F> {
    mask_into_expr(a, condition).to_max_quadratic_constraint()
}

/// returns 0 if condition == `false` and `a` if condition == `true`
pub fn mask_into_expr<F: PrimeField>(a: &Num<F>, condition: &Boolean) -> Expr<F> {
    Expr::from(*a) * Expr::from(*condition)
}

pub fn mask_linear_term_into_constraint<F: PrimeField>(
    a: &Constraint<F>,
    condition: &Boolean,
) -> Constraint<F> {
    mask_linear_term_into_expr(a, condition).to_max_quadratic_constraint()
}

pub fn mask_linear_term_into_expr<F: PrimeField>(
    a: &Constraint<F>,
    condition: &Boolean,
) -> Expr<F> {
    assert!(a.degree() <= 1);
    let result = Expr::from(a.clone()) * Expr::from(*condition);
    assert!(result.degree() <= 2);

    result
}

pub fn mask_linear_term_by_boolean_into_accumulator_constraint<F: PrimeField>(
    boolean: &Boolean,
    input: &Constraint<F>,
    accumulator: Constraint<F>,
) -> Constraint<F> {
    mask_linear_term_by_boolean_into_accumulator_expr(boolean, input, Expr::from(accumulator))
        .to_max_quadratic_constraint()
}

pub fn mask_linear_term_by_boolean_into_accumulator_expr<F: PrimeField>(
    boolean: &Boolean,
    input: &Constraint<F>,
    accumulator: Expr<F>,
) -> Expr<F> {
    assert!(input.degree() <= 1);
    accumulator + Expr::from(input.clone()) * Expr::from(*boolean)
}

#[derive(Clone, Debug)]
pub struct PreprocessedConstraintForEval<F: PrimeField> {
    quadratic_trivial_additions: Vec<(Variable, Variable)>,
    quadratic_trivial_subtractions: Vec<(Variable, Variable)>,
    quadratic_nontrivial: Vec<(F, Variable, Variable)>,
    linear_trivial_additions: Vec<Variable>,
    linear_trivial_subtractions: Vec<Variable>,
    linear_nontrivial: Vec<(F, Variable)>,
    constant_term: F,
}

impl<F: PrimeField> PreprocessedConstraintForEval<F> {
    pub fn from_constraint(constraint: Constraint<F>) -> Self {
        let (quadratic_terms, linear_terms, constant_term) =
            constraint.clone().split_max_quadratic();

        // split quadratic terms and linear terms into cases where coefficient is 1 or not
        let mut quadratic_trivial_additions = vec![];
        let mut quadratic_trivial_subtractions = vec![];
        let mut quadratic_nontrivial = vec![];
        for (c, a, b) in quadratic_terms.into_iter() {
            assert!(c != F::ZERO);
            if c == F::ONE {
                quadratic_trivial_additions.push((a, b));
            } else if c == F::MINUS_ONE {
                quadratic_trivial_subtractions.push((a, b));
            } else {
                quadratic_nontrivial.push((c, a, b));
            }
        }

        let mut linear_trivial_additions = vec![];
        let mut linear_trivial_subtractions = vec![];
        let mut linear_nontrivial = vec![];
        for (c, a) in linear_terms.into_iter() {
            assert!(c != F::ZERO);
            if c == F::ONE {
                linear_trivial_additions.push(a);
            } else if c == F::MINUS_ONE {
                linear_trivial_subtractions.push(a);
            } else {
                linear_nontrivial.push((c, a));
            }
        }

        Self {
            quadratic_trivial_additions,
            quadratic_trivial_subtractions,
            quadratic_nontrivial,
            linear_trivial_additions,
            linear_trivial_subtractions,
            linear_nontrivial,
            constant_term,
        }
    }

    pub fn evaluate_with_placer<W: WitnessPlacer<F>>(&self, placer: &mut W) -> W::Field {
        let mut value = <W as WitnessTypeSet<F>>::Field::constant(self.constant_term);

        for (a, b) in self.quadratic_trivial_additions.iter() {
            let a = placer.get_field(*a);
            let b = placer.get_field(*b);
            value.add_assign_product(&a, &b);
        }

        for (a, b) in self.quadratic_trivial_subtractions.iter() {
            let mut a = placer.get_field(*a);
            let b = placer.get_field(*b);
            a.mul_assign(&b);
            value.sub_assign(&a);
        }

        for (constant, a, b) in self.quadratic_nontrivial.iter() {
            let constant = <W as WitnessTypeSet<F>>::Field::constant(*constant);
            let mut a = placer.get_field(*a);
            let b = placer.get_field(*b);
            a.mul_assign(&constant);
            value.add_assign_product(&a, &b);
        }

        for a in self.linear_trivial_additions.iter() {
            let a = placer.get_field(*a);
            value.add_assign(&a);
        }

        for a in self.linear_trivial_subtractions.iter() {
            let a = placer.get_field(*a);
            value.sub_assign(&a);
        }

        for (constant, a) in self.linear_nontrivial.iter() {
            let constant = <W as WitnessTypeSet<F>>::Field::constant(*constant);
            let a = placer.get_field(*a);
            value.add_assign_product(&constant, &a);
        }

        value
    }
}

#[track_caller]
fn collapse_max_quadratic_constraint_into_fixed<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
    constraint: Constraint<F>,
    result: Variable,
) {
    let preprocessed_constraint = PreprocessedConstraintForEval::from_constraint(constraint);

    let value_fn = move |placer: &mut CS::WitnessPlacer| {
        let value = preprocessed_constraint.evaluate_with_placer(placer);

        placer.assign_field(result, &value);
    };

    cs.set_values(value_fn);
}
