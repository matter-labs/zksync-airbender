use super::*;
use crate::constraint::{Constraint, Term};
use crate::cs::circuit::*;
use crate::cs::witness_placer::*;
use crate::types::*;
use field::PrimeField;

#[track_caller]
pub fn mask_linear_term<F: PrimeField, C: Circuit<F>>(
    cs: &mut C,
    term: Term<F>,
    mask: Boolean,
) -> Variable {
    cs.add_variable_from_constraint(term * mask.get_terms())
}

#[track_caller]
pub fn collapse_max_quadratic_constraint_into<F: PrimeField, C: Circuit<F>>(
    cs: &mut C,
    constraint: Constraint<F>,
    result: Variable,
) {
    return collapse_max_quadratic_constraint_into_fixed(cs, constraint, result);
}

pub(crate) fn check_constants<F: PrimeField>(num1: &Num<F>, num2: &Num<F>) -> (bool, bool) {
    let first_is_constant = match num1 {
        Num::Constant(_) => true,
        _ => false,
    };

    let second_is_constant = match num2 {
        Num::Constant(_) => true,
        _ => false,
    };

    (first_is_constant, second_is_constant)
}

pub fn mask_by_boolean_into_accumulator_constraint<F: PrimeField>(
    boolean: &Boolean,
    variable: &Num<F>,
    accumulator: Constraint<F>,
) -> Constraint<F> {
    match (variable, boolean) {
        (&Num::Var(self_var), _) => {
            match boolean {
                &Boolean::Constant(flag) => {
                    if flag {
                        let constr = accumulator + Term::from(self_var);
                        constr
                    } else {
                        accumulator
                    }
                }
                &Boolean::Is(bit) => {
                    let constr = (Term::from(self_var) * Term::from(bit)) + accumulator;
                    constr
                }
                &Boolean::Not(not_bit) => {
                    // a - a*bit + accumulator
                    let constr =
                        Term::from(self_var) * (Term::from(1) - Term::from(not_bit)) + accumulator;
                    constr
                }
            }
        }
        (&Num::Constant(variable), &Boolean::Is(bit)) => {
            let constr = Term::from_field(variable) * Term::from(bit) + accumulator;
            constr
        }
        (&Num::Constant(constant), &Boolean::Not(bit)) => {
            let constr =
                Term::from_field(constant) * (Term::from(1) - Term::from(bit)) + accumulator;
            constr
        }
        (&Num::Constant(constant), &Boolean::Constant(bit)) => {
            if bit {
                let constr = accumulator + Term::from_field(constant);
                constr
            } else {
                accumulator
            }
        }
    }
}

pub fn mask_by_boolean_into_accumulator_constraint_with_shift<F: PrimeField>(
    boolean: &Boolean,
    variable: &Num<F>,
    accumulator: Constraint<F>,
    shift: F,
) -> Constraint<F> {
    match (variable, boolean) {
        (&Num::Var(self_var), _) => {
            match boolean {
                &Boolean::Constant(flag) => {
                    if flag {
                        let constr = accumulator + Term::from((shift, self_var));
                        constr
                    } else {
                        accumulator
                    }
                }
                &Boolean::Is(bit) => {
                    let constr = (Term::from((shift, self_var)) * Term::from(bit)) + accumulator;
                    constr
                }
                &Boolean::Not(not_bit) => {
                    // a - a*bit + accumulator
                    let constr = Term::from((shift, self_var))
                        * (Term::from(1) - Term::from(not_bit))
                        + accumulator;
                    constr
                }
            }
        }
        (&Num::Constant(constant), &Boolean::Is(bit)) => {
            let mut constant = constant;
            constant.mul_assign(&shift);
            let constr = Term::from_field(constant) * Term::from(bit) + accumulator;
            constr
        }
        (&Num::Constant(constant), &Boolean::Not(bit)) => {
            let mut constant = constant;
            constant.mul_assign(&shift);
            let constr =
                Term::from_field(constant) * (Term::from(1) - Term::from(bit)) + accumulator;
            constr
        }
        (&Num::Constant(constant), &Boolean::Constant(bit)) => {
            let mut constant = constant;
            constant.mul_assign(&shift);
            if bit {
                let constr = accumulator + Term::from_field(constant);
                constr
            } else {
                accumulator
            }
        }
    }
}

/// returns 0 if condition == `false` and `a` if condition == `true`
pub fn mask_into_constraint<F: PrimeField>(a: &Num<F>, condition: &Boolean) -> Constraint<F> {
    match (a, condition) {
        (&Num::Constant(a), &Boolean::Constant(flag)) => {
            if flag {
                Constraint::from_field(a)
            } else {
                Constraint::from(0)
            }
        }
        (&Num::Var(var), &Boolean::Constant(flag)) => {
            if flag {
                Constraint::from(var)
            } else {
                Constraint::from(0)
            }
        }
        (&Num::Var(var), &Boolean::Is(bit)) => {
            let cnstr: Constraint<F> = { Term::from(var) * Term::from(bit) };
            cnstr
        }
        (&Num::Var(var), &Boolean::Not(bit)) => {
            let cnstr: Constraint<F> = { Term::from(var) * (Term::from(1) - Term::from(bit)) };
            cnstr
        }
        (&Num::Constant(a), &Boolean::Is(bit)) => {
            let cnstr: Constraint<F> = { Term::from_field(a) * Term::from(bit) };
            cnstr
        }
        (&Num::Constant(a), &Boolean::Not(bit)) => {
            let cnstr: Constraint<F> = { Term::from_field(a) * (Term::from(1) - Term::from(bit)) };
            cnstr
        }
    }
}

pub fn mask_linear_term_into_constraint<F: PrimeField>(
    a: &Constraint<F>,
    condition: &Boolean,
) -> Constraint<F> {
    assert!(a.degree() <= 1);
    let result = if a.degree() == 0 {
        let constant_value = a.as_constant();
        let mut result = Constraint::<F>::from(condition.get_terms());
        result.scale(constant_value);

        result
    } else {
        let term = condition.get_terms();
        a.clone() * term
    };
    assert!(result.degree() <= 2);

    result
}

pub fn mask_linear_term_by_boolean_into_accumulator_constraint<F: PrimeField>(
    boolean: &Boolean,
    input: &Constraint<F>,
    accumulator: Constraint<F>,
) -> Constraint<F> {
    accumulator + (input.clone() * Constraint::from(*boolean))
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
        let (quatratic_terms, linear_terms, constant_term) =
            constraint.clone().split_max_quadratic();

        // split quadratic terms and linear terms into cases where coefficient is 1 or not
        let mut quadratic_trivial_additions = vec![];
        let mut quadratic_trivial_subtractions = vec![];
        let mut quadratic_nontrivial = vec![];
        for (c, a, b) in quatratic_terms.into_iter() {
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
