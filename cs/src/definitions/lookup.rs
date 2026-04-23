use super::*;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LookupInput<F: PrimeField> {
    Variable(Variable),
    Expression {
        linear_terms: Vec<(F, Variable)>,
        constant_coeff: F,
    },
}
