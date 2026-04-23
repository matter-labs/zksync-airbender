use super::*;
use alloc::boxed::Box;

#[derive(
    Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
pub struct Degree2Constraint<F: PrimeField> {
    pub quadratic_terms: Box<[(F, Variable, Variable)]>,
    pub linear_terms: Box<[(F, Variable)]>,
    pub constant_term: F,
}

#[derive(
    Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
pub struct Degree1Constraint<F: PrimeField> {
    pub linear_terms: Box<[(F, Variable)]>,
    pub constant_term: F,
}
