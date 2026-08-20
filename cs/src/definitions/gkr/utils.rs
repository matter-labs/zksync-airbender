use super::*;
use field::PrimeField;

#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct NoFieldLinearRelation<F: PrimeField> {
    pub linear_terms: Box<[(F, GKRAddress)]>,
    pub constant: F,
}

impl<F: PrimeField> NoFieldLinearRelation<F> {
    pub fn is_trivial_single_input(&self) -> bool {
        self.linear_terms.len() == 1 && self.linear_terms[0].0 == F::ONE && self.constant == F::ZERO
    }
    pub fn from_single_input(input: GKRAddress) -> Self {
        Self {
            linear_terms: Box::new([(F::ONE, input)]),
            constant: F::ZERO,
        }
    }
}
