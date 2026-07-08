use super::*;
use field::PrimeField;

#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct NoFieldLinearRelation<F: PrimeField> {
    pub linear_terms: Box<[(F, GKRAddress)]>,
    pub constant: F,
}

impl<F: PrimeField> NoFieldLinearRelation<F> {
    pub fn is_trivial_single_input(&self) -> bool {
        self.linear_terms.len() == 1
            && self.linear_terms[0].0 == F::ONE
            && self.constant == F::ZERO
    }
    pub fn from_single_input(input: GKRAddress) -> Self {
        let mut linear_terms = Vec::with_capacity(1);
        linear_terms.push((F::ONE, input));
        Self {
            linear_terms: linear_terms.into_boxed_slice(),
            constant: F::ZERO,
        }
    }
}
