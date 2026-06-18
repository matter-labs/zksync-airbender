use super::*;

#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct NoFieldLinearRelation {
    pub linear_terms: Box<[(u32, GKRAddress)]>,
    pub constant: u32,
}

impl NoFieldLinearRelation {
    pub fn is_trivial_single_input(&self) -> bool {
        self.linear_terms.len() == 1 && self.linear_terms[0].0 == 1 && self.constant == 0
    }
    pub fn from_single_input(input: GKRAddress) -> Self {
        let mut linear_terms = Vec::with_capacity(1);
        linear_terms.push((1, input));
        Self {
            linear_terms: linear_terms.into_boxed_slice(),
            constant: 0,
        }
    }
}
