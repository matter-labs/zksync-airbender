use super::*;
use alloc::boxed::Box;

#[derive(Clone, Copy, Hash, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct VerifierCompiledDegree1Constraint<'a, F: PrimeField> {
    pub linear_terms: &'a [(F, ColumnAddress)],
    pub constant_term: F,
}

#[derive(Clone, Copy, Hash, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct VerifierCompiledDegree2Constraint<'a, F: PrimeField> {
    pub quadratic_terms: &'a [(F, ColumnAddress, ColumnAddress)],
    pub linear_terms: &'a [(F, ColumnAddress)],
    pub constant_term: F,
}

pub type StaticVerifierCompiledDegree1Constraint<F: PrimeField> =
    VerifierCompiledDegree1Constraint<'static, F>;
pub type StaticVerifierCompiledDegree2Constraint<F: PrimeField> =
    VerifierCompiledDegree2Constraint<'static, F>;

#[derive(Clone, Copy, Hash, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum BoundaryConstraintLocation {
    FirstRow,
    LastRow,
    OneBeforeLastRow,
}

#[derive(
    Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
pub struct CompiledDegree2Constraint<F: PrimeField> {
    pub quadratic_terms: Box<[(F, ColumnAddress, ColumnAddress)]>,
    pub linear_terms: Box<[(F, ColumnAddress)]>,
    pub constant_term: F,
}

impl<F: PrimeField> CompiledDegree2Constraint<F> {
    pub fn as_compiled<'a>(&'a self) -> VerifierCompiledDegree2Constraint<'a, F> {
        VerifierCompiledDegree2Constraint {
            quadratic_terms: &self.quadratic_terms,
            linear_terms: &self.linear_terms,
            constant_term: self.constant_term,
        }
    }

    pub fn is_boolean_constraint(&self) -> bool {
        if self.linear_terms.len() != 1 {
            return false;
        };
        let var = self.linear_terms[0].1;

        self.constant_term.is_zero()
            && &*self.linear_terms == &[(F::MINUS_ONE, var)]
            && &*self.quadratic_terms == &[(F::ONE, var, var)]
    }

    pub fn normalize(&mut self) {
        for (_, a, b) in self.quadratic_terms.iter_mut() {
            if *a > *b {
                core::mem::swap(a, b);
            }
        }

        self.quadratic_terms
            .sort_by(|a, b| (a.1, a.2).cmp(&(b.1, b.2)));

        self.linear_terms.sort_by(|a, b| (a.1).cmp(&(b.1)));
    }
}

#[derive(
    Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
pub struct CompiledDegree1Constraint<F: PrimeField> {
    pub linear_terms: Box<[(F, ColumnAddress)]>,
    pub constant_term: F,
}

impl<F: PrimeField> CompiledDegree1Constraint<F> {
    pub fn as_compiled<'a>(&'a self) -> VerifierCompiledDegree1Constraint<'a, F> {
        VerifierCompiledDegree1Constraint {
            linear_terms: &self.linear_terms,
            constant_term: self.constant_term,
        }
    }

    pub fn normalize(&mut self) {
        self.linear_terms.sort_by(|a, b| (a.1).cmp(&(b.1)));
    }
}
