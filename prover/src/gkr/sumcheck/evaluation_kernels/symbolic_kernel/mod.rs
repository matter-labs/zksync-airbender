use super::*;

pub mod impls;
pub(crate) mod utils;

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
pub enum ChallengeType {
    PermutationDelinearization { index: usize },
    PermutationAdditivePart,
    LookupMultiplicativePart { power: usize },
    LookupAdditivePart,
}

impl ChallengeType {
    pub fn evaluate<F: PrimeField, E: FieldExtension<F> + Field>(
        &self,
        constants: &BatchedGKRTermDescriptionConstants<F, E>,
    ) -> E {
        match self {
            Self::LookupAdditivePart => constants.lookup_challenges_additive_part,
            Self::LookupMultiplicativePart { power } => constants
                .lookup_challenges_multiplicative_part
                .pow(*power as u32),
            Self::PermutationAdditivePart => {
                constants
                    .external_challenges
                    .permutation_argument_additive_part
            }
            Self::PermutationDelinearization { index } => {
                constants
                    .external_challenges
                    .permutation_argument_linearization_challenges[*index]
            }
        }
    }
}

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
pub struct SymbolicGKRCoefficient<F: PrimeField> {
    pub constant: F,
    pub challenge: Option<ChallengeType>,
}

impl<F: PrimeField> SymbolicGKRCoefficient<F> {
    pub fn one() -> Self {
        Self {
            constant: F::ONE,
            challenge: None,
        }
    }

    pub fn is_one(&self) -> bool {
        self.constant.is_one() && self.challenge.is_none()
    }

    pub fn from_base_field(constant: F) -> Self {
        Self {
            challenge: None,
            constant,
        }
    }

    pub fn is_in_base(&self) -> bool {
        self.challenge.is_none()
    }

    pub fn evaluate<E: FieldExtension<F> + Field>(
        &self,
        constants: &BatchedGKRTermDescriptionConstants<F, E>,
    ) -> E {
        match self.challenge {
            None => E::from_base(self.constant),
            Some(challenge) => {
                let mut t = challenge.evaluate(constants);
                t.mul_assign_by_base(&self.constant);

                t
            }
        }
    }
}

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
pub enum SymbolicGKRInput {
    BaseField(GKRAddress),
    ExtensionField(GKRAddress),
}

impl SymbolicGKRInput {
    pub fn raw_address(&self) -> GKRAddress {
        match self {
            Self::BaseField(inner) | Self::ExtensionField(inner) => *inner,
        }
    }
}

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
pub struct SymbolicGKRQuadraticTerm<F: PrimeField> {
    pub a: SymbolicGKRInput,
    pub b: SymbolicGKRInput,
    pub coefficient_0: SymbolicGKRCoefficient<F>,
    pub coefficient_1: SymbolicGKRCoefficient<F>,
}

impl<F: PrimeField> SymbolicGKRQuadraticTerm<F> {
    pub fn prefactor_is_in_base(&self) -> bool {
        self.coefficient_0.is_in_base() && self.coefficient_1.is_in_base()
    }
}

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
pub struct SymbolicGKRLinearTerm<F: PrimeField> {
    pub a: SymbolicGKRInput,
    pub coefficient_0: SymbolicGKRCoefficient<F>,
    pub coefficient_1: SymbolicGKRCoefficient<F>,
}

impl<F: PrimeField> SymbolicGKRLinearTerm<F> {
    pub fn prefactor_is_in_base(&self) -> bool {
        self.coefficient_0.is_in_base() && self.coefficient_1.is_in_base()
    }
}

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
pub struct SymbolicGKRConstantTerm<F: PrimeField> {
    pub coefficient_0: SymbolicGKRCoefficient<F>,
    pub coefficient_1: SymbolicGKRCoefficient<F>,
}

impl<F: PrimeField> SymbolicGKRConstantTerm<F> {
    pub fn is_in_base(&self) -> bool {
        self.coefficient_0.is_in_base() && self.coefficient_1.is_in_base()
    }
}

#[derive(Clone, Debug, Default)]
pub struct SymbolicGKRTermDescription<F: PrimeField> {
    pub quadratic_terms: Vec<SymbolicGKRQuadraticTerm<F>>, // no deduplication, next step transformations will take care of it
    pub linear_terms: Vec<SymbolicGKRLinearTerm<F>>, // no deduplication, next step transformations will take care of it
    pub constant_terms: Vec<SymbolicGKRConstantTerm<F>>,
    pub output: Option<SymbolicGKRInput>,
}

impl<F: PrimeField> SymbolicGKRTermDescription<F> {
    pub fn set_base_output(&mut self, output: GKRAddress) {
        assert!(self.output.is_none());
        self.output = Some(SymbolicGKRInput::BaseField(output));
    }

    pub fn set_extension_output(&mut self, output: GKRAddress) {
        assert!(self.output.is_none());
        self.output = Some(SymbolicGKRInput::ExtensionField(output));
    }

    pub fn add_simple_constant_term(&mut self, c: SymbolicGKRCoefficient<F>) {
        self.constant_terms.push(SymbolicGKRConstantTerm {
            coefficient_0: c,
            coefficient_1: SymbolicGKRCoefficient::one(),
        });
    }

    pub fn add_linear_terms(
        &mut self,
        a: (
            Vec<SymbolicGKRLinearTerm<F>>,
            Vec<SymbolicGKRCoefficient<F>>,
        ),
    ) {
        let (a_linear, a_constant) = a;
        self.linear_terms.extend(a_linear);
        for c in a_constant.into_iter() {
            self.add_simple_constant_term(c);
        }
    }

    pub fn add_product_of_linear_base_terms(
        &mut self,
        a: (
            Vec<SymbolicGKRLinearTerm<F>>,
            Vec<SymbolicGKRCoefficient<F>>,
        ),
        b: (
            Vec<SymbolicGKRLinearTerm<F>>,
            Vec<SymbolicGKRCoefficient<F>>,
        ),
    ) {
        let (a_linear, a_constant) = a;
        let (b_linear, b_constant) = b;

        for a in a_linear.iter().copied() {
            for b in b_linear.iter().copied() {
                assert!(a.coefficient_1.is_one());
                assert!(b.coefficient_1.is_one());

                if a.coefficient_0.is_one() {
                    self.quadratic_terms.push(SymbolicGKRQuadraticTerm {
                        a: a.a,
                        b: b.a,
                        coefficient_0: b.coefficient_0,
                        coefficient_1: SymbolicGKRCoefficient::one(),
                    });
                } else if b.coefficient_0.is_one() {
                    self.quadratic_terms.push(SymbolicGKRQuadraticTerm {
                        a: a.a,
                        b: b.a,
                        coefficient_0: a.coefficient_0,
                        coefficient_1: SymbolicGKRCoefficient::one(),
                    });
                } else {
                    self.quadratic_terms.push(SymbolicGKRQuadraticTerm {
                        a: a.a,
                        b: b.a,
                        coefficient_0: a.coefficient_0,
                        coefficient_1: b.coefficient_0,
                    });
                }
            }
        }

        for (linear, constant) in [
            (a_linear, b_constant.clone()),
            (b_linear, a_constant.clone()),
        ] {
            for a in linear.into_iter() {
                for c in constant.iter().copied() {
                    assert!(a.coefficient_1.is_one());
                    if a.coefficient_0.is_one() {
                        self.linear_terms.push(SymbolicGKRLinearTerm {
                            a: a.a,
                            coefficient_0: c,
                            coefficient_1: SymbolicGKRCoefficient::one(),
                        });
                    } else {
                        self.linear_terms.push(SymbolicGKRLinearTerm {
                            a: a.a,
                            coefficient_0: a.coefficient_0,
                            coefficient_1: c,
                        });
                    }
                }
            }
        }

        for a in a_constant.into_iter() {
            for b in b_constant.iter().copied() {
                if a.is_one() {
                    self.constant_terms.push(SymbolicGKRConstantTerm {
                        coefficient_0: b,
                        coefficient_1: SymbolicGKRCoefficient::one(),
                    });
                } else {
                    self.constant_terms.push(SymbolicGKRConstantTerm {
                        coefficient_0: a,
                        coefficient_1: b,
                    });
                }
            }
        }
    }
}

pub trait SameSizeSymbolicGKRKernel<F: PrimeField> {
    fn num_challenges(&self) -> usize {
        self.terms().len()
    }

    fn terms(&self) -> Vec<SymbolicGKRTermDescription<F>>;
}
