use crate::constraint::{Constraint, Term};
use crate::definitions::{TableType, Variable};
use crate::types::{Boolean, Num};
use field::PrimeField;

/// Source-level arithmetic expression metadata for constraints.
///
/// `Constraint` intentionally stores a flattened sparse polynomial, so it is
/// useful for today's max-quadratic compiler path but cannot preserve authored
/// grouping such as `a * (b + c)`. `Expr` keeps that grouping around as metadata
/// while still being able to lower into the existing flat representation.
#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum Expr<F: PrimeField> {
    Constant(F),
    Var(Variable),
    Sum(Vec<Expr<F>>),
    Product(Vec<Expr<F>>),
}

/// Statement-level meaning for a structured expression.
///
/// The expression tree only describes arithmetic. The statement records whether
/// that arithmetic was an assertion or a directed variable definition.
#[derive(Clone, Debug, Hash, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum StructuredStatement<F: PrimeField> {
    AssertZero {
        expr: Expr<F>,
        compiled_constraint: Constraint<F>,
        prevent_optimizations: bool,
    },
    Define {
        dst: Variable,
        compiled_constraint: Constraint<F>,
        expr: Expr<F>,
        output_layer: usize,
    },
}

impl<F: PrimeField> Expr<F> {
    pub fn constant(value: F) -> Self {
        Self::Constant(value)
    }

    pub fn var(variable: Variable) -> Self {
        Self::Var(variable)
    }

    pub fn zero() -> Self {
        Self::Constant(F::ZERO)
    }

    pub fn one() -> Self {
        Self::Constant(F::ONE)
    }

    /// Builds a sum while dropping additive identity terms and flattening nested sums.
    pub fn sum(terms: Vec<Self>) -> Self {
        let mut normalized_terms = Vec::with_capacity(terms.len());
        let mut constant = F::ZERO;
        let mut constant_index = None;
        for term in terms {
            Self::push_sum_term(
                &mut normalized_terms,
                &mut constant,
                &mut constant_index,
                term,
            );
        }

        if constant != F::ZERO {
            let constant_index = constant_index.expect("sum constant must have an insertion index");
            normalized_terms.insert(constant_index, Self::Constant(constant));
        }

        match normalized_terms.len() {
            0 => Self::zero(),
            1 => normalized_terms.pop().expect("single sum term must exist"),
            _ => Self::Sum(normalized_terms),
        }
    }

    /// Builds a product while dropping multiplicative identity factors and flattening nested products.
    pub fn product(factors: Vec<Self>) -> Self {
        let mut normalized_factors = Vec::with_capacity(factors.len());
        let mut constant = F::ONE;
        let mut constant_index = None;
        for factor in factors {
            if Self::push_product_factor(
                &mut normalized_factors,
                &mut constant,
                &mut constant_index,
                factor,
            ) {
                // A single zero factor makes the whole product zero, so any
                // structure accumulated from the other factors is irrelevant.
                return Self::zero();
            }
        }

        if constant != F::ONE {
            let constant_index =
                constant_index.expect("product constant must have an insertion index");
            normalized_factors.insert(constant_index, Self::Constant(constant));
        }

        match normalized_factors.len() {
            0 => Self::one(),
            1 => normalized_factors
                .pop()
                .expect("single product factor must exist"),
            _ => Self::Product(normalized_factors),
        }
    }

    fn push_sum_term(
        terms: &mut Vec<Self>,
        constant: &mut F,
        constant_index: &mut Option<usize>,
        term: Self,
    ) {
        match term {
            Self::Constant(value) if value == F::ZERO => {}
            Self::Constant(value) => {
                constant_index.get_or_insert(terms.len());
                constant.add_assign(&value);
            }
            Self::Sum(nested_terms) => {
                for nested_term in nested_terms {
                    Self::push_sum_term(terms, constant, constant_index, nested_term);
                }
            }
            term => terms.push(term),
        }
    }

    /// Pushes a product factor into the normalized accumulator.
    ///
    /// Returns `true` when the factor tree contains zero, which means the caller
    /// can replace the whole product by zero.
    fn push_product_factor(
        factors: &mut Vec<Self>,
        constant: &mut F,
        constant_index: &mut Option<usize>,
        factor: Self,
    ) -> bool {
        match factor {
            Self::Constant(value) if value == F::ZERO => true,
            Self::Constant(value) if value == F::ONE => false,
            Self::Constant(value) => {
                constant_index.get_or_insert(factors.len());
                constant.mul_assign(&value);
                false
            }
            Self::Product(nested_factors) => {
                for nested_factor in nested_factors {
                    if Self::push_product_factor(factors, constant, constant_index, nested_factor) {
                        return true;
                    }
                }
                false
            }
            factor => {
                factors.push(factor);
                false
            }
        }
    }

    pub fn mask(self, flag: Boolean) -> Self {
        self * Self::from(flag)
    }

    pub fn degree(&self) -> usize {
        match self {
            Self::Constant(_) => 0,
            Self::Var(_) => 1,
            Self::Sum(terms) => terms.iter().map(Self::degree).max().unwrap_or(0),
            Self::Product(factors) => factors.iter().map(Self::degree).sum(),
        }
    }

    #[track_caller]
    pub fn validate_degree_at_most(&self, max_degree: usize) {
        let degree = self.degree();
        assert!(
            degree <= max_degree,
            "structured expression degree {degree} exceeds supported degree {max_degree}"
        );
    }

    /// Applies the minimal normalization we currently want for metadata.
    ///
    /// This intentionally only removes neutral elements, folds constants within
    /// the same associative node, flattens same-kind associative nodes, and
    /// collapses empty or single-item nodes. It does not sort terms or distribute
    /// multiplication over addition.
    pub fn canonicalize(self) -> Self {
        match self {
            Self::Sum(terms) => Self::sum(terms.into_iter().map(Self::canonicalize).collect()),
            Self::Product(factors) => {
                Self::product(factors.into_iter().map(Self::canonicalize).collect())
            }
            expr => expr,
        }
    }

    /// Lower the expression into today's executable constraint representation.
    ///
    /// This deliberately rejects degree-3 and degree-4 expressions even though
    /// the metadata IR can represent them. The current compiler path normalizes
    /// constraints as max-quadratic polynomials, so accepting higher degree here
    /// would hide unsupported executable behavior behind valid metadata.
    #[track_caller]
    pub fn to_max_quadratic_constraint(&self) -> Constraint<F> {
        self.validate_degree_at_most(2);

        let mut constraint = self.to_constraint_unchecked();
        constraint.normalize();

        constraint
    }

    fn to_constraint_unchecked(&self) -> Constraint<F> {
        match self {
            Self::Constant(value) => Constraint::constant(*value),
            Self::Var(variable) => Constraint::from(*variable),
            Self::Sum(terms) => {
                let mut result = Constraint::empty();
                for term in terms {
                    result += term.to_constraint_unchecked();
                }

                result
            }
            Self::Product(factors) => {
                let mut result = Constraint::constant(F::ONE);
                for factor in factors {
                    result = result * factor.to_constraint_unchecked();
                }

                result
            }
        }
    }
}

impl<F: PrimeField> From<Variable> for Expr<F> {
    fn from(value: Variable) -> Self {
        Self::Var(value)
    }
}

impl<F: PrimeField> From<Term<F>> for Expr<F> {
    fn from(value: Term<F>) -> Self {
        match value {
            Term::Constant(value) => Self::Constant(value),
            Term::Expression {
                coeff,
                inner,
                degree,
            } => {
                if coeff == F::ZERO {
                    return Self::zero();
                }

                let mut factors = Vec::with_capacity(degree + usize::from(coeff != F::ONE));
                if coeff != F::ONE {
                    factors.push(Self::Constant(coeff));
                }
                factors.extend(inner[..degree].iter().copied().map(Self::Var));

                Self::product(factors)
            }
        }
    }
}

impl<F: PrimeField> From<Constraint<F>> for Expr<F> {
    fn from(value: Constraint<F>) -> Self {
        Self::sum(value.terms.into_iter().map(Self::from).collect())
    }
}

impl<F: PrimeField> From<Num<F>> for Expr<F> {
    fn from(value: Num<F>) -> Self {
        match value {
            Num::Var(variable) => Self::Var(variable),
            Num::Constant(value) => Self::Constant(value),
        }
    }
}

impl<F: PrimeField> From<Boolean> for Expr<F> {
    fn from(value: Boolean) -> Self {
        match value {
            Boolean::Is(variable) => Self::Var(variable),
            Boolean::Not(variable) => Self::from(1u32) - Self::Var(variable),
            Boolean::Constant(value) => Self::from(value as u32),
        }
    }
}

impl<F: PrimeField> From<TableType> for Expr<F> {
    fn from(value: TableType) -> Self {
        Self::Constant(F::from_u32(value as u32).expect("must fit"))
    }
}

impl<F: PrimeField> From<u32> for Expr<F> {
    fn from(value: u32) -> Self {
        Self::Constant(F::from_u32_with_reduction(value))
    }
}

impl<F: PrimeField> From<bool> for Expr<F> {
    fn from(value: bool) -> Self {
        Self::from(value as u32)
    }
}

impl<F: PrimeField> std::ops::Add for Expr<F> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self::sum(vec![self, rhs])
    }
}

impl<F: PrimeField> std::ops::Sub for Expr<F> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        Self::sum(vec![self, -rhs])
    }
}

impl<F: PrimeField> std::ops::Neg for Expr<F> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        match self {
            Self::Constant(mut value) => {
                value.negate();
                Self::Constant(value)
            }
            expr => Self::product(vec![Self::Constant(F::MINUS_ONE), expr]),
        }
    }
}

impl<F: PrimeField> std::ops::Mul for Expr<F> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        Self::product(vec![self, rhs])
    }
}

impl<F: PrimeField> std::ops::Mul<F> for Expr<F> {
    type Output = Self;

    fn mul(self, rhs: F) -> Self::Output {
        Self::product(vec![Self::Constant(rhs), self])
    }
}
