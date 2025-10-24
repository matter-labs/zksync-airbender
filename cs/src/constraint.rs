//! Polynomial algebra for expressing constraints.
//!
//! Term: the atomic piece of a polynomial either a constant or a single monomial
//! coeff * x1 * x2 * ... .
//! Terms follow the usual polynomial laws: multiplication is associativeand distributes over addition.
//! We keep terms normalized.
//! Constraint: a sum of Term that we keep at most quadratic after normalization.
//! Performing arithmetic on constraints automatically combines like terms and asserts that the final degree does
//! not exceed 2.
//! Think of Constraint as “the polynomial” and each Term as one of its
//! pieces. While Term can momentarily reach degree 4 to allow
//! intermediate products, our API`s ensure that a normalized Constraint
//! ends up quadratic (degree <= 2).
//!
//! All arithmetic is over a generic [field::PrimeField].

use crate::cs::circuit::Circuit;
use crate::definitions::*;
use crate::types::{Boolean, Num};
use field::PrimeField;

pub const TERM_INNER_CAPACITY: usize = 4;

// #[derive(Clone, Debug, Copy, PartialEq, Eq)]
#[derive(Clone, Copy, PartialEq, Eq)]

/// [Term::Expression] is coeff * prod(inner[0..degree]). The inner[..degree] slice is kept sorted, repeated variables encode powers.
pub enum Term<F: PrimeField> {
    Constant(F),
    Expression {
        coeff: F,
        inner: [Variable; TERM_INNER_CAPACITY], // we count on the fact that the degree is always <= 4
        degree: usize,
    },
}

impl<F: PrimeField> PartialOrd for Term<F> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<F: PrimeField> Ord for Term<F> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let t = other.degree().cmp(&self.degree());
        if t != std::cmp::Ordering::Equal {
            return t;
        }

        match (self, other) {
            (Term::Constant(s), Term::Constant(o)) => s.as_u64_reduced().cmp(&o.as_u64_reduced()),
            (Term::Constant(..), Term::Expression { .. }) => std::cmp::Ordering::Less,
            (Term::Expression { .. }, Term::Constant(..)) => std::cmp::Ordering::Greater,
            (
                Term::Expression {
                    degree: s_d,
                    coeff: s_coeff,
                    inner: s_inner,
                },
                Term::Expression {
                    degree: o_d,
                    coeff: o_coeff,
                    inner: o_inner,
                },
            ) => {
                assert_eq!(*s_d, *o_d);
                assert!(s_inner[..*s_d].is_sorted());
                assert!(o_inner[..*o_d].is_sorted());
                let t = s_inner[..*s_d].cmp(&o_inner[..*o_d]);
                if t != std::cmp::Ordering::Equal {
                    return t;
                }

                s_coeff.as_u64_reduced().cmp(&o_coeff.as_u64_reduced())
            }
        }
    }
}

impl<F: PrimeField> std::fmt::Debug for Term<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::Constant(constant) => f
                .debug_struct("Term::Constant")
                .field("coeff", constant)
                .finish(),
            Term::Expression {
                coeff,
                inner,
                degree,
            } => f
                .debug_struct("Term::Expression")
                .field("coeff", coeff)
                .field("variables", &&inner[..*degree])
                .field("degree", degree)
                .finish(),
        }
    }
}

impl<F: PrimeField> Term<F> {
    pub fn is_constant(&self) -> bool {
        match self {
            Term::Constant(_) => true,
            Term::Expression { .. } => false,
        }
    }

    pub fn get_coef(&self) -> F {
        match self {
            Term::Constant(f) => *f,
            Term::Expression { coeff, .. } => *coeff,
        }
    }

    pub fn degree(&self) -> usize {
        match self {
            Term::Constant(_) => 0,
            Term::Expression { degree, .. } => *degree,
        }
    }

    /// Normalizes the term inplace.
    /// Zero coefficients collapse to Constant(0).
    /// For expressions, asserts unused slots are placeholders and sorts inner[..degree].
    /// Multiplication is commutative, x*y and y*x must be represented identically. Sorting inner[..degree] makes the representation unique.
    /// `combine` and `same_multiple` rely on simple slice equality. Sorting guarantees that equal monomials compare equal, so coefficients can be merged.
    pub fn normalize(&mut self) {
        if let Self::Expression { coeff, .. } = &*self {
            if coeff.is_zero() {
                *self = Self::Constant(F::ZERO);
            }
        }
        match self {
            Term::Constant(_) => {}
            Term::Expression { degree, inner, .. } => {
                for el in inner[*degree..].iter() {
                    assert!(el.is_placeholder());
                }
                inner[..*degree].sort();
            }
        }
    }

    /// Returns `true` if both terms are the same monomial up to a scalar
    /// multiple (i.e. identical variable multiset and degree).
    pub fn same_multiple(&self, other: &Self) -> bool {
        if self.degree() != other.degree() {
            return false;
        }

        match (self, other) {
            (Term::Constant(..), Term::Constant(..)) => true,
            (Term::Constant(..), Term::Expression { degree, .. }) => {
                assert!(*degree > 0);
                false
            }
            (Term::Expression { degree, .. }, Term::Constant(..)) => {
                assert!(*degree > 0);
                false
            }
            (
                Term::Expression {
                    degree: s_d,
                    inner: s_inner,
                    ..
                },
                Term::Expression {
                    degree: o_d,
                    inner: o_inner,
                    ..
                },
            ) => {
                assert_eq!(*s_d, *o_d);

                &s_inner[..*s_d] == &o_inner[..*o_d]
            }
        }
    }

    /// Adds other into self if they are like terms and returns true.
    /// For constants, adds constant values. For expressions, adds coefficients if inner[..degree] matches exactly. Returns false otherwise.
    pub fn combine(&mut self, other: &Self) -> bool {
        if self.degree() != other.degree() {
            return false;
        }

        match (self, other) {
            (Term::Constant(c), Term::Constant(o)) => {
                c.add_assign(&*o);

                true
            }
            (Term::Constant(..), Term::Expression { degree, .. }) => {
                assert!(*degree > 0);
                false
            }
            (Term::Expression { degree, .. }, Term::Constant(..)) => {
                assert!(*degree > 0);
                false
            }
            (
                Term::Expression {
                    degree: s_d,
                    coeff: s_coeff,
                    inner: s_inner,
                },
                Term::Expression {
                    degree: o_d,
                    coeff: o_coeff,
                    inner: o_inner,
                },
            ) => {
                assert_eq!(*s_d, *o_d);

                if &s_inner[..*s_d] == &o_inner[..*o_d] {
                    s_coeff.add_assign(&*o_coeff);

                    true
                } else {
                    false
                }
            }
        }
    }

    /// Adds a scalar to the coefficient (or to the constant value).
    pub fn add_constant_multiple(&mut self, to_add: &F) {
        match self {
            Term::Constant(f) => f.add_assign(to_add),
            Term::Expression { coeff, .. } => coeff.add_assign(to_add),
        };
    }

    /// Scales the whole term by scaling_factor (a field element).
    /// For Term::Constant(c), we do c *= scaling_factor.
    /// For Term::Expression { coeff, .. }, we do coeff *= scaling_factor.
    /// Scaling by 0 turns the term into zero, scaling by a field inverse models division.
    pub fn scale(&mut self, scaling_factor: &F) {
        match self {
            Term::Constant(f) => f.mul_assign(scaling_factor),
            Term::Expression { coeff, .. } => coeff.mul_assign(scaling_factor),
        };
    }

    /// Returns true if the coefficient (or constant value) is zero.
    pub fn is_zero(&self) -> bool {
        match self {
            Term::Constant(f) => f.is_zero(),
            Term::Expression { coeff, .. } => coeff.is_zero(),
        }
    }

    /// Returns true if the monomial contains variable.
    pub fn contains_var(&self, variable: &Variable) -> bool {
        match self {
            Term::Constant(_) => false,
            Term::Expression { degree, inner, .. } => inner[..*degree].contains(variable),
        }
    }

    /// Returns the multiplicity (power) of variable in this monomial.
    pub fn degree_for_var(&self, variable: &Variable) -> usize {
        match self {
            Term::Constant(_) => 0,
            Term::Expression { degree, inner, .. } => {
                let mut var_degree = 0;
                for var in inner[..*degree].iter() {
                    if var == variable {
                        var_degree += 1
                    }
                }

                var_degree
            }
        }
    }

    /// If this term is exactly 1 * variable, returns that variable.
    /// Otherwise returns None.
    pub fn get_variable(&self) -> Option<Variable> {
        match self {
            Term::Constant(_) => None,
            Term::Expression {
                coeff,
                degree,
                inner,
            } => {
                if *coeff != F::ONE {
                    return None;
                }
                if *degree != 1 {
                    return None;
                }

                Some(inner[0])
            }
        }
    }

    /// Returns the coefficient assuming the term contains variable once.
    /// Panics if the term is constant or variable is not present.
    pub fn prefactor_for_var(&self, variable: &Variable) -> F {
        assert!(self.contains_var(variable));
        match self {
            Term::Constant(_) => {
                panic!("it's a constant term");
            }
            Term::Expression { coeff, .. } => *coeff,
        }
    }

    /// Returns a view over inner[..degree].
    pub fn as_slice(&self) -> &[Variable] {
        match self {
            Term::Constant(_) => &[],
            Term::Expression { degree, inner, .. } => &inner[..*degree],
        }
    }
}

#[derive(Clone, Debug)]
/// A polynomial represented as a sparse sum of monomial Terms.
/// Arithmetic on constraints behaves like ordinary polynomial algebra: we normalize, combine like terms, and assert that after normalization the degree is <= 2.
pub struct Constraint<F: PrimeField> {
    pub terms: Vec<Term<F>>,
}

impl<F: PrimeField> From<Variable> for Constraint<F> {
    fn from(value: Variable) -> Self {
        let term = Term::<F>::from(value);
        Constraint { terms: vec![term] }
    }
}
impl<F: PrimeField> From<Num<F>> for Constraint<F> {
    fn from(value: Num<F>) -> Self {
        let term = Term::<F>::from(value);
        Constraint { terms: vec![term] }
    }
}
impl<F: PrimeField> From<Boolean> for Constraint<F> {
    fn from(value: Boolean) -> Self {
        let term = Term::<F>::from(value);
        Constraint { terms: vec![term] }
    }
}
impl<F: PrimeField> From<Term<F>> for Constraint<F> {
    fn from(value: Term<F>) -> Self {
        Constraint { terms: vec![value] }
    }
}

impl<F: PrimeField> Constraint<F> {
    /// Creates a constant constraint from a field element.
    pub fn from_field(value: F) -> Self {
        let term = Term::<F>::from_field(value);
        Constraint { terms: vec![term] }
    }
}

impl<F: PrimeField> From<u64> for Constraint<F> {
    fn from(value: u64) -> Self {
        let term = Term::Constant(F::from_u64(value).unwrap());
        Constraint { terms: vec![term] }
    }
}
impl<F: PrimeField> From<bool> for Constraint<F> {
    fn from(value: bool) -> Self {
        let term = Term::Constant(F::from_u64(value as u64).unwrap());
        Constraint { terms: vec![term] }
    }
}

impl<F: PrimeField> Constraint<F> {
    pub fn empty() -> Self {
        Self {
            terms: Vec::<Term<F>>::new(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.terms.is_empty()
    }

    pub fn constant(fr: F) -> Self {
        let term = Term::Constant(fr);
        Self { terms: vec![term] }
    }

    /// Splits the constraint into quadratic terms, linear terms and a constant.
    /// Returns a triple (quadratic, linear, constant) where
    /// quadratic: Vec<(coeff, a, b)>
    /// linear: Vec<(coeff, a)>
    /// constant: F
    /// Panics if the constraint contains terms of degree > 2 or multiple constants.
    pub fn split_max_quadratic(mut self) -> (Vec<(F, Variable, Variable)>, Vec<(F, Variable)>, F) {
        self.normalize();
        let mut quadratic_terms = Vec::with_capacity(self.terms.len());
        let mut linear_terms = Vec::with_capacity(self.terms.len());
        let mut constant_term = F::ZERO;
        let mut constant_used = false;
        for term in self.terms.into_iter() {
            match term.degree() {
                2 => {
                    let Term::Expression {
                        coeff,
                        inner,
                        degree,
                    } = term
                    else {
                        panic!();
                    };
                    assert_eq!(degree, 2);
                    quadratic_terms.push((coeff, inner[0], inner[1]));
                }
                1 => {
                    let Term::Expression {
                        coeff,
                        inner,
                        degree,
                    } = term
                    else {
                        panic!();
                    };
                    assert_eq!(degree, 1);
                    linear_terms.push((coeff, inner[0]));
                }
                0 => {
                    assert!(constant_used == false);
                    constant_term = term.get_coef();
                    constant_used = true;
                }
                a @ _ => {
                    panic!("Degree {} is not supported", a);
                }
            }
        }

        (quadratic_terms, linear_terms, constant_term)
    }

    /// Scales all coefficients and the constant by scaling_factor.
    pub fn scale(&mut self, scaling_factor: F) {
        for term in self.terms.iter_mut() {
            match term {
                Term::Constant(ref mut fr) => {
                    fr.mul_assign(&scaling_factor);
                }
                Term::Expression { ref mut coeff, .. } => {
                    coeff.mul_assign(&scaling_factor);
                }
            }
        }
    }

    /// Returns the maximum degree among all terms.
    pub fn degree(&self) -> usize {
        self.terms.iter().fold(0, |cur_degree, term| {
            let term_degree = match term {
                Term::Constant(_) => 0,
                Term::Expression { degree, .. } => *degree,
            };
            std::cmp::max(cur_degree, term_degree)
        })
    }

    /// Interprets this constraint as a constant and returns the value. Panics if the degree is non-zero or there is more than one term.
    pub fn as_constant(&self) -> F {
        assert!(self.degree() == 0);
        assert_eq!(self.terms.len(), 1);
        self.terms[0].get_coef()
    }

    /// Interprets this constraint as a single term and returns it.
    /// Panics if the degree is greater than 1 or there is not exactly one term.
    pub fn as_term(&self) -> Term<F> {
        assert!(self.degree() <= 1);
        assert_eq!(self.terms.len(), 1);
        self.terms[0]
    }

    #[track_caller]
    /// Normalizes every term, sorts terms by the total order defined on Term, combines like terms and removes zeros, asserts the final degree is <= 2, converts a single zero term into an empty constraint.
    pub fn normalize(&mut self) {
        self.terms.iter_mut().for_each(|el| el.normalize());
        self.terms.sort();

        let initial_degree = self.degree();

        let mut combined: Vec<Term<F>> = Vec::with_capacity(self.terms.len());
        for el in self.terms.drain(..) {
            let mut did_combine = false;
            for existing in combined.iter_mut() {
                if existing.combine(&el) {
                    existing.normalize();
                    did_combine = true;
                    break;
                }
            }
            if did_combine {
                continue;
            } else {
                combined.push(el);
                // sorting again is not needed
            }
        }

        self.terms = combined
            .into_iter()
            .filter(|el| el.is_zero() == false)
            .collect();
        let final_degree = self.degree();
        assert!(final_degree <= 2);

        if final_degree == 0 && self.terms == vec![Term::Constant(F::ZERO)] {
            *self = Constraint::empty();
            return;
        }

        self.terms.iter_mut().for_each(|el| el.normalize());
        self.terms.sort();

        // it's possible that terms will cancel each other
        assert!(final_degree <= initial_degree);
    }

    /// Returns true if any term contains variable.
    pub fn contains_var(&self, variable: &Variable) -> bool {
        for term in self.terms.iter() {
            if term.contains_var(variable) {
                return true;
            }
        }

        false
    }

    /// Returns the maximum multiplicity of variable across all terms.
    pub fn degree_for_var(&self, variable: &Variable) -> usize {
        let mut degree = 0;

        for term in self.terms.iter() {
            degree = std::cmp::max(degree, term.degree_for_var(variable));
        }

        degree
    }

    /// Solves this linear constraint for variable and returns the expression.
    /// Interprets the constraint as a * x + rest = 0 and returns x = -(a^{-1}) * rest.
    /// Panics if the constraint does not contain variable linearly.
    pub fn express_variable(&self, variable: Variable) -> Self {
        assert!(self.contains_var(&variable));
        assert!(self.degree_for_var(&variable) == 1);

        let mut new_terms = Vec::with_capacity(self.terms.len() - 1);
        let mut prefactor = F::ZERO;
        for term in self.terms.iter() {
            if term.contains_var(&variable) {
                assert!(term.degree_for_var(&variable) == 1);
                prefactor = term.prefactor_for_var(&variable);
            } else {
                new_terms.push(term.clone());
            }
        }
        let mut prefactor = prefactor.inverse().unwrap();
        prefactor.negate();
        for el in new_terms.iter_mut() {
            el.scale(&prefactor);
        }

        let mut new = Self { terms: new_terms };
        new.normalize();

        new
    }

    /// Substitutes variable by a expression and returns the result.
    /// If variable appears linearly in a term, scales and adds the expression.
    /// If variable appears together with another variable in a quadratic term, produces a product of expression and the other variable.
    /// Panics if variable appears with multiplicity > 1 in any term.
    pub fn substitute_variable(&self, variable: Variable, expression: Constraint<F>) -> Self {
        assert!(self.contains_var(&variable));
        assert!(self.degree_for_var(&variable) == 1);

        let mut extra_constraints_to_add = vec![];
        let mut new_terms = Vec::with_capacity(self.terms.len());
        for term in self.terms.iter() {
            if term.contains_var(&variable) {
                let Term::Expression {
                    coeff,
                    inner,
                    degree,
                } = term
                else {
                    panic!("can not be a constant term");
                };
                // remove the variable of interest from there
                if *degree == 1 {
                    let mut expression = expression.clone();
                    expression.scale(*coeff);
                    extra_constraints_to_add.push(expression);
                } else {
                    assert!(*degree == 2);
                    // we only need to take constant coeff and other variable
                    let other_var = if inner[0] == variable {
                        inner[1]
                    } else if inner[1] == variable {
                        inner[0]
                    } else {
                        unreachable!()
                    };
                    assert!(other_var.is_placeholder() == false);
                    let term = Term::from((*coeff, other_var));
                    extra_constraints_to_add.push(expression.clone() * term);
                }
            } else {
                new_terms.push(term.clone());
            }
        }
        let mut new = Self { terms: new_terms };
        for el in extra_constraints_to_add.into_iter() {
            new = new + el;
            assert!(new.degree() <= 2);
        }
        new.normalize();

        new
    }

    /// Evaluates the constraint using witness values from a circuit,
    /// returning the concrete field value if all variables are assigned.
    pub fn get_value<CS: Circuit<F>>(&self, cs: &CS) -> Option<F> {
        let (quad, linear, constant_term) = self.clone().split_max_quadratic();
        let mut result = constant_term;
        for (coeff, a, b) in quad.into_iter() {
            let mut t = cs.get_value(a)?;
            t.mul_assign(&cs.get_value(b)?);
            t.mul_assign(&coeff);
            result.add_assign(&t);
        }

        for (coeff, a) in linear.into_iter() {
            let mut t = cs.get_value(a)?;
            t.mul_assign(&coeff);
            result.add_assign(&t);
        }

        Some(result)
    }
}

//CONSTRAINT -> CONSTRAINT OPS
impl<F: PrimeField> std::ops::Add for Constraint<F> {
    type Output = Self;

    /// Adds two constraints and normalizes the result.
    fn add(self, rhs: Self) -> Self::Output {
        let mut ans = self;
        ans.terms.extend(rhs.terms);
        ans.normalize();
        // rhs.terms.into_iter().for_each(|term| ans.add_assign(term));
        ans
    }
}

impl<F: PrimeField> std::ops::Sub for Constraint<F> {
    type Output = Self;

    /// Subtracts two constraints and normalizes the result.
    fn sub(self, rhs: Self) -> Self::Output {
        let mut ans = self;
        ans.terms.extend(rhs.terms.into_iter().map(|mut el| {
            el.scale(&F::MINUS_ONE);

            el
        }));
        ans.normalize();
        // rhs.terms.into_iter().for_each(|term| {
        //     ans.sub_assign(term);
        // });
        ans
    }
}

impl<F: PrimeField> std::ops::Mul for Constraint<F> {
    type Output = Self;

    /// Multiplies two constraints by distributing over their terms.
    ///
    /// Panics during normalization if the resulting degree exceeds 2.
    fn mul(self, rhs: Self) -> Self::Output {
        let mut ans = Constraint::empty();
        for term in self.terms {
            ans = ans + term * rhs.clone();
        }
        ans
    }
}

//CONSTRAINT -> TERM OPS
impl<F: PrimeField> std::ops::Add<Term<F>> for Constraint<F> {
    type Output = Self;

    /// Adds a single term to the constraint (without immediate normalization).
    fn add(self, rhs: Term<F>) -> Self::Output {
        let mut ans = self;
        ans.terms.push(rhs);
        ans
    }
}

impl<F: PrimeField> std::ops::AddAssign<Term<F>> for Constraint<F> {
    /// Pushes a single term into the constraint (without immediate normalization).
    fn add_assign(&mut self, rhs: Term<F>) {
        self.terms.push(rhs);
    }
}

impl<F: PrimeField> std::ops::Sub<Term<F>> for Constraint<F> {
    type Output = Self;

    /// Subtracts a single term from the constraint (without immediate normalization).
    fn sub(self, rhs: Term<F>) -> Self::Output {
        let mut ans = self;
        let inv_term = match rhs {
            Term::Expression {
                coeff,
                inner,
                degree,
            } => {
                let mut v = coeff;
                v.mul_assign(&F::MINUS_ONE);
                Term::Expression {
                    coeff: v,
                    inner,
                    degree,
                }
            }
            Term::Constant(coeff) => {
                let mut v = coeff;
                v.mul_assign(&F::MINUS_ONE);
                Term::Constant(v)
            }
        };
        ans.terms.push(inv_term);
        ans
    }
}

impl<F: PrimeField> std::ops::SubAssign<Term<F>> for Constraint<F> {
    /// Subtracts a single term from the constraint (without immediate normalization).
    fn sub_assign(&mut self, rhs: Term<F>) {
        let minus_one: Term<F> = Term::from_field(F::MINUS_ONE);
        let t: Constraint<F> = rhs * minus_one;
        self.terms.push(t.terms[0]);
    }
}

impl<F: PrimeField> std::ops::Mul<Term<F>> for Constraint<F> {
    type Output = Self;

    /// Multiplies the entire constraint by a single term and normalizes.
    fn mul(self, rhs: Term<F>) -> Self::Output {
        let mut ans = Constraint::empty();
        for existing in self.terms.into_iter() {
            let intermediate_constraint = existing * rhs;
            ans = ans + intermediate_constraint;
        }
        ans.normalize();

        ans
    }
}

//TERM -> CONSTRAINT OPS
impl<F: PrimeField> std::ops::Mul<Constraint<F>> for Term<F> {
    type Output = Constraint<F>;

    fn mul(self, rhs: Constraint<F>) -> Self::Output {
        rhs * self
    }
}

//TERM -> TERM OPS
impl<F: PrimeField> std::ops::Add for Term<F> {
    type Output = Constraint<F>;

    fn add(self, rhs: Term<F>) -> Self::Output {
        let mut constraint = Constraint::empty();
        constraint.terms.push(self);
        constraint.terms.push(rhs);
        constraint
    }
}

impl<F: PrimeField> std::ops::Sub for Term<F> {
    type Output = Constraint<F>;

    fn sub(self, rhs: Term<F>) -> Self::Output {
        let mut constraint = Constraint::empty();
        let inv_term = match rhs {
            Term::Expression {
                coeff,
                inner,
                degree,
            } => {
                let mut v = coeff;
                v.mul_assign(&F::MINUS_ONE);
                Term::Expression {
                    coeff: v,
                    inner,
                    degree,
                }
            }
            Term::Constant(coeff) => {
                let mut v = coeff;
                v.mul_assign(&F::MINUS_ONE);
                Term::Constant(v)
            }
        };
        constraint.terms.push(self);
        constraint.terms.push(inv_term);
        constraint
    }
}

impl<F: PrimeField> std::ops::Mul for Term<F> {
    type Output = Constraint<F>;

    /// Multiplies two terms, producing a single term constraint.
    /// Panics if the product degree exceeds TERM_INNER_CAPACITY.
    /// The caller is expected to ensure that any subsequent use inside a Constraint remains <= quadratic after normalization.
    fn mul(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (
                Term::Expression {
                    coeff,
                    inner,
                    degree,
                },
                Term::Expression {
                    coeff: coeff2,
                    inner: inner2,
                    degree: degree2,
                },
            ) => {
                assert!(
                    degree + degree2 <= 4,
                    "Degree overflow, {} + {} > 4",
                    degree,
                    degree2
                );
                let mut res_inner = inner;
                for i in 0..degree2 {
                    res_inner[degree + i] = inner2[i];
                }
                let mut res_coeff = coeff;
                res_coeff.mul_assign(&coeff2);
                let mut constraint = Constraint::empty();
                constraint.terms.push(Term::Expression {
                    coeff: res_coeff,
                    inner: res_inner,
                    degree: degree + degree2,
                });
                constraint
            }
            (
                Term::Expression {
                    coeff,
                    inner,
                    degree,
                },
                Term::Constant(coeff2),
            ) => {
                let mut res_coeff = coeff;
                res_coeff.mul_assign(&coeff2);
                let mut constraint = Constraint::empty();
                constraint.terms.push(Term::Expression {
                    coeff: res_coeff,
                    inner,
                    degree,
                });
                constraint
            }
            (
                Term::Constant(coeff),
                Term::Expression {
                    coeff: coeff2,
                    inner: inner2,
                    degree: degree2,
                },
            ) => {
                let mut res_coeff = coeff;
                res_coeff.mul_assign(&coeff2);
                let mut constraint = Constraint::empty();
                constraint.terms.push(Term::Expression {
                    coeff: res_coeff,
                    inner: inner2,
                    degree: degree2,
                });
                constraint
            }
            (Term::Constant(coeff), Term::Constant(coeff2)) => {
                let mut res_coeff = coeff;
                res_coeff.mul_assign(&coeff2);
                let mut constraint = Constraint::empty();
                constraint.terms.push(Term::Constant(res_coeff));
                constraint
            }
        }
    }
}

//CAST
impl<F: PrimeField> Term<F> {
    /// Creates a constant term from a field element.
    pub fn from_field(value: F) -> Self {
        Term::Constant(value)
    }
}

impl<F: PrimeField> From<u64> for Term<F> {
    /// Creates a constant term from a u64 (reduced into the field).
    fn from(value: u64) -> Self {
        Term::Constant(F::from_u64(value).unwrap())
    }
}

impl<F: PrimeField> From<Variable> for Term<F> {
    /// Creates a linear term 1 * variable.
    fn from(value: Variable) -> Self {
        let mut inner = [Variable::placeholder_variable(); 4];
        inner[0] = value;
        Term::Expression {
            coeff: F::ONE,
            inner,
            degree: 1,
        }
    }
}

impl<F: PrimeField> From<(F, Variable)> for Term<F> {
    /// Creates a linear term coeff * variable.
    fn from(value: (F, Variable)) -> Self {
        let mut inner = [Variable::placeholder_variable(); 4];
        inner[0] = value.1;
        Term::Expression {
            coeff: value.0,
            inner,
            degree: 1,
        }
    }
}

impl<F: PrimeField> From<Num<F>> for Term<F> {
    /// Creates a term from a numeric value (constant or variable).
    fn from(value: Num<F>) -> Self {
        match value {
            Num::Constant(value) => Term::from_field(value),
            Num::Var(value) => Term::from(value),
        }
    }
}

impl<F: PrimeField> From<Boolean> for Term<F> {
    /// Creates a term from a boolean value (constant or variable).
    fn from(value: Boolean) -> Self {
        match value {
            Boolean::Constant(value) => Term::from(value as u64),
            Boolean::Is(value) => Self::from(value),
            Boolean::Not(_) => {
                unreachable!()
            }
        }
    }
}

impl<F: PrimeField> Term<F> {
    /// Structural equality that ignores the coefficient.
    /// Returns true if both terms are constants, or if both are expressions with the same degree and identical inner[..degree] sequences.
    pub fn are_equal_terms(left: &Self, right: &Self) -> bool {
        match (left, right) {
            (Term::Constant(_), Term::Constant(_)) => true,
            (
                Term::Expression {
                    inner: inner_left,
                    degree: degree_left,
                    ..
                },
                Term::Expression {
                    inner: inner_right,
                    degree: degree_right,
                    ..
                },
            ) => {
                let degrees_are_equalt = *degree_left == *degree_right;
                let arrays_are_equal = inner_left[0..*degree_left]
                    .iter()
                    .zip(inner_right[0..*degree_right].iter())
                    .map(|(left_var, right_var)| left_var.0 == right_var.0)
                    .all(|x| x);
                degrees_are_equalt && arrays_are_equal
            }
            _ => false,
        }
    }
}
