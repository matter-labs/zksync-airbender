use crate::cs::circuit::Circuit;
use crate::definitions::*;
use crate::types::{Boolean, Num};
use field::PrimeField;

pub const TERM_INNER_CAPACITY: usize = 4;

// #[derive(Clone, Debug, Copy, PartialEq, Eq)]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Term<F: PrimeField> {
    Constant(F),
    Expression {
        coeff: F,
        inner: [Variable; TERM_INNER_CAPACITY], // we count on the fact that the degree is always <= 4
        degree: usize,
    },
}

impl<F: PrimeField> std::fmt::Display for Term<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Constant(c) => {
                write!(f, "{c}")
            }
            Self::Expression {
                coeff,
                inner,
                degree,
            } => {
                let coeff = coeff.as_u64_reduced();
                let coeff_opp = F::CHARACTERISTICS - coeff;
                if coeff < coeff_opp {
                    if coeff != 1 {
                        write!(f, " + {coeff}")?;
                    } else {
                        write!(f, " + ")?;
                    }
                } else {
                    if coeff_opp != 1 {
                        write!(f, " - {coeff_opp}")?;
                    } else {
                        write!(f, " - ")?;
                    }
                }
                if coeff != 0 {
                    for &Variable(var) in inner.into_iter().take(*degree) {
                        write!(f, "(v{var})")?;
                    }
                }
                Ok(())
            }
        }
    }
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

    pub fn add_constant_multiple(&mut self, to_add: &F) {
        match self {
            Term::Constant(f) => f.add_assign(to_add),
            Term::Expression { coeff, .. } => coeff.add_assign(to_add),
        };
    }

    pub fn scale(&mut self, scaling_factor: &F) {
        match self {
            Term::Constant(f) => f.mul_assign(scaling_factor),
            Term::Expression { coeff, .. } => coeff.mul_assign(scaling_factor),
        };
    }

    pub fn is_zero(&self) -> bool {
        match self {
            Term::Constant(f) => f.is_zero(),
            Term::Expression { coeff, .. } => coeff.is_zero(),
        }
    }

    pub fn contains_var(&self, variable: &Variable) -> bool {
        match self {
            Term::Constant(_) => false,
            Term::Expression { degree, inner, .. } => inner[..*degree].contains(variable),
        }
    }

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

    pub fn prefactor_for_var(&self, variable: &Variable) -> F {
        assert!(self.contains_var(variable));
        match self {
            Term::Constant(_) => {
                panic!("it's a constant term");
            }
            Term::Expression { coeff, .. } => *coeff,
        }
    }

    pub fn as_slice(&self) -> &[Variable] {
        match self {
            Term::Constant(_) => &[],
            Term::Expression { degree, inner, .. } => &inner[..*degree],
        }
    }
}

#[derive(Clone, Debug)]
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
    #[track_caller]
    fn from(value: Boolean) -> Self {
        match value {
            Boolean::Not(var) => {
                let one = Term::<F>::from(1);
                let term = Term::<F>::from(var);
                one - term
            }
            _ => {
                let term = Term::<F>::from(value);
                Constraint { terms: vec![term] }
            }
        }
    }
}
impl<F: PrimeField> From<Term<F>> for Constraint<F> {
    fn from(value: Term<F>) -> Self {
        Constraint { terms: vec![value] }
    }
}

impl<F: PrimeField> Constraint<F> {
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

    pub fn degree(&self) -> usize {
        self.terms.iter().fold(0, |cur_degree, term| {
            let term_degree = match term {
                Term::Constant(_) => 0,
                Term::Expression { degree, .. } => *degree,
            };
            std::cmp::max(cur_degree, term_degree)
        })
    }

    pub fn as_constant(&self) -> F {
        assert!(self.degree() == 0);
        assert_eq!(self.terms.len(), 1);
        self.terms[0].get_coef()
    }

    pub fn as_term(&self) -> Term<F> {
        assert!(self.degree() <= 1);
        assert_eq!(self.terms.len(), 1);
        self.terms[0]
    }

    /// Normalize by degree, then variable indexes
    #[track_caller]
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

    pub fn contains_var(&self, variable: &Variable) -> bool {
        for term in self.terms.iter() {
            if term.contains_var(variable) {
                return true;
            }
        }

        false
    }

    pub fn degree_for_var(&self, variable: &Variable) -> usize {
        let mut degree = 0;

        for term in self.terms.iter() {
            degree = std::cmp::max(degree, term.degree_for_var(variable));
        }

        degree
    }

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

    fn add(self, rhs: Self) -> Self::Output {
        let mut ans = self;
        ans.terms.extend(rhs.terms);
        ans.normalize();
        // rhs.terms.into_iter().for_each(|term| ans.add_assign(term));
        ans
    }
}

impl<F: PrimeField> std::ops::AddAssign<Constraint<F>> for Constraint<F> {
    fn add_assign(&mut self, rhs: Constraint<F>) {
        self.terms.extend(rhs.terms);
        self.normalize();
    }
}

impl<F: PrimeField> std::ops::Sub for Constraint<F> {
    type Output = Self;

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

    fn add(self, rhs: Term<F>) -> Self::Output {
        let mut ans = self;
        ans.terms.push(rhs);
        ans
    }
}

impl<F: PrimeField> std::ops::AddAssign<Term<F>> for Constraint<F> {
    fn add_assign(&mut self, rhs: Term<F>) {
        self.terms.push(rhs);
    }
}

impl<F: PrimeField> std::ops::Sub<Term<F>> for Constraint<F> {
    type Output = Self;

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
    fn sub_assign(&mut self, rhs: Term<F>) {
        let minus_one: Term<F> = Term::from_field(F::MINUS_ONE);
        let t: Constraint<F> = rhs * minus_one;
        self.terms.push(t.terms[0]);
    }
}

impl<F: PrimeField> std::ops::Mul<Term<F>> for Constraint<F> {
    type Output = Self;

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
    pub fn from_field(value: F) -> Self {
        Term::Constant(value)
    }
}

impl<F: PrimeField> From<u64> for Term<F> {
    fn from(value: u64) -> Self {
        Term::Constant(F::from_u64(value).unwrap())
    }
}

impl<F: PrimeField> From<Variable> for Term<F> {
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
    fn from(value: Num<F>) -> Self {
        match value {
            Num::Constant(value) => Term::from_field(value),
            Num::Var(value) => Term::from(value),
        }
    }
}

impl<F: PrimeField> From<Boolean> for Term<F> {
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
