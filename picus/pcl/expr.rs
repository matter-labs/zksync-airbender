use std::collections::HashMap;
use std::fmt::Display;
use std::fmt::Formatter;
use std::fmt::{self};
use std::iter::Product;
use std::iter::Sum;
use std::ops::Add;
use std::ops::AddAssign;
use std::ops::Mul;
use std::ops::MulAssign;
use std::ops::Neg;
use std::ops::Sub;
use std::ops::SubAssign;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;
use std::sync::Arc;
use std::sync::OnceLock;
use std::sync::RwLock;

use field::Mersenne31Field;
use field::PrimeField;

/// Mapping from column ids to variable names. This mapping should be derived in the `PicusInfo`
/// struct
static PICUS_NAMES_GLOBAL: OnceLock<RwLock<HashMap<usize, String>>> = OnceLock::new();

/// Maintains col indices for fresh variables during the course of extraction
static FRESH_VAR_CTR: OnceLock<AtomicUsize> = OnceLock::new();
pub fn set_picus_names(map: HashMap<usize, String>) {
    let _ = PICUS_NAMES_GLOBAL.set(RwLock::new(map));
}

// Get or initialize the fresh var counter
fn ctr() -> &'static AtomicUsize {
    FRESH_VAR_CTR.get_or_init(|| AtomicUsize::new(0))
}

// set the fresh counter val to something
pub fn initialize_fresh_var_ctr(val: usize) {
    let _ = FRESH_VAR_CTR.set(AtomicUsize::new(val));
}

pub fn fresh_picus_var_id() -> usize {
    let cur_var = ctr().load(Ordering::Relaxed);
    ctr().store(cur_var + 1, Ordering::Relaxed);
    cur_var
}

pub fn fresh_picus_var() -> PicusAtom {
    PicusAtom::new_var(fresh_picus_var_id())
}

// update the counter
pub fn fresh_picus_expr() -> PicusExpr {
    PicusExpr::Var(fresh_picus_var_id())
}

/// Global, thread-safe holder for the PCL prime field modulus.
///
/// This is initialized exactly once via [`set_field_modulus`]. Arithmetic
/// that combines only constants will be reduced modulo this value when set.
static FIELD_MODULUS: OnceLock<Arc<u64>> = OnceLock::new();
pub type Felt = Mersenne31Field;

/// Sets the field modulus for PCL
pub fn set_field_modulus(p: u64) -> Result<(), u64> {
    // set only once; returns Err(p) if already set
    FIELD_MODULUS
        .set(Arc::new(p))
        .map_err(|arc| Arc::try_unwrap(arc).unwrap_or_else(|a| *a))
}

/// Get PCL field modulus
pub fn current_modulus() -> Option<u64> {
    Some(Felt::CHARACTERISTICS)
}

/// Given an integer reduce it into the field
pub fn reduce_mod(c: i64) -> u64 {
    if let Some(p) = current_modulus() {
        (c.rem_euclid(p as i64)) as u64
    } else {
        c as u64
    }
}

/// Arithmetic expressions over the Picus constraint language (PCL).
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum PicusExpr {
    /// Constant field element. We use a `u64` to be safe because the prime is 31 bits and we don't
    /// want to deal with underflows or overflows
    Const(u64),
    /// Variable identified by `(name, index, tag)`, printed as `name_index_tag`. NOTE: Tag might
    /// be droppable
    Var(usize),
    /// Add.
    Add(Box<PicusExpr>, Box<PicusExpr>),
    /// Sub.
    Sub(Box<PicusExpr>, Box<PicusExpr>),
    /// Mul
    Mul(Box<PicusExpr>, Box<PicusExpr>),
    /// Div (probably can delete)
    Div(Box<PicusExpr>, Box<PicusExpr>),
    /// Unary negation.
    Neg(Box<PicusExpr>),
    /// Exponentiation
    Pow(u64, Box<PicusExpr>),
}

impl Default for PicusExpr {
    fn default() -> Self {
        PicusExpr::Const(0)
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, PartialOrd, Ord, Hash)]
pub enum PicusAtom {
    Const(u64),
    Var(usize),
}

impl PicusAtom {
    pub fn new_var(id: usize) -> Self {
        Self::Var(id)
    }
}

impl Display for PicusAtom {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Const(c) => write!(f, "{c}"),
            Self::Var(id) => {
                if let Some(lock) = PICUS_NAMES_GLOBAL.get() {
                    if let Some(name) = lock.read().unwrap().get(id) {
                        return f.write_str(name);
                    }
                }
                write!(f, "v{id}")
            }
        }
    }
}

impl From<PicusAtom> for PicusExpr {
    fn from(value: PicusAtom) -> Self {
        match value {
            PicusAtom::Const(c) => PicusExpr::Const(c),
            PicusAtom::Var(id) => PicusExpr::Var(id),
        }
    }
}

impl From<Felt> for PicusExpr {
    fn from(value: Felt) -> Self {
        PicusExpr::Const(value.to_reduced_u32() as u64)
    }
}

impl Add<Felt> for PicusAtom {
    type Output = PicusExpr;

    fn add(self, rhs: Felt) -> Self::Output {
        match self {
            PicusAtom::Const(c) => {
                PicusExpr::Const((c + (rhs.0 as u64)).rem_euclid(Felt::CHARACTERISTICS))
            }
            PicusAtom::Var(v) => PicusExpr::Var(v) + PicusExpr::Const(rhs.as_u64()),
        }
    }
}

impl Add<PicusAtom> for PicusAtom {
    type Output = PicusExpr;

    fn add(self, rhs: PicusAtom) -> Self::Output {
        PicusExpr::Add(Box::new(self.into()), Box::new(rhs.into()))
    }
}

impl Add<PicusExpr> for PicusAtom {
    type Output = PicusExpr;

    fn add(self, rhs: PicusExpr) -> Self::Output {
        let left_expr: PicusExpr = self.into();
        left_expr + rhs
    }
}

impl Sub<Felt> for PicusAtom {
    type Output = PicusExpr;

    fn sub(self, rhs: Felt) -> Self::Output {
        let self_expr: PicusExpr = self.into();
        self_expr - rhs
    }
}

impl Sub<PicusAtom> for PicusAtom {
    type Output = PicusExpr;

    fn sub(self, rhs: PicusAtom) -> Self::Output {
        let self_expr: PicusExpr = self.into();
        let rhs_expr: PicusExpr = rhs.into();
        self_expr - rhs_expr
    }
}

impl Sub<PicusExpr> for PicusAtom {
    type Output = PicusExpr;

    fn sub(self, rhs: PicusExpr) -> Self::Output {
        let self_expr: PicusExpr = self.into();
        self_expr - rhs
    }
}

impl Mul<PicusAtom> for PicusAtom {
    type Output = PicusExpr;

    fn mul(self, rhs: PicusAtom) -> Self::Output {
        let self_expr: PicusExpr = self.into();
        let rhs_expr: PicusExpr = rhs.into();
        self_expr * rhs_expr
    }
}

impl Mul<Felt> for PicusAtom {
    type Output = PicusExpr;

    fn mul(self, rhs: Felt) -> Self::Output {
        let self_expr: PicusExpr = self.into();
        self_expr * rhs
    }
}

impl Mul<PicusExpr> for PicusAtom {
    type Output = PicusExpr;

    fn mul(self, rhs: PicusExpr) -> Self::Output {
        let self_expr: PicusExpr = self.into();
        self_expr * rhs
    }
}

impl Sum for PicusExpr {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        let mut output: PicusExpr = 0.into();
        for item in iter {
            output += item;
        }
        output
    }
}

impl Product for PicusExpr {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        let mut output: PicusExpr = 1.into();
        for item in iter {
            output *= item;
        }
        output
    }
}

impl PicusExpr {
    /// Approximate tree size (number of nodes).
    ///
    /// Useful as a heuristic for introducing temporary variables (e.g., to keep
    /// expressions small for solvers). `Pow` is counted as 1 by design.
    #[must_use]
    pub fn size(&self) -> usize {
        match self {
            Self::Const(_) | Self::Var(_) | Self::Pow(_, _) => 1,
            Self::Add(a, b) | Self::Sub(a, b) | Self::Mul(a, b) | Self::Div(a, b) => {
                1 + a.size() + b.size()
            }
            Self::Neg(a) => 1 + a.size(),
        }
    }
    /// Helper to construct a `Var` with a column index.
    pub fn var(idx: usize) -> Self {
        PicusExpr::Var(idx)
    }
    #[must_use]
    /// Convenience for exponentiating by a non-negative `u32` power.
    pub fn pow(self, k: u32) -> Self {
        PicusExpr::Pow(k.into(), Box::new(self))
    }
    /// Returns `true` iff this is exactly the constant zero.
    #[inline]
    #[must_use]
    pub fn is_const_zero(&self) -> bool {
        matches!(self, PicusExpr::Const(c) if *c == 0)
    }
}

macro_rules! impl_from_ints {
    ($($t:ty),* $(,)?) => {$(
        impl From<$t> for PicusExpr {
            fn from(v: $t) -> Self {
                PicusExpr::Const(v as u64)
            }
        }
    )*}
}

impl_from_ints!(u8, u16, u32, u64, usize, i8, i16, i32, i64, isize);

/// Pointwise addition with light constant folding.
///
/// - If both sides are constant, the sum is reduced modulo the current field (if set).
/// - Adding zero returns the other side.
/// - Otherwise, constructs `Add(lhs, rhs)`.
impl Add<PicusExpr> for PicusExpr {
    type Output = PicusExpr;
    fn add(self, rhs: PicusExpr) -> Self::Output {
        let lhs = self.clone();
        match (lhs.clone(), rhs.clone()) {
            (PicusExpr::Const(c_1), PicusExpr::Const(c_2)) => {
                (reduce_mod((c_1 + c_2) as i64)).into()
            }
            (PicusExpr::Const(c), _) => {
                if c == 0 {
                    rhs
                } else {
                    PicusExpr::Add(Box::new(lhs), Box::new(rhs))
                }
            }
            (_, PicusExpr::Const(c)) => {
                if c == 0 {
                    lhs
                } else {
                    PicusExpr::Add(Box::new(lhs), Box::new(rhs))
                }
            }
            _ => PicusExpr::Add(Box::new(lhs), Box::new(rhs)),
        }
    }
}

impl Add<Felt> for PicusExpr {
    type Output = PicusExpr;

    fn add(self, rhs: Felt) -> Self::Output {
        let rhs_expr: Self = rhs.into();
        self + rhs_expr
    }
}

impl Add<PicusAtom> for PicusExpr {
    type Output = PicusExpr;

    fn add(self, rhs: PicusAtom) -> Self::Output {
        let rhs_expr: Self = rhs.into();
        self + rhs_expr
    }
}

impl AddAssign<PicusExpr> for PicusExpr {
    fn add_assign(&mut self, rhs: PicusExpr) {
        *self = self.clone() + rhs;
    }
}

/// Pointwise subtraction with light constant folding.
///
/// - If both sides are constant, the difference is reduced modulo the current field (if set).
/// - Subtracting zero returns the left-hand side.
/// - Otherwise, constructs `Sub(lhs, rhs)`.
impl Sub<PicusExpr> for PicusExpr {
    type Output = PicusExpr;
    fn sub(self, rhs: PicusExpr) -> Self::Output {
        let lhs = self.clone();
        match (lhs.clone(), rhs.clone()) {
            (PicusExpr::Const(c_1), PicusExpr::Const(c_2)) => {
                reduce_mod((c_1 as i64) - (c_2 as i64)).into()
            }
            (_, PicusExpr::Const(c)) => {
                if c == 0 {
                    lhs
                } else {
                    PicusExpr::Sub(Box::new(self), Box::new(rhs))
                }
            }
            _ => PicusExpr::Sub(Box::new(self), Box::new(rhs)),
        }
    }
}

impl Sub<Felt> for PicusExpr {
    type Output = PicusExpr;

    fn sub(self, rhs: Felt) -> Self::Output {
        let rhs_expr: Self = rhs.into();
        self - rhs_expr
    }
}

impl Sub<PicusAtom> for PicusExpr {
    type Output = PicusExpr;

    fn sub(self, rhs: PicusAtom) -> Self::Output {
        let rhs_expr: Self = rhs.into();
        self - rhs_expr
    }
}

impl SubAssign<PicusExpr> for PicusExpr {
    fn sub_assign(&mut self, rhs: PicusExpr) {
        *self = self.clone() - rhs;
    }
}

/// Unary negation with constant folding.
///
/// - If the input is a constant, returns the additive inverse reduced modulo the current field (if
///   set). Otherwise constructs `Neg`.
impl Neg for PicusExpr {
    type Output = PicusExpr;
    fn neg(self) -> Self::Output {
        let lhs = self.clone();
        match lhs.clone() {
            PicusExpr::Const(c) => reduce_mod((current_modulus().unwrap() - c) as i64).into(),
            _ => PicusExpr::Neg(Box::new(lhs)),
        }
    }
}

/// Pointwise multiplication with light constant folding and scalar routing.
///
/// - If either side is a constant, routes to the `(PicusExpr * Integer)` impl to share logic.
/// - Otherwise constructs `Mul(lhs, rhs)`.
impl Mul<PicusExpr> for PicusExpr {
    type Output = PicusExpr;
    fn mul(self, rhs: PicusExpr) -> Self::Output {
        let lhs = self.clone();
        match (lhs.clone(), rhs.clone()) {
            (PicusExpr::Const(c), _) => rhs * c,
            (_, PicusExpr::Const(c)) => lhs * c,
            _ => PicusExpr::Mul(Box::new(lhs), Box::new(rhs)),
        }
    }
}

impl Mul<Felt> for PicusExpr {
    type Output = PicusExpr;

    fn mul(self, rhs: Felt) -> Self::Output {
        let rhs_expr: PicusExpr = rhs.into();
        self * rhs_expr
    }
}

impl Mul<PicusAtom> for PicusExpr {
    type Output = PicusExpr;

    fn mul(self, rhs: PicusAtom) -> Self::Output {
        let rhs_expr: PicusExpr = rhs.into();
        self * rhs_expr
    }
}

impl MulAssign<PicusExpr> for PicusExpr {
    fn mul_assign(&mut self, rhs: PicusExpr) {
        *self = self.clone() * rhs;
    }
}

/// Scalar multiplication with constant folding.
///
/// - Multiplying by `0` yields `0`.
/// - Multiplying by `1` yields the original expression.
/// - If the left is also a constant, multiply and reduce modulo the current field (if set).
/// - Otherwise constructs `Mul(lhs, Const(rhs))`.
impl Mul<u64> for PicusExpr {
    type Output = PicusExpr;
    fn mul(self, rhs: u64) -> Self::Output {
        if rhs == 0 {
            return PicusExpr::Const(0);
        }
        if rhs == 1 {
            return self.clone();
        }
        let lhs = self.clone();
        match lhs {
            PicusExpr::Const(c_1) => reduce_mod((c_1 * rhs) as i64).into(),
            _ => PicusExpr::Mul(Box::new(lhs), Box::new(rhs.into())),
        }
    }
}

/// Boolean/relational constraints over `PicusExpr`.
#[derive(Debug, Clone)]
pub enum PicusConstraint {
    /// x < y
    Lt(Box<PicusExpr>, Box<PicusExpr>),
    /// x <= y
    Leq(Box<PicusExpr>, Box<PicusExpr>),
    /// x > y
    Gt(Box<PicusExpr>, Box<PicusExpr>),
    /// x >= y
    Geq(Box<PicusExpr>, Box<PicusExpr>),
    /// p => q
    Implies(Box<PicusConstraint>, Box<PicusConstraint>),
    /// -p
    Not(Box<PicusConstraint>),
    /// p <=> q
    Iff(Box<PicusConstraint>, Box<PicusConstraint>),
    /// p && q
    And(Box<PicusConstraint>, Box<PicusConstraint>),
    /// p || q
    Or(Box<PicusConstraint>, Box<PicusConstraint>),
    /// Determinism predicate over an expression
    Det(Box<PicusExpr>),
    /// Canonical equality-to-zero form: `Eq(e)` represents `e = 0`.
    Eq(Box<PicusExpr>),
}

impl PicusConstraint {
    /// Build an equality constraint `left = right` by moving to zero:
    /// returns `Eq(left - right)`.
    #[must_use]
    pub fn new_equality(left: PicusExpr, right: PicusExpr) -> PicusConstraint {
        PicusConstraint::Eq(Box::new(left - right))
    }

    #[must_use]
    /// Builds a bit constraint
    pub fn new_bit(left: PicusExpr) -> PicusConstraint {
        PicusConstraint::Eq(Box::new(
            left.clone() * (left.clone() - PicusExpr::Const(1u64)),
        ))
    }

    /// Build a comparison constraint `left < right`
    #[must_use]
    pub fn new_lt(left: PicusExpr, right: PicusExpr) -> PicusConstraint {
        PicusConstraint::Lt(Box::new(left), Box::new(right))
    }

    /// Build a comparison constraint `left <= right`
    #[must_use]
    pub fn new_leq(left: PicusExpr, right: PicusExpr) -> PicusConstraint {
        PicusConstraint::Leq(Box::new(left), Box::new(right))
    }

    /// Build a comparison constraint `left > right`
    #[must_use]
    pub fn new_gt(left: PicusExpr, right: PicusExpr) -> PicusConstraint {
        PicusConstraint::Gt(Box::new(left), Box::new(right))
    }

    /// Build a comparison constraint `left >= right`
    #[must_use]
    pub fn new_geq(left: PicusExpr, right: PicusExpr) -> PicusConstraint {
        PicusConstraint::Geq(Box::new(left), Box::new(right))
    }

    /// Build a determinism predicate `Det(expr)`.
    #[must_use]
    pub fn new_det(expr: PicusExpr) -> PicusConstraint {
        PicusConstraint::Det(Box::new(expr))
    }

    /// Assumes ``l`` and ``u`` fit into the prime
    /// Generates constraints l <= e <= u
    #[must_use]
    pub fn in_range(e: PicusExpr, l: usize, u: usize) -> Vec<PicusConstraint> {
        assert!(l < u);
        vec![
            PicusConstraint::new_geq(e.clone(), l.into()),
            PicusConstraint::new_leq(e, u.into()),
        ]
    }

    #[must_use]
    pub fn apply_multiplier(&self, multiplier: PicusExpr) -> PicusConstraint {
        use PicusConstraint::*;
        if let PicusExpr::Const(1) = multiplier {
            return self.clone();
        }
        match self {
            And(l, r) => {
                let new_left = l.apply_multiplier(multiplier.clone());
                let new_right = r.apply_multiplier(multiplier);
                PicusConstraint::And(Box::new(new_left), Box::new(new_right))
            }
            Lt(l, r) => {
                let new_left = multiplier.clone() * (*l.clone());
                let new_right = multiplier.clone() * (*r.clone());
                PicusConstraint::Lt(Box::new(new_left), Box::new(new_right))
            }
            Leq(l, r) => {
                let new_left = multiplier.clone() * (*l.clone());
                let new_right = multiplier.clone() * (*r.clone());
                PicusConstraint::Leq(Box::new(new_left), Box::new(new_right))
            }
            Gt(l, r) => {
                let new_left = multiplier.clone() * (*l.clone());
                let new_right = multiplier.clone() * (*r.clone());
                PicusConstraint::Gt(Box::new(new_left), Box::new(new_right))
            }
            Geq(l, r) => {
                let new_left = multiplier.clone() * (*l.clone());
                let new_right = multiplier.clone() * (*r.clone());
                PicusConstraint::Geq(Box::new(new_left), Box::new(new_right))
            }
            Implies(l, r) => {
                let new_left = l.apply_multiplier(multiplier.clone());
                let new_right = r.apply_multiplier(multiplier);
                PicusConstraint::Implies(Box::new(new_left), Box::new(new_right))
            }
            Not(c) => {
                let new_c = c.apply_multiplier(multiplier.clone());
                PicusConstraint::Not(Box::new(new_c))
            }
            Iff(l, r) => {
                let new_left = l.apply_multiplier(multiplier.clone());
                let new_right = r.apply_multiplier(multiplier);
                PicusConstraint::Iff(Box::new(new_left), Box::new(new_right))
            }
            Or(l, r) => {
                let new_left = l.apply_multiplier(multiplier.clone());
                let new_right = r.apply_multiplier(multiplier);
                PicusConstraint::Or(Box::new(new_left), Box::new(new_right))
            }
            Det(e) => PicusConstraint::Det(Box::new(*e.clone())),
            Eq(e) => {
                let new_e = multiplier.clone() * (*e.clone());
                PicusConstraint::Eq(Box::new(new_e))
            }
        }
    }
}
