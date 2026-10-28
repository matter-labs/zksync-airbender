//! Forward-layer (output-construction) relation ARCHETYPES behind the
//! [`GKRBackend`](super::GKRBackend) seam: the row-wise maps every GKR layer
//! evaluates to materialize the next layer's polynomials. Every forward
//! relation of the compiled circuits is one of a handful of shapes:
//!
//! - rational-pair add `a/b + c/d -> (a d + c b, b d)` over extension inputs;
//! - the lookup fraction adds over base or extension inputs
//!   `1/(b+γ) + 1/(d+γ) -> ((b+γ) + (d+γ), (b+γ)(d+γ))` and their unbalanced
//!   (`a/b + 1/(d+γ)`) and setup-subtracting (`1/(b+γ) - c/(d+γ)`,
//!   `a/(b+γ) - c/(d+γ)`) variants;
//! - extension products and the mask-into-identity product;
//! - the "affine plan" of the memory argument: `additive + Σ_k ch_k ·
//!   (const_k + Σ_j coef_kj · col_kj)` over base columns (memory tuples, the
//!   inits/teardowns tuples, grand-product term expressions), possibly the
//!   product of two such plans.
//!
//! This module holds the shape descriptions and the PORTABLE scalar
//! implementations the trait's default methods run; arch backends override
//! the methods with SoA kernels. The contract is value equality: outputs are
//! field elements, so any correct evaluation order is byte-identical.

use core::mem::MaybeUninit;
use field::{Field, FieldExtension, PrimeField};
use worker::Worker;

/// One linear term of an [`AffinePlan`]: `challenge · (constant + Σ coef · col)`
/// (`challenge == None`: the base-field sum is added to the result directly).
#[derive(Clone, Debug)]
pub struct AffineTerm<F: PrimeField, E: FieldExtension<F> + Field> {
    pub challenge: Option<E>,
    /// `(coefficient, column index into the caller's column table)`.
    pub columns: Vec<(F, usize)>,
    pub constant: F,
}

/// `additive + Σ terms` over a table of base columns.
#[derive(Clone, Debug)]
pub struct AffinePlan<F: PrimeField, E: FieldExtension<F> + Field> {
    pub additive: E,
    pub terms: Vec<AffineTerm<F, E>>,
}

impl<F: PrimeField, E: FieldExtension<F> + Field> AffinePlan<F, E> {
    pub fn new(additive: E) -> Self {
        Self {
            additive,
            terms: Vec::new(),
        }
    }

    /// `challenge · (constant + Σ coef · col)`.
    pub fn linear(&mut self, challenge: E, columns: Vec<(F, usize)>, constant: F) {
        self.terms.push(AffineTerm {
            challenge: Some(challenge),
            columns,
            constant,
        });
    }

    /// `constant + Σ coef · col` added as a base-field value.
    pub fn base(&mut self, columns: Vec<(F, usize)>, constant: F) {
        self.terms.push(AffineTerm {
            challenge: None,
            columns,
            constant,
        });
    }

    #[inline(always)]
    pub fn eval_row(&self, row: usize, columns: &[&[F]]) -> E {
        let mut acc = self.additive;
        for term in self.terms.iter() {
            let mut a = term.constant;
            for (coef, col) in term.columns.iter() {
                let mut v = unsafe { *columns.get_unchecked(*col).get_unchecked(row) };
                if *coef != F::ONE {
                    v.mul_assign(coef);
                }
                a.add_assign(&v);
            }
            match term.challenge {
                Some(ch) => {
                    let mut t = ch;
                    t.mul_assign_by_base(&a);
                    acc.add_assign(&t);
                }
                None => {
                    acc.add_assign_base(&a);
                }
            }
        }
        acc
    }
}

struct OutPtr<T>(*mut MaybeUninit<T>);
impl<T> Clone for OutPtr<T> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<T> Copy for OutPtr<T> {}
unsafe impl<T> Send for OutPtr<T> {}
unsafe impl<T> Sync for OutPtr<T> {}

/// Row-chunked parallel map into `N` uninitialized output columns; `f(row)`
/// yields the `N` values of one row.
pub(crate) fn map_rows<E: Send + Sync, const N: usize>(
    trace_len: usize,
    outs: [&mut [MaybeUninit<E>]; N],
    worker: &Worker,
    f: impl Fn(usize) -> [E; N] + Sync,
) {
    for o in outs.iter() {
        assert_eq!(o.len(), trace_len);
    }
    let ptrs: [OutPtr<E>; N] = core::array::from_fn(|k| OutPtr(outs[k].as_ptr() as *mut _));
    let f = &f;
    worker.scope(trace_len, |scope, geometry| {
        for thread_idx in 0..geometry.len() {
            let start = geometry.get_chunk_start_pos(thread_idx);
            let end = start + geometry.get_chunk_size(thread_idx);
            let ptrs = ptrs;
            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                for row in start..end {
                    let v = f(row);
                    for (k, val) in v.into_iter().enumerate() {
                        unsafe { ptrs[k].0.add(row).write(MaybeUninit::new(val)) };
                    }
                }
            });
        }
    });
}

/// `(a d + c b, b d)`.
pub(crate) fn rational_pair_add<F: PrimeField, E: FieldExtension<F> + Field>(
    a: &[E],
    b: &[E],
    c: &[E],
    d: &[E],
    num: &mut [MaybeUninit<E>],
    den: &mut [MaybeUninit<E>],
    worker: &Worker,
) {
    let n = a.len();
    assert!(b.len() == n && c.len() == n && d.len() == n);
    map_rows(n, [num, den], worker, |i| unsafe {
        let (a, b, c, d) = (
            *a.get_unchecked(i),
            *b.get_unchecked(i),
            *c.get_unchecked(i),
            *d.get_unchecked(i),
        );
        let mut num = a;
        num.mul_assign(&d);
        let mut cb = c;
        cb.mul_assign(&b);
        num.add_assign(&cb);
        let mut den = b;
        den.mul_assign(&d);
        [num, den]
    });
}

/// `a b`.
pub(crate) fn ext_product<F: PrimeField, E: FieldExtension<F> + Field>(
    a: &[E],
    b: &[E],
    out: &mut [MaybeUninit<E>],
    worker: &Worker,
) {
    let n = a.len();
    assert_eq!(b.len(), n);
    map_rows(n, [out], worker, |i| unsafe {
        let mut r = *a.get_unchecked(i);
        r.mul_assign(b.get_unchecked(i));
        [r]
    });
}

/// `((b+γ) + (d+γ), (b+γ)(d+γ))` over base inputs.
pub(crate) fn base_pair_lookup<F: PrimeField, E: FieldExtension<F> + Field>(
    b: &[F],
    d: &[F],
    gamma: E,
    num: &mut [MaybeUninit<E>],
    den: &mut [MaybeUninit<E>],
    worker: &Worker,
) {
    let n = b.len();
    assert_eq!(d.len(), n);
    map_rows(n, [num, den], worker, |i| unsafe {
        let mut bg = gamma;
        bg.add_assign_base(b.get_unchecked(i));
        let mut dg = gamma;
        dg.add_assign_base(d.get_unchecked(i));
        let mut num = bg;
        num.add_assign(&dg);
        let mut den = bg;
        den.mul_assign(&dg);
        [num, den]
    });
}

/// `((b+γ) + (d+γ), (b+γ)(d+γ))` over extension inputs.
pub(crate) fn ext_pair_lookup<F: PrimeField, E: FieldExtension<F> + Field>(
    b: &[E],
    d: &[E],
    gamma: E,
    num: &mut [MaybeUninit<E>],
    den: &mut [MaybeUninit<E>],
    worker: &Worker,
) {
    let n = b.len();
    assert_eq!(d.len(), n);
    map_rows(n, [num, den], worker, |i| unsafe {
        let mut bg = *b.get_unchecked(i);
        bg.add_assign(&gamma);
        let mut dg = *d.get_unchecked(i);
        dg.add_assign(&gamma);
        let mut num = bg;
        num.add_assign(&dg);
        let mut den = bg;
        den.mul_assign(&dg);
        [num, den]
    });
}

/// `a/b + 1/(d+γ) -> (a (d+γ) + b, b (d+γ))`, `d` in the base field.
pub(crate) fn unbalanced_base_lookup<F: PrimeField, E: FieldExtension<F> + Field>(
    a: &[E],
    b: &[E],
    d: &[F],
    gamma: E,
    num: &mut [MaybeUninit<E>],
    den: &mut [MaybeUninit<E>],
    worker: &Worker,
) {
    let n = a.len();
    assert!(b.len() == n && d.len() == n);
    map_rows(n, [num, den], worker, |i| unsafe {
        let mut dg = gamma;
        dg.add_assign_base(d.get_unchecked(i));
        let mut num = *a.get_unchecked(i);
        num.mul_assign(&dg);
        num.add_assign(b.get_unchecked(i));
        let mut den = *b.get_unchecked(i);
        den.mul_assign(&dg);
        [num, den]
    });
}

/// `a/b + 1/(d+γ) -> (a (d+γ) + b, b (d+γ))`, `d` in the extension.
pub(crate) fn unbalanced_ext_lookup<F: PrimeField, E: FieldExtension<F> + Field>(
    a: &[E],
    b: &[E],
    d: &[E],
    gamma: E,
    num: &mut [MaybeUninit<E>],
    den: &mut [MaybeUninit<E>],
    worker: &Worker,
) {
    let n = a.len();
    assert!(b.len() == n && d.len() == n);
    map_rows(n, [num, den], worker, |i| unsafe {
        let mut dg = *d.get_unchecked(i);
        dg.add_assign(&gamma);
        let mut num = *a.get_unchecked(i);
        num.mul_assign(&dg);
        num.add_assign(b.get_unchecked(i));
        let mut den = *b.get_unchecked(i);
        den.mul_assign(&dg);
        [num, den]
    });
}

/// `1/(b+γ) - c/(d+γ) -> ((d+γ) - c (b+γ), (b+γ)(d+γ))`, all base inputs.
pub(crate) fn base_lookup_minus_setup<F: PrimeField, E: FieldExtension<F> + Field>(
    b: &[F],
    c: &[F],
    d: &[F],
    gamma: E,
    num: &mut [MaybeUninit<E>],
    den: &mut [MaybeUninit<E>],
    worker: &Worker,
) {
    let n = b.len();
    assert!(c.len() == n && d.len() == n);
    map_rows(n, [num, den], worker, |i| unsafe {
        let mut bg = gamma;
        bg.add_assign_base(b.get_unchecked(i));
        let mut dg = gamma;
        dg.add_assign_base(d.get_unchecked(i));
        let mut cb = bg;
        cb.mul_assign_by_base(c.get_unchecked(i));
        let mut num = dg;
        num.sub_assign(&cb);
        let mut den = bg;
        den.mul_assign(&dg);
        [num, den]
    });
}

/// `a/(b+γ) - c/(d+γ) -> (a (d+γ) - c (b+γ), (b+γ)(d+γ))`, `a, c` base, `b, d` ext.
pub(crate) fn masked_ext_lookup_minus_setup<F: PrimeField, E: FieldExtension<F> + Field>(
    a: &[F],
    c: &[F],
    b: &[E],
    d: &[E],
    gamma: E,
    num: &mut [MaybeUninit<E>],
    den: &mut [MaybeUninit<E>],
    worker: &Worker,
) {
    let n = a.len();
    assert!(b.len() == n && c.len() == n && d.len() == n);
    map_rows(n, [num, den], worker, |i| unsafe {
        let mut bg = *b.get_unchecked(i);
        bg.add_assign(&gamma);
        let mut dg = *d.get_unchecked(i);
        dg.add_assign(&gamma);
        let mut ad = dg;
        ad.mul_assign_by_base(a.get_unchecked(i));
        let mut cb = bg;
        cb.mul_assign_by_base(c.get_unchecked(i));
        let mut num = ad;
        num.sub_assign(&cb);
        let mut den = bg;
        den.mul_assign(&dg);
        [num, den]
    });
}

/// `mask ? value : 1` for a boolean base mask.
pub(crate) fn mask_into_identity<F: PrimeField, E: FieldExtension<F> + Field>(
    mask: &[F],
    value: &[E],
    out: &mut [MaybeUninit<E>],
    worker: &Worker,
) {
    let n = mask.len();
    assert_eq!(value.len(), n);
    map_rows(n, [out], worker, |i| unsafe {
        if mask.get_unchecked(i).as_boolean() {
            [*value.get_unchecked(i)]
        } else {
            [E::ONE]
        }
    });
}

/// One affine plan over the column table.
pub(crate) fn affine_plan<F: PrimeField, E: FieldExtension<F> + Field>(
    plan: &AffinePlan<F, E>,
    columns: &[&[F]],
    out: &mut [MaybeUninit<E>],
    worker: &Worker,
) {
    let n = out.len();
    for c in columns.iter() {
        assert_eq!(c.len(), n);
    }
    map_rows(n, [out], worker, |i| [plan.eval_row(i, columns)]);
}

/// The product of two affine plans over the column table.
pub(crate) fn affine_plan_product<F: PrimeField, E: FieldExtension<F> + Field>(
    lhs: &AffinePlan<F, E>,
    rhs: &AffinePlan<F, E>,
    columns: &[&[F]],
    out: &mut [MaybeUninit<E>],
    worker: &Worker,
) {
    let n = out.len();
    for c in columns.iter() {
        assert_eq!(c.len(), n);
    }
    map_rows(n, [out], worker, |i| {
        let mut r = lhs.eval_row(i, columns);
        r.mul_assign(&rhs.eval_row(i, columns));
        [r]
    });
}
