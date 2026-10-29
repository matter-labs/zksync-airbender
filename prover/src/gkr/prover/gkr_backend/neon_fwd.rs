//! NEON SoA kernels of the forward-layer relation archetypes
//! ([`forward`](super::forward)) for the aarch64 BabyBear/Ext4 backend.
//!
//! Layout: every kernel walks the trace in blocks of 4 rows. The 4 rows of an
//! `Ext4` column are ONE `ld4` (`vld4q_u32`), which de-interleaves the 64 B
//! into the four limb vectors (SoA: lane = row); the outputs go back through
//! `st4`. Base columns are plain 16 B loads. Arithmetic reuses the lazy
//! Montgomery machinery of the same-size kernels
//! ([`neon_w3`](super::neon_w3)): raw `u64` cross products accumulated per
//! limb, a conditional subtract after every four, ONE REDC per output limb
//! (`ext_mul_lazy`), lane-indexed `umlal` for ext-by-base products. Values are
//! identical to the scalar maps (canonical field elements), checked by the
//! A/B tests at the bottom.

use super::super::sumcheck_loop::windowed_mode::neon::{add4, mont_mul4, soa_r11v, sub4};
use super::forward;
use super::neon_w3::{condsub4, ext_mul_lazy, mla4, r_mont, redc4, Acc};
use super::AffinePlan;
use ::field::baby_bear::{base::BabyBearField, ext4::BabyBearExt4};
use ::field::{Field, PrimeField};
use core::arch::aarch64::*;
use core::mem::MaybeUninit;
use worker::Worker;

pub(super) type BB = BabyBearField;
pub(super) type E4 = BabyBearExt4;
type Limbs = [uint32x4_t; 4];

/// Below this many rows the scalar maps run (block/thread overheads).
const VECTOR_MIN_ROWS: usize = 64;

#[inline(always)]
fn vector_applicable(n: usize) -> bool {
    n >= VECTOR_MIN_ROWS && n % 4 == 0
}

#[inline(always)]
unsafe fn ld_ext(p: *const E4) -> Limbs {
    let v = vld4q_u32(p as *const u32);
    [v.0, v.1, v.2, v.3]
}

#[inline(always)]
unsafe fn st_ext(p: *mut MaybeUninit<E4>, l: Limbs) {
    vst4q_u32(p as *mut u32, uint32x4x4_t(l[0], l[1], l[2], l[3]));
}

#[inline(always)]
unsafe fn ld_base(p: *const BB) -> uint32x4_t {
    vld1q_u32(p as *const u32)
}

#[inline(always)]
unsafe fn bcast_ext(e: &E4) -> Limbs {
    let p = e as *const E4 as *const u32;
    core::array::from_fn(|l| vdupq_n_u32(*p.add(l)))
}

#[inline(always)]
unsafe fn add_ext(a: &Limbs, b: &Limbs) -> Limbs {
    core::array::from_fn(|l| add4(a[l], b[l]))
}

#[inline(always)]
unsafe fn sub_ext(a: &Limbs, b: &Limbs) -> Limbs {
    core::array::from_fn(|l| sub4(a[l], b[l]))
}

/// `e * t` for an ext vector group and a base vector (4 canonical products).
#[inline(always)]
unsafe fn mul_ext_base(e: &Limbs, t: uint32x4_t) -> Limbs {
    core::array::from_fn(|l| mont_mul4(e[l], t))
}

/// `base + γ` as an ext vector group: limb 0 adds, limbs 1..3 are γ's.
#[inline(always)]
unsafe fn base_plus_ext(b: uint32x4_t, g: &Limbs) -> Limbs {
    [add4(b, g[0]), g[1], g[2], g[3]]
}

/// `a (x) b + c (x) d` with one REDC per limb: both products' raw cross terms
/// (8 per limb) share the accumulators, with a condsub after every SECOND
/// raw product — the lazy range rule (`R P + 2 P^2 < 2^64`, see `neon_w3`).
/// A condsub only after the first four let the sum reach `R P + 4 P^2 >
/// 2^64` and wrap on rare rows (non-canonical or wrong limbs in the
/// lookup-pair outputs; found by the output-substitution self-check).
#[inline(always)]
unsafe fn ext_mul2_lazy(a: &Limbs, b: &Limbs, c: &Limbs, d: &Limbs, r11v: uint32x4_t) -> Limbs {
    let b1s = mont_mul4(b[1], r11v);
    let b2s = mont_mul4(b[2], r11v);
    let b3s = mont_mul4(b[3], r11v);
    let d1s = mont_mul4(d[1], r11v);
    let d2s = mont_mul4(d[2], r11v);
    let d3s = mont_mul4(d[3], r11v);
    // the 8 (x, y) raw products of one output limb, condsub after each pair
    #[inline(always)]
    unsafe fn limb(terms: [(uint32x4_t, uint32x4_t); 8]) -> uint32x4_t {
        let mut l = Acc::zero();
        for (k, (x, y)) in terms.iter().enumerate() {
            l.mla(*x, *y);
            if k % 2 == 1 && k < 7 {
                l.condsub();
            }
        }
        l.redc()
    }
    [
        limb([
            (a[0], b[0]),
            (a[1], b1s),
            (a[2], b3s),
            (a[3], b2s),
            (c[0], d[0]),
            (c[1], d1s),
            (c[2], d3s),
            (c[3], d2s),
        ]),
        limb([
            (a[0], b[1]),
            (a[1], b[0]),
            (a[2], b[2]),
            (a[3], b3s),
            (c[0], d[1]),
            (c[1], d[0]),
            (c[2], d[2]),
            (c[3], d3s),
        ]),
        limb([
            (a[0], b[2]),
            (a[2], b[0]),
            (a[1], b3s),
            (a[3], b1s),
            (c[0], d[2]),
            (c[2], d[0]),
            (c[1], d3s),
            (c[3], d1s),
        ]),
        limb([
            (a[0], b[3]),
            (a[1], b[2]),
            (a[2], b[1]),
            (a[3], b[0]),
            (c[0], d[3]),
            (c[1], d[2]),
            (c[2], d[1]),
            (c[3], d[0]),
        ]),
    ]
}

/// Rows per dynamically scheduled task (2^23 rows -> 1024 tasks): the
/// kernels take milliseconds per column, so a statically chunked scope is at
/// the mercy of one slow (efficiency-core) thread; small work-stolen tasks
/// are not.
const ROWS_PER_TASK: usize = 8192;

/// Row ranges (multiples of 4) over the worker pool: `f(first_row, end_row)`.
fn par_blocks(n: usize, worker: &Worker, f: impl Fn(usize, usize) + Sync) {
    use worker::rayon::prelude::*;
    debug_assert_eq!(n % 4, 0);
    let tasks = n.div_ceil(ROWS_PER_TASK);
    let f = &f;
    worker.pool.install(|| {
        (0..tasks).into_par_iter().for_each(|t| {
            let start = t * ROWS_PER_TASK;
            let end = (start + ROWS_PER_TASK).min(n);
            f(start, end)
        })
    });
}

/// Shared raw column pointer (whole-struct capture: closures must call
/// `get()`, not read the field, or edition-2021 disjoint capture takes the
/// bare pointer and loses `Sync`).
#[derive(Clone, Copy)]
struct P<T>(*const T);
unsafe impl<T> Send for P<T> {}
unsafe impl<T> Sync for P<T> {}
impl<T> P<T> {
    #[inline(always)]
    fn get(&self) -> *const T {
        self.0
    }
}
#[derive(Clone, Copy)]
struct PM<T>(*mut MaybeUninit<T>);
unsafe impl<T> Send for PM<T> {}
unsafe impl<T> Sync for PM<T> {}
impl<T> PM<T> {
    #[inline(always)]
    fn get(&self) -> *mut MaybeUninit<T> {
        self.0
    }
}

// ---------------------------------------------------------------------------
// kernels
// ---------------------------------------------------------------------------

pub(super) fn rational_pair_add(
    a: &[E4],
    b: &[E4],
    c: &[E4],
    d: &[E4],
    num: &mut [MaybeUninit<E4>],
    den: &mut [MaybeUninit<E4>],
    worker: &Worker,
) {
    let n = a.len();
    assert!(b.len() == n && c.len() == n && d.len() == n && num.len() == n && den.len() == n);
    if !vector_applicable(n) {
        return forward::rational_pair_add::<BB, E4>(a, b, c, d, num, den, worker);
    }
    let (a, b, c, d) = (P(a.as_ptr()), P(b.as_ptr()), P(c.as_ptr()), P(d.as_ptr()));
    let (num, den) = (PM(num.as_mut_ptr()), PM(den.as_mut_ptr()));
    par_blocks(n, worker, |s, e| unsafe {
        let r11v = soa_r11v();
        let mut i = s;
        while i < e {
            let av = ld_ext(a.get().add(i));
            let bv = ld_ext(b.get().add(i));
            let cv = ld_ext(c.get().add(i));
            let dv = ld_ext(d.get().add(i));
            st_ext(num.get().add(i), ext_mul2_lazy(&av, &dv, &cv, &bv, r11v));
            st_ext(den.get().add(i), ext_mul_lazy(&bv, &dv, r11v));
            i += 4;
        }
    });
}

pub(super) fn ext_product(a: &[E4], b: &[E4], out: &mut [MaybeUninit<E4>], worker: &Worker) {
    let n = a.len();
    assert!(b.len() == n && out.len() == n);
    if !vector_applicable(n) {
        return forward::ext_product::<BB, E4>(a, b, out, worker);
    }
    let (a, b, out) = (P(a.as_ptr()), P(b.as_ptr()), PM(out.as_mut_ptr()));
    par_blocks(n, worker, |s, e| unsafe {
        let r11v = soa_r11v();
        let mut i = s;
        while i < e {
            let av = ld_ext(a.get().add(i));
            let bv = ld_ext(b.get().add(i));
            st_ext(out.get().add(i), ext_mul_lazy(&av, &bv, r11v));
            i += 4;
        }
    });
}

pub(super) fn base_pair_lookup(
    b: &[BB],
    d: &[BB],
    gamma: E4,
    num: &mut [MaybeUninit<E4>],
    den: &mut [MaybeUninit<E4>],
    worker: &Worker,
) {
    let n = b.len();
    assert!(d.len() == n && num.len() == n && den.len() == n);
    if !vector_applicable(n) {
        return forward::base_pair_lookup::<BB, E4>(b, d, gamma, num, den, worker);
    }
    let (b, d) = (P(b.as_ptr()), P(d.as_ptr()));
    let (num, den) = (PM(num.as_mut_ptr()), PM(den.as_mut_ptr()));
    par_blocks(n, worker, |s, e| unsafe {
        let r11v = soa_r11v();
        let g = bcast_ext(&gamma);
        let mut i = s;
        while i < e {
            let bg = base_plus_ext(ld_base(b.get().add(i)), &g);
            let dg = base_plus_ext(ld_base(d.get().add(i)), &g);
            st_ext(num.get().add(i), add_ext(&bg, &dg));
            st_ext(den.get().add(i), ext_mul_lazy(&bg, &dg, r11v));
            i += 4;
        }
    });
}

pub(super) fn ext_pair_lookup(
    b: &[E4],
    d: &[E4],
    gamma: E4,
    num: &mut [MaybeUninit<E4>],
    den: &mut [MaybeUninit<E4>],
    worker: &Worker,
) {
    let n = b.len();
    assert!(d.len() == n && num.len() == n && den.len() == n);
    if !vector_applicable(n) {
        return forward::ext_pair_lookup::<BB, E4>(b, d, gamma, num, den, worker);
    }
    let (b, d) = (P(b.as_ptr()), P(d.as_ptr()));
    let (num, den) = (PM(num.as_mut_ptr()), PM(den.as_mut_ptr()));
    par_blocks(n, worker, |s, e| unsafe {
        let r11v = soa_r11v();
        let g = bcast_ext(&gamma);
        let mut i = s;
        while i < e {
            let bg = add_ext(&ld_ext(b.get().add(i)), &g);
            let dg = add_ext(&ld_ext(d.get().add(i)), &g);
            st_ext(num.get().add(i), add_ext(&bg, &dg));
            st_ext(den.get().add(i), ext_mul_lazy(&bg, &dg, r11v));
            i += 4;
        }
    });
}

pub(super) fn unbalanced_base_lookup(
    a: &[E4],
    b: &[E4],
    d: &[BB],
    gamma: E4,
    num: &mut [MaybeUninit<E4>],
    den: &mut [MaybeUninit<E4>],
    worker: &Worker,
) {
    let n = a.len();
    assert!(b.len() == n && d.len() == n && num.len() == n && den.len() == n);
    if !vector_applicable(n) {
        return forward::unbalanced_base_lookup::<BB, E4>(a, b, d, gamma, num, den, worker);
    }
    let (a, b, d) = (P(a.as_ptr()), P(b.as_ptr()), P(d.as_ptr()));
    let (num, den) = (PM(num.as_mut_ptr()), PM(den.as_mut_ptr()));
    par_blocks(n, worker, |s, e| unsafe {
        let r11v = soa_r11v();
        let g = bcast_ext(&gamma);
        let mut i = s;
        while i < e {
            let av = ld_ext(a.get().add(i));
            let bv = ld_ext(b.get().add(i));
            let dg = base_plus_ext(ld_base(d.get().add(i)), &g);
            st_ext(
                num.get().add(i),
                add_ext(&ext_mul_lazy(&av, &dg, r11v), &bv),
            );
            st_ext(den.get().add(i), ext_mul_lazy(&bv, &dg, r11v));
            i += 4;
        }
    });
}

pub(super) fn unbalanced_ext_lookup(
    a: &[E4],
    b: &[E4],
    d: &[E4],
    gamma: E4,
    num: &mut [MaybeUninit<E4>],
    den: &mut [MaybeUninit<E4>],
    worker: &Worker,
) {
    let n = a.len();
    assert!(b.len() == n && d.len() == n && num.len() == n && den.len() == n);
    if !vector_applicable(n) {
        return forward::unbalanced_ext_lookup::<BB, E4>(a, b, d, gamma, num, den, worker);
    }
    let (a, b, d) = (P(a.as_ptr()), P(b.as_ptr()), P(d.as_ptr()));
    let (num, den) = (PM(num.as_mut_ptr()), PM(den.as_mut_ptr()));
    par_blocks(n, worker, |s, e| unsafe {
        let r11v = soa_r11v();
        let g = bcast_ext(&gamma);
        let mut i = s;
        while i < e {
            let av = ld_ext(a.get().add(i));
            let bv = ld_ext(b.get().add(i));
            let dg = add_ext(&ld_ext(d.get().add(i)), &g);
            st_ext(
                num.get().add(i),
                add_ext(&ext_mul_lazy(&av, &dg, r11v), &bv),
            );
            st_ext(den.get().add(i), ext_mul_lazy(&bv, &dg, r11v));
            i += 4;
        }
    });
}

pub(super) fn base_lookup_minus_setup(
    b: &[BB],
    c: &[BB],
    d: &[BB],
    gamma: E4,
    num: &mut [MaybeUninit<E4>],
    den: &mut [MaybeUninit<E4>],
    worker: &Worker,
) {
    let n = b.len();
    assert!(c.len() == n && d.len() == n && num.len() == n && den.len() == n);
    if !vector_applicable(n) {
        return forward::base_lookup_minus_setup::<BB, E4>(b, c, d, gamma, num, den, worker);
    }
    let (b, c, d) = (P(b.as_ptr()), P(c.as_ptr()), P(d.as_ptr()));
    let (num, den) = (PM(num.as_mut_ptr()), PM(den.as_mut_ptr()));
    par_blocks(n, worker, |s, e| unsafe {
        let r11v = soa_r11v();
        let g = bcast_ext(&gamma);
        let mut i = s;
        while i < e {
            let bg = base_plus_ext(ld_base(b.get().add(i)), &g);
            let dg = base_plus_ext(ld_base(d.get().add(i)), &g);
            let cb = mul_ext_base(&bg, ld_base(c.get().add(i)));
            st_ext(num.get().add(i), sub_ext(&dg, &cb));
            st_ext(den.get().add(i), ext_mul_lazy(&bg, &dg, r11v));
            i += 4;
        }
    });
}

pub(super) fn masked_ext_lookup_minus_setup(
    a: &[BB],
    c: &[BB],
    b: &[E4],
    d: &[E4],
    gamma: E4,
    num: &mut [MaybeUninit<E4>],
    den: &mut [MaybeUninit<E4>],
    worker: &Worker,
) {
    let n = a.len();
    assert!(b.len() == n && c.len() == n && d.len() == n && num.len() == n && den.len() == n);
    if !vector_applicable(n) {
        return forward::masked_ext_lookup_minus_setup::<BB, E4>(
            a, c, b, d, gamma, num, den, worker,
        );
    }
    let (a, c, b, d) = (P(a.as_ptr()), P(c.as_ptr()), P(b.as_ptr()), P(d.as_ptr()));
    let (num, den) = (PM(num.as_mut_ptr()), PM(den.as_mut_ptr()));
    par_blocks(n, worker, |s, e| unsafe {
        let r11v = soa_r11v();
        let g = bcast_ext(&gamma);
        let mut i = s;
        while i < e {
            let bg = add_ext(&ld_ext(b.get().add(i)), &g);
            let dg = add_ext(&ld_ext(d.get().add(i)), &g);
            let ad = mul_ext_base(&dg, ld_base(a.get().add(i)));
            let cb = mul_ext_base(&bg, ld_base(c.get().add(i)));
            st_ext(num.get().add(i), sub_ext(&ad, &cb));
            st_ext(den.get().add(i), ext_mul_lazy(&bg, &dg, r11v));
            i += 4;
        }
    });
}

pub(super) fn mask_into_identity(
    mask: &[BB],
    value: &[E4],
    out: &mut [MaybeUninit<E4>],
    worker: &Worker,
) {
    let n = mask.len();
    assert!(value.len() == n && out.len() == n);
    if !vector_applicable(n) {
        return forward::mask_into_identity::<BB, E4>(mask, value, out, worker);
    }
    let (mask, value, out) = (P(mask.as_ptr()), P(value.as_ptr()), PM(out.as_mut_ptr()));
    par_blocks(n, worker, |s, e| unsafe {
        let one = r_mont();
        let zero = vdupq_n_u32(0);
        let mut i = s;
        while i < e {
            let m = ld_base(mask.get().add(i));
            let v = ld_ext(value.get().add(i));
            // boolean mask: 0 -> ONE, otherwise the value
            let is_zero = vceqq_u32(m, zero);
            st_ext(
                out.get().add(i),
                [
                    vbslq_u32(is_zero, one, v[0]),
                    vbslq_u32(is_zero, zero, v[1]),
                    vbslq_u32(is_zero, zero, v[2]),
                    vbslq_u32(is_zero, zero, v[3]),
                ],
            );
            i += 4;
        }
    });
}

// ---------------------------------------------------------------------------
// affine plans
// ---------------------------------------------------------------------------

struct NeonTerm {
    /// Broadcast-ready challenge limbs (`None`: base-field term).
    challenge: Option<uint32x4_t>,
    /// `(raw Montgomery coefficient, is_one, column pointer)`.
    columns: Vec<(u32, bool, P<BB>)>,
    constant: u32,
}
unsafe impl Send for NeonTerm {}
unsafe impl Sync for NeonTerm {}

struct NeonPlan {
    additive: Limbs,
    terms: Vec<NeonTerm>,
}
unsafe impl Send for NeonPlan {}
unsafe impl Sync for NeonPlan {}

impl NeonPlan {
    unsafe fn new(plan: &AffinePlan<BB, E4>, columns: &[&[BB]]) -> Self {
        let terms = plan
            .terms
            .iter()
            .map(|t| NeonTerm {
                challenge: t
                    .challenge
                    .map(|c| vld1q_u32(&c as *const E4 as *const u32)),
                columns: t
                    .columns
                    .iter()
                    .map(|(coef, col)| {
                        (
                            coef.raw_u32_value(),
                            *coef == BB::ONE,
                            P(columns[*col].as_ptr()),
                        )
                    })
                    .collect(),
                constant: t.constant.raw_u32_value(),
            })
            .collect();
        Self {
            additive: bcast_ext(&plan.additive),
            terms,
        }
    }

    /// The plan's canonical value for rows `i .. i + 4`.
    #[inline(always)]
    unsafe fn eval(&self, i: usize) -> Limbs {
        let mut acc = [Acc::zero(), Acc::zero(), Acc::zero(), Acc::zero()];
        let rm = r_mont();
        let mut since_condsub = 0usize;
        for term in self.terms.iter() {
            let mut a = vdupq_n_u32(term.constant);
            for (coef, is_one, col) in term.columns.iter() {
                let v = ld_base(col.get().add(i));
                a = add4(
                    a,
                    if *is_one {
                        v
                    } else {
                        mont_mul4(v, vdupq_n_u32(*coef))
                    },
                );
            }
            match term.challenge {
                Some(ch) => mla4(&mut acc, a, ch),
                None => acc[0].mla(a, rm),
            }
            // lazy range rule: a condsub after every second raw product
            // (`R P + 2 P^2 < 2^64`; three let the sum wrap on rare rows)
            since_condsub += 1;
            if since_condsub == 2 {
                condsub4(&mut acc);
                since_condsub = 0;
            }
        }
        add_ext(&redc4(&acc), &self.additive)
    }
}

pub(super) fn affine_plan(
    plan: &AffinePlan<BB, E4>,
    columns: &[&[BB]],
    out: &mut [MaybeUninit<E4>],
    worker: &Worker,
) {
    let n = out.len();
    for c in columns.iter() {
        assert_eq!(c.len(), n);
    }
    if !vector_applicable(n) {
        return forward::affine_plan::<BB, E4>(plan, columns, out, worker);
    }
    let np = unsafe { NeonPlan::new(plan, columns) };
    let out = PM(out.as_mut_ptr());
    par_blocks(n, worker, |s, e| unsafe {
        let mut i = s;
        while i < e {
            st_ext(out.get().add(i), np.eval(i));
            i += 4;
        }
    });
}

pub(super) fn affine_plan_product(
    lhs: &AffinePlan<BB, E4>,
    rhs: &AffinePlan<BB, E4>,
    columns: &[&[BB]],
    out: &mut [MaybeUninit<E4>],
    worker: &Worker,
) {
    let n = out.len();
    for c in columns.iter() {
        assert_eq!(c.len(), n);
    }
    if !vector_applicable(n) {
        return forward::affine_plan_product::<BB, E4>(lhs, rhs, columns, out, worker);
    }
    let (nl, nr) = unsafe { (NeonPlan::new(lhs, columns), NeonPlan::new(rhs, columns)) };
    let out = PM(out.as_mut_ptr());
    par_blocks(n, worker, |s, e| unsafe {
        let r11v = soa_r11v();
        let mut i = s;
        while i < e {
            let l = nl.eval(i);
            let r = nr.eval(i);
            st_ext(out.get().add(i), ext_mul_lazy(&l, &r, r11v));
            i += 4;
        }
    });
}

// ---------------------------------------------------------------------------
// A/B against the scalar maps
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    const PR: u64 = 0x7800_0001;

    fn splitmix(state: &mut u64) -> u64 {
        *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = *state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn rb(st: &mut u64) -> BB {
        BB::new((splitmix(st) % PR) as u32)
    }

    fn re(st: &mut u64) -> E4 {
        E4::from_array_of_base(core::array::from_fn(|_| rb(st)))
    }

    fn base_col(n: usize, st: &mut u64) -> Vec<BB> {
        (0..n).map(|_| rb(st)).collect()
    }

    fn ext_col(n: usize, st: &mut u64) -> Vec<E4> {
        (0..n).map(|_| re(st)).collect()
    }

    fn bool_col(n: usize, st: &mut u64) -> Vec<BB> {
        (0..n)
            .map(|_| {
                if splitmix(st) & 1 == 0 {
                    BB::ZERO
                } else {
                    BB::ONE
                }
            })
            .collect()
    }

    fn out(n: usize) -> Vec<MaybeUninit<E4>> {
        vec![MaybeUninit::uninit(); n]
    }

    fn init(v: Vec<MaybeUninit<E4>>) -> Vec<E4> {
        v.into_iter().map(|x| unsafe { x.assume_init() }).collect()
    }

    const N: usize = 1 << 10;

    #[test]
    fn rational_pair_add_matches_scalar() {
        let worker = Worker::new_with_num_threads(3);
        let mut st = 1u64;
        let (a, b, c, d) = (
            ext_col(N, &mut st),
            ext_col(N, &mut st),
            ext_col(N, &mut st),
            ext_col(N, &mut st),
        );
        let (mut n0, mut d0, mut n1, mut d1) = (out(N), out(N), out(N), out(N));
        forward::rational_pair_add::<BB, E4>(&a, &b, &c, &d, &mut n0, &mut d0, &worker);
        rational_pair_add(&a, &b, &c, &d, &mut n1, &mut d1, &worker);
        assert_eq!(init(n0), init(n1));
        assert_eq!(init(d0), init(d1));
    }

    #[test]
    fn ext_product_matches_scalar() {
        let worker = Worker::new_with_num_threads(3);
        let mut st = 2u64;
        let (a, b) = (ext_col(N, &mut st), ext_col(N, &mut st));
        let (mut o0, mut o1) = (out(N), out(N));
        forward::ext_product::<BB, E4>(&a, &b, &mut o0, &worker);
        ext_product(&a, &b, &mut o1, &worker);
        assert_eq!(init(o0), init(o1));
    }

    #[test]
    fn pair_lookups_match_scalar() {
        let worker = Worker::new_with_num_threads(3);
        let mut st = 3u64;
        let g = re(&mut st);
        let (b, d) = (base_col(N, &mut st), base_col(N, &mut st));
        let (mut n0, mut d0, mut n1, mut d1) = (out(N), out(N), out(N), out(N));
        forward::base_pair_lookup::<BB, E4>(&b, &d, g, &mut n0, &mut d0, &worker);
        base_pair_lookup(&b, &d, g, &mut n1, &mut d1, &worker);
        assert_eq!(init(n0), init(n1));
        assert_eq!(init(d0), init(d1));
        let (be, de) = (ext_col(N, &mut st), ext_col(N, &mut st));
        let (mut n0, mut d0, mut n1, mut d1) = (out(N), out(N), out(N), out(N));
        forward::ext_pair_lookup::<BB, E4>(&be, &de, g, &mut n0, &mut d0, &worker);
        ext_pair_lookup(&be, &de, g, &mut n1, &mut d1, &worker);
        assert_eq!(init(n0), init(n1));
        assert_eq!(init(d0), init(d1));
    }

    #[test]
    fn unbalanced_lookups_match_scalar() {
        let worker = Worker::new_with_num_threads(3);
        let mut st = 4u64;
        let g = re(&mut st);
        let (a, b) = (ext_col(N, &mut st), ext_col(N, &mut st));
        let db = base_col(N, &mut st);
        let (mut n0, mut d0, mut n1, mut d1) = (out(N), out(N), out(N), out(N));
        forward::unbalanced_base_lookup::<BB, E4>(&a, &b, &db, g, &mut n0, &mut d0, &worker);
        unbalanced_base_lookup(&a, &b, &db, g, &mut n1, &mut d1, &worker);
        assert_eq!(init(n0), init(n1));
        assert_eq!(init(d0), init(d1));
        let de = ext_col(N, &mut st);
        let (mut n0, mut d0, mut n1, mut d1) = (out(N), out(N), out(N), out(N));
        forward::unbalanced_ext_lookup::<BB, E4>(&a, &b, &de, g, &mut n0, &mut d0, &worker);
        unbalanced_ext_lookup(&a, &b, &de, g, &mut n1, &mut d1, &worker);
        assert_eq!(init(n0), init(n1));
        assert_eq!(init(d0), init(d1));
    }

    #[test]
    fn setup_lookups_match_scalar() {
        let worker = Worker::new_with_num_threads(3);
        let mut st = 5u64;
        let g = re(&mut st);
        let (b, c, d) = (
            base_col(N, &mut st),
            base_col(N, &mut st),
            base_col(N, &mut st),
        );
        let (mut n0, mut d0, mut n1, mut d1) = (out(N), out(N), out(N), out(N));
        forward::base_lookup_minus_setup::<BB, E4>(&b, &c, &d, g, &mut n0, &mut d0, &worker);
        base_lookup_minus_setup(&b, &c, &d, g, &mut n1, &mut d1, &worker);
        assert_eq!(init(n0), init(n1));
        assert_eq!(init(d0), init(d1));
        let (be, de) = (ext_col(N, &mut st), ext_col(N, &mut st));
        let (mut n0, mut d0, mut n1, mut d1) = (out(N), out(N), out(N), out(N));
        forward::masked_ext_lookup_minus_setup::<BB, E4>(
            &b, &c, &be, &de, g, &mut n0, &mut d0, &worker,
        );
        masked_ext_lookup_minus_setup(&b, &c, &be, &de, g, &mut n1, &mut d1, &worker);
        assert_eq!(init(n0), init(n1));
        assert_eq!(init(d0), init(d1));
    }

    #[test]
    fn mask_into_identity_matches_scalar() {
        let worker = Worker::new_with_num_threads(3);
        let mut st = 6u64;
        let m = bool_col(N, &mut st);
        let v = ext_col(N, &mut st);
        let (mut o0, mut o1) = (out(N), out(N));
        forward::mask_into_identity::<BB, E4>(&m, &v, &mut o0, &worker);
        mask_into_identity(&m, &v, &mut o1, &worker);
        assert_eq!(init(o0), init(o1));
    }

    fn random_plan(st: &mut u64, num_cols: usize) -> AffinePlan<BB, E4> {
        let mut plan = AffinePlan::new(re(st));
        for k in 0..7 {
            let cols: Vec<(BB, usize)> = (0..(1 + k % 3))
                .map(|j| {
                    let coef = if j == 0 { BB::ONE } else { rb(st) };
                    (coef, (splitmix(st) as usize) % num_cols)
                })
                .collect();
            let constant = if k % 2 == 0 { BB::ZERO } else { rb(st) };
            if k == 2 {
                plan.base(cols, constant);
            } else {
                plan.linear(re(st), cols, constant);
            }
        }
        plan
    }

    #[test]
    fn affine_plans_match_scalar() {
        let worker = Worker::new_with_num_threads(3);
        let mut st = 7u64;
        let cols: Vec<Vec<BB>> = (0..9).map(|_| base_col(N, &mut st)).collect();
        let refs: Vec<&[BB]> = cols.iter().map(|c| &c[..]).collect();
        let (pl, pr) = (random_plan(&mut st, 9), random_plan(&mut st, 9));
        let (mut o0, mut o1) = (out(N), out(N));
        forward::affine_plan::<BB, E4>(&pl, &refs, &mut o0, &worker);
        affine_plan(&pl, &refs, &mut o1, &worker);
        assert_eq!(init(o0), init(o1));
        let (mut o0, mut o1) = (out(N), out(N));
        forward::affine_plan_product::<BB, E4>(&pl, &pr, &refs, &mut o0, &worker);
        affine_plan_product(&pl, &pr, &refs, &mut o1, &worker);
        assert_eq!(init(o0), init(o1));
    }

    /// Single-thread scalar vs NEON cost per row of every archetype
    /// (`FWD_BENCH_LOG2`, default 20; min of 3). `#[ignore]`d.
    #[test]
    #[ignore]
    fn forward_kernels_bench() {
        let log2: usize = std::env::var("FWD_BENCH_LOG2")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(20);
        let n = 1usize << log2;
        let worker = Worker::new_with_num_threads(1);
        let mut st = 11u64;
        let g = re(&mut st);
        let (a, b, c, d) = (
            ext_col(n, &mut st),
            ext_col(n, &mut st),
            ext_col(n, &mut st),
            ext_col(n, &mut st),
        );
        let (bb, cb, db) = (
            base_col(n, &mut st),
            base_col(n, &mut st),
            base_col(n, &mut st),
        );
        let mb = bool_col(n, &mut st);
        let cols: Vec<Vec<BB>> = (0..12).map(|_| base_col(n, &mut st)).collect();
        let refs: Vec<&[BB]> = cols.iter().map(|c| &c[..]).collect();
        let (pl, pr) = (random_plan(&mut st, 12), random_plan(&mut st, 12));
        let mut o0 = out(n);
        let mut o1 = out(n);
        let mut time =
            |name: &str,
             scalar: &dyn Fn(&mut [MaybeUninit<E4>], &mut [MaybeUninit<E4>]),
             neon: &dyn Fn(&mut [MaybeUninit<E4>], &mut [MaybeUninit<E4>])| {
                let mut best = [f64::MAX; 2];
                for _ in 0..3 {
                    let t = std::time::Instant::now();
                    scalar(&mut o0, &mut o1);
                    best[0] = best[0].min(t.elapsed().as_secs_f64());
                    let t = std::time::Instant::now();
                    neon(&mut o0, &mut o1);
                    best[1] = best[1].min(t.elapsed().as_secs_f64());
                }
                println!(
                    "[fwd-bench] {name:<28} scalar {:7.2} ns/row  neon {:6.2} ns/row  {:4.2}x",
                    best[0] * 1e9 / n as f64,
                    best[1] * 1e9 / n as f64,
                    best[0] / best[1]
                );
            };
        let w = &worker;
        time(
            "rational_pair_add",
            &|x, y| forward::rational_pair_add::<BB, E4>(&a, &b, &c, &d, x, y, w),
            &|x, y| rational_pair_add(&a, &b, &c, &d, x, y, w),
        );
        time(
            "ext_product",
            &|x, _| forward::ext_product::<BB, E4>(&a, &b, x, w),
            &|x, _| ext_product(&a, &b, x, w),
        );
        time(
            "base_pair_lookup",
            &|x, y| forward::base_pair_lookup::<BB, E4>(&bb, &db, g, x, y, w),
            &|x, y| base_pair_lookup(&bb, &db, g, x, y, w),
        );
        time(
            "ext_pair_lookup",
            &|x, y| forward::ext_pair_lookup::<BB, E4>(&a, &b, g, x, y, w),
            &|x, y| ext_pair_lookup(&a, &b, g, x, y, w),
        );
        time(
            "unbalanced_base_lookup",
            &|x, y| forward::unbalanced_base_lookup::<BB, E4>(&a, &b, &db, g, x, y, w),
            &|x, y| unbalanced_base_lookup(&a, &b, &db, g, x, y, w),
        );
        time(
            "unbalanced_ext_lookup",
            &|x, y| forward::unbalanced_ext_lookup::<BB, E4>(&a, &b, &d, g, x, y, w),
            &|x, y| unbalanced_ext_lookup(&a, &b, &d, g, x, y, w),
        );
        time(
            "base_lookup_minus_setup",
            &|x, y| forward::base_lookup_minus_setup::<BB, E4>(&bb, &cb, &db, g, x, y, w),
            &|x, y| base_lookup_minus_setup(&bb, &cb, &db, g, x, y, w),
        );
        time(
            "masked_ext_lookup_minus_setup",
            &|x, y| forward::masked_ext_lookup_minus_setup::<BB, E4>(&bb, &cb, &a, &b, g, x, y, w),
            &|x, y| masked_ext_lookup_minus_setup(&bb, &cb, &a, &b, g, x, y, w),
        );
        time(
            "mask_into_identity",
            &|x, _| forward::mask_into_identity::<BB, E4>(&mb, &a, x, w),
            &|x, _| mask_into_identity(&mb, &a, x, w),
        );
        time(
            "affine_plan (7 terms)",
            &|x, _| forward::affine_plan::<BB, E4>(&pl, &refs, x, w),
            &|x, _| affine_plan(&pl, &refs, x, w),
        );
        time(
            "affine_plan_product (7+7)",
            &|x, _| forward::affine_plan_product::<BB, E4>(&pl, &pr, &refs, x, w),
            &|x, _| affine_plan_product(&pl, &pr, &refs, x, w),
        );
    }
}
