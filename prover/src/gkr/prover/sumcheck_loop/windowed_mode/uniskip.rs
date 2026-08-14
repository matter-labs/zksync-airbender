//! Univariate-skip (k = 3) round protocol helpers.
//!
//! The prover evaluates the skipped-round univariate q on the 16 points
//! H u gH (H = <w8>, g = w16; index idx < 8 sits at w16^(2*idx) = w8^idx,
//! idx >= 8 at the odd powers w16^(2*(idx-8)+1), so the 16 points form the
//! size-16 subgroup <w16>), converts to monomial coefficients C_0..C_15 with
//! one 16-point inverse DFT and commits THOSE. The verifier side:
//!   claim == sum_j eq8[j] * q(w8^j) == sum_{t<8} (C_t + C_{t+8}) * W_t,
//!   next claim = q(r) by Horner,
//! and each input poly folds 8 -> 1 with the Lagrange weights L_j(r) on H
//! (node w8^j corresponds to boolean corner j of the standard eq-table
//! order). Mirrors the monomial-form verifier validated in
//! `windowed_mode::program` consumers (coeff fold + DFT + Horner + product-form fold
//! weights agree with the barycentric reference on every pass).
//!
//! `omega16` is the size-16 domain generator of F, passed in by the caller
//! (the fns stay free of a TwoAdicField bound).

use ::field::{Field, FieldExtension, PrimeField};

#[inline]
fn exp_of(idx: usize) -> usize {
    if idx < 8 {
        2 * idx
    } else {
        2 * (idx - 8) + 1
    }
}

#[inline]
fn small_pow2_int<F: PrimeField>(log2: usize) -> F {
    let mut v = F::ONE;
    for _ in 0..log2 {
        v.double();
    }
    v
}

/// q's 16 values on H u gH -> monomial coefficients, one 16-point inverse DFT.
pub(crate) fn uniskip16_to_monomial<F: PrimeField, E: FieldExtension<F> + Field>(
    q: &[E; 16],
    omega16: F,
) -> [E; 16] {
    let omega16_inv = omega16.inverse().expect("domain generator is non-zero");
    let sixteenth = small_pow2_int::<F>(4).inverse().expect("16 != 0 in F");
    core::array::from_fn(|m| {
        let mut acc = E::ZERO;
        for idx in 0..16 {
            let tw = omega16_inv.pow((exp_of(idx) * m % 16) as u32);
            let mut t = q[idx];
            t.mul_assign_by_base(&tw);
            acc.add_assign(&t);
        }
        acc.mul_assign_by_base(&sixteenth);
        acc
    })
}

/// Verifier claim check from monomial coefficients: the eq-weighted sum of q
/// over H folds to `sum_{t<8} (C_t + C_{t+8}) * W_t` with
/// `W_t = sum_j eq8[j] * w8^(j*t)`; W is periodic in t because w8^8 = 1, and
/// W_0 = 1 because eq sums to one over the cube, so the t = 0 term is free.
pub(crate) fn uniskip16_claim_from_monomial<F: PrimeField, E: FieldExtension<F> + Field>(
    c: &[E; 16],
    eq8: &[E; 8],
    omega16: F,
) -> E {
    let mut omega8 = omega16;
    omega8.square();
    let folded: [E; 8] = core::array::from_fn(|t| {
        let mut v = c[t];
        v.add_assign(&c[t + 8]);
        v
    });
    let w: [E; 8] = core::array::from_fn(|t| {
        let mut acc = E::ZERO;
        for j in 0..8 {
            let tw = omega8.pow((j * t % 8) as u32);
            let mut v = eq8[j];
            v.mul_assign_by_base(&tw);
            acc.add_assign(&v);
        }
        acc
    });
    assert_eq!(w[0], E::ONE, "eq table must sum to 1");
    let mut claim = folded[0];
    for t in 1..8 {
        let mut v = folded[t];
        v.mul_assign(&w[t]);
        claim.add_assign(&v);
    }
    claim
}

/// Next claim q(r): plain Horner over C_15..C_0.
pub(crate) fn uniskip16_horner<E: Field>(c: &[E; 16], r: &E) -> E {
    let mut acc = c[15];
    for m in (0..15).rev() {
        acc.mul_assign(r);
        acc.add_assign(&c[m]);
    }
    acc
}

/// Fold weights on H in node order j, inversion-free product form:
///   L_j(r) = [prod_{k != j} (r - w8^k)] * D_j,
///   D_j = 1 / prod_{k != j} (w8^j - w8^k)
/// (the D_j are base-field domain constants; only they get inverted, once per
/// call, which is layer-level cost).
pub(crate) fn uniskip8_fold_weights<F: PrimeField, E: FieldExtension<F> + Field>(
    r: &E,
    omega16: F,
) -> [E; 8] {
    let mut omega8 = omega16;
    omega8.square();
    let nodes: [F; 8] = core::array::from_fn(|k| omega8.pow(k as u32));
    let d_consts: [F; 8] = core::array::from_fn(|j| {
        let mut d = F::ONE;
        for k in 0..8 {
            if k != j {
                let mut t = nodes[j];
                t.sub_assign(&nodes[k]);
                d.mul_assign(&t);
            }
        }
        d.inverse().expect("distinct interpolation nodes")
    });
    let diffs: [E; 8] = core::array::from_fn(|k| {
        let mut t = *r;
        t.sub_assign(&E::from_base(nodes[k]));
        t
    });
    let mut prefix = [E::ONE; 9];
    for k in 0..8 {
        let mut t = prefix[k];
        t.mul_assign(&diffs[k]);
        prefix[k + 1] = t;
    }
    let mut suffix = [E::ONE; 9];
    for k in (0..8).rev() {
        let mut t = suffix[k + 1];
        t.mul_assign(&diffs[k]);
        suffix[k] = t;
    }
    core::array::from_fn(|j| {
        let mut l = prefix[j];
        l.mul_assign(&suffix[j + 1]);
        l.mul_assign_by_base(&d_consts[j]);
        l
    })
}
