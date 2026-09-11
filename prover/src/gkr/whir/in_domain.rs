//! WHIR in-domain query terms handled SYMBOLICALLY instead of as materialized
//! equality tables.
//!
//! Every in-domain query of round `r` (point `rho` in the RS query domain,
//! delinearization weight `ch`) adds `ch * eq(x, pows(rho))` to the sumcheck
//! weight of the folded polynomial, `pows(rho) = (rho, rho^2, rho^4, ..)`.
//! For hypercube evaluations `f` with monomial coefficients `c` and
//! `f_hat(y) = sum_i c_i y^i`, `sum_x f(x) eq(x, pows(rho)) = f_hat(rho)`, and
//! binding the LSB variable to `t` gives
//! `eq((t, x'), pows(rho)) = eq(t, rho) * eq(x', pows(rho^2))` with
//! `sum_{x'} f(t, x') eq(x', pows(rho^2)) = E(rho) + t * O(rho)`,
//! `E(rho) = (f_hat(rho) + f_hat(-rho)) / 2`, `O(rho) = (f_hat(rho) - f_hat(-rho)) / (2 rho)`.
//! So a term contributes the degree-2 polynomial
//! `factor * ch * eq(t, rho) * (E + t O)` to every sumcheck step (added
//! straight into the round's univariate coefficients), where
//! `factor` accumulates `eq(alpha_j, rho^{2^j})` over the steps already bound
//! and the point squares each step. After binding `alpha`, the folded
//! polynomial satisfies `f_hat'(y) = E(sqrt y) + alpha O(sqrt y)`, so a
//! round's `k` steps need `f_hat` on the coset `rho * mu_{2^k}` — a LEAF of the
//! round's oracle, read locally at the start of the round (the current
//! oracle only; the coset folds like the verifier's `fold_coset`).
//!
//! Costs per round: one leaf read + `O(2^k)` per term, instead of an
//! `n`-sized equality table per query.

use super::{evals_to_multilinear_coeffs, offsets_vec_for_leaf_construction};
use fft::{
    bitreverse_enumeration_inplace, bitreverse_index, domain_generator_for_size,
    materialize_powers_serial_starting_with_one,
};
use field::{Field, FieldExtension, PrimeField, TwoAdicField};
use std::alloc::Global;

struct Term<F, E> {
    ch: E,
    factor: E,
    /// the current point `rho^{2^s}`
    point: F,
    /// exponent of `point` w.r.t. the generator of the field's maximal
    /// two-adic subgroup (`2^F::TWO_ADICITY`), kept exactly under squaring
    exp: u64,
    /// the round's leaf, folded `s` times: evaluations of the current folded
    /// polynomial on `base^{2^s} * mu_{2^{k-s}}`, coset order bit-reversed
    values: Vec<E>,
    /// position of `point` in `values`
    pos: usize,
    base_root: F,
    base_root_inv: F,
}

pub(crate) struct InDomainTerms<F, E> {
    terms: Vec<Term<F, E>>,
    two_inv: F,
    /// bit-reversed powers of the leaf-set generator inverse (the conversion's
    /// `high_powers_offsets`) and of the generator itself, for the round's `k`
    hp: Vec<F>,
    hp_inv: Vec<F>,
    k: usize,
}

impl<F: PrimeField + TwoAdicField, E: FieldExtension<F> + Field> InDomainTerms<F, E> {
    pub(crate) fn new() -> Self {
        Self {
            terms: Vec::new(),
            two_inv: F::TWO.inverse().unwrap(),
            hp: Vec::new(),
            hp_inv: Vec::new(),
            k: 0,
        }
    }

    pub(crate) fn len(&self) -> usize {
        self.terms.len()
    }

    /// A query at `query_domain_generator^query_index` in a query domain of
    /// size `2^query_domain_log2`, with weight `ch`.
    pub(crate) fn add(&mut self, point: F, query_index: usize, query_domain_log2: usize, ch: E) {
        assert!(query_domain_log2 <= F::TWO_ADICITY);
        let exp = (query_index as u64) << (F::TWO_ADICITY - query_domain_log2);
        self.terms.push(Term {
            ch,
            factor: E::ONE,
            point,
            exp,
            values: Vec::new(),
            pos: 0,
            base_root: F::ONE,
            base_root_inv: F::ONE,
        });
    }

    /// Load every term's leaf of the CURRENT oracle (domain `2^domain_log2`,
    /// leaves of `2^k` values; `fetch(folded index)` returns them and whether
    /// they are in coefficient form, in which case they are converted back to
    /// evaluations).
    pub(crate) fn start_round(
        &mut self,
        k: usize,
        domain_log2: usize,
        fetch: impl Fn(usize) -> (Vec<E>, bool),
    ) {
        self.k = k;
        let n = 1usize << k;
        if k > 0 {
            let set_generator = domain_generator_for_size::<F>(n as u64);
            let mut hp = materialize_powers_serial_starting_with_one::<F, Global>(
                set_generator.inverse().unwrap(),
                n / 2,
            );
            bitreverse_enumeration_inplace(&mut hp);
            let mut hp_inv =
                materialize_powers_serial_starting_with_one::<F, Global>(set_generator, n / 2);
            bitreverse_enumeration_inplace(&mut hp_inv);
            self.hp = hp;
            self.hp_inv = hp_inv;
        } else {
            self.hp.clear();
            self.hp_inv.clear();
        }
        if self.terms.is_empty() {
            return;
        }
        assert!(domain_log2 <= F::TWO_ADICITY && k <= domain_log2);
        let domain = 1u64 << domain_log2;
        let num_leaves_log2 = domain_log2 - k;
        let generator = domain_generator_for_size::<F>(domain);
        let mut scratch_a = vec![E::ZERO; n];
        let mut scratch_b = vec![E::ZERO; n];
        for term in self.terms.iter_mut() {
            let shift = F::TWO_ADICITY - domain_log2;
            assert_eq!(
                term.exp & ((1u64 << shift) - 1),
                0,
                "an in-domain point must lie in the current oracle's domain"
            );
            let e = term.exp >> shift;
            let leaf_index = (e & ((1u64 << num_leaves_log2) - 1)) as usize;
            let natural_pos = (e >> num_leaves_log2) as usize;
            term.pos = bitreverse_index(natural_pos, k as u32);
            term.base_root = generator.pow(leaf_index as u32);
            term.base_root_inv = term.base_root.inverse().unwrap();
            assert_eq!(
                {
                    let mut p = term.base_root;
                    let set_gen = domain_generator_for_size::<F>(n as u64);
                    p.mul_assign(&set_gen.pow(natural_pos as u32));
                    p
                },
                term.point,
                "leaf bookkeeping disagrees with the tracked point"
            );
            let (mut values, coefficient_form) = fetch(leaf_index);
            assert_eq!(values.len(), n);
            if coefficient_form {
                multilinear_coeffs_to_evals(
                    &mut values,
                    &term.base_root,
                    &self.hp_inv,
                    k,
                    &mut scratch_a,
                    &mut scratch_b,
                );
            }
            term.values = values;
        }
    }

    /// `(E, O)` of a term's current pair.
    #[inline(always)]
    fn even_odd(&self, term: &Term<F, E>) -> (E, E) {
        let j = term.pos >> 1;
        let a = term.values[2 * j];
        let b = term.values[2 * j + 1];
        let mut even = a;
        even.add_assign(&b);
        even.mul_assign_by_base(&self.two_inv);
        let mut root_inv = term.base_root_inv;
        root_inv.mul_assign(&self.hp[j]);
        let mut odd = a;
        odd.sub_assign(&b);
        odd.mul_assign_by_base(&self.two_inv);
        odd.mul_assign_by_base(&root_inv);
        (even, odd)
    }

    /// Add every term's degree-2 sumcheck polynomial
    /// `factor * ch * (1 - rho + t (2 rho - 1)) * (E + t O)` to the round's
    /// univariate coefficients (`coeffs[i]` multiplies `t^i`): with
    /// `a = 1 - rho`, `b = 2 rho - 1` that is `w a E + w (a O + b E) t + w b O t^2`.
    pub(crate) fn add_univariate_coeffs(&self, coeffs: &mut [E; 3]) {
        if self.terms.is_empty() {
            return;
        }
        assert!(
            self.k > 0,
            "no folding step is pending for the loaded leaves"
        );
        for term in self.terms.iter() {
            assert!(
                !term.values.is_empty(),
                "start_round must precede the sumcheck"
            );
            let (even, odd) = self.even_odd(term);
            let mut w = term.factor;
            w.mul_assign(&term.ch);
            let mut a = F::ONE;
            a.sub_assign(&term.point);
            let mut b = term.point;
            b.double();
            b.sub_assign(&F::ONE);
            // c0 = w a E
            let mut c0 = even;
            c0.mul_assign_by_base(&a);
            c0.mul_assign(&w);
            coeffs[0].add_assign(&c0);
            // c1 = w (a O + b E)
            let mut c1 = odd;
            c1.mul_assign_by_base(&a);
            let mut be = even;
            be.mul_assign_by_base(&b);
            c1.add_assign(&be);
            c1.mul_assign(&w);
            coeffs[1].add_assign(&c1);
            // c2 = w b O
            let mut c2 = odd;
            c2.mul_assign_by_base(&b);
            c2.mul_assign(&w);
            coeffs[2].add_assign(&c2);
        }
    }

    /// The terms' summed degree-2 polynomial as coefficients.
    pub(crate) fn univariate_coeffs(&self) -> [E; 3] {
        let mut coeffs = [E::ZERO; 3];
        self.add_univariate_coeffs(&mut coeffs);
        coeffs
    }

    /// Bind the current variable to `alpha`: fold every term's leaf, multiply
    /// its factor by `eq(alpha, rho)`, square its point.
    pub(crate) fn fold(&mut self, alpha: &E) {
        if self.terms.is_empty() {
            return;
        }
        assert!(self.k > 0);
        let two_inv = self.two_inv;
        for term in self.terms.iter_mut() {
            let half = term.values.len() / 2;
            assert!(half > 0, "more folding steps than the loaded leaf supports");
            // eq(alpha, rho) = 1 - rho + alpha (2 rho - 1)
            let mut two_rho_m1 = term.point;
            two_rho_m1.double();
            two_rho_m1.sub_assign(&F::ONE);
            let mut eq = *alpha;
            eq.mul_assign_by_base(&two_rho_m1);
            let mut one_minus_rho = F::ONE;
            one_minus_rho.sub_assign(&term.point);
            eq.add_assign(&E::from_base(one_minus_rho));
            term.factor.mul_assign(&eq);
            // pairs (2j, 2j+1) -> E_j + alpha O_j, the same butterfly as the
            // first stage of the leaf coefficient conversion
            for j in 0..half {
                let a = term.values[2 * j];
                let b = term.values[2 * j + 1];
                let mut even = a;
                even.add_assign(&b);
                even.mul_assign_by_base(&two_inv);
                let mut root_inv = term.base_root_inv;
                root_inv.mul_assign(&self.hp[j]);
                let mut odd = a;
                odd.sub_assign(&b);
                odd.mul_assign_by_base(&two_inv);
                odd.mul_assign_by_base(&root_inv);
                odd.mul_assign(alpha);
                even.add_assign(&odd);
                term.values[j] = even;
            }
            term.values.truncate(half);
            term.pos >>= 1;
            term.point.square();
            term.exp = (term.exp << 1) & ((1u64 << F::TWO_ADICITY) - 1);
            term.base_root.square();
            term.base_root_inv.square();
        }
        self.k -= 1;
    }

    /// Self-check: every loaded leaf value at the term's position must be the
    /// current polynomial's univariate value at the term's point.
    #[allow(dead_code)]
    pub(crate) fn assert_matches_monomial_form(
        &self,
        monomial_form: &[E],
        worker: &worker::Worker,
    ) {
        for (i, term) in self.terms.iter().enumerate() {
            let expected =
                super::evaluate_monomial_form(monomial_form, &E::from_base(term.point), worker);
            assert_eq!(
                term.values[term.pos], expected,
                "in-domain term {i}: leaf value at pos {} (exp {:#x}) != f_hat(point)",
                term.pos, term.exp
            );
        }
    }

    /// `sum_s factor_s * ch_s * f_hat(rho_s)` at the current fold depth (the
    /// terms' share of `sum_x f(x) W(x)`; self-checks).
    #[allow(dead_code)]
    pub(crate) fn sum_at_current(&self) -> E {
        let mut acc = E::ZERO;
        for term in self.terms.iter() {
            let mut v = term.values[term.pos];
            v.mul_assign(&term.factor);
            v.mul_assign(&term.ch);
            acc.add_assign(&v);
        }
        acc
    }
}

/// Exact inverse of [`evals_to_multilinear_coeffs`]: the stages run backwards
/// with `root = base_root^{2^s} * hp_inv[set]` (`hp_inv` = bit-reversed
/// powers of the set generator), `a = c_even + c_odd * root`,
/// `b = c_even - c_odd * root`.
pub(crate) fn multilinear_coeffs_to_evals<
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
>(
    data: &mut [E],
    base_root: &F,
    hp_inv: &[F],
    num_folding_rounds: usize,
    buf_a: &mut [E],
    buf_b: &mut [E],
) {
    let n = 1usize << num_folding_rounds;
    assert_eq!(data.len(), n);
    if num_folding_rounds == 0 {
        return;
    }
    assert!(buf_a.len() >= n && buf_b.len() >= n);
    // roots per stage: base_root^{2^s}
    let mut roots = Vec::with_capacity(num_folding_rounds);
    let mut r = *base_root;
    for _ in 0..num_folding_rounds {
        roots.push(r);
        r.square();
    }
    // the forward pass's stage `s` writes buf_a for even `s`, buf_b for odd
    // `s`; the backward pass starts from its last stage's output buffer
    if (num_folding_rounds - 1) % 2 == 0 {
        buf_a[..n].copy_from_slice(data);
    } else {
        buf_b[..n].copy_from_slice(data);
    }
    for stage in (0..num_folding_rounds).rev() {
        let (src, dst): (&[E], &mut [E]) = if stage % 2 == 0 {
            (
                unsafe { core::slice::from_raw_parts(buf_a.as_ptr(), n) },
                &mut buf_b[..n],
            )
        } else {
            (
                unsafe { core::slice::from_raw_parts(buf_b.as_ptr(), n) },
                &mut buf_a[..n],
            )
        };
        let num_existing = 1usize << stage;
        let bit = 1usize << stage;
        let block_len = n >> stage;
        let half = block_len / 2;
        let root_stage = roots[stage];
        for idx in 0..num_existing {
            let base = idx * block_len;
            let out_base = idx * half;
            let linear_base = (idx | bit) * half;
            for set_idx in 0..half {
                let c_even = src[out_base + set_idx];
                let c_odd = src[linear_base + set_idx];
                let mut root = root_stage;
                root.mul_assign(&hp_inv[set_idx]);
                let mut t = c_odd;
                t.mul_assign_by_base(&root);
                let mut a = c_even;
                a.add_assign(&t);
                let mut b = c_even;
                b.sub_assign(&t);
                dst[base + 2 * set_idx] = a;
                dst[base + 2 * set_idx + 1] = b;
            }
        }
    }
    // stage 0 wrote its output into buf_b
    data.copy_from_slice(&buf_b[..n]);
}

/// The committed leaf of natural leaf index `leaf_index` of one coset column
/// (the `offsets` gather), for callers without an oracle object.
#[allow(dead_code)]
pub(crate) fn leaf_from_column<E: Copy>(
    column: &[E],
    leaf_index: usize,
    values_per_leaf: usize,
) -> Vec<E> {
    let offsets = offsets_vec_for_leaf_construction(column.len(), values_per_leaf);
    offsets.iter().map(|o| column[o + leaf_index]).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use field::baby_bear::{base::BabyBearField as F, ext4::BabyBearExt4 as E};
    use field::Rand;

    #[test]
    fn coeffs_to_evals_inverts_the_conversion() {
        let mut rng = rand::thread_rng();
        for k in 1..=6usize {
            let n = 1usize << k;
            let set_generator = domain_generator_for_size::<F>(n as u64);
            let mut hp = materialize_powers_serial_starting_with_one::<F, Global>(
                set_generator.inverse().unwrap(),
                n / 2,
            );
            bitreverse_enumeration_inplace(&mut hp);
            let mut hp_inv =
                materialize_powers_serial_starting_with_one::<F, Global>(set_generator, n / 2);
            bitreverse_enumeration_inplace(&mut hp_inv);
            let two_inv = F::TWO.inverse().unwrap();
            let base_root = F::random_element(&mut rng);
            let base_root_inv = base_root.inverse().unwrap();
            let evals: Vec<E> = (0..n).map(|_| E::random_element(&mut rng)).collect();
            let mut data = evals.clone();
            let mut a = vec![E::ZERO; n];
            let mut b = vec![E::ZERO; n];
            evals_to_multilinear_coeffs(
                &mut data,
                &base_root_inv,
                &hp,
                &two_inv,
                k,
                &mut a,
                &mut b,
            );
            assert_ne!(data, evals);
            // fresh scratch: the inverse must not depend on the forward's leftovers
            let mut a = vec![E::ZERO; n];
            let mut b = vec![E::ZERO; n];
            multilinear_coeffs_to_evals(&mut data, &base_root, &hp_inv, k, &mut a, &mut b);
            assert_eq!(data, evals, "k = {k}");
        }
    }
}
