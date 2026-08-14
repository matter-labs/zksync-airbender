//! LSB-binding backward (sumcheck) engine for the dimension-reducing layers.
//!
//! The gate set here is fixed (pairwise products and logup fraction-add
//! reduction), so this path deliberately steps away from
//! `BatchedGKRKernel`/`EvaluationFormStorage` and works on the raw backing
//! slices directly.
//!
//! # Index conventions
//!
//! An input poly of the layer has `2 * M` values, interleaved with the GATE
//! dimension in the LOWEST bit: `input index = 2*Y + b`, where `b` is the
//! gate's paired bit and `Y` (of `log2(M)` variables) is the sumcheck space.
//! The sumcheck binds Y LSB-FIRST: round `s` binds bit 0 of the CURRENT Y,
//! so a round pairs `Y = 2j` with `Y = 2j + 1`, i.e. it reads the input
//! indices
//!
//! ```text
//!   block of 4 consecutive values:  [4j + 0, 4j + 1, 4j + 2, 4j + 3]
//!                                     Y=2j,b=0 Y=2j,b=1 Y=2j+1,b=0 Y=2j+1,b=1
//! ```
//!
//! -- perfectly contiguous reads, unlike the MSB path's stride-`M/2` pairs
//! (`get_f0_and_f1` reads `[index, next_layer_size + index]`).
//!
//! # Folding
//!
//! LSB folding is not in-place (the surviving values are not a prefix of the
//! old layout), so the engine ping-pongs: each round reads the current live
//! region and writes the folded poly DENSELY into the other half of a
//! per-poly scratch buffer:
//!
//! ```text
//!   dst[2j + b] = (1 - r) * src[4j + b] + r * src[4j + 2 + b]
//! ```
//!
//! # Round messages
//!
//! With the eq factor split Gruen-style around the bound bit,
//! `eq(tau, Y) = eqw_s(X) * T_s(rest)`, the round polynomial is
//! `q_s(X) = eqw_s(X) * h_s(X)` with
//! `h_s(X) = sum_j T_s(j) * sum_k alpha_k * gate_k(inputs at (X, j))`.
//! `h_s` is quadratic (gates are quadratic, inputs linear in X), so the
//! engine accumulates `[h(0), h(1), h(inf)]` and emits the CUBIC monomial
//! coefficients `[c0, c1, c2, c3]` of `q_s`. Soundness bookkeeping is the
//! standard chaining `q_s(0) + q_s(1) == claim_s`, `claim_{s+1} = q_s(r_s)`.

use field::{Field, FieldExtension, PrimeField};

/// One batched relation of a dimension-reducing layer, referring to input
/// polys by their position in the engine's poly list.
#[derive(Clone, Copy, Debug)]
pub enum LsbDimReducingRelation<E> {
    /// `out(Y) = p(2Y) * p(2Y+1)`, batched with weight `alpha`.
    PairwiseProduct { input: usize, alpha: E },
    /// Logup fraction add over a (numerator, denominator) pair:
    /// `out_num(Y) = n(2Y) * d(2Y+1) + n(2Y+1) * d(2Y)`,
    /// `out_den(Y) = d(2Y) * d(2Y+1)`, batched with `alpha_num`, `alpha_den`.
    LogupPair {
        num: usize,
        den: usize,
        alpha_num: E,
        alpha_den: E,
    },
}

/// Ping-pong folding scratch for one poly: a single allocation of the input
/// size; round `s` reads the previous round's dense region and writes the
/// next dense region into the other half.
struct PingPong<E> {
    buf: Vec<E>,
    /// offset of the current live region
    live_at: usize,
    live_len: usize,
}

impl<E: Field> PingPong<E> {
    fn new(initial: &[E]) -> Self {
        let mut buf = initial.to_vec();
        buf.resize(initial.len() + initial.len() / 2, E::ZERO);
        PingPong {
            buf,
            live_at: 0,
            live_len: initial.len(),
        }
    }

    #[inline(always)]
    fn live(&self) -> &[E] {
        &self.buf[self.live_at..self.live_at + self.live_len]
    }

    /// `dst[2j + b] = (1 - r)*src[4j + b] + r*src[4j + 2 + b]`, written
    /// densely into the non-live half.
    fn fold(&mut self, r: &E) {
        let new_len = self.live_len / 2;
        let dst_at = if self.live_at == 0 { self.live_len } else { 0 };
        debug_assert!(dst_at + new_len <= self.buf.len());
        let (src_ptr, dst_ptr) = unsafe {
            (
                self.buf.as_ptr().add(self.live_at),
                self.buf.as_mut_ptr().add(dst_at),
            )
        };
        for j in 0..(new_len / 2) {
            for b in 0..2 {
                unsafe {
                    let lo = *src_ptr.add(4 * j + b);
                    let hi = *src_ptr.add(4 * j + 2 + b);
                    let mut v = hi;
                    v.sub_assign(&lo);
                    v.mul_assign(r);
                    v.add_assign(&lo);
                    *dst_ptr.add(2 * j + b) = v;
                }
            }
        }
        self.live_at = dst_at;
        self.live_len = new_len;
    }
}

#[inline(always)]
fn gate_batch<E: Field>(
    relations: &[LsbDimReducingRelation<E>],
    at: impl Fn(usize, usize) -> E, // (poly, local index within a Y-cell: 0 = b0, 1 = b1)
) -> E {
    let mut acc = E::ZERO;
    for rel in relations {
        match rel {
            LsbDimReducingRelation::PairwiseProduct { input, alpha } => {
                let mut t = at(*input, 0);
                t.mul_assign(&at(*input, 1));
                t.mul_assign(alpha);
                acc.add_assign(&t);
            }
            LsbDimReducingRelation::LogupPair {
                num,
                den,
                alpha_num,
                alpha_den,
            } => {
                let (n0, n1) = (at(*num, 0), at(*num, 1));
                let (d0, d1) = (at(*den, 0), at(*den, 1));
                let mut nn = n0;
                nn.mul_assign(&d1);
                let mut t = n1;
                t.mul_assign(&d0);
                nn.add_assign(&t);
                nn.mul_assign(alpha_num);
                acc.add_assign(&nn);
                let mut dd = d0;
                dd.mul_assign(&d1);
                dd.mul_assign(alpha_den);
                acc.add_assign(&dd);
            }
        }
    }
    acc
}

/// Result of one LSB dimension-reducing sumcheck: the per-round cubic
/// coefficients, the challenges consumed, the final claim, and the final
/// (fully folded) two values `[p(., 0), p(., 1)]` of every input poly.
pub struct LsbDimReducingSumcheckOutput<E> {
    pub round_coefficients: Vec<[E; 4]>,
    pub final_claim: E,
    pub final_values: Vec<[E; 2]>,
    /// `prod_s eqw_s(r_s)` -- the eq factor of the bound variables; the
    /// final claim satisfies `final_claim == eq_factor * gate(final_values)`.
    pub eq_factor: E,
}

/// Runs the full LSB-binding sumcheck for one dimension-reducing layer.
///
/// * `polys` — the layer's input polys (each `2 * M` values, `2Y + b`
///   interleaved); consumed as working copies.
/// * `relations` — the batched gate list over those polys.
/// * `tau` — the eq challenges of the OUTPUT claim point, ordered
///   low-variable-first (`tau[s]` is the coordinate of the variable bound at
///   round `s`).
/// * `claim` — the batched claim `sum_Y eq(tau, Y) * batched_gate(Y)`.
/// * `challenges` — the folding challenges to bind, one per round (in
///   production these come from the transcript after absorbing each round's
///   coefficients; the caller controls that interaction).
///
/// The eq suffix tables `T_s` are maintained INCREMENTALLY: `T_0` is the eq
/// table over `tau[1..]` and each round drops its lowest variable by the
/// standard doubling contraction, so no per-round table rebuild is needed.
pub fn lsb_dim_reducing_sumcheck_prove<F: PrimeField, E: FieldExtension<F> + Field>(
    polys: &[&[E]],
    relations: &[LsbDimReducingRelation<E>],
    tau: &[E],
    claim: E,
    challenges: &[E],
) -> LsbDimReducingSumcheckOutput<E> {
    let rounds = tau.len();
    assert_eq!(challenges.len(), rounds);
    let m = 1usize << rounds;
    for p in polys {
        assert_eq!(p.len(), 2 * m);
    }

    // T_0 over tau[1..], low-variable-first: T[j] = prod_b f_{tau[1+b]}(j_b)
    let mut t_table = vec![E::ONE; m / 2];
    for b in 0..rounds.saturating_sub(1) {
        let half = 1usize << b;
        let c = tau[1 + b];
        let mut one_minus = E::ONE;
        one_minus.sub_assign(&c);
        for i in 0..half {
            let mut hi = t_table[i];
            hi.mul_assign(&c);
            t_table[i + half] = hi;
            t_table[i].mul_assign(&one_minus);
        }
    }

    let mut buffers: Vec<PingPong<E>> = polys.iter().map(|p| PingPong::new(p)).collect();
    let mut round_coefficients = Vec::with_capacity(rounds);
    let mut claim = claim;
    let mut final_values = Vec::new();
    // accumulated eq prefix over the already-bound variables:
    // prod_{t<s} eqw_t(r_t); it scales every later round polynomial
    let mut eq_prefix = E::ONE;

    for s in 0..rounds {
        let pairs = 1usize << (rounds - 1 - s);
        // accumulate h(0), h(1), h(inf) over all pairs, T-weighted
        let mut h = [E::ZERO; 3];
        for j in 0..pairs {
            let w = t_table[j];
            // h(0): gate at Y' = 2j (indices 4j + b)
            let v0 = gate_batch(relations, |p, b| buffers[p].live()[4 * j + b]);
            // h(1): gate at Y' = 2j + 1 (indices 4j + 2 + b)
            let v1 = gate_batch(relations, |p, b| buffers[p].live()[4 * j + 2 + b]);
            // h(inf): gate's leading X-coefficient = gate on the differences
            let vinf = gate_batch(relations, |p, b| {
                let live = buffers[p].live();
                let mut d = live[4 * j + 2 + b];
                d.sub_assign(&live[4 * j + b]);
                d
            });
            for (dst, v) in h.iter_mut().zip([v0, v1, vinf]) {
                let mut t = v;
                t.mul_assign(&w);
                dst.add_assign(&t);
            }
        }
        // h(X) = h0 + h1x*X + hinf*X^2 with h1x = h(1) - h(0) - h(inf)
        let (h0, hinf) = (h[0], h[2]);
        let mut h1x = h[1];
        h1x.sub_assign(&h0);
        h1x.sub_assign(&hinf);
        // eqw(X) = (1 - tau_s) + (2*tau_s - 1)*X
        let mut e0 = E::ONE;
        e0.sub_assign(&tau[s]);
        let mut e1 = tau[s];
        e1.sub_assign(&e0); // 2*tau_s - 1
        // q = eqw * h -> cubic coefficients
        let mut c0 = e0;
        c0.mul_assign(&h0);
        let mut c1 = e0;
        c1.mul_assign(&h1x);
        let mut t = e1;
        t.mul_assign(&h0);
        c1.add_assign(&t);
        let mut c2 = e0;
        c2.mul_assign(&hinf);
        let mut t = e1;
        t.mul_assign(&h1x);
        c2.add_assign(&t);
        let mut c3 = e1;
        c3.mul_assign(&hinf);
        let mut coeffs = [c0, c1, c2, c3];
        for c in coeffs.iter_mut() {
            c.mul_assign(&eq_prefix);
        }
        let [c0, c1, c2, c3] = coeffs;

        // soundness bookkeeping: q(0) + q(1) must reproduce the claim
        #[cfg(feature = "gkr_self_checks")]
        {
            let mut q01 = c0;
            q01.add_assign(&c0);
            q01.add_assign(&c1);
            q01.add_assign(&c2);
            q01.add_assign(&c3);
            assert_eq!(q01, claim, "LSB dim-reducing round {} claim mismatch", s);
        }

        // bind the challenge: claim = q(r), fold polys, contract T
        let r = challenges[s];
        let mut new_claim = c3;
        new_claim.mul_assign(&r);
        new_claim.add_assign(&c2);
        new_claim.mul_assign(&r);
        new_claim.add_assign(&c1);
        new_claim.mul_assign(&r);
        new_claim.add_assign(&c0);
        claim = new_claim;

        // eq_prefix *= eqw_s(r)
        let mut ew = e1;
        ew.mul_assign(&r);
        ew.add_assign(&e0);
        eq_prefix.mul_assign(&ew);

        for buf in buffers.iter_mut() {
            buf.fold(&r);
        }
        // contract T: drop its (new) lowest variable by partial evaluation at
        // the NEXT round's own tau -- i.e. simply halve by keeping the
        // eq-structure: T_{s+1}[j] = T_s[2j] + ... is NOT needed because
        // T tables are pure products: T_s[j] = prod f_{tau[s+1+b]}(j_b), so
        // T_{s+1}[j] = T_s[j (low bit dropped)] / f_{tau[s+1]}(j_0). We keep
        // it simple and exact instead: T_{s+1}[j] = T_s[2j] / (1 - tau[s+1])
        // is division-heavy, so rebuild by contraction: entries with j_0 = 0
        // already carry f(0) = 1 - tau[s+1]; strip it via the complementary
        // sum: f(0)*x + f(1)*x = x. Sum of the pair = T_{s+1}[j].
        if s + 1 < rounds {
            let next = pairs / 2;
            for j in 0..next.max(1) {
                let mut v = t_table[2 * j];
                v.add_assign(&t_table[2 * j + 1]);
                t_table[j] = v;
            }
        }

        round_coefficients.push(coeffs);
    }

    for buf in buffers.iter() {
        let live = buf.live();
        assert_eq!(live.len(), 2);
        final_values.push([live[0], live[1]]);
    }

    // final identity: the claim after all rounds equals the batched gate on
    // the fully folded values (eq fully consumed by the eqw factors)
    #[cfg(feature = "gkr_self_checks")]
    {
        let fv = &final_values;
        let mut g = gate_batch(relations, |p, b| fv[p][b]);
        g.mul_assign(&eq_prefix);
        assert_eq!(g, claim, "LSB dim-reducing final gate identity");
    }

    LsbDimReducingSumcheckOutput {
        round_coefficients,
        final_claim: claim,
        final_values,
        eq_factor: eq_prefix,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ::field::baby_bear::base::BabyBearField;
    use ::field::baby_bear::ext4::BabyBearExt4;

    type F = BabyBearField;
    type E = BabyBearExt4;

    fn pseudo(seed: &mut u64) -> E {
        BabyBearExt4::from_array_of_base(core::array::from_fn(|_| {
            *seed = seed
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            BabyBearField::from_u32_with_reduction((*seed >> 33) as u32)
        }))
    }

    #[test]
    fn lsb_dim_reducing_sumcheck_chains() {
        let mut seed = 7u64;
        let rounds = 6usize;
        let m = 1usize << rounds;
        // three polys: one for pairwise product, a (num, den) logup pair
        let polys: Vec<Vec<E>> = (0..3)
            .map(|_| (0..2 * m).map(|_| pseudo(&mut seed)).collect())
            .collect();
        let poly_refs: Vec<&[E]> = polys.iter().map(|p| &p[..]).collect();
        let relations = [
            LsbDimReducingRelation::PairwiseProduct {
                input: 0,
                alpha: pseudo(&mut seed),
            },
            LsbDimReducingRelation::LogupPair {
                num: 1,
                den: 2,
                alpha_num: pseudo(&mut seed),
                alpha_den: pseudo(&mut seed),
            },
        ];
        let tau: Vec<E> = (0..rounds).map(|_| pseudo(&mut seed)).collect();
        let challenges: Vec<E> = (0..rounds).map(|_| pseudo(&mut seed)).collect();

        // direct claim: sum over Y of eq(tau, Y) * batched gate, with the
        // LOW-variable-first eq convention (bit b of Y <-> tau[b])
        let mut eq = vec![E::ONE; m];
        for b in 0..rounds {
            let half = 1usize << b;
            let c = tau[b];
            let mut om = E::ONE;
            om.sub_assign(&c);
            for i in 0..half {
                let mut hi = eq[i];
                hi.mul_assign(&c);
                eq[i + half] = hi;
                eq[i].mul_assign(&om);
            }
        }
        let mut claim = E::ZERO;
        for y in 0..m {
            let v = gate_batch(&relations, |p, b| polys[p][2 * y + b]);
            let mut t = v;
            t.mul_assign(&eq[y]);
            claim.add_assign(&t);
        }

        let out = lsb_dim_reducing_sumcheck_prove::<F, E>(
            &poly_refs,
            &relations,
            &tau,
            claim,
            &challenges,
        );

        // external verification of the chaining (independent of the internal
        // gkr_self_checks asserts): q_s(0) + q_s(1) == claim_s, claim_{s+1} =
        // q_s(r_s), and the final gate identity
        let mut c = claim;
        for (s, coeffs) in out.round_coefficients.iter().enumerate() {
            let [c0, c1, c2, c3] = *coeffs;
            let mut q01 = c0;
            q01.add_assign(&c0);
            q01.add_assign(&c1);
            q01.add_assign(&c2);
            q01.add_assign(&c3);
            assert_eq!(q01, c, "round {} chaining", s);
            let r = challenges[s];
            let mut v = c3;
            v.mul_assign(&r);
            v.add_assign(&c2);
            v.mul_assign(&r);
            v.add_assign(&c1);
            v.mul_assign(&r);
            v.add_assign(&c0);
            c = v;
        }
        assert_eq!(c, out.final_claim);
        let mut g = gate_batch(&relations, |p, b| out.final_values[p][b]);
        g.mul_assign(&out.eq_factor);
        assert_eq!(g, out.final_claim, "final folded gate identity");
    }
}

/// Worker-parallel, transcript-driven variant of
/// [`lsb_dim_reducing_sumcheck_prove`]: each round's `[h(0), h(1), h(inf)]`
/// accumulation and the ping-pong fold are chunked over the worker, and the
/// bound challenge is obtained from `draw_challenge(&coeffs)` -- the caller
/// absorbs the round coefficients into the transcript and returns the drawn
/// challenge, exactly like the naive loop's `commit_field_els` +
/// `draw_random_field_els` pair.
pub fn lsb_dim_reducing_sumcheck_prove_parallel<
    F: PrimeField,
    E: FieldExtension<F> + Field,
>(
    polys: &[&[E]],
    relations: &[LsbDimReducingRelation<E>],
    tau: &[E],
    claim: E,
    worker: &worker::Worker,
    mut draw_challenge: impl FnMut(&[E; 4]) -> E,
) -> (LsbDimReducingSumcheckOutput<E>, Vec<E>) {
    use crate::gkr::PAR_THRESHOLD;

    let rounds = tau.len();
    let m = 1usize << rounds;
    for p in polys {
        assert_eq!(p.len(), 2 * m);
    }

    // T_0 over tau[1..], low-variable-first
    let mut t_table = vec![E::ONE; m / 2];
    for b in 0..rounds.saturating_sub(1) {
        let half = 1usize << b;
        let c = tau[1 + b];
        let mut one_minus = E::ONE;
        one_minus.sub_assign(&c);
        for i in 0..half {
            let mut hi = t_table[i];
            hi.mul_assign(&c);
            t_table[i + half] = hi;
            t_table[i].mul_assign(&one_minus);
        }
    }

    let mut buffers: Vec<PingPong<E>> = polys.iter().map(|p| PingPong::new(p)).collect();
    let mut round_coefficients = Vec::with_capacity(rounds);
    let mut challenges = Vec::with_capacity(rounds);
    let mut claim = claim;
    let mut eq_prefix = E::ONE;

    for s in 0..rounds {
        let pairs = 1usize << (rounds - 1 - s);
        // parallel accumulation of [h(0), h(1), h(inf)]
        let mut h = [E::ZERO; 3];
        {
            let geometry = worker.get_geometry_with_threshold(pairs, PAR_THRESHOLD);
            let mut partials = vec![[E::ZERO; 3]; geometry.num_chunks];
            let live_ptrs: Vec<usize> =
                buffers.iter().map(|b| b.live().as_ptr() as usize).collect();
            let t_ptr = t_table.as_ptr() as usize;
            worker.scope_with_threshold(pairs, PAR_THRESHOLD, |scope, geometry| {
                let mut it = partials.iter_mut();
                for thread_idx in 0..geometry.num_chunks {
                    let chunk_start = geometry.get_chunk_start_pos(thread_idx);
                    let chunk_size = geometry.get_chunk_size(thread_idx);
                    let live_ptrs = live_ptrs.clone();
                    let dst = it.next().unwrap();
                    worker::Worker::smart_spawn(
                        scope,
                        thread_idx == geometry.len() - 1,
                        move |_| {
                            let t_tab = t_ptr as *const E;
                            let at = |p: usize, idx: usize| -> E {
                                unsafe { *(live_ptrs[p] as *const E).add(idx) }
                            };
                            let mut acc = [E::ZERO; 3];
                            for j in chunk_start..(chunk_start + chunk_size) {
                                let w = unsafe { *t_tab.add(j) };
                                let v0 = gate_batch(relations, |p, b| at(p, 4 * j + b));
                                let v1 = gate_batch(relations, |p, b| at(p, 4 * j + 2 + b));
                                let vinf = gate_batch(relations, |p, b| {
                                    let mut d = at(p, 4 * j + 2 + b);
                                    d.sub_assign(&at(p, 4 * j + b));
                                    d
                                });
                                for (dst, v) in acc.iter_mut().zip([v0, v1, vinf]) {
                                    let mut t = v;
                                    t.mul_assign(&w);
                                    dst.add_assign(&t);
                                }
                            }
                            *dst = acc;
                        },
                    )
                }
            });
            for p in partials {
                for i in 0..3 {
                    h[i].add_assign(&p[i]);
                }
            }
        }
        let (h0, hinf) = (h[0], h[2]);
        let mut h1x = h[1];
        h1x.sub_assign(&h0);
        h1x.sub_assign(&hinf);
        let mut e0 = E::ONE;
        e0.sub_assign(&tau[s]);
        let mut e1 = tau[s];
        e1.sub_assign(&e0);
        let mut c0 = e0;
        c0.mul_assign(&h0);
        let mut c1 = e0;
        c1.mul_assign(&h1x);
        let mut t = e1;
        t.mul_assign(&h0);
        c1.add_assign(&t);
        let mut c2 = e0;
        c2.mul_assign(&hinf);
        let mut t = e1;
        t.mul_assign(&h1x);
        c2.add_assign(&t);
        let mut c3 = e1;
        c3.mul_assign(&hinf);
        let mut coeffs = [c0, c1, c2, c3];
        for c in coeffs.iter_mut() {
            c.mul_assign(&eq_prefix);
        }

        #[cfg(feature = "gkr_self_checks")]
        {
            let [c0, c1, c2, c3] = coeffs;
            let mut q01 = c0;
            q01.add_assign(&c0);
            q01.add_assign(&c1);
            q01.add_assign(&c2);
            q01.add_assign(&c3);
            assert_eq!(q01, claim, "LSB dim-reducing round {} claim mismatch", s);
        }

        let r = draw_challenge(&coeffs);
        challenges.push(r);
        let [c0, c1, c2, c3] = coeffs;
        let mut new_claim = c3;
        new_claim.mul_assign(&r);
        new_claim.add_assign(&c2);
        new_claim.mul_assign(&r);
        new_claim.add_assign(&c1);
        new_claim.mul_assign(&r);
        new_claim.add_assign(&c0);
        claim = new_claim;

        let mut ew = e1;
        ew.mul_assign(&r);
        ew.add_assign(&e0);
        eq_prefix.mul_assign(&ew);

        // parallel ping-pong fold
        {
            let new_len = buffers[0].live_len / 2;
            let out_pairs = new_len / 2;
            let fold_ptrs: Vec<(usize, usize)> = buffers
                .iter_mut()
                .map(|b| {
                    let dst_at = if b.live_at == 0 { b.live_len } else { 0 };
                    (
                        unsafe { b.buf.as_ptr().add(b.live_at) } as usize,
                        unsafe { b.buf.as_mut_ptr().add(dst_at) } as usize,
                    )
                })
                .collect();
            if out_pairs == 0 {
                for b in buffers.iter_mut() {
                    b.fold(&r);
                }
            } else {
                worker.scope_with_threshold(out_pairs, PAR_THRESHOLD, |scope, geometry| {
                    for thread_idx in 0..geometry.num_chunks {
                        let chunk_start = geometry.get_chunk_start_pos(thread_idx);
                        let chunk_size = geometry.get_chunk_size(thread_idx);
                        let fold_ptrs = fold_ptrs.clone();
                        worker::Worker::smart_spawn(
                            scope,
                            thread_idx == geometry.len() - 1,
                            move |_| {
                                for (src_a, dst_a) in fold_ptrs.iter() {
                                    let src = *src_a as *const E;
                                    let dst = *dst_a as *mut E;
                                    for j in chunk_start..(chunk_start + chunk_size) {
                                        for b in 0..2 {
                                            unsafe {
                                                let lo = *src.add(4 * j + b);
                                                let hi = *src.add(4 * j + 2 + b);
                                                let mut v = hi;
                                                v.sub_assign(&lo);
                                                v.mul_assign(&r);
                                                v.add_assign(&lo);
                                                *dst.add(2 * j + b) = v;
                                            }
                                        }
                                    }
                                }
                            },
                        )
                    }
                });
                for b in buffers.iter_mut() {
                    let dst_at = if b.live_at == 0 { b.live_len } else { 0 };
                    b.live_at = dst_at;
                    b.live_len = new_len;
                }
            }
        }

        if s + 1 < rounds {
            let next = pairs / 2;
            for j in 0..next {
                let mut v = t_table[2 * j];
                v.add_assign(&t_table[2 * j + 1]);
                t_table[j] = v;
            }
        }

        round_coefficients.push(coeffs);
    }

    let mut final_values = Vec::new();
    for buf in buffers.iter() {
        let live = buf.live();
        assert_eq!(live.len(), 2);
        final_values.push([live[0], live[1]]);
    }

    #[cfg(feature = "gkr_self_checks")]
    {
        let fv = &final_values;
        let mut g = gate_batch(relations, |p, b| fv[p][b]);
        g.mul_assign(&eq_prefix);
        assert_eq!(g, claim, "LSB dim-reducing final gate identity");
    }

    (
        LsbDimReducingSumcheckOutput {
            round_coefficients,
            final_claim: claim,
            final_values,
            eq_factor: eq_prefix,
        },
        challenges,
    )
}

/// Values of one poly's gate-pair over a window's `{0,1,inf}^w` grid.
/// `cells[c]` for cell coordinate `(x_0..x_{w-1})` in base-3 digits (LSB
/// variable = digit 0): 0/1 = the boolean tap, inf = the per-variable leading
/// coefficient (f1 - f0), built by the usual recursive extrapolation.
#[inline(always)]
fn window_cells<E: Field, const W: usize>(taps: &[E], out: &mut [E]) {
    // taps: 2^W boolean values (y_s = bit s); out: 3^W cells
    let pow3 = 3usize.pow(W as u32);
    debug_assert_eq!(taps.len(), 1 << W);
    debug_assert!(out.len() >= pow3);
    // seed boolean cells
    let mut strides3 = [0usize; W];
    let mut p3 = 1usize;
    for s in 0..W {
        strides3[s] = p3;
        p3 *= 3;
    }
    for y in 0..(1usize << W) {
        let mut c = 0usize;
        for s in 0..W {
            if (y >> s) & 1 == 1 {
                c += strides3[s];
            }
        }
        out[c] = taps[y];
    }
    // extrapolate inf per variable, level by level (var s: cells with digit
    // s == 2 from digits 0/1, all combinations of other digits < current
    // level allowed to be 0..3, later vars boolean)
    for s in 0..W {
        // iterate all cells where digit s == 0, digits > s are boolean (0/1),
        // digits < s can be anything 0..3
        let mut idx = [0usize; W];
        loop {
            // compute base cell with digit s = 0
            let mut ok = true;
            for t in s..W {
                if t == s {
                    continue;
                }
                if idx[t] > 1 {
                    ok = false;
                    break;
                }
            }
            if ok && idx[s] == 0 {
                let mut c0 = 0usize;
                for t in 0..W {
                    c0 += idx[t] * strides3[t];
                }
                let c1 = c0 + strides3[s];
                let cinf = c0 + 2 * strides3[s];
                let mut v = out[c1];
                v.sub_assign(&out[c0]);
                out[cinf] = v;
            }
            // advance odometer over digits != s (digit s stays 0)
            let mut t = 0;
            loop {
                if t == s {
                    t += 1;
                    if t == W {
                        break;
                    }
                    continue;
                }
                idx[t] += 1;
                if idx[t] < 3 {
                    break;
                }
                idx[t] = 0;
                t += 1;
                if t == W {
                    break;
                }
            }
            if t == W {
                break;
            }
            if W == 1 {
                break;
            }
        }
        if W == 1 {
            // only one variable: nothing to iterate beyond the single cell
            let mut v = out[1];
            v.sub_assign(&out[0]);
            out[2] = v;
        }
    }
}

/// Windowed (window <= 3) LSB dimension-reducing sumcheck: each window
/// computes the `{0,1,inf}^w` accumulator of the T-weighted batched gate in
/// ONE parallel pass over the live buffers, then runs the bind chain (per
/// round: contract remaining window vars with boolean eq weights, emit the
/// cubic `[E;4]`, absorb/draw via the callback, bind the accumulator with
/// `f(r) = f0 + r*(f1-f0) + (r^2-r)*f_inf`), and finally folds every poly by
/// all `w` challenges in ONE `2^w`-tap pass (dense ping-pong write).
pub fn lsb_dim_reducing_windowed_prove_parallel<
    F: PrimeField,
    E: FieldExtension<F> + Field,
>(
    polys: &[&[E]],
    relations: &[LsbDimReducingRelation<E>],
    tau: &[E],
    claim: E,
    worker: &worker::Worker,
    mut draw_challenge: impl FnMut(&[E; 4]) -> E,
) -> (LsbDimReducingSumcheckOutput<E>, Vec<E>) {
    use crate::gkr::PAR_THRESHOLD;

    let rounds = tau.len();
    let m = 1usize << rounds;
    for p in polys {
        assert_eq!(p.len(), 2 * m);
    }

    let mut t_table = vec![E::ONE; m.max(2) / 2];
    // T over tau[1..] initially; for windowed use we rebuild the suffix table
    // per window instead (suffix over tau[window_end..])
    let build_t = |from: usize, len_log2: usize| -> Vec<E> {
        let mut t = vec![E::ONE; 1 << len_log2];
        for b in 0..len_log2 {
            let half = 1usize << b;
            let c = tau[from + b];
            let mut om = E::ONE;
            om.sub_assign(&c);
            for i in 0..half {
                let mut hi = t[i];
                hi.mul_assign(&c);
                t[i + half] = hi;
                t[i].mul_assign(&om);
            }
        }
        t
    };
    let _ = &mut t_table;

    let mut buffers: Vec<PingPong<E>> = polys.iter().map(|p| PingPong::new(p)).collect();
    let mut round_coefficients = Vec::with_capacity(rounds);
    let mut challenges = Vec::with_capacity(rounds);
    let mut claim = claim;
    let mut eq_prefix = E::ONE;
    let mut done = 0usize;

    while done < rounds {
        let w = (rounds - done).min(3);
        let pow3 = 3usize.pow(w as u32);
        let rows = 1usize << (rounds - done - w);
        let t_win = build_t(done + w, rounds - done - w);

        // ---- one parallel pass: T-weighted {0,1,inf}^w gate accumulator ----
        let mut acc = vec![E::ZERO; pow3];
        {
            let geometry = worker.get_geometry_with_threshold(rows, (PAR_THRESHOLD >> w).max(1));
            let mut partials = vec![vec![E::ZERO; pow3]; geometry.num_chunks];
            let live_ptrs: Vec<usize> =
                buffers.iter().map(|b| b.live().as_ptr() as usize).collect();
            let t_ptr = t_win.as_ptr() as usize;
            worker.scope_with_threshold(rows, (PAR_THRESHOLD >> w).max(1), |scope, geometry| {
                let mut it = partials.iter_mut();
                for thread_idx in 0..geometry.num_chunks {
                    let chunk_start = geometry.get_chunk_start_pos(thread_idx);
                    let chunk_size = geometry.get_chunk_size(thread_idx);
                    let live_ptrs = live_ptrs.clone();
                    let dst = it.next().unwrap();
                    worker::Worker::smart_spawn(
                        scope,
                        thread_idx == geometry.len() - 1,
                        move |_| {
                            let t_tab = t_ptr as *const E;
                            let npolys = live_ptrs.len();
                            // per poly per gate-bit: 3^w window cells
                            let mut grids = vec![E::ZERO; npolys * 2 * 27];
                            let mut taps = [E::ZERO; 8];
                            let mut local = vec![E::ZERO; dst.len()];
                            for j in chunk_start..(chunk_start + chunk_size) {
                                let base_idx = (2usize << w) * j;
                                for p in 0..npolys {
                                    let src = live_ptrs[p] as *const E;
                                    for b in 0..2 {
                                        for y in 0..(1usize << w) {
                                            taps[y] =
                                                unsafe { *src.add(base_idx + 2 * y + b) };
                                        }
                                        let g = &mut grids
                                            [(p * 2 + b) * 27..(p * 2 + b) * 27 + 27];
                                        match w {
                                            3 => window_cells::<E, 3>(&taps[..8], g),
                                            2 => window_cells::<E, 2>(&taps[..4], g),
                                            1 => window_cells::<E, 1>(&taps[..2], g),
                                            _ => unreachable!(),
                                        }
                                    }
                                }
                                let tw = unsafe { *t_tab.add(j) };
                                for c in 0..local.len() {
                                    let v = gate_batch(relations, |p, b| {
                                        grids[(p * 2 + b) * 27 + c]
                                    });
                                    let mut t = v;
                                    t.mul_assign(&tw);
                                    local[c].add_assign(&t);
                                }
                            }
                            for (d, v) in dst.iter_mut().zip(local.into_iter()) {
                                d.add_assign(&v);
                            }
                        },
                    )
                }
            });
            for p in partials {
                for (a, v) in acc.iter_mut().zip(p.into_iter()) {
                    a.add_assign(&v);
                }
            }
        }

        // ---- bind chain over the window ----
        let mut win_rs = [E::ZERO; 3];
        for s in 0..w {
            let rem = w - s - 1; // unbound window vars after this one
            let pow3_rem = 3usize.pow(rem as u32);
            // contract remaining vars with their boolean eq weights
            let mut h = [E::ZERO; 3];
            for x in 0..3usize {
                let mut v = E::ZERO;
                for rest in 0..pow3_rem {
                    // rest in base-3; boolean digits only contribute
                    let mut digits_ok = true;
                    let mut wgt = E::ONE;
                    let mut rr = rest;
                    for t in 0..rem {
                        let d = rr % 3;
                        rr /= 3;
                        if d == 2 {
                            digits_ok = false;
                            break;
                        }
                        let c = tau[done + s + 1 + t];
                        if d == 1 {
                            wgt.mul_assign(&c);
                        } else {
                            let mut om = E::ONE;
                            om.sub_assign(&c);
                            wgt.mul_assign(&om);
                        }
                    }
                    if !digits_ok {
                        continue;
                    }
                    let mut t = acc[x + 3 * rest];
                    t.mul_assign(&wgt);
                    v.add_assign(&t);
                }
                h[x] = v;
            }
            let (h0, h1v, hinf) = (h[0], h[1], h[2]);
            let mut h1x = h1v;
            h1x.sub_assign(&h0);
            h1x.sub_assign(&hinf);
            let mut e0 = E::ONE;
            e0.sub_assign(&tau[done + s]);
            let mut e1 = tau[done + s];
            e1.sub_assign(&e0);
            let mut c0 = e0;
            c0.mul_assign(&h0);
            let mut c1 = e0;
            c1.mul_assign(&h1x);
            let mut t = e1;
            t.mul_assign(&h0);
            c1.add_assign(&t);
            let mut c2 = e0;
            c2.mul_assign(&hinf);
            let mut t = e1;
            t.mul_assign(&h1x);
            c2.add_assign(&t);
            let mut c3 = e1;
            c3.mul_assign(&hinf);
            let mut coeffs = [c0, c1, c2, c3];
            for c in coeffs.iter_mut() {
                c.mul_assign(&eq_prefix);
            }
            #[cfg(feature = "gkr_self_checks")]
            {
                let [c0, c1, c2, c3] = coeffs;
                let mut q01 = c0;
                q01.add_assign(&c0);
                q01.add_assign(&c1);
                q01.add_assign(&c2);
                q01.add_assign(&c3);
                assert_eq!(
                    q01, claim,
                    "LSB windowed round {} claim mismatch",
                    done + s
                );
            }
            let r = draw_challenge(&coeffs);
            challenges.push(r);
            win_rs[s] = r;
            let [c0, c1, c2, c3] = coeffs;
            let mut nc = c3;
            nc.mul_assign(&r);
            nc.add_assign(&c2);
            nc.mul_assign(&r);
            nc.add_assign(&c1);
            nc.mul_assign(&r);
            nc.add_assign(&c0);
            claim = nc;
            let mut ew = e1;
            ew.mul_assign(&r);
            ew.add_assign(&e0);
            eq_prefix.mul_assign(&ew);
            round_coefficients.push(coeffs);
            // bind the accumulator: f(r) = f0 + r*(f1-f0) + (r^2-r)*finf
            let mut r2mr = r;
            r2mr.mul_assign(&r);
            r2mr.sub_assign(&r);
            for rest in 0..pow3_rem {
                let f0 = acc[3 * rest];
                let f1 = acc[3 * rest + 1];
                let finf = acc[3 * rest + 2];
                let mut v = f1;
                v.sub_assign(&f0);
                v.mul_assign(&r);
                v.add_assign(&f0);
                let mut t = finf;
                t.mul_assign(&r2mr);
                v.add_assign(&t);
                acc[rest] = v;
            }
            acc.truncate(pow3_rem);
        }

        // ---- one 2^w-tap fold by all window challenges ----
        {
            // multilinear weights over the window's y bits
            let mut wts = [E::ZERO; 8];
            let nw = 1usize << w;
            for y in 0..nw {
                let mut v = E::ONE;
                for s in 0..w {
                    let r = win_rs[s];
                    if (y >> s) & 1 == 1 {
                        v.mul_assign(&r);
                    } else {
                        let mut om = E::ONE;
                        om.sub_assign(&r);
                        v.mul_assign(&om);
                    }
                }
                wts[y] = v;
            }
            let new_len = buffers[0].live_len >> w;
            let out_pairs = new_len / 2;
            let fold_ptrs: Vec<(usize, usize)> = buffers
                .iter_mut()
                .map(|b| {
                    let dst_at = if b.live_at == 0 { b.live_len } else { 0 };
                    (
                        unsafe { b.buf.as_ptr().add(b.live_at) } as usize,
                        unsafe { b.buf.as_mut_ptr().add(dst_at) } as usize,
                    )
                })
                .collect();
            worker.scope_with_threshold(
                out_pairs.max(1),
                (PAR_THRESHOLD >> w).max(1),
                |scope, geometry| {
                    for thread_idx in 0..geometry.num_chunks {
                        let chunk_start = geometry.get_chunk_start_pos(thread_idx);
                        let chunk_size = geometry.get_chunk_size(thread_idx);
                        let fold_ptrs = fold_ptrs.clone();
                        worker::Worker::smart_spawn(
                            scope,
                            thread_idx == geometry.len() - 1,
                            move |_| {
                                for (src_a, dst_a) in fold_ptrs.iter() {
                                    let src = *src_a as *const E;
                                    let dst = *dst_a as *mut E;
                                    for j in chunk_start..(chunk_start + chunk_size) {
                                        for b in 0..2 {
                                            let mut v = E::ZERO;
                                            for y in 0..nw {
                                                let mut t = wts[y];
                                                t.mul_assign(unsafe {
                                                    &*src.add((2 << w) * j + 2 * y + b)
                                                });
                                                v.add_assign(&t);
                                            }
                                            unsafe {
                                                *dst.add(2 * j + b) = v;
                                            }
                                        }
                                    }
                                }
                            },
                        )
                    }
                },
            );
            for b in buffers.iter_mut() {
                let dst_at = if b.live_at == 0 { b.live_len } else { 0 };
                b.live_at = dst_at;
                b.live_len = new_len;
            }
        }

        done += w;
    }

    let mut final_values = Vec::new();
    for buf in buffers.iter() {
        let live = buf.live();
        assert_eq!(live.len(), 2);
        final_values.push([live[0], live[1]]);
    }
    #[cfg(feature = "gkr_self_checks")]
    {
        let fv = &final_values;
        let mut g = gate_batch(relations, |p, b| fv[p][b]);
        g.mul_assign(&eq_prefix);
        assert_eq!(g, claim, "LSB windowed final gate identity");
    }
    (
        LsbDimReducingSumcheckOutput {
            round_coefficients,
            final_claim: claim,
            final_values,
            eq_factor: eq_prefix,
        },
        challenges,
    )
}

/// Redesigned per-round LSB engine ("Step A prime"):
/// * NO input copies: round 0 streams the SOURCE slices; the fold writes into
///   a 0.75x-input scratch (fold-0 output in `[0..m]`, later rounds ping-pong
///   inside it);
/// * COLUMN-WISE gate evaluation: gates are input-disjoint, so each relation
///   streams its own columns over the chunk, accumulating alpha-scaled
///   `[v0, v1, vinf]` triples into a per-thread, chunk-sized buffer (first
///   relation writes, later ones add) -- no per-index relation dispatch;
/// * the eq weighting is ONE column-wise dot product of the triple buffer
///   with the T column, fused into the same chunk while the triples are hot.
pub fn lsb_dim_reducing_sumcheck_prove_columns<
    F: PrimeField,
    E: FieldExtension<F> + Field,
>(
    polys: &[&[E]],
    relations: &[LsbDimReducingRelation<E>],
    tau: &[E],
    claim: E,
    worker: &worker::Worker,
    mut draw_challenge: impl FnMut(&[E; 4]) -> E,
) -> (LsbDimReducingSumcheckOutput<E>, Vec<E>) {
    use crate::gkr::PAR_THRESHOLD;

    let rounds = tau.len();
    let m = 1usize << rounds;
    for p in polys {
        assert_eq!(p.len(), 2 * m);
    }

    let mut t_table = vec![E::ONE; m / 2];
    for b in 0..rounds.saturating_sub(1) {
        let half = 1usize << b;
        let c = tau[1 + b];
        let mut om = E::ONE;
        om.sub_assign(&c);
        for i in 0..half {
            let mut hi = t_table[i];
            hi.mul_assign(&c);
            t_table[i + half] = hi;
            t_table[i].mul_assign(&om);
        }
    }

    // fold scratch: 0.75x of the input size per poly; round 0 reads sources
    let mut scratch: Vec<Vec<E>> = polys.iter().map(|_| vec![E::ZERO; m + m / 2]).collect();
    // (ptr, live offset in scratch or usize::MAX for "source")
    let mut live_src = true;
    let mut live_at = 0usize;
    let mut live_len = 2 * m;

    let mut round_coefficients = Vec::with_capacity(rounds);
    let mut challenges = Vec::with_capacity(rounds);
    let mut claim = claim;
    let mut eq_prefix = E::ONE;

    for s in 0..rounds {
        let pairs = live_len / 4;
        let cur_ptrs: Vec<usize> = if live_src {
            polys.iter().map(|p| p.as_ptr() as usize).collect()
        } else {
            scratch
                .iter()
                .map(|b| unsafe { b.as_ptr().add(live_at) } as usize)
                .collect()
        };
        let t_ptr = t_table.as_ptr() as usize;

        let mut h2 = [E::ZERO; 2];
        {
            let geometry = worker.get_geometry_with_threshold(pairs, PAR_THRESHOLD);
            let mut partials = vec![[E::ZERO; 2]; geometry.num_chunks];
            worker.scope_with_threshold(pairs, PAR_THRESHOLD, |scope, geometry| {
                let mut it = partials.iter_mut();
                for thread_idx in 0..geometry.num_chunks {
                    let chunk_start = geometry.get_chunk_start_pos(thread_idx);
                    let chunk_size = geometry.get_chunk_size(thread_idx);
                    let cur_ptrs = cur_ptrs.clone();
                    let dst = it.next().unwrap();
                    worker::Worker::smart_spawn(
                        scope,
                        thread_idx == geometry.len() - 1,
                        move |_| {
                            // [v0, vinf] only: h(1) is derived from the
                            // round claim, matching the naive path's trick
                            let mut tri = vec![[E::ZERO; 2]; chunk_size];
                            let mut first = true;
                            for rel in relations.iter() {
                                match rel {
                                    LsbDimReducingRelation::PairwiseProduct { input, alpha } => {
                                        let p = cur_ptrs[*input] as *const E;
                                        for (jj, t) in tri.iter_mut().enumerate() {
                                            let j = chunk_start + jj;
                                            let (a0, b0, a1, b1) = unsafe {
                                                (
                                                    *p.add(4 * j),
                                                    *p.add(4 * j + 1),
                                                    *p.add(4 * j + 2),
                                                    *p.add(4 * j + 3),
                                                )
                                            };
                                            let mut v0 = a0;
                                            v0.mul_assign(&b0);
                                            v0.mul_assign(alpha);
                                            let mut da = a1;
                                            da.sub_assign(&a0);
                                            let mut db = b1;
                                            db.sub_assign(&b0);
                                            let mut vinf = da;
                                            vinf.mul_assign(&db);
                                            vinf.mul_assign(alpha);
                                            if first {
                                                *t = [v0, vinf];
                                            } else {
                                                t[0].add_assign(&v0);
                                                t[1].add_assign(&vinf);
                                            }
                                        }
                                    }
                                    LsbDimReducingRelation::LogupPair {
                                        num,
                                        den,
                                        alpha_num,
                                        alpha_den,
                                    } => {
                                        let n = cur_ptrs[*num] as *const E;
                                        let d = cur_ptrs[*den] as *const E;
                                        for (jj, t) in tri.iter_mut().enumerate() {
                                            let j = chunk_start + jj;
                                            let (n0, n1, n2, n3) = unsafe {
                                                (
                                                    *n.add(4 * j),
                                                    *n.add(4 * j + 1),
                                                    *n.add(4 * j + 2),
                                                    *n.add(4 * j + 3),
                                                )
                                            };
                                            let (d0, d1, d2, d3) = unsafe {
                                                (
                                                    *d.add(4 * j),
                                                    *d.add(4 * j + 1),
                                                    *d.add(4 * j + 2),
                                                    *d.add(4 * j + 3),
                                                )
                                            };
                                            // X = 0 point: pair (n0,n1,d0,d1); X = inf: diffs
                                            let quad = |na: E, nb: E, da_: E, db_: E| -> (E, E) {
                                                let mut num_v = na;
                                                num_v.mul_assign(&db_);
                                                let mut t2 = nb;
                                                t2.mul_assign(&da_);
                                                num_v.add_assign(&t2);
                                                let mut den_v = da_;
                                                den_v.mul_assign(&db_);
                                                (num_v, den_v)
                                            };
                                            let (num0, den0) = quad(n0, n1, d0, d1);
                                            let mut dn0 = n2;
                                            dn0.sub_assign(&n0);
                                            let mut dn1 = n3;
                                            dn1.sub_assign(&n1);
                                            let mut dd0 = d2;
                                            dd0.sub_assign(&d0);
                                            let mut dd1 = d3;
                                            dd1.sub_assign(&d1);
                                            let (numi, deni) = quad(dn0, dn1, dd0, dd1);
                                            let mut vals = [E::ZERO; 2];
                                            for (k, (nv, dv)) in
                                                [(num0, den0), (numi, deni)].into_iter().enumerate()
                                            {
                                                let mut v = nv;
                                                v.mul_assign(alpha_num);
                                                let mut w = dv;
                                                w.mul_assign(alpha_den);
                                                v.add_assign(&w);
                                                vals[k] = v;
                                            }
                                            if first {
                                                *t = vals;
                                            } else {
                                                t[0].add_assign(&vals[0]);
                                                t[1].add_assign(&vals[1]);
                                            }
                                        }
                                    }
                                }
                                first = false;
                            }
                            // fused eq dot product over the hot triples
                            let t_tab = t_ptr as *const E;
                            let mut acc = [E::ZERO; 2];
                            for (jj, t) in tri.iter().enumerate() {
                                let w = unsafe { *t_tab.add(chunk_start + jj) };
                                for k in 0..2 {
                                    let mut v = t[k];
                                    v.mul_assign(&w);
                                    acc[k].add_assign(&v);
                                }
                            }
                            *dst = acc;
                        },
                    )
                }
            });
            for p in partials {
                for k in 0..2 {
                    h2[k].add_assign(&p[k]);
                }
            }
        }

        let (h0, hinf) = (h2[0], h2[1]);
        let h1v = derive_h1_from_claim(&claim, &eq_prefix, &h0, &tau[s]);
        let coeffs = cubic_round_message(&h0, &h1v, &hinf, &tau[s], &eq_prefix);
        #[cfg(feature = "gkr_self_checks")]
        {
            let [c0, c1, c2, c3] = coeffs;
            let mut q01 = c0;
            q01.add_assign(&c0);
            q01.add_assign(&c1);
            q01.add_assign(&c2);
            q01.add_assign(&c3);
            assert_eq!(q01, claim, "LSB columns round {} claim mismatch", s);
        }
        let r = draw_challenge(&coeffs);
        challenges.push(r);
        round_coefficients.push(coeffs);
        claim = horner4(&coeffs, &r);
        eq_prefix.mul_assign(&eq_weight(&tau[s], &r));

        // column-wise fold: src (round 0) or scratch live region -> next region
        {
            let new_len = live_len / 2;
            let dst_at = if live_src {
                0
            } else if live_at == 0 {
                m
            } else {
                0
            };
            let out_pairs = new_len / 2;
            let fold_ptrs: Vec<(usize, usize)> = (0..polys.len())
                .map(|p| {
                    let src_p = cur_ptrs[p];
                    let dst_p = unsafe { scratch[p].as_mut_ptr().add(dst_at) } as usize;
                    (src_p, dst_p)
                })
                .collect();
            worker.scope_with_threshold(
                out_pairs.max(1),
                PAR_THRESHOLD,
                |scope, geometry| {
                    for thread_idx in 0..geometry.num_chunks {
                        let chunk_start = geometry.get_chunk_start_pos(thread_idx);
                        let chunk_size = geometry.get_chunk_size(thread_idx);
                        let fold_ptrs = fold_ptrs.clone();
                        worker::Worker::smart_spawn(
                            scope,
                            thread_idx == geometry.len() - 1,
                            move |_| {
                                for (src_a, dst_a) in fold_ptrs.iter() {
                                    let src = *src_a as *const E;
                                    let dst = *dst_a as *mut E;
                                    for j in chunk_start..(chunk_start + chunk_size) {
                                        for b in 0..2 {
                                            unsafe {
                                                let lo = *src.add(4 * j + b);
                                                let hi = *src.add(4 * j + 2 + b);
                                                let mut v = hi;
                                                v.sub_assign(&lo);
                                                v.mul_assign(&r);
                                                v.add_assign(&lo);
                                                *dst.add(2 * j + b) = v;
                                            }
                                        }
                                    }
                                }
                            },
                        )
                    }
                },
            );
            live_src = false;
            live_at = dst_at;
            live_len = new_len;
        }

        if s + 1 < rounds {
            let next = pairs / 2;
            for j in 0..next {
                let mut v = t_table[2 * j];
                v.add_assign(&t_table[2 * j + 1]);
                t_table[j] = v;
            }
        }
    }

    let mut final_values = Vec::new();
    for b in scratch.iter() {
        let live = &b[live_at..live_at + 2];
        final_values.push([live[0], live[1]]);
    }
    #[cfg(feature = "gkr_self_checks")]
    {
        let fv = &final_values;
        let mut g = gate_batch(relations, |p, b| fv[p][b]);
        g.mul_assign(&eq_prefix);
        assert_eq!(g, claim, "LSB columns final gate identity");
    }
    (
        LsbDimReducingSumcheckOutput {
            round_coefficients,
            final_claim: claim,
            final_values,
            eq_factor: eq_prefix,
        },
        challenges,
    )
}


/// Portable scalar chunk kernel of the fused sweep (the naive backend's
/// choice). Platform-specialized kernels live in the platform backends.
#[allow(clippy::too_many_arguments)]
use crate::gkr::prover::{SendConstPtr, SendPtr};

/// h(1) from the round claim: `claim = eq_prefix * ((1 - tau)*h(0) + tau*h(1))`.
#[inline]
pub(crate) fn derive_h1_from_claim<E: Field>(claim: &E, eq_prefix: &E, h0: &E, tau_s: &E) -> E {
    let mut e0 = E::ONE;
    e0.sub_assign(tau_s);
    let mut v = *claim;
    v.mul_assign(&eq_prefix.inverse().expect("eq prefix nonzero"));
    let mut t = e0;
    t.mul_assign(h0);
    v.sub_assign(&t);
    v.mul_assign(&tau_s.inverse().expect("tau nonzero"));
    v
}

/// Monomial coefficients of the cubic round message
/// `q(X) = eq_prefix * eqw(X) * h(X)` from the `(h0, h1, hinf)` triple, with
/// `eqw(X) = (1 - tau) + (2*tau - 1)*X` and
/// `h(X) = h0 + (h1 - h0 - hinf)*X + hinf*X^2`.
#[inline]
pub(crate) fn cubic_round_message<E: Field>(h0: &E, h1: &E, hinf: &E, tau_s: &E, eq_prefix: &E) -> [E; 4] {
    let mut h1x = *h1;
    h1x.sub_assign(h0);
    h1x.sub_assign(hinf);
    let mut e0 = E::ONE;
    e0.sub_assign(tau_s);
    let mut e1 = *tau_s;
    e1.sub_assign(&e0);
    let mut c0 = e0;
    c0.mul_assign(h0);
    let mut c1 = e0;
    c1.mul_assign(&h1x);
    let mut t = e1;
    t.mul_assign(h0);
    c1.add_assign(&t);
    let mut c2 = e0;
    c2.mul_assign(hinf);
    let mut t = e1;
    t.mul_assign(&h1x);
    c2.add_assign(&t);
    let mut c3 = e1;
    c3.mul_assign(hinf);
    let mut coeffs = [c0, c1, c2, c3];
    for c in coeffs.iter_mut() {
        c.mul_assign(eq_prefix);
    }
    coeffs
}

/// Horner evaluation of the 4-coefficient round message at `r`.
#[inline]
pub(crate) fn horner4<E: Field>(c: &[E; 4], r: &E) -> E {
    let mut nc = c[3];
    nc.mul_assign(r);
    nc.add_assign(&c[2]);
    nc.mul_assign(r);
    nc.add_assign(&c[1]);
    nc.mul_assign(r);
    nc.add_assign(&c[0]);
    nc
}

/// Coordinate of the output-layer variable bound at round `s`: the incoming
/// point is in the dimension-reducing emission layout `[bits 1.., bit 0]`
/// (gate coordinate stored last), so round 0 (output bit 0) reads the LAST
/// entry and round `s >= 1` reads entry `s - 1`.
#[inline(always)]
fn round_coord<E: Field>(output_point: &[E], s: usize) -> E {
    if s == 0 {
        output_point[output_point.len() - 1]
    } else {
        output_point[s - 1]
    }
}

/// The bound round's eq weight `(1 - tau) + (2*tau - 1)*r = eq(r, tau)`.
#[inline]
pub(crate) fn eq_weight<E: Field>(tau_s: &E, r: &E) -> E {
    let mut e0 = E::ONE;
    e0.sub_assign(tau_s);
    let mut e1 = *tau_s;
    e1.sub_assign(&e0);
    let mut ew = e1;
    ew.mul_assign(r);
    ew.add_assign(&e0);
    ew
}

/// Per-poly fetch of the CURRENT 4 pair values, folding + storing on the fly
/// when a challenge is pending. Ancestor layout: value (Y', b) at index
/// 2*Y' + b; the pending fold combines Y' = 2q, 2q+1 -> q, so the current
/// pair j covers folded Y in {2j, 2j+1}, i.e. ancestors Y' in {4j..4j+4}.
#[inline(always)]
fn scalar_fetch_pair4<E: Field>(
    cur_ptrs: &[SendConstPtr<E>],
    dst_ptrs: &[SendPtr<E>],
    rp: &Option<E>,
    p: usize,
    j: usize,
) -> [E; 4] {
    let src = cur_ptrs[p].0;
    match rp {
        None => unsafe {
            [
                *src.add(4 * j),
                *src.add(4 * j + 1),
                *src.add(4 * j + 2),
                *src.add(4 * j + 3),
            ]
        },
        Some(r) => unsafe {
            let d = dst_ptrs[p].0;
            let mut out = [E::ZERO; 4];
            for yy in 0..2 {
                for b in 0..2 {
                    let lo = *src.add(2 * (4 * j + 2 * yy) + b);
                    let hi = *src.add(2 * (4 * j + 2 * yy + 1) + b);
                    let mut v = hi;
                    v.sub_assign(&lo);
                    v.mul_assign(r);
                    v.add_assign(&lo);
                    *d.add(2 * (2 * j + yy) + b) = v;
                    out[2 * yy + b] = v;
                }
            }
            out
        },
    }
}

/// num = na*db + nb*da, den = da*db.
#[inline(always)]
fn scalar_logup_quad<E: Field>(na: E, nb: E, da: E, db: E) -> (E, E) {
    let mut num_v = na;
    num_v.mul_assign(&db);
    let mut t2 = nb;
    t2.mul_assign(&da);
    num_v.add_assign(&t2);
    let mut den_v = da;
    den_v.mul_assign(&db);
    (num_v, den_v)
}

pub(crate) fn scalar_fused_chunk<E: Field>(
    cur_ptrs: &[SendConstPtr<E>],
    dst_ptrs: &[SendPtr<E>],
    out_ptrs: &[[SendConstPtr<E>; 2]],
    relations: &[LsbDimReducingRelation<E>],
    rp: Option<E>,
    t_ptr: SendConstPtr<E>,
    chunk_start: usize,
    chunk_size: usize,
    scratch: SendPtr<[u128; 2]>,
) -> [E; 2] {
    // caller-provided tri scratch: [v0, vinf] per row
    let tri =
        unsafe { core::slice::from_raw_parts_mut(scratch.0 as *mut [E; 2], chunk_size) };
    for t in tri.iter_mut() {
        *t = [E::ZERO; 2];
    }
    let mut first = true;
    for (rel_idx, rel) in relations.iter().enumerate() {
        match rel {
            LsbDimReducingRelation::PairwiseProduct { input, alpha } => {
                for (jj, t) in tri.iter_mut().enumerate() {
                    let j = chunk_start + jj;
                    let [a0, b0, a1, b1] =
                        scalar_fetch_pair4(cur_ptrs, dst_ptrs, &rp, *input, j);
                    // round 0: the output layer already holds the gate value
                    // at X = 0 -- read it instead of re-evaluating
                    let mut v0 = if rp.is_none() && !out_ptrs.is_empty() {
                        unsafe { *out_ptrs[rel_idx][0].0.add(2 * j) }
                    } else {
                        let mut v = a0;
                        v.mul_assign(&b0);
                        v
                    };
                    v0.mul_assign(alpha);
                    let mut da = a1;
                    da.sub_assign(&a0);
                    let mut db = b1;
                    db.sub_assign(&b0);
                    let mut vinf = da;
                    vinf.mul_assign(&db);
                    vinf.mul_assign(alpha);
                    if first {
                        *t = [v0, vinf];
                    } else {
                        t[0].add_assign(&v0);
                        t[1].add_assign(&vinf);
                    }
                }
            }
            LsbDimReducingRelation::LogupPair {
                num,
                den,
                alpha_num,
                alpha_den,
            } => {
                for (jj, t) in tri.iter_mut().enumerate() {
                    let j = chunk_start + jj;
                    let [n0, n1, n2, n3] =
                        scalar_fetch_pair4(cur_ptrs, dst_ptrs, &rp, *num, j);
                    let [d0, d1, d2, d3] =
                        scalar_fetch_pair4(cur_ptrs, dst_ptrs, &rp, *den, j);
                    let (num0, den0) = if rp.is_none() && !out_ptrs.is_empty() {
                        unsafe {
                            (
                                *out_ptrs[rel_idx][0].0.add(2 * j),
                                *out_ptrs[rel_idx][1].0.add(2 * j),
                            )
                        }
                    } else {
                        scalar_logup_quad(n0, n1, d0, d1)
                    };
                    let mut dn0 = n2;
                    dn0.sub_assign(&n0);
                    let mut dn1 = n3;
                    dn1.sub_assign(&n1);
                    let mut dd0 = d2;
                    dd0.sub_assign(&d0);
                    let mut dd1 = d3;
                    dd1.sub_assign(&d1);
                    let (numi, deni) = scalar_logup_quad(dn0, dn1, dd0, dd1);
                    let mut vals = [E::ZERO; 2];
                    for (k, (nv, dv)) in
                        [(num0, den0), (numi, deni)].into_iter().enumerate()
                    {
                        let mut v = nv;
                        v.mul_assign(alpha_num);
                        let mut w = dv;
                        w.mul_assign(alpha_den);
                        v.add_assign(&w);
                        vals[k] = v;
                    }
                    if first {
                        *t = vals;
                    } else {
                        t[0].add_assign(&vals[0]);
                        t[1].add_assign(&vals[1]);
                    }
                }
            }
        }
        first = false;
    }
    let t_tab = t_ptr.0;
    let mut acc = [E::ZERO; 2];
    for (jj, t) in tri.iter().enumerate() {
        let w = unsafe { *t_tab.add(chunk_start + jj) };
        for k in 0..2 {
            let mut v = t[k];
            v.mul_assign(&w);
            acc[k].add_assign(&v);
        }
    }
    acc

}

/// Fold-on-read variant of [`lsb_dim_reducing_sumcheck_prove_columns`]: the
/// fold by round `s-1`'s challenge is FUSED into round `s`'s evaluation
/// sweep -- each output pair reads its 8 not-yet-folded ancestors, folds them
/// to 4 current values (stored for the next round), and feeds the tri buffer
/// from the hot results. One memory sweep per round (12 traffic units vs 16
/// for eval + separate fold), mirroring the naive path's
/// `get_for_sumcheck_round_1` fusion. The LAST challenge's fold runs as a
/// tiny epilogue to produce the final `[E;2]` lines.
pub fn lsb_dim_reducing_sumcheck_prove_fused<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    CK: Fn(
            &[SendConstPtr<E>],
            &[SendPtr<E>],
            &[[SendConstPtr<E>; 2]],
            &[LsbDimReducingRelation<E>],
            Option<E>,
            SendConstPtr<E>,
            usize,
            usize,
            SendPtr<[u128; 2]>,
        ) -> [E; 2]
        + Send
        + Sync
        + Copy,
>(
    polys: &[&[E]],
    relations: &[LsbDimReducingRelation<E>],
    output_ptrs: &[[SendConstPtr<E>; 2]],
    tau: &[E],
    claim: E,
    worker: &worker::Worker,
    schedule: &[crate::gkr::prover_config::SumcheckStep],
    fold_scratch: &mut [Box<[core::mem::MaybeUninit<E>]>],
    tri_scratch: &mut [Box<[core::mem::MaybeUninit<[u128; 2]>]>],
    chunk_kernel: CK,
    mut draw_challenge: impl FnMut(&[E; 4]) -> E,
    mut on_round0_done: impl FnMut(),
) -> (LsbDimReducingSumcheckOutput<E>, Vec<E>) {
    use crate::gkr::PAR_THRESHOLD;

    let rounds = tau.len();
    let m = 1usize << rounds;
    for p in polys {
        assert_eq!(p.len(), 2 * m);
    }

    // suffix eq table over the round-1.. coordinates. In the emission layout
    // these are exactly the CONTIGUOUS prefix `tau[..rounds - 1]` (bits 1..
    // stored first), so no reordering of any kind is needed.
    let mut t_table =
        crate::gkr::sumcheck::eq_poly::make_eq_table_lsb_first(&tau[..rounds - 1], worker);

    // Caller-provided uninitialized fold scratch: writes are tracked by
    // construction (each round writes exactly the region the next round
    // reads), raw pointers only.
    assert_eq!(fold_scratch.len(), polys.len());
    for b in fold_scratch.iter() {
        assert!(b.len() >= m + m / 2);
    }
    let scratch = fold_scratch;
    // caller-provided per-worker-slot tri scratch (max-sized across layers)
    assert!(tri_scratch.len() >= worker.num_cores);
    let tri_need = (m / 2).div_ceil(worker.num_cores).max(PAR_THRESHOLD);
    for b in tri_scratch.iter() {
        assert!(b.len() >= tri_need);
    }
    // state: data folded through challenges[..s-1] lives at (src flag, at, len);
    // pending = challenge whose fold has not been materialized yet
    let mut live_src = true;
    let mut live_at = 0usize;
    let mut live_len = 2 * m;
    let mut pending_r: Option<E> = None;

    let mut round_coefficients = Vec::with_capacity(rounds);
    let mut challenges = Vec::with_capacity(rounds);
    let mut claim = claim;
    let mut eq_prefix = E::ONE;
    let mut done = 0usize;

    // ---- windowed head: leading WindowedOp steps of the schedule ----
    // Each head window computes the T-weighted {0,1,inf}^w accumulator in one
    // pass over the CURRENT live data, runs the bind chain (w rounds of
    // transcript interaction), and folds all polys by the window's
    // challenges in one 2^w-tap pass into the uninit scratch. Sizes are
    // tiered: worker-parallel rows, then thread-per-relation, then serial.
    {
        use crate::gkr::prover_config::SumcheckStep;
        let mut t_full: Option<Vec<E>> = None;
        for step in schedule {
            let w = match step {
                SumcheckStep::WindowedOp(op) => match op {
                    crate::gkr::prover_config::WindowedOp::Initial { window }
                    | crate::gkr::prover_config::WindowedOp::Transition { window }
                    | crate::gkr::prover_config::WindowedOp::Interior { window } => *window,
                },
                _ => break, // naive tail handled by the per-round loop below
            };
            assert!(w >= 1 && w <= 3);
            assert!(done + w <= rounds);
            let pow3 = 3usize.pow(w as u32);
            // current data length is live_len (2 * remaining Y-space);
            // each window row covers 2^w Y values = 2^(w+1) data values
            let win_rows = live_len >> (w + 1);
            // suffix table over tau[done + w ..]
            let t_win = {
                let len_log2 = rounds - done - w;
                let mut t = vec![E::ONE; 1 << len_log2];
                for b in 0..len_log2 {
                    let half = 1usize << b;
                    let c = round_coord(tau, done + w + b);
                    let mut om = E::ONE;
                    om.sub_assign(&c);
                    for i in 0..half {
                        let mut hi = t[i];
                        hi.mul_assign(&c);
                        t[i + half] = hi;
                        t[i].mul_assign(&om);
                    }
                }
                t
            };
            let _ = &mut t_full;
            let cur_ptrs: Vec<usize> = if live_src {
                polys.iter().map(|p| p.as_ptr() as usize).collect()
            } else {
                scratch
                    .iter()
                    .map(|b| unsafe { (b.as_ptr() as *const E).add(live_at) } as usize)
                    .collect()
            };
            // ---- accumulator pass, size-tiered ----
            let acc_pass = |chunk_start: usize, chunk_size: usize| -> Vec<E> {
                let mut local = vec![E::ZERO; pow3];
                let mut taps = [E::ZERO; 8];
                let npolys = cur_ptrs.len();
                let mut grids = vec![E::ZERO; npolys * 2 * 27];
                for j in chunk_start..(chunk_start + chunk_size) {
                    let base_idx = (2usize << w) * j;
                    for p in 0..npolys {
                        let src = cur_ptrs[p] as *const E;
                        for b in 0..2 {
                            for y in 0..(1usize << w) {
                                taps[y] = unsafe { *src.add(base_idx + 2 * y + b) };
                            }
                            let g = &mut grids[(p * 2 + b) * 27..(p * 2 + b) * 27 + 27];
                            match w {
                                3 => window_cells::<E, 3>(&taps[..8], g),
                                2 => window_cells::<E, 2>(&taps[..4], g),
                                1 => window_cells::<E, 1>(&taps[..2], g),
                                _ => unreachable!(),
                            }
                        }
                    }
                    let tw = t_win[j];
                    for c in 0..pow3 {
                        let v = gate_batch(relations, |p, b| grids[(p * 2 + b) * 27 + c]);
                        let mut t = v;
                        t.mul_assign(&tw);
                        local[c].add_assign(&t);
                    }
                }
                local
            };
            const SERIAL_ROWS: usize = 1 << 8;
            let mut acc = vec![E::ZERO; pow3];
            if win_rows <= SERIAL_ROWS {
                // fully serial
                acc = acc_pass(0, win_rows);
            } else if win_rows <= crate::gkr::PAR_THRESHOLD {
                // thread-per-relation band: each relation streams all rows
                let n_rel = relations.len().max(1);
                let mut partials = vec![vec![E::ZERO; pow3]; n_rel];
                std::thread::scope(|sc| {
                    for (ri, dst) in partials.iter_mut().enumerate() {
                        let cur_ptrs = cur_ptrs.clone();
                        let t_win = &t_win;
                        let rel = relations[ri];
                        sc.spawn(move || {
                            let one_rel = [rel];
                            let mut local = vec![E::ZERO; pow3];
                            let mut taps = [E::ZERO; 8];
                            let mut grids = vec![E::ZERO; 2 * 2 * 27];
                            for j in 0..win_rows {
                                let base_idx = (2usize << w) * j;
                                // load only this relation's polys
                                let mut load = |slot: usize, p: usize| {
                                    let src = cur_ptrs[p] as *const E;
                                    for b in 0..2 {
                                        for y in 0..(1usize << w) {
                                            taps[y] =
                                                unsafe { *src.add(base_idx + 2 * y + b) };
                                        }
                                        let g = &mut grids
                                            [(slot * 2 + b) * 27..(slot * 2 + b) * 27 + 27];
                                        match w {
                                            3 => window_cells::<E, 3>(&taps[..8], g),
                                            2 => window_cells::<E, 2>(&taps[..4], g),
                                            1 => window_cells::<E, 1>(&taps[..2], g),
                                            _ => unreachable!(),
                                        }
                                    }
                                };
                                let remap = match rel {
                                    LsbDimReducingRelation::PairwiseProduct { input, alpha } => {
                                        load(0, input);
                                        [LsbDimReducingRelation::PairwiseProduct {
                                            input: 0,
                                            alpha,
                                        }; 1]
                                    }
                                    LsbDimReducingRelation::LogupPair {
                                        num,
                                        den,
                                        alpha_num,
                                        alpha_den,
                                    } => {
                                        load(0, num);
                                        load(1, den);
                                        [LsbDimReducingRelation::LogupPair {
                                            num: 0,
                                            den: 1,
                                            alpha_num,
                                            alpha_den,
                                        }; 1]
                                    }
                                };
                                let _ = &one_rel;
                                let tw = t_win[j];
                                for c in 0..pow3 {
                                    let v = gate_batch(&remap, |p, b| {
                                        grids[(p * 2 + b) * 27 + c]
                                    });
                                    let mut t = v;
                                    t.mul_assign(&tw);
                                    local[c].add_assign(&t);
                                }
                            }
                            *dst = local;
                        });
                    }
                });
                for p in partials {
                    for (a, v) in acc.iter_mut().zip(p.into_iter()) {
                        a.add_assign(&v);
                    }
                }
            } else {
                // worker-parallel rows
                let geometry = worker
                    .get_geometry_with_threshold(win_rows, (crate::gkr::PAR_THRESHOLD >> w).max(1));
                let mut partials = vec![vec![E::ZERO; pow3]; geometry.num_chunks];
                worker.scope_with_threshold(
                    win_rows,
                    (crate::gkr::PAR_THRESHOLD >> w).max(1),
                    |scope, geometry| {
                        let mut it = partials.iter_mut();
                        for thread_idx in 0..geometry.num_chunks {
                            let chunk_start = geometry.get_chunk_start_pos(thread_idx);
                            let chunk_size = geometry.get_chunk_size(thread_idx);
                            let dst = it.next().unwrap();
                            let acc_pass = &acc_pass;
                            worker::Worker::smart_spawn(
                                scope,
                                thread_idx == geometry.len() - 1,
                                move |_| {
                                    *dst = acc_pass(chunk_start, chunk_size);
                                },
                            )
                        }
                    },
                );
                for p in partials {
                    for (a, v) in acc.iter_mut().zip(p.into_iter()) {
                        a.add_assign(&v);
                    }
                }
            }
            // ---- bind chain over the window ----
            let mut win_rs = [E::ZERO; 3];
            for si in 0..w {
                let rem = w - si - 1;
                let pow3_rem = 3usize.pow(rem as u32);
                let mut h = [E::ZERO; 3];
                for x in 0..3usize {
                    let mut v = E::ZERO;
                    for rest in 0..pow3_rem {
                        let mut wgt = E::ONE;
                        let mut rr = rest;
                        let mut ok = true;
                        for tvar in 0..rem {
                            let d = rr % 3;
                            rr /= 3;
                            if d == 2 {
                                ok = false;
                                break;
                            }
                            let c = round_coord(tau, done + si + 1 + tvar);
                            if d == 1 {
                                wgt.mul_assign(&c);
                            } else {
                                let mut om = E::ONE;
                                om.sub_assign(&c);
                                wgt.mul_assign(&om);
                            }
                        }
                        if !ok {
                            continue;
                        }
                        let mut t = acc[x + 3 * rest];
                        t.mul_assign(&wgt);
                        v.add_assign(&t);
                    }
                    h[x] = v;
                }
                let (h0, h1v, hinf) = (h[0], h[1], h[2]);
                let coeffs =
                    cubic_round_message(&h0, &h1v, &hinf, &round_coord(tau, done + si), &eq_prefix);
                #[cfg(feature = "gkr_self_checks")]
                {
                    let [c0, c1, c2, c3] = coeffs;
                    let mut q01 = c0;
                    q01.add_assign(&c0);
                    q01.add_assign(&c1);
                    q01.add_assign(&c2);
                    q01.add_assign(&c3);
                    assert_eq!(q01, claim, "LSB head round {} claim mismatch", done + si);
                }
                let r = draw_challenge(&coeffs);
                challenges.push(r);
                round_coefficients.push(coeffs);
                win_rs[si] = r;
                claim = horner4(&coeffs, &r);
                eq_prefix.mul_assign(&eq_weight(&round_coord(tau, done + si), &r));
                // bind the accumulator
                let mut r2mr = r;
                r2mr.mul_assign(&r);
                r2mr.sub_assign(&r);
                for rest in 0..pow3_rem {
                    let f0 = acc[3 * rest];
                    let f1 = acc[3 * rest + 1];
                    let finf = acc[3 * rest + 2];
                    let mut v = f1;
                    v.sub_assign(&f0);
                    v.mul_assign(&r);
                    v.add_assign(&f0);
                    let mut t = finf;
                    t.mul_assign(&r2mr);
                    v.add_assign(&t);
                    acc[rest] = v;
                }
                acc.truncate(pow3_rem.max(1));
            }
            // ---- one 2^w-tap fold into the scratch ----
            {
                let nw = 1usize << w;
                let mut wts = [E::ZERO; 8];
                for y in 0..nw {
                    let mut v = E::ONE;
                    for si in 0..w {
                        let r = win_rs[si];
                        if (y >> si) & 1 == 1 {
                            v.mul_assign(&r);
                        } else {
                            let mut om = E::ONE;
                            om.sub_assign(&r);
                            v.mul_assign(&om);
                        }
                    }
                    wts[y] = v;
                }
                let new_len = live_len >> w;
                let dst_at = if live_src {
                    0
                } else if live_at == 0 {
                    m
                } else {
                    0
                };
                let out_pairs = (new_len / 2).max(1);
                let dst_ptrs2: Vec<usize> = scratch
                    .iter_mut()
                    .map(|b| unsafe { (b.as_mut_ptr() as *mut E).add(dst_at) } as usize)
                    .collect();
                worker.scope_with_threshold(
                    out_pairs,
                    (crate::gkr::PAR_THRESHOLD >> w).max(1),
                    |scope, geometry| {
                        for thread_idx in 0..geometry.num_chunks {
                            let chunk_start = geometry.get_chunk_start_pos(thread_idx);
                            let chunk_size = geometry.get_chunk_size(thread_idx);
                            let cur_ptrs = cur_ptrs.clone();
                            let dst_ptrs2 = dst_ptrs2.clone();
                            worker::Worker::smart_spawn(
                                scope,
                                thread_idx == geometry.len() - 1,
                                move |_| {
                                    for (src_a, dst_a) in
                                        cur_ptrs.iter().zip(dst_ptrs2.iter())
                                    {
                                        let src = *src_a as *const E;
                                        let dst = *dst_a as *mut E;
                                        for jj in chunk_start..(chunk_start + chunk_size) {
                                            for b in 0..2 {
                                                let mut v = E::ZERO;
                                                for y in 0..nw {
                                                    let mut t = wts[y];
                                                    t.mul_assign(unsafe {
                                                        &*src.add((2 << w) * jj + 2 * y + b)
                                                    });
                                                    v.add_assign(&t);
                                                }
                                                unsafe {
                                                    *dst.add(2 * jj + b) = v;
                                                }
                                            }
                                        }
                                    }
                                },
                            )
                        }
                    },
                );
                live_src = false;
                live_at = dst_at;
                live_len = new_len;
            }
            done += w;
            if done == w {
                // outputs (never read by the windowed head) are dead
                on_round0_done();
            }
        }
    }

    // after a windowed head the data is already folded (and the output layer
    // possibly purged): the tail must never take the round-0 output-read path
    let tail_output_ptrs: &[[SendConstPtr<E>; 2]] = if done == 0 { output_ptrs } else { &[] };
    // the head consumed `done` variables: rebuild the tail's suffix eq table
    // over tau[done + 1 ..] (the per-round contraction takes over from there)
    if done > 0 && done < rounds {
        let len_log2 = rounds - done - 1;
        for v in t_table.iter_mut().take(1 << len_log2) {
            *v = E::ONE;
        }
        for b in 0..len_log2 {
            let half = 1usize << b;
            let c = tau[done + 1 + b];
            let mut om = E::ONE;
            om.sub_assign(&c);
            for i in 0..half {
                let mut hi = t_table[i];
                hi.mul_assign(&c);
                t_table[i + half] = hi;
                t_table[i].mul_assign(&om);
            }
        }
    }
    for s in done..rounds {
        // pairs of the CURRENT round (after the pending fold is applied)
        let cur_len = if pending_r.is_some() {
            live_len / 2
        } else {
            live_len
        };
        let pairs = cur_len / 4;
        let cur_ptrs: Vec<SendConstPtr<E>> = if live_src {
            polys.iter().map(|p| SendConstPtr(p.as_ptr())).collect()
        } else {
            scratch
                .iter()
                .map(|b| SendConstPtr(unsafe { (b.as_ptr() as *const E).add(live_at) }))
                .collect()
        };
        // fold destination (only used when a fold is pending)
        let dst_at = if live_src {
            0
        } else if live_at == 0 {
            m
        } else {
            0
        };
        let dst_ptrs: Vec<SendPtr<E>> = scratch
            .iter_mut()
            .map(|b| SendPtr(unsafe { (b.as_mut_ptr() as *mut E).add(dst_at) }))
            .collect();
        let t_ptr = SendConstPtr(t_table.as_ptr());
        let rp = pending_r;

        let mut h2 = [E::ZERO; 2];
        {
            let geometry = worker.get_geometry_with_threshold(pairs, PAR_THRESHOLD);
            let mut partials = vec![[E::ZERO; 2]; geometry.num_chunks];
            worker.scope_with_threshold(pairs, PAR_THRESHOLD, |scope, geometry| {
                let mut it = partials.iter_mut();
                let mut sit = tri_scratch.iter_mut();
                for thread_idx in 0..geometry.num_chunks {
                    let chunk_start = geometry.get_chunk_start_pos(thread_idx);
                    let chunk_size = geometry.get_chunk_size(thread_idx);
                    let cur_ptrs = cur_ptrs.clone();
                    let dst_ptrs = dst_ptrs.clone();
                    let dst = it.next().unwrap();
                    let sc = sit.next().expect("chunks never exceed worker slots");
                    debug_assert!(chunk_size <= sc.len());
                    let scratch_ptr = SendPtr(sc.as_mut_ptr() as *mut [u128; 2]);
                    worker::Worker::smart_spawn(
                        scope,
                        thread_idx == geometry.len() - 1,
                        move |_| {
                            *dst = chunk_kernel(
                                &cur_ptrs,
                                &dst_ptrs,
                                tail_output_ptrs,
                                relations,
                                rp,
                                t_ptr,
                                chunk_start,
                                chunk_size,
                                scratch_ptr,
                            );
                        },
                    )
                }
            });
            for p in partials {
                for k in 0..2 {
                    h2[k].add_assign(&p[k]);
                }
            }
        }
        // commit the materialized fold
        if pending_r.is_some() {
            live_src = false;
            live_at = dst_at;
            live_len = cur_len;
        }
        if s == 0 {
            // the output layer's values were consumed by round 0's pass and
            // are dead from here on -- the caller can purge them now (frees
            // pages the fold scratch immediately reuses)
            on_round0_done();
        }

        let (h0, hinf) = (h2[0], h2[1]);
        let h1v = derive_h1_from_claim(&claim, &eq_prefix, &h0, &round_coord(tau, s));
        let coeffs = cubic_round_message(&h0, &h1v, &hinf, &round_coord(tau, s), &eq_prefix);
        let r = draw_challenge(&coeffs);
        challenges.push(r);
        round_coefficients.push(coeffs);
        claim = horner4(&coeffs, &r);
        eq_prefix.mul_assign(&eq_weight(&round_coord(tau, s), &r));
        pending_r = Some(r);

        if s + 1 < rounds {
            let next = pairs / 2;
            for j in 0..next {
                let mut v = t_table[2 * j];
                v.add_assign(&t_table[2 * j + 1]);
                t_table[j] = v;
            }
        }
    }

    // epilogue: materialize the last fold (4 -> 2 values per poly) when a
    // naive round left one pending; an all-window schedule folds eagerly and
    // arrives here with the live region already at its final 2 values
    let mut final_values = Vec::new();
    for (p, _) in polys.iter().enumerate() {
        // the live region is fully initialized by the last materialized fold
        let src: &[E] = if live_src {
            polys[p]
        } else {
            unsafe {
                core::slice::from_raw_parts(
                    (scratch[p].as_ptr() as *const E).add(live_at),
                    live_len,
                )
            }
        };
        let fv = match pending_r {
            Some(r) => {
                assert_eq!(src.len(), 4);
                let mut fv = [E::ZERO; 2];
                for b in 0..2 {
                    let lo = src[b];
                    let hi = src[2 + b];
                    let mut v = hi;
                    v.sub_assign(&lo);
                    v.mul_assign(&r);
                    v.add_assign(&lo);
                    fv[b] = v;
                }
                fv
            }
            None => {
                assert_eq!(src.len(), 2, "all-window schedule must end at 2 values");
                [src[0], src[1]]
            }
        };
        final_values.push(fv);
    }
    #[cfg(feature = "gkr_self_checks")]
    {
        let fv = &final_values;
        let mut g = gate_batch(relations, |p, b| fv[p][b]);
        g.mul_assign(&eq_prefix);
        assert_eq!(g, claim, "LSB fused final gate identity");
    }
    (
        LsbDimReducingSumcheckOutput {
            round_coefficients,
            final_claim: claim,
            final_values,
            eq_factor: eq_prefix,
        },
        challenges,
    )
}

