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
//! -- perfectly contiguous reads.
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
//! engine accumulates `[h(0), h(inf)]` (h(1) is derived from the running
//! claim) and emits the CUBIC monomial coefficients `[c0, c1, c2, c3]` of
//! `q_s`. Soundness bookkeeping is the standard chaining
//! `q_s(0) + q_s(1) == claim_s`, `claim_{s+1} = q_s(r_s)`.
//!
//! # Production shape
//!
//! The production path is split around the transcript interaction of round 0:
//! [`lsb_dim_reducing_sumcheck_initial_round`] reads the gate values at
//! `X = 0` straight from the OUTPUT layer polys and folds nothing; after the
//! caller draws `r_0` it may drop the output pointers and purge the output
//! layer from storage, then run [`lsb_dim_reducing_sumcheck_continue`] — a
//! deliberately trivial cycle over the remaining rounds: evaluate the round
//! (one kernel sweep that folds the pending challenge on read), then re-point
//! source/destination for the next round.

use std::collections::BTreeMap;

use crate::gkr::prover::{SendConstPtr, SendPtr};
use cs::definitions::GKRAddress;
use field::{Field, FieldExtension, PrimeField};

/// One batched relation of a dimension-reducing layer, referring to its
/// input AND output polys by their storage addresses.
#[derive(Clone, Copy, Debug)]
pub enum LsbDimReducingRelation<E> {
    /// `out(Y) = p(2Y) * p(2Y+1)`, batched with weight `alpha`.
    PairwiseProduct {
        input: GKRAddress,
        output: GKRAddress,
        alpha: E,
    },
    /// Logup fraction add over a (numerator, denominator) pair:
    /// `out_num(Y) = n(2Y) * d(2Y+1) + n(2Y+1) * d(2Y)`,
    /// `out_den(Y) = d(2Y) * d(2Y+1)`, batched with `alpha_num`, `alpha_den`.
    LogupPair {
        num: GKRAddress,
        den: GKRAddress,
        num_output: GKRAddress,
        den_output: GKRAddress,
        alpha_num: E,
        alpha_den: E,
    },
}

impl<E> LsbDimReducingRelation<E> {
    /// The relation's input addresses (1 or 2).
    pub fn input_addresses(&self) -> impl Iterator<Item = GKRAddress> + '_ {
        let pair: [Option<GKRAddress>; 2] = match self {
            LsbDimReducingRelation::PairwiseProduct { input, .. } => [Some(*input), None],
            LsbDimReducingRelation::LogupPair { num, den, .. } => [Some(*num), Some(*den)],
        };
        pair.into_iter().flatten()
    }

    /// The relation's output addresses (1 or 2).
    pub fn output_addresses(&self) -> impl Iterator<Item = GKRAddress> + '_ {
        let pair: [Option<GKRAddress>; 2] = match self {
            LsbDimReducingRelation::PairwiseProduct { output, .. } => [Some(*output), None],
            LsbDimReducingRelation::LogupPair {
                num_output,
                den_output,
                ..
            } => [Some(*num_output), Some(*den_output)],
        };
        pair.into_iter().flatten()
    }
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
    at: impl Fn(GKRAddress, usize) -> E, // (poly address, local index within a Y-cell: 0 = b0, 1 = b1)
) -> E {
    let mut acc = E::ZERO;
    for rel in relations {
        match rel {
            LsbDimReducingRelation::PairwiseProduct { input, alpha, .. } => {
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
                ..
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
/// coefficients, the final claim, and the final (fully folded) two values
/// `[p(., 0), p(., 1)]` of every input poly, keyed by its address.
pub struct LsbDimReducingSumcheckOutput<E> {
    pub round_coefficients: Vec<[E; 4]>,
    pub final_claim: E,
    pub final_values: BTreeMap<GKRAddress, [E; 2]>,
    /// `prod_s eqw_s(r_s)` -- the eq factor of the bound variables; the
    /// final claim satisfies `final_claim == eq_factor * gate(final_values)`.
    pub eq_factor: E,
}

/// Runs the full LSB-binding sumcheck for one dimension-reducing layer
/// (serial reference implementation, kept for tests).
///
/// * `polys` — the layer's input polys by address (each `2 * M` values,
///   `2Y + b` interleaved); consumed as working copies.
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
    polys: &BTreeMap<GKRAddress, &[E]>,
    relations: &[LsbDimReducingRelation<E>],
    tau: &[E],
    claim: E,
    challenges: &[E],
) -> LsbDimReducingSumcheckOutput<E> {
    let rounds = tau.len();
    assert_eq!(challenges.len(), rounds);
    let m = 1usize << rounds;
    for p in polys.values() {
        assert_eq!(p.len(), 2 * m);
    }

    // T_0 over tau[1..], low-variable-first: T[j] = prod_b f_{tau[1+b]}(j_b),
    // materialized into a 3/4-sized ping-pong buffer (front live region +
    // room for the dense contraction writes)
    let mut t_table = vec![E::ONE; m / 2 + m / 4];
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
    let mut t_at = 0usize;
    let mut t_len = m / 2;

    let mut buffers: BTreeMap<GKRAddress, PingPong<E>> = polys
        .iter()
        .map(|(addr, p)| (*addr, PingPong::new(p)))
        .collect();
    let mut round_coefficients = Vec::with_capacity(rounds);
    let mut claim = claim;
    // accumulated eq prefix over the already-bound variables:
    // prod_{t<s} eqw_t(r_t); it scales every later round polynomial
    let mut eq_prefix = E::ONE;

    for s in 0..rounds {
        let pairs = 1usize << (rounds - 1 - s);
        // accumulate h(0), h(1), h(inf) over all pairs, T-weighted
        let mut h = [E::ZERO; 3];
        for j in 0..pairs {
            let w = t_table[t_at + j];
            // h(0): gate at Y' = 2j (indices 4j + b)
            let v0 = gate_batch(relations, |a, b| buffers[&a].live()[4 * j + b]);
            // h(1): gate at Y' = 2j + 1 (indices 4j + 2 + b)
            let v1 = gate_batch(relations, |a, b| buffers[&a].live()[4 * j + 2 + b]);
            // h(inf): gate's leading X-coefficient = gate on the differences
            let vinf = gate_batch(relations, |a, b| {
                let live = buffers[&a].live();
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
        // q(X) = eqw(X) * h(X), scaled by the accumulated eq prefix
        let coeffs = cubic_round_message(&h[0], &h[1], &h[2], &tau[s], &eq_prefix);

        // soundness bookkeeping: q(0) + q(1) must reproduce the claim
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

        // bind the challenge: claim = q(r), fold polys, contract T
        let r = challenges[s];
        claim = horner4(&coeffs, &r);
        eq_prefix.mul_assign(&eq_weight(&tau[s], &r));

        for buf in buffers.values_mut() {
            buf.fold(&r);
        }
        // contract T: the pair sum drops the (new) lowest variable exactly --
        // f(0)*x + f(1)*x = x per table factor
        if s + 1 < rounds {
            (t_at, t_len) = contract_t_table(&mut t_table, t_at, t_len);
        }

        round_coefficients.push(coeffs);
    }

    let final_values: BTreeMap<GKRAddress, [E; 2]> = buffers
        .iter()
        .map(|(addr, buf)| {
            let live = buf.live();
            assert_eq!(live.len(), 2);
            (*addr, [live[0], live[1]])
        })
        .collect();

    // final identity: the claim after all rounds equals the batched gate on
    // the fully folded values (eq fully consumed by the eqw factors)
    #[cfg(feature = "gkr_self_checks")]
    {
        let fv = &final_values;
        let mut g = gate_batch(relations, |a, b| fv[&a][b]);
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
pub(crate) fn cubic_round_message<E: Field>(
    h0: &E,
    h1: &E,
    hinf: &E,
    tau_s: &E,
    eq_prefix: &E,
) -> [E; 4] {
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

/// Direct fetch of the 4 pair values of row `j` (no pending fold).
#[inline(always)]
unsafe fn scalar_fetch4<E: Field>(src: *const E, j: usize) -> [E; 4] {
    [
        *src.add(4 * j),
        *src.add(4 * j + 1),
        *src.add(4 * j + 2),
        *src.add(4 * j + 3),
    ]
}

/// Fold-on-read fetch of the CURRENT 4 pair values of row `j`: ancestor
/// layout has value (Y', b) at index 2*Y' + b; the pending fold combines
/// Y' = 2q, 2q+1 -> q, so pair j covers folded Y in {2j, 2j+1}, i.e.
/// ancestors Y' in {4j..4j+4}. The folded values are stored to `dst` for the
/// next round while hot.
#[inline(always)]
unsafe fn scalar_fold_fetch4<E: Field>(src: *const E, dst: *mut E, r: &E, j: usize) -> [E; 4] {
    let mut out = [E::ZERO; 4];
    for yy in 0..2 {
        for b in 0..2 {
            let lo = *src.add(2 * (4 * j + 2 * yy) + b);
            let hi = *src.add(2 * (4 * j + 2 * yy + 1) + b);
            let mut v = hi;
            v.sub_assign(&lo);
            v.mul_assign(r);
            v.add_assign(&lo);
            *dst.add(2 * (2 * j + yy) + b) = v;
            out[2 * yy + b] = v;
        }
    }
    out
}

/// Portable scalar chunk kernel of the INITIAL round: gate values at `X = 0`
/// are read straight from the OUTPUT layer polys, `X = inf` from the input
/// differences; nothing is folded. Returns the T-weighted `[h0, hinf]`
/// partial sums of the chunk.
///
/// # Safety
///
/// The kernel reads the borrowed slices unchecked; the caller must
/// guarantee for rows `chunk_start..chunk_start + chunk_size`:
/// * every `inputs` slice is the layer's full input poly (`8 * pairs`
///   values, read at indices `4j..4j + 4`) and every `outputs` slice the
///   full output poly (`2 * pairs` values, read at index `2j`);
/// * `t_ptr` is the base of the round's suffix eq table `T` with at least
///   `pairs` entries (read at index `j`) — the T-weighting of the row sums;
/// * `scratch` is this thread's EXCLUSIVE tri scratch slot with capacity for
///   `chunk_size` `[E; 2]` rows (`[v0, vinf]` accumulators); it may be
///   uninitialized — the kernel writes every row before reading it.
pub(crate) unsafe fn scalar_initial_chunk<E: Field>(
    inputs: &BTreeMap<GKRAddress, &[E]>,
    outputs: &BTreeMap<GKRAddress, &[E]>,
    relations: &[LsbDimReducingRelation<E>],
    t_ptr: SendConstPtr<E>,
    chunk_start: usize,
    chunk_size: usize,
    scratch: SendPtr<[E; 2]>,
) -> [E; 2] {
    // caller-provided typed tri scratch: [v0, vinf] per row
    let tri = unsafe { core::slice::from_raw_parts_mut(scratch.0, chunk_size) };
    for t in tri.iter_mut() {
        *t = [E::ZERO; 2];
    }
    let mut first = true;
    for rel in relations.iter() {
        match rel {
            LsbDimReducingRelation::PairwiseProduct {
                input,
                output,
                alpha,
            } => {
                let src = inputs[input].as_ptr();
                let out = outputs[output].as_ptr();
                for (jj, t) in tri.iter_mut().enumerate() {
                    let j = chunk_start + jj;
                    let [a0, b0, a1, b1] = unsafe { scalar_fetch4(src, j) };
                    // the output layer already holds the gate value at X = 0
                    let mut v0 = unsafe { *out.add(2 * j) };
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
                num_output,
                den_output,
                alpha_num,
                alpha_den,
            } => {
                let n_src = inputs[num].as_ptr();
                let d_src = inputs[den].as_ptr();
                let n_out = outputs[num_output].as_ptr();
                let d_out = outputs[den_output].as_ptr();
                for (jj, t) in tri.iter_mut().enumerate() {
                    let j = chunk_start + jj;
                    let [n0, n1, n2, n3] = unsafe { scalar_fetch4(n_src, j) };
                    let [d0, d1, d2, d3] = unsafe { scalar_fetch4(d_src, j) };
                    // X = 0 from the output layer
                    let (num0, den0) = unsafe { (*n_out.add(2 * j), *d_out.add(2 * j)) };
                    // X = inf on the differences
                    let (mut dn0, mut dn1) = (n2, n3);
                    dn0.sub_assign(&n0);
                    dn1.sub_assign(&n1);
                    let (mut dd0, mut dd1) = (d2, d3);
                    dd0.sub_assign(&d0);
                    dd1.sub_assign(&d1);
                    let (numi, deni) = scalar_logup_quad(dn0, dn1, dd0, dd1);
                    let mut v0 = num0;
                    v0.mul_assign(alpha_num);
                    let mut t2 = den0;
                    t2.mul_assign(alpha_den);
                    v0.add_assign(&t2);
                    let mut vinf = numi;
                    vinf.mul_assign(alpha_num);
                    let mut t2 = deni;
                    t2.mul_assign(alpha_den);
                    vinf.add_assign(&t2);
                    if first {
                        *t = [v0, vinf];
                    } else {
                        t[0].add_assign(&v0);
                        t[1].add_assign(&vinf);
                    }
                }
            }
        }
        first = false;
    }

    // fused T-dot over the hot tri rows
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

/// Portable scalar chunk kernel of a CONTINUING round: folds the previous
/// round's `folding_challenge` on read (writing the folded polys densely to
/// `dst`) and feeds the gate accumulators from the hot folded values.
/// Returns the T-weighted `[h0, hinf]` partial sums of the chunk.
///
/// # Safety
///
/// The kernel dereferences the raw pointers behind the trackers and
/// parameters; the caller must guarantee for rows
/// `chunk_start..chunk_start + chunk_size`:
/// * every tracker's INPUT range covers the round's UNFOLDED source
///   (`8 * pairs` values, read at indices `8j..8j + 8`) and its OUTPUT
///   range a DISJOINT destination for the folded poly (`4 * pairs` values,
///   written at indices `4j..4j + 4`) — [`FoldBufferTracker`] maintains
///   exactly this shape;
/// * `t_ptr` is the base of the round's suffix eq table `T` with at least
///   `pairs` entries (read at index `j`) — the T-weighting of the row sums;
/// * `scratch` is this thread's EXCLUSIVE tri scratch slot with capacity for
///   `chunk_size` `[E; 2]` rows (`[v0, vinf]` accumulators); it may be
///   uninitialized — the kernel writes every row before reading it.
pub(crate) unsafe fn scalar_continuing_chunk<E: Field>(
    buffers: &BTreeMap<GKRAddress, FoldBufferTracker<E>>,
    relations: &[LsbDimReducingRelation<E>],
    folding_challenge: E,
    t_ptr: SendConstPtr<E>,
    chunk_start: usize,
    chunk_size: usize,
    scratch: SendPtr<[E; 2]>,
) -> [E; 2] {
    // caller-provided typed tri scratch: [v0, vinf] per row
    let tri = unsafe { core::slice::from_raw_parts_mut(scratch.0, chunk_size) };
    for t in tri.iter_mut() {
        *t = [E::ZERO; 2];
    }
    let r = &folding_challenge;
    let mut first = true;
    for rel in relations.iter() {
        match rel {
            LsbDimReducingRelation::PairwiseProduct { input, alpha, .. } => {
                let src = buffers[input].input_ptr_range().start;
                let d = buffers[input].output_ptr_range().start;
                for (jj, t) in tri.iter_mut().enumerate() {
                    let j = chunk_start + jj;
                    let [a0, b0, a1, b1] = unsafe { scalar_fold_fetch4(src, d, r, j) };
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
                ..
            } => {
                let n_src = buffers[num].input_ptr_range().start;
                let n_dst = buffers[num].output_ptr_range().start;
                let d_src = buffers[den].input_ptr_range().start;
                let d_dst = buffers[den].output_ptr_range().start;
                for (jj, t) in tri.iter_mut().enumerate() {
                    let j = chunk_start + jj;
                    let [n0, n1, n2, n3] = unsafe { scalar_fold_fetch4(n_src, n_dst, r, j) };
                    let [d0, d1, d2, d3] = unsafe { scalar_fold_fetch4(d_src, d_dst, r, j) };
                    let (num0, den0) = scalar_logup_quad(n0, n1, d0, d1);
                    let (mut dn0, mut dn1) = (n2, n3);
                    dn0.sub_assign(&n0);
                    dn1.sub_assign(&n1);
                    let (mut dd0, mut dd1) = (d2, d3);
                    dd0.sub_assign(&d0);
                    dd1.sub_assign(&d1);
                    let (numi, deni) = scalar_logup_quad(dn0, dn1, dd0, dd1);
                    let mut v0 = num0;
                    v0.mul_assign(alpha_num);
                    let mut t2 = den0;
                    t2.mul_assign(alpha_den);
                    v0.add_assign(&t2);
                    let mut vinf = numi;
                    vinf.mul_assign(alpha_num);
                    let mut t2 = deni;
                    t2.mul_assign(alpha_den);
                    vinf.add_assign(&t2);
                    if first {
                        *t = [v0, vinf];
                    } else {
                        t[0].add_assign(&v0);
                        t[1].add_assign(&vinf);
                    }
                }
            }
        }
        first = false;
    }

    // fused T-dot over the hot tri rows
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

/// One T-weighted sweep over `pairs` rows, chunked over the worker with the
/// per-slot tri scratch; `run_chunk(chunk_start, chunk_size, tri_slot)`
/// returns the chunk's `[h0, hinf]` partials. Shared by the initial and
/// continuing rounds.
fn tri_weighted_sweep<E: Field, S: Send + Sync>(
    pairs: usize,
    worker: &worker::Worker,
    tri_scratch: &mut [Box<[core::mem::MaybeUninit<S>]>],
    run_chunk: impl Fn(usize, usize, SendPtr<S>) -> [E; 2] + Send + Sync + Copy,
) -> [E; 2] {
    use crate::gkr::PAR_THRESHOLD;
    let geometry = worker.get_geometry_with_threshold(pairs, PAR_THRESHOLD);
    let mut partials = vec![[E::ZERO; 2]; geometry.num_chunks];
    worker.scope_with_threshold(pairs, PAR_THRESHOLD, |scope, geometry| {
        let mut it = partials.iter_mut();
        let mut sit = tri_scratch.iter_mut();
        for thread_idx in 0..geometry.num_chunks {
            let chunk_start = geometry.get_chunk_start_pos(thread_idx);
            let chunk_size = geometry.get_chunk_size(thread_idx);
            let dst = it.next().unwrap();
            let sc = sit.next().expect("chunks never exceed worker slots");
            debug_assert!(chunk_size <= sc.len());
            let scratch_ptr = SendPtr(sc.as_mut_ptr() as *mut S);
            worker::Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                *dst = run_chunk(chunk_start, chunk_size, scratch_ptr);
            });
        }
    });
    let mut h = [E::ZERO; 2];
    for p in partials {
        for k in 0..2 {
            h[k].add_assign(&p[k]);
        }
    }
    h
}

/// Ping-pong tracker over ONE poly's fold scratch for the continuing
/// rounds, replacing loose `SendPtr` bookkeeping: it carries the FULL
/// uninitialized allocation as a pointer range plus the current round's
/// INPUT (read) and OUTPUT (fold-write) pointer ranges in a single
/// structure.
///
/// Round 1 reads the ORIGINAL input poly (outside the allocation) and
/// writes the allocation's front half; [`Self::step`] then promotes the
/// output to the next round's input and carves the next (half-sized) output
/// out of the now-dead previous input's region — for the first step that
/// region is the storage-owned original, so the output is carved from the
/// allocation's tail instead; from then on the two allocation halves
/// alternate (the dense ping-pong the engine always used).
pub struct FoldBufferTracker<E> {
    /// the full scratch allocation
    full: core::ops::Range<*mut E>,
    /// current input (read) region
    input: core::ops::Range<*const E>,
    /// current output (fold destination) region
    output: core::ops::Range<*mut E>,
}

// SAFETY: the tracker only CARRIES raw region bounds — every dereference
// happens in the kernels under the engine's exclusivity contract (one
// tracker per poly, disjoint input/output regions, chunked writers never
// overlapping). Declaring it Send + Sync lets the sweep share the tracker
// map across worker threads.
unsafe impl<E: Send> Send for FoldBufferTracker<E> {}
unsafe impl<E: Sync> Sync for FoldBufferTracker<E> {}

impl<E> FoldBufferTracker<E> {
    /// `full`/`full_len` is the poly's uninit scratch allocation (at least
    /// `3 * poly_len / 4` elements) for a poly of `poly_len` values. The
    /// tracker starts with an EMPTY input range — round 1 reads the
    /// storage-borrowed original installed via [`Self::set_external_input`]
    /// — and the allocation's front half as the first output.
    pub fn new(full: *mut E, full_len: usize, poly_len: usize) -> Self {
        assert!(poly_len.is_power_of_two());
        assert!(full_len >= poly_len / 2 + poly_len / 4);
        Self {
            full: full..unsafe { full.add(full_len) },
            input: core::ptr::null()..core::ptr::null(),
            output: full..unsafe { full.add(poly_len / 2) },
        }
    }

    /// Install the round-1 input: the storage-borrowed ORIGINAL poly, which
    /// lives outside the scratch allocation ([`Self::step`] detects that and
    /// carves the second output from the allocation's tail).
    pub fn set_external_input(&mut self, original: &[E]) {
        assert_eq!(original.len(), 2 * self.output_len());
        self.input = original.as_ptr_range();
    }

    /// Current input region as a pointer range.
    #[inline(always)]
    pub fn input_ptr_range(&self) -> core::ops::Range<*const E> {
        self.input.clone()
    }

    /// Current output region as a pointer range.
    #[inline(always)]
    pub fn output_ptr_range(&self) -> core::ops::Range<*mut E> {
        self.output.clone()
    }

    /// Length of the current input region, in elements.
    #[inline(always)]
    pub fn input_len(&self) -> usize {
        (self.input.end as usize - self.input.start as usize) / core::mem::size_of::<E>()
    }

    /// Length of the current output region, in elements.
    #[inline(always)]
    pub fn output_len(&self) -> usize {
        (self.output.end as usize - self.output.start as usize) / core::mem::size_of::<E>()
    }

    /// Chunk of the input region (element offset + length), for parallel
    /// consumers that want a bounded view.
    #[inline(always)]
    pub fn input_chunk(&self, start: usize, len: usize) -> core::ops::Range<*const E> {
        assert!(start + len <= self.input_len());
        unsafe { self.input.start.add(start)..self.input.start.add(start + len) }
    }

    /// Chunk of the output region (element offset + length), for parallel
    /// producers that want a bounded view.
    #[inline(always)]
    pub fn output_chunk(&self, start: usize, len: usize) -> core::ops::Range<*mut E> {
        assert!(start + len <= self.output_len());
        unsafe { self.output.start.add(start)..self.output.start.add(start + len) }
    }

    /// Current input region as a slice.
    ///
    /// # Safety
    ///
    /// The caller must guarantee the region is fully initialized — true for
    /// the original poly and for any region a completed round has written.
    #[inline(always)]
    pub unsafe fn input_slice(&self) -> &[E] {
        core::slice::from_raw_parts(self.input.start, self.input_len())
    }

    /// Advance to the next round: the just-written output becomes the input,
    /// and the next (half-sized) output is carved from the previous input's
    /// region — or from the allocation's tail when that input was the
    /// external original poly.
    pub fn step(&mut self) {
        let prev_input_start = self.input.start;
        let next_output_len = self.output_len() / 2;
        let next_output_start = if self.full.contains(&(prev_input_start as *mut E)) {
            prev_input_start as *mut E
        } else {
            // first step: the original poly is not ours to write; carve the
            // tail right behind the front-half output
            self.output.end
        };
        self.input = (self.output.start as *const E)..(self.output.end as *const E);
        self.output = next_output_start..unsafe { next_output_start.add(next_output_len) };
    }
}

/// One suffix-eq-table contraction, `t'[j] = t[2j] + t[2j+1]` — dropping the
/// table's lowest remaining variable EXACTLY (`f(0)*x + f(1)*x = x` per
/// factor) — written DENSELY into the OTHER ping-pong region of the table's
/// 3/4-sized buffer, exactly like the poly fold scratch: source and
/// destination are disjoint and the round always reads a contiguous region.
/// Takes the current live `(offset, len)` and returns the new one.
fn contract_t_table<E: Field>(buf: &mut [E], at: usize, len: usize) -> (usize, usize) {
    assert!(len >= 2);
    let next = len / 2;
    let dst_at = if at == 0 { len } else { 0 };
    debug_assert!(dst_at + next <= buf.len());
    let (src_ptr, dst_ptr) = unsafe { (buf.as_ptr().add(at), buf.as_mut_ptr().add(dst_at)) };
    for j in 0..next {
        unsafe {
            let mut v = *src_ptr.add(2 * j);
            v.add_assign(&*src_ptr.add(2 * j + 1));
            *dst_ptr.add(j) = v;
        }
    }
    (dst_at, next)
}

/// Round 0 of the production dimension-reducing sumcheck: the gate values at
/// `X = 0` are read straight from the OUTPUT layer polys (they hold exactly
/// `gate(inputs)` pointwise), `X = inf` from the input differences; nothing
/// is folded — so the polys come in as plain BORROWED slices. Returns the
/// round's cubic coefficients AND its suffix eq table (over `tau[1..]`) so
/// [`lsb_dim_reducing_sumcheck_continue`] can contract it instead of
/// re-materializing. After absorbing the coefficients and drawing `r_0` the
/// caller's borrows have ended: it can purge the output layer from storage
/// (no later round touches it), re-select the input polys, and run
/// [`lsb_dim_reducing_sumcheck_continue`].
pub fn lsb_dim_reducing_sumcheck_initial_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: Send + Sync,
    CKI: Fn(
            &BTreeMap<GKRAddress, &[E]>,
            &BTreeMap<GKRAddress, &[E]>,
            &[LsbDimReducingRelation<E>],
            SendConstPtr<E>,
            usize,
            usize,
            SendPtr<S>,
        ) -> [E; 2]
        + Send
        + Sync
        + Copy,
>(
    inputs: &BTreeMap<GKRAddress, &[E]>,
    outputs: &BTreeMap<GKRAddress, &[E]>,
    relations: &[LsbDimReducingRelation<E>],
    tau: &[E],
    claim: E,
    worker: &worker::Worker,
    tri_scratch: &mut [Box<[core::mem::MaybeUninit<S>]>],
    chunk_kernel: CKI,
) -> ([E; 4], Vec<E>) {
    let rounds = tau.len();
    let m = 1usize << rounds;
    for p in inputs.values() {
        assert_eq!(p.len(), 2 * m);
    }
    for p in outputs.values() {
        assert_eq!(p.len(), m);
    }
    assert!(tri_scratch.len() >= worker.num_cores);

    // round 0's suffix eq table covers tau[1..]; reserve room for it to
    // grow into the continuing rounds' 3/4-sized ping-pong contraction
    // buffer without reallocating
    let t_table = crate::gkr::sumcheck::eq_poly::make_eq_table_lsb_first_with_capacity(
        &tau[1..],
        m / 2 + m / 4,
        worker,
    );

    let t_ptr = SendConstPtr(t_table.as_ptr());
    let [h0, hinf] = tri_weighted_sweep(m / 2, worker, tri_scratch, |start, size, tri| {
        chunk_kernel(inputs, outputs, relations, t_ptr, start, size, tri)
    });

    let h1 = derive_h1_from_claim(&claim, &E::ONE, &h0, &tau[0]);
    let coefficients = cubic_round_message(&h0, &h1, &hinf, &tau[0], &E::ONE);
    (coefficients, t_table)
}

/// Continuing rounds `1..rounds` of the production dimension-reducing
/// sumcheck — a deliberately trivial cycle. Each iteration:
///
/// 1. evaluates the round: ONE kernel sweep over the trackers' current
///    input regions that folds `folding_challenge` on read, writes the
///    folded polys to the trackers' output regions, and returns the
///    T-weighted `[h0, hinf]`;
/// 2. emits the cubic round message (h(1) derived from the running claim)
///    and draws the next challenge through `draw_challenge`;
/// 3. steps every [`FoldBufferTracker`]: the just-written output becomes the
///    next input and the next output is carved for the halved size.
///
/// `inputs` holds the BORROWED original polys round 1 reads (re-selected
/// from storage after the caller purged the output layer);
/// `round_0_coefficients`/`r_0`/`t_table` are the initial round's message,
/// drawn challenge, and suffix eq table (over `tau[1..]`, see
/// [`lsb_dim_reducing_sumcheck_initial_round`]) — the table is contracted
/// here instead of re-materialized. The returned coefficients/challenges
/// cover rounds `1..` only.
#[allow(clippy::too_many_arguments)]
pub fn lsb_dim_reducing_sumcheck_continue<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    S: Send + Sync,
    CK: Fn(
            &BTreeMap<GKRAddress, FoldBufferTracker<E>>,
            &[LsbDimReducingRelation<E>],
            E,
            SendConstPtr<E>,
            usize,
            usize,
            SendPtr<S>,
        ) -> [E; 2]
        + Send
        + Sync
        + Copy,
>(
    inputs: &BTreeMap<GKRAddress, &[E]>,
    buffers: &mut BTreeMap<GKRAddress, FoldBufferTracker<E>>,
    relations: &[LsbDimReducingRelation<E>],
    tau: &[E],
    round_0_coefficients: &[E; 4],
    r_0: E,
    mut t_table: Vec<E>,
    worker: &worker::Worker,
    tri_scratch: &mut [Box<[core::mem::MaybeUninit<S>]>],
    chunk_kernel: CK,
    mut draw_challenge: impl FnMut(&[E; 4]) -> E,
) -> (LsbDimReducingSumcheckOutput<E>, Vec<E>) {
    let rounds = tau.len();
    assert!(rounds >= 2);
    let m = 1usize << rounds;
    assert_eq!(inputs.len(), buffers.len());
    // round 1 special case: its input pointers derive from the BORROWED
    // original polys, not from tracker-owned regions — install them before
    // the cycle so the kernel path stays uniform
    for (addr, tracker) in buffers.iter_mut() {
        let original = inputs[addr];
        assert_eq!(original.len(), 2 * m);
        assert_eq!(tracker.output_len(), m);
        tracker.set_external_input(original);
    }
    assert!(tri_scratch.len() >= worker.num_cores);

    let mut round_coefficients = Vec::with_capacity(rounds - 1);
    let mut challenges = Vec::with_capacity(rounds - 1);
    let mut claim = horner4(round_0_coefficients, &r_0);
    let mut eq_prefix = eq_weight(&tau[0], &r_0);
    let mut folding_challenge = r_0;

    // the initial round's table covers tau[1..]; grow it into a 3/4-sized
    // ping-pong buffer, then one contraction drops the round-0 variable so
    // it covers tau[2..] for round 1, and later rounds keep contracting it
    assert_eq!(t_table.len(), m / 2);
    assert!(
        t_table.capacity() >= m / 2 + m / 4,
        "the initial round must reserve the contraction buffer"
    );
    t_table.resize(m / 2 + m / 4, E::ZERO);
    let (mut t_at, mut t_len) = contract_t_table(&mut t_table, 0, m / 2);

    for s in 1..rounds {
        let pairs = (m >> s) / 2;

        debug_assert_eq!(t_len, pairs);
        // computational part: one T-weighted sweep over the trackers'
        // current regions, folding `folding_challenge` on read
        let t_ptr = SendConstPtr(unsafe { t_table.as_ptr().add(t_at) });
        let buffers_ref = &*buffers;
        let [h0, hinf] = tri_weighted_sweep(pairs, worker, tri_scratch, |start, size, tri| {
            chunk_kernel(
                buffers_ref,
                relations,
                folding_challenge,
                t_ptr,
                start,
                size,
                tri,
            )
        });

        let h1 = derive_h1_from_claim(&claim, &eq_prefix, &h0, &tau[s]);
        let coeffs = cubic_round_message(&h0, &h1, &hinf, &tau[s], &eq_prefix);
        let r = draw_challenge(&coeffs);
        round_coefficients.push(coeffs);
        challenges.push(r);
        claim = horner4(&coeffs, &r);
        eq_prefix.mul_assign(&eq_weight(&tau[s], &r));

        // pointer adjustment for the next round: every tracker promotes its
        // just-written output to the next input and carves the next output
        for tracker in buffers.values_mut() {
            tracker.step();
        }
        folding_challenge = r;

        if s + 1 < rounds {
            (t_at, t_len) = contract_t_table(&mut t_table, t_at, t_len);
        }
    }

    // epilogue: the last challenge's fold is still pending on the final 4
    // values per poly — materialize the [p(., 0), p(., 1)] lines
    let final_values: BTreeMap<GKRAddress, [E; 2]> = buffers
        .iter()
        .map(|(a, tracker)| {
            let src = unsafe { tracker.input_slice() };
            assert_eq!(src.len(), 4);
            let mut fv = [E::ZERO; 2];
            for b in 0..2 {
                let lo = src[b];
                let hi = src[2 + b];
                let mut v = hi;
                v.sub_assign(&lo);
                v.mul_assign(&folding_challenge);
                v.add_assign(&lo);
                fv[b] = v;
            }
            (*a, fv)
        })
        .collect();

    // final identity: the claim after all rounds equals the batched gate on
    // the fully folded values (eq fully consumed by the eqw factors)
    #[cfg(feature = "gkr_self_checks")]
    {
        let fv = &final_values;
        let mut g = gate_batch(relations, |a, b| fv[&a][b]);
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

    fn addr(offset: usize) -> GKRAddress {
        GKRAddress::InnerLayer { layer: 0, offset }
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
        let poly_map: BTreeMap<GKRAddress, &[E]> = polys
            .iter()
            .enumerate()
            .map(|(i, p)| (addr(i), &p[..]))
            .collect();
        let relations = [
            LsbDimReducingRelation::PairwiseProduct {
                input: addr(0),
                output: addr(16),
                alpha: pseudo(&mut seed),
            },
            LsbDimReducingRelation::LogupPair {
                num: addr(1),
                den: addr(2),
                num_output: addr(17),
                den_output: addr(18),
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
            let v = gate_batch(&relations, |a, b| poly_map[&a][2 * y + b]);
            let mut t = v;
            t.mul_assign(&eq[y]);
            claim.add_assign(&t);
        }

        let out =
            lsb_dim_reducing_sumcheck_prove::<F, E>(&poly_map, &relations, &tau, claim, &challenges);

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
            c = horner4(coeffs, &challenges[s]);
        }
        assert_eq!(c, out.final_claim);
        let mut g = gate_batch(&relations, |a, b| out.final_values[&a][b]);
        g.mul_assign(&out.eq_factor);
        assert_eq!(g, out.final_claim, "final folded gate identity");
    }
}
