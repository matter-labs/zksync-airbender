//! Test-only layer-oracle harness for backward-VM protocol parity.
//!
//! REV2: this lives in the prover's `#[cfg(test)]` tree as `pub(crate)`. It has no
//! public API and no doc-hidden surface — G2 (the backward-VM parity gate, Task 10)
//! is a prover unit test, so nothing here is exported from the crate.
//!
//! [`run_layer_oracle`] wraps the exact production `KernelCollector::from_layer` +
//! [`run_sumcheck_loop`] path, threading a [`SumcheckLoopCapture`] through it to
//! surface the per-round observables. The capture is transcript-inert: it never
//! touches the Fiat-Shamir `Seed`, so the sequence of `commit_field_els` /
//! `draw_random_field_els` calls is byte-identical to the production `None` path
//! (proven by the twin-run smoke).
//!
//! [`recover_and_emit`] reconstructs the committed univariate `[E; 4]` monomial
//! form from the round-polynomial evaluations `(g(0), g(2))` a backward VM would
//! produce, delegating to the production emission helper. It lives here (not in
//! `gkr_eval_isa`) precisely because it depends on that prover-side helper;
//! placing it upstream would reverse the crate dependency direction.

use super::*;
use std::collections::BTreeMap;

/// All per-round + summary observables of a single layer's batched sumcheck run.
pub(crate) struct LayerOracleRun<E> {
    pub(crate) folding_challenges: Vec<E>,
    pub(crate) round_coeffs: Vec<[E; 4]>,
    /// `[c0, c2]` (constant + quadratic monomial coefficients) BEFORE normalization.
    pub(crate) per_round_reduced: Vec<[E; 2]>,
    /// Claim entering each round.
    pub(crate) per_round_claims: Vec<E>,
    pub(crate) per_round_eq_prefactor: Vec<E>,
    pub(crate) last_evaluations: BTreeMap<GKRAddress, [E; 2]>,
    /// `run_sumcheck_loop`'s 4th return: the NORMALIZED final claim.
    pub(crate) final_normalized_claim: E,
    /// The initial combined claim the collector assembled from the output claims.
    pub(crate) initial_combined_claim: E,
    /// The per-relation batch weights the collector assigned (for the Task 10
    /// alpha-slot pin).
    pub(crate) per_relation_weights: Vec<E>,
}

/// Run one layer's batched sumcheck over `storage`, mirroring the
/// `KernelCollector::from_layer` + `run_sumcheck_loop::<F, E, 2, true>` arm of
/// `evaluate_sumcheck_for_layer`, and capture every per-round observable.
///
/// The transcript effects are exactly those of the wrapped loop; the extra
/// post-loop commits that `evaluate_sumcheck_for_layer` performs (final at-point
/// evaluations + next batching challenge) are intentionally NOT replicated —
/// the harness is scoped to the sumcheck loop itself.
pub(crate) fn run_layer_oracle<F, E>(
    layer_idx: usize,
    layer: &GKRLayerDescription,
    output_claims: &BTreeMap<GKRAddress, E>,
    prev_challenges: &[E],
    storage: &mut GKRStorage<F, E>,
    batch_challenge_base: E,
    trace_len: usize,
    lookup_challenges_multiplicative_part: E,
    lookup_challenges_additive_part: E,
    inits_and_teardowns_top_bits: &[u32],
    address_high_bits_shift: u32,
    external_challenges: &GKRExternalChallenges<F, E>,
    seed: &mut Seed,
    worker: &Worker,
) -> LayerOracleRun<E>
where
    F: PrimeField,
    E: FieldExtension<F> + Field,
    [(); E::DEGREE]: Sized,
{
    assert!(trace_len.is_power_of_two());
    let folding_steps = trace_len.trailing_zeros() as usize;

    let eq_polys = make_eq_poly_in_full::<E>(prev_challenges, worker);

    let collector = KernelCollector::from_layer(
        layer,
        layer_idx,
        batch_challenge_base,
        lookup_challenges_multiplicative_part,
        lookup_challenges_additive_part,
        inits_and_teardowns_top_bits,
        address_high_bits_shift,
    );
    assert!(!collector.is_empty());

    let initial_combined_claim = collector.compute_combined_claim(output_claims);

    // The batch weights the collector assigned, in kernel-registration order.
    let per_relation_weights: Vec<E> = collector
        .kernels
        .iter()
        .flat_map(|kernel| kernel.batch_challenges().iter().copied())
        .collect();

    let challenge_constants = BatchedGKRTermDescriptionConstants::<F, E> {
        external_challenges: *external_challenges,
        lookup_challenges_multiplicative_part,
        lookup_challenges_additive_part,
        _marker: core::marker::PhantomData,
    };

    let mut capture = SumcheckLoopCapture::<E>::default();

    let (folding_challenges, round_coeffs, last_evaluations, final_normalized_claim) =
        run_sumcheck_loop::<F, E, 2, true>(
            &collector,
            initial_combined_claim,
            prev_challenges,
            &eq_polys,
            storage,
            &challenge_constants,
            folding_steps,
            worker,
            seed,
            Some(&mut capture),
        );

    LayerOracleRun {
        folding_challenges,
        round_coeffs,
        per_round_reduced: capture.per_round_reduced,
        per_round_claims: capture.per_round_claims,
        per_round_eq_prefactor: capture.per_round_eq_prefactor,
        last_evaluations,
        final_normalized_claim,
        initial_combined_claim,
        per_relation_weights,
    }
}

/// Reconstruct the committed univariate `[E; 4]` monomial form (and the recovered
/// linear coefficient `d`) from the round-polynomial evaluations `q0 = g(0)`,
/// `q2 = g(2)`, delegating the final assembly to the production emission helper.
///
/// Algebra (Codex-verified): given the folding challenge `z` from the previous
/// round, the (un-normalized) `claim`, and its `eq_prefactor`,
///
/// ```text
/// b  = 1 - z
/// C  = claim / eq_prefactor
/// e  = q0                       (= g(0), the constant coefficient)
/// q1 = (C - b * q0) / z         (= g(1), pinned by the sumcheck sum constraint)
/// c  = (q2 - 2*q1 + q0) / 2      (the quadratic / leading coefficient)
/// d  = q1 - q0 - c              (the linear coefficient)
/// ```
///
/// then emits `output_univariate_monomial_form_max_quadratic(z, C, e, c)` and
/// returns `d` separately.
pub(crate) fn recover_and_emit<F, E>(z: E, claim: E, eq_prefactor: E, q0: E, q2: E) -> ([E; 4], E)
where
    F: PrimeField,
    E: FieldExtension<F> + Field,
{
    // b = 1 - z
    let mut b = E::ONE;
    b.sub_assign(&z);

    // C = claim / eq_prefactor
    let mut big_c = claim;
    big_c.mul_assign(&eq_prefactor.inverse().expect("eq prefactor non-zero"));

    // e = q0
    let e = q0;

    // q1 = (C - b * q0) / z
    let mut bq0 = b;
    bq0.mul_assign(&q0);
    let mut q1 = big_c;
    q1.sub_assign(&bq0);
    q1.mul_assign(&z.inverse().expect("folding challenge z non-zero"));

    // c = (q2 - 2*q1 + q0) / 2
    let mut two_q1 = q1;
    two_q1.double();
    let mut c = q2;
    c.sub_assign(&two_q1);
    c.add_assign(&q0);
    let mut two = E::ONE;
    two.add_assign(&E::ONE);
    c.mul_assign(&two.inverse().expect("2 is non-zero"));

    // d = q1 - q0 - c
    let mut d = q1;
    d.sub_assign(&q0);
    d.sub_assign(&c);

    let coeffs = output_univariate_monomial_form_max_quadratic::<F, E>(z, big_c, e, c);
    (coeffs, d)
}
