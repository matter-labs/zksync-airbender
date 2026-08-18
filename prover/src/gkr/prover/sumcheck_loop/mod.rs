use crate::gkr::prover::SumcheckIntermediateProofValues;
use std::collections::BTreeMap;

use crate::gkr::prover::GKRExternalChallenges;
use crate::gkr::sumcheck::evaluation_kernels::*;
use crate::gkr::{
    prover::dimension_reduction::forward::DimensionReducingInputOutput,
    sumcheck::{
        access_and_fold::GKRStorage,
        eq_poly::{
            evaluate_constant_and_quadratic_coeffs_with_precomputed_eq,
            evaluate_with_precomputed_eq, evaluate_with_precomputed_eq_ext,
            make_eq_poly_in_full_lsb,
        },
        evaluate_eq_poly, evaluate_small_univariate_poly,
        output_univariate_monomial_form_max_quadratic,
    },
};
use crate::worker::Worker;
use field::{Field, FieldExtension, PrimeField};

use crate::gkr::prover::transcript_utils::{commit_field_els, draw_random_field_els};
use crate::gkr::prover::EvaluationPointEntry;
use cs::gkr_compiler::GKRLayerDescription;
use cs::{definitions::GKRAddress, gkr_compiler::OutputType};
use kernel_collector::KernelCollector;
use transcript::Transcript;

pub(crate) mod batch_evaluation;
mod distribution_analysis;
mod kernel_collector;
pub(crate) mod windowed_mode;

pub use windowed_mode::lsb_chain::SameSizeChainOps;
pub use windowed_mode::program::OwnedSoaProgram;

pub fn flatten_claim_point<E: Field>(point: &[EvaluationPointEntry<E>]) -> Vec<E> {
    let mut result = Vec::new();
    for el in point.iter() {
        match el {
            EvaluationPointEntry::Coordinate { point } => {
                result.push(*point);
            }
            EvaluationPointEntry::Uniskip { point, width } => {
                unimplemented!("uniskip steps are not supported for now");
            }
        }
    }

    result
}

/// LSB-binding dimension-reducing backward pass for one layer:
/// the sumcheck binds the OUTPUT space's variables LSB-first through the raw
/// slice engine (`dimension_reduction::lsb_backward`), reading contiguous
/// 4-blocks per round and folding with dense ping-pong writes. The claim
/// point is emitted in plain variable order: `[r_last, lsb challenges..]`
/// (`r_last` binds the gate bit = input bit 0).
///
/// The pass is split around round 0's transcript interaction: the initial
/// round reads gate values straight from the OUTPUT layer polys; once its
/// challenge is drawn the output pointer map is dropped and the output layer
/// purged from storage, then the continuing rounds run as a plain cycle over
/// the input polys and the fold scratch.
///
/// `S` is the chunk kernels' per-row tri-scratch slot type — an
/// implementation detail of the kernels (typed `[E; 2]` rows for the scalar
/// kernels, vector-compatible erased slots for SIMD kernels); this function
/// only sizes and hands out the slots.
#[allow(clippy::too_many_arguments)]
pub fn evaluate_dimension_reducing_sumcheck_for_layer_lsb<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    TR: Transcript<F, E>,
    S: Send + Sync,
    CKI: Fn(
            &BTreeMap<GKRAddress, &[E]>,
            &BTreeMap<GKRAddress, &[E]>,
            &[crate::gkr::prover::dimension_reduction::lsb_backward::LsbDimReducingRelation<E>],
            crate::gkr::prover::SendConstPtr<E>,
            usize,
            usize,
            crate::gkr::prover::SendPtr<S>,
        ) -> [E; 2]
        + Send
        + Sync
        + Copy,
    CK: Fn(
            &BTreeMap<
                GKRAddress,
                crate::gkr::prover::dimension_reduction::lsb_backward::FoldBufferTracker<E>,
            >,
            &[crate::gkr::prover::dimension_reduction::lsb_backward::LsbDimReducingRelation<E>],
            E,
            crate::gkr::prover::SendConstPtr<E>,
            usize,
            usize,
            crate::gkr::prover::SendPtr<S>,
        ) -> [E; 2]
        + Send
        + Sync
        + Copy,
>(
    initial_chunk_kernel: CKI,
    continuing_chunk_kernel: CK,
    schedule: &[crate::gkr::prover_config::SumcheckStep],
    layer_idx: usize,
    layer: &BTreeMap<OutputType, DimensionReducingInputOutput>,
    claim_points: &mut BTreeMap<usize, Vec<EvaluationPointEntry<E>>>,
    claims_storage: &mut BTreeMap<usize, BTreeMap<GKRAddress, E>>,
    gkr_storage: &mut GKRStorage<F, E>,
    batching_challenge: &mut E,
    seed: &mut TR::Seed,
    trace_len_after_reduction: usize,
    worker: &Worker,
    scratch: &mut crate::gkr::prover::gkr_backend::DimReducingSumcheckScratch<E, S>,
) -> SumcheckIntermediateProofValues<F, E>
where
    [(); E::DEGREE]: Sized,
{
    use crate::gkr::prover::dimension_reduction::lsb_backward::{
        lsb_dim_reducing_sumcheck_continue, lsb_dim_reducing_sumcheck_initial_round,
        FoldBufferTracker, LsbDimReducingRelation,
    };

    // the production engines run naive (one variable per round) schedules
    // only; windowed dimension-reducing passes were removed
    assert!(
        schedule
            .iter()
            .all(|s| matches!(s, crate::gkr::prover_config::SumcheckStep::NaiveSumcheck)),
        "the dimension-reducing engines support only naive round schedules; got {:?}",
        schedule
    );

    println!("Evaluating layer {layer_idx} (dimension reducing, LSB) in sumcheck direction");
    let layer_timer = std::time::Instant::now();
    let output_layer_idx = layer_idx + 1;

    let output_claims = claims_storage
        .get(&output_layer_idx)
        .expect("claims for output layer must exist");
    let prev_challenges = claim_points
        .get(&output_layer_idx)
        .expect("claim points for output layer must exist");
    let prev_challenges = flatten_claim_point(prev_challenges);

    assert!(trace_len_after_reduction.is_power_of_two());
    let folding_steps = trace_len_after_reduction.trailing_zeros() as usize;
    assert!(folding_steps >= 2, "need at least 2 folding steps");

    let batch_challenge_base = *batching_challenge;

    // relation list + combined claim, mirroring
    // KernelCollector::from_dimension_reducing_relations (challenge powers
    // start at ONE and multiply by the base per challenge)
    let mut cbc = E::ONE;
    let mut relations: Vec<LsbDimReducingRelation<E>> = vec![];
    let mut claim = E::ZERO;
    for (k, v) in layer {
        match *k {
            OutputType::PermutationProduct | OutputType::InitsAndTeardownsProduct => {
                for (inp, out) in v.inputs.iter().zip(v.output.iter()) {
                    let alpha = cbc;
                    cbc.mul_assign(&batch_challenge_base);
                    relations.push(LsbDimReducingRelation::PairwiseProduct {
                        input: *inp,
                        output: *out,
                        alpha,
                    });
                    let mut t = alpha;
                    t.mul_assign(&output_claims[out]);
                    claim.add_assign(&t);
                }
            }
            OutputType::Lookup16Bits | OutputType::LookupTimestamps | OutputType::GenericLookup => {
                let alpha_num = cbc;
                cbc.mul_assign(&batch_challenge_base);
                let alpha_den = cbc;
                cbc.mul_assign(&batch_challenge_base);
                relations.push(LsbDimReducingRelation::LogupPair {
                    num: v.inputs[0],
                    den: v.inputs[1],
                    num_output: v.output[0],
                    den_output: v.output[1],
                    alpha_num,
                    alpha_den,
                });
                let mut t = alpha_num;
                t.mul_assign(&output_claims[&v.output[0]]);
                claim.add_assign(&t);
                let mut t = alpha_den;
                t.mul_assign(&output_claims[&v.output[1]]);
                claim.add_assign(&t);
            }
            _ => panic!("unexpected output type in dimension-reducing layer"),
        }
    }

    let input_addrs: std::collections::BTreeSet<GKRAddress> = relations
        .iter()
        .flat_map(|rel| rel.input_addresses())
        .collect();
    fn select_slices<'a, F: PrimeField, E: FieldExtension<F> + Field>(
        gkr_storage: &'a GKRStorage<F, E>,
        addrs: &std::collections::BTreeSet<GKRAddress>,
    ) -> BTreeMap<GKRAddress, &'a [E]> {
        addrs
            .iter()
            .map(|addr| {
                let poly: &[E] = gkr_storage
                    .try_get_ext_poly(*addr)
                    .expect("dimension-reducing polys live in the extension field");
                (*addr, poly)
            })
            .collect()
    }

    // incoming claim points are stored in plain variable order (bit 0 first),
    // exactly the low-variable-first order the engine binds in, so the point
    // passes through untouched
    let tau: &[E] = &prev_challenges[..];

    // fold + tri scratch shared across ALL dimension-reducing layers,
    // max-sized and owned by the backward-pass driver loop; each input poly
    // gets a ping-pong tracker over its (scratch-only) pool allocation
    let crate::gkr::prover::gkr_backend::DimReducingSumcheckScratch { fold, tri } = scratch;
    assert!(fold.len() >= input_addrs.len());
    let input_poly_len = 2 * trace_len_after_reduction;
    let mut fold_buffers: BTreeMap<GKRAddress, FoldBufferTracker<E>> = input_addrs
        .iter()
        .zip(fold.iter_mut())
        .map(|(addr, pool)| {
            (
                *addr,
                FoldBufferTracker::new(pool.as_mut_ptr() as *mut E, pool.len(), input_poly_len),
            )
        })
        .collect();

    // ---- round 0 over plain BORROWED slices (nothing is written); the
    // borrows end before the transcript interaction, and its suffix eq table
    // is handed to the continuing rounds for contraction
    let (round_0_coefficients, t_table) = {
        let inputs = select_slices(gkr_storage, &input_addrs);
        let outputs = select_slices(
            gkr_storage,
            &relations
                .iter()
                .flat_map(|rel| rel.output_addresses())
                .collect(),
        );
        lsb_dim_reducing_sumcheck_initial_round::<F, E, S, CKI>(
            &inputs,
            &outputs,
            &relations,
            tau,
            claim,
            worker,
            &mut tri[..],
            initial_chunk_kernel,
        )
    };
    commit_field_els::<F, E, TR>(seed, &round_0_coefficients);
    let r_0 = draw_random_field_els::<F, E, TR>(seed, 1)[0];

    // the output layer is fully consumed by round 0: free it now so the
    // fold scratch reuses the pages fault-free
    gkr_storage.purge_up_to_layer(layer_idx);

    // ---- rounds 1..: the trivial fold-and-evaluate cycle; only the INPUT
    // polys are re-selected after the purge — round 1 reads them as
    // borrowed slices, every later round reads tracker-owned regions
    let continue_inputs = select_slices(gkr_storage, &input_addrs);
    let (out, continuing_challenges) = lsb_dim_reducing_sumcheck_continue::<F, E, S, CK>(
        &continue_inputs,
        &mut fold_buffers,
        &relations,
        tau,
        &round_0_coefficients,
        r_0,
        t_table,
        worker,
        &mut tri[..],
        continuing_chunk_kernel,
        |coeffs| {
            commit_field_els::<F, E, TR>(seed, coeffs);
            draw_random_field_els::<F, E, TR>(seed, 1)[0]
        },
    );
    let lsb_challenges: Vec<E> = core::iter::once(r_0)
        .chain(continuing_challenges.into_iter())
        .collect();

    // the engine's final values ARE the [E;2] LSB lines per input address
    let lsb_lines: BTreeMap<GKRAddress, [E; 2]> = out.final_values;

    let final_step_evaluations: BTreeMap<GKRAddress, Vec<E>> =
        lsb_lines.iter().map(|(k, v)| (*k, v.to_vec())).collect();

    let transcript_inputs: Vec<E> = lsb_lines.values().flatten().copied().collect();
    commit_field_els::<F, E, TR>(seed, &transcript_inputs);

    let challenges = draw_random_field_els::<F, E, TR>(seed, 2);
    let [r_last, next_batching_challenge] = challenges.try_into().unwrap();

    // r_last actually binds a bit 0 in enumeration
    let mut folding_challenges: Vec<E> = Vec::with_capacity(lsb_challenges.len() + 1);
    folding_challenges.push(r_last);
    folding_challenges.extend(lsb_challenges);

    let new_claims: BTreeMap<_, _> = lsb_lines
        .iter()
        .map(|(addr, [lsb0, lsb1])| (*addr, interpolate_linear::<E>(*lsb0, *lsb1, &r_last)))
        .collect();

    #[cfg(feature = "gkr_self_checks")]
    {
        println!("Self-checking explicit at-point evaluations (LSB path)");
        // the emitted point is in plain variable order (bit 0 = r_last first),
        // so the plain LSB-first builder consumes it directly
        let eq = crate::gkr::sumcheck::eq_poly::make_eq_table_lsb_first::<E>(
            &folding_challenges,
            worker,
        );
        for (k, v) in new_claims.iter() {
            if let Some(poly) = gkr_storage.try_get_base_poly(*k) {
                let eval = evaluate_with_precomputed_eq(poly, &eq[..]);
                assert_eq!(eval, *v, "claim diverged for poly {k:?}");
            } else if let Some(poly) = gkr_storage.try_get_ext_poly(*k) {
                let eval = evaluate_with_precomputed_eq_ext(poly, &eq[..]);
                assert_eq!(eval, *v, "claim diverged for poly {k:?}");
            } else {
                unreachable!()
            }
        }
    }

    claims_storage.insert(layer_idx, new_claims);
    // the claim/evaluation coordinate must ALWAYS have one entry per bound
    // variable of the INPUT layer: the output rounds plus the kernel-fixed
    // gate bit bound by `r_last` (holds for any schedule, incl. uniskips)
    assert_eq!(folding_challenges.len(), folding_steps + 1);
    claim_points.insert(
        layer_idx,
        folding_challenges
            .into_iter()
            .map(|el| EvaluationPointEntry::Coordinate { point: el })
            .collect::<Vec<_>>(),
    );

    gkr_storage.purge_up_to_layer(layer_idx);

    *batching_challenge = next_batching_challenge;

    println!(
        "Dimension-reducing layer {layer_idx} sumcheck took {:?}",
        layer_timer.elapsed()
    );

    SumcheckIntermediateProofValues {
        sumcheck_num_rounds: folding_steps,
        internal_round_coefficients: core::iter::once(round_0_coefficients)
            .chain(out.round_coefficients.into_iter())
            .map(crate::gkr::prover::SumcheckRoundCoefficients::Multilinear)
            .collect(),
        final_step_evaluations,
        extra_evaluations_from_caching_relations: BTreeMap::new(), // none are possible here
        _marker: core::marker::PhantomData,
    }
}

/// Outcome of one same-size case engine (naive / windowed / uniskip),
/// before the shared postlude: the emitted transcript rounds, the layer's
/// own claim point (in emission = variable order), and the per-input
/// at-point claims.
struct SameSizeOutcome<E: Field> {
    rounds: Vec<crate::gkr::prover::SumcheckRoundCoefficients<E>>,
    point_entries: Vec<EvaluationPointEntry<E>>,
    new_claims: BTreeMap<GKRAddress, E>,
}

/// Same-size layer sumcheck driver (called through
/// [`GKRBackend::evaluate_same_size_sumcheck_for_layer`](crate::gkr::prover::gkr_backend::GKRBackend::evaluate_same_size_sumcheck_for_layer)):
/// builds the layer's batched relation, selects the schedule from the
/// [`ProverConfig`](crate::gkr::prover_config::ProverConfig) by layer width,
/// validates it against the STRICT grammar, branches early into the
/// all-naive / windowed / uniskip case engine, and finishes with the shared
/// claim-emission postlude. The `make_*_fold_buffers` closures are the
/// backend's fold-buffer constructors
/// (`(schedule, trace_len, num_base_polys, num_ext_polys)`), called only
/// for the class that actually runs.
///
/// # Panics
/// Panics if claims or challenge points for the output layer are missing
/// from storage, or if the configured schedule is invalid for this layer.
#[allow(clippy::too_many_arguments)]
pub fn evaluate_sumcheck_for_layer<
    F: PrimeField + field::TwoAdicField,
    E: FieldExtension<F> + Field,
    TR: Transcript<F, E>,
    C: SameSizeChainOps<F, E>,
>(
    layer_idx: usize,
    layer: &GKRLayerDescription<F>,
    claim_point_entries: &mut BTreeMap<usize, Vec<crate::gkr::prover::EvaluationPointEntry<E>>>,
    claims_storage: &mut BTreeMap<usize, BTreeMap<GKRAddress, E>>,
    gkr_storage: &mut GKRStorage<F, E>,
    batching_challenge: &mut E,
    trace_len: usize,
    lookup_challenges_multiplicative_part: E,
    lookup_challenges_additive_part: E,
    inits_and_teardowns_top_bits: &[u32],
    address_high_bits_shift: u32,
    external_challenges: &GKRExternalChallenges<F, E>,
    prover_config: &crate::gkr::prover_config::ProverConfig,
    seed: &mut TR::Seed,
    worker: &Worker,
    make_uniskip_fold_buffers: impl FnOnce(
        &[crate::gkr::prover_config::SumcheckStep],
        usize,
        usize,
        usize,
    ) -> Vec<Box<[core::mem::MaybeUninit<E>]>>,
    make_windowed_fold_buffers: impl FnOnce(
        &[crate::gkr::prover_config::SumcheckStep],
        usize,
        usize,
        usize,
    ) -> Vec<Box<[core::mem::MaybeUninit<E>]>>,
    make_chain: impl FnOnce(OwnedSoaProgram<F, E>) -> C,
) -> SumcheckIntermediateProofValues<F, E>
where
    [(); E::DEGREE]: Sized,
{
    use crate::gkr::prover_config::{validate_sumcheck_schedule, SumcheckScheduleClass};

    println!("Evaluating layer {layer_idx} in sumcheck direction");

    let output_layer_idx = layer_idx + 1;
    let output_claims = claims_storage
        .get(&output_layer_idx)
        .expect("claims for output layer must exist");
    // the previous layer's point: scalar coordinates and/or mixed entries
    // (a uniskip-scheduled producer emits Uniskip entries); cloned so the
    // map stays free for this layer's own insertion
    let prev_entries: Vec<EvaluationPointEntry<E>> = claim_point_entries
        .get(&output_layer_idx)
        .unwrap_or_else(|| panic!("Missing evaluation point for layer {}", output_layer_idx))
        .clone();

    assert!(trace_len.is_power_of_two());
    let folding_steps = trace_len.trailing_zeros() as usize;
    assert!(folding_steps >= 4, "need at least 4 folding steps");
    assert_eq!(
        prev_entries.iter().map(|e| e.bound_vars()).sum::<usize>(),
        folding_steps,
        "prev point must cover every variable"
    );

    let batch_challenge_base = *batching_challenge;
    let collector = KernelCollector::from_layer(
        layer,
        layer_idx,
        batch_challenge_base,
        lookup_challenges_multiplicative_part,
        lookup_challenges_additive_part,
        inits_and_teardowns_top_bits,
        address_high_bits_shift,
    );
    debug_assert!(!collector.is_empty());
    let claim = collector.compute_combined_claim(output_claims);
    let challenge_constants = BatchedGKRTermDescriptionConstants::<F, E> {
        external_challenges: *external_challenges,
        lookup_challenges_multiplicative_part,
        lookup_challenges_additive_part,
        _marker: core::marker::PhantomData,
    };

    let description = collector.make_batched_description(&challenge_constants, collector.layer);
    let (_compact, chain_base_addrs, chain_ext_addrs) =
        windowed_mode::full_size_scratch::produce_descriptions_from_batched_description(
            &description,
        );
    let width = chain_base_addrs.len() + chain_ext_addrs.len();
    let schedule = prover_config.same_size_sumcheck_schedule.as_slice();
    let class = validate_sumcheck_schedule(schedule, folding_steps)
        .unwrap_or_else(|e| panic!("same_size_sumcheck_schedule: {e}"));
    println!(
        "[ss-schedule] layer {layer_idx}: {width} input polys -> {:?}",
        class
    );

    let outcome = match class {
        SumcheckScheduleClass::Naive => same_size_naive_sumcheck::<F, E, TR>(
            &collector,
            &challenge_constants,
            claim,
            &prev_entries,
            folding_steps,
            gkr_storage,
            seed,
            worker,
        ),
        SumcheckScheduleClass::Uniskip | SumcheckScheduleClass::Windowed => {
            let mut fold_buffers = if class == SumcheckScheduleClass::Uniskip {
                make_uniskip_fold_buffers(
                    schedule,
                    trace_len,
                    chain_base_addrs.len(),
                    chain_ext_addrs.len(),
                )
            } else {
                make_windowed_fold_buffers(
                    schedule,
                    trace_len,
                    chain_base_addrs.len(),
                    chain_ext_addrs.len(),
                )
            };
            let chain_timer = std::time::Instant::now();
            let prog = windowed_mode::program::build_soa_program(
                &description,
                &collector,
                layer,
                &challenge_constants,
                &chain_base_addrs,
                &chain_ext_addrs,
            );
            let chain = make_chain(prog);
            let outcome = same_size_chain_sumcheck::<F, E, TR, C>(
                schedule,
                &chain,
                &chain_base_addrs,
                &chain_ext_addrs,
                claim,
                &prev_entries,
                folding_steps,
                gkr_storage,
                &mut fold_buffers,
                seed,
                worker,
            );
            println!(
                "LSB chain for same-size layer {layer_idx} took {:?}",
                chain_timer.elapsed()
            );
            outcome
        }
    };

    finish_same_size_layer::<F, E, TR>(
        layer_idx,
        layer,
        outcome,
        folding_steps,
        claim_point_entries,
        claims_storage,
        gkr_storage,
        batching_challenge,
        external_challenges,
        lookup_challenges_multiplicative_part,
        seed,
        worker,
    )
}

/// The all-naive case: the per-round batched evaluator with the lazy
/// (merged) fold. The initial round and the continuing rounds run through
/// the same [`run_sumcheck_loop`] (round 0 reads the original polys, every
/// later round folds the previous challenge on read).
#[allow(clippy::too_many_arguments)]
fn same_size_naive_sumcheck<F: PrimeField, E: FieldExtension<F> + Field, TR: Transcript<F, E>>(
    collector: &KernelCollector<F, E>,
    challenge_constants: &BatchedGKRTermDescriptionConstants<F, E>,
    claim: E,
    prev_entries: &[EvaluationPointEntry<E>],
    folding_steps: usize,
    gkr_storage: &mut GKRStorage<F, E>,
    seed: &mut TR::Seed,
    worker: &Worker,
) -> SameSizeOutcome<E>
where
    [(); E::DEGREE]: Sized,
{
    // the scalar loop consumes a plain per-variable point
    let prev_challenges: Vec<E> = prev_entries
        .iter()
        .map(|e| match e {
            EvaluationPointEntry::Coordinate { point } => *point,
            other => panic!(
                "the naive same-size path needs a scalar previous point, got {other:?} \
                 (a uniskip-scheduled producer must be followed by a chain schedule)"
            ),
        })
        .collect();
    let eq_polys = make_eq_poly_in_full_lsb::<E>(&prev_challenges, worker);

    let (folding_challenges, internal_round_coefficients, last_evaluations, _final_claim) =
        run_sumcheck_loop::<F, E, TR, 2, true>(
            collector,
            claim,
            &prev_challenges,
            &eq_polys,
            gkr_storage,
            challenge_constants,
            folding_steps,
            worker,
            seed,
        );
    assert_eq!(folding_challenges.len(), folding_steps);
    assert_eq!(internal_round_coefficients.len(), folding_steps);

    // the last folding challenge fixes the final coordinate: reduce every
    // input poly's line [f0, f1] to its at-point evaluation
    let last_r = *folding_challenges.last().expect("at least one round");
    let new_claims: BTreeMap<_, _> = last_evaluations
        .iter()
        .map(|(addr, &[f0, f1])| (*addr, interpolate_linear::<E>(f0, f1, &last_r)))
        .collect();

    #[cfg(feature = "gkr_self_checks")]
    {
        // final claim vs the batched gate on the at-point evaluations
        let augmented_claims: BTreeMap<_, [E; 2]> = new_claims
            .iter()
            .map(|(addr, v)| (*addr, [*v, E::ZERO]))
            .collect();
        let recomputed = collector
            .compute_last_step_accumulator_from_evals(challenge_constants, &augmented_claims);
        assert_eq!(
            recomputed[0], _final_claim,
            "last_evaluations inconsistent with final accumulator constant term G(0)"
        );
    }

    SameSizeOutcome {
        rounds: internal_round_coefficients
            .into_iter()
            .map(crate::gkr::prover::SumcheckRoundCoefficients::Multilinear)
            .collect(),
        point_entries: folding_challenges
            .into_iter()
            .map(|point| EvaluationPointEntry::Coordinate { point })
            .collect(),
        new_claims,
    }
}

/// Running transcript/claim state of a chain (uniskip or windowed) case.
struct ChainState<E: Field> {
    running_claim: E,
    /// the single last-round eq factor of the scalar-round convention,
    /// REPLACED per scalar round (uniskip rounds consume raw claims and
    /// never touch it)
    eq_prefactor: E,
    rounds: Vec<crate::gkr::prover::SumcheckRoundCoefficients<E>>,
    entries: Vec<EvaluationPointEntry<E>>,
    vars_bound: usize,
    pass_idx: usize,
}

/// Prev-point weight blocks fully inside the variable window `[lo, hi)`
/// (panics if an entry straddles the window).
fn blocks_in<'a, E: Field>(
    lo: usize,
    hi: usize,
    spans: &[(usize, usize)],
    prev_blocks: &'a [Vec<E>],
) -> Vec<&'a [E]> {
    let mut out = Vec::new();
    for ((s0, w), b) in spans.iter().zip(prev_blocks.iter()) {
        if *s0 >= lo && s0 + w <= hi {
            out.push(&b[..]);
        } else {
            assert!(
                s0 + w <= lo || *s0 >= hi,
                "entry straddles the pass window [{lo}, {hi})"
            );
        }
    }
    assert_eq!(
        out.iter()
            .map(|b| b.len().trailing_zeros() as usize)
            .sum::<usize>(),
        hi - lo
    );
    out
}

/// The prev point's SCALAR coordinate of `var` (must be a width-1 block: a
/// straddling uniskip block in the producer would make scalar rounds
/// unschedulable there).
fn scalar_coord<E: Field>(var: usize, spans: &[(usize, usize)], prev_blocks: &[Vec<E>]) -> E {
    let (bi, _) = spans
        .iter()
        .enumerate()
        .find(|(_, (s0, w))| *s0 == var && *w == 1)
        .map(|(i, sp)| (i, *sp))
        .expect("scalar rounds need width-1 prev blocks at their variables");
    prev_blocks[bi][1]
}

/// One scalar chain round (a window-pass round or a tail round) binding the
/// current variable, in the SAME single-eq-factor form as the naive
/// per-round loop (byte-identical message for identical inputs).
fn scalar_chain_round<F: PrimeField, E: FieldExtension<F> + Field, TR: Transcript<F, E>>(
    st: &mut ChainState<E>,
    tau: E,
    h0: E,
    hinf: E,
    seed: &mut TR::Seed,
) -> E {
    let mut normalized_claim = st.running_claim;
    normalized_claim.mul_assign(&st.eq_prefactor.inverse().expect("eq prefactor non-zero"));
    let coeffs =
        output_univariate_monomial_form_max_quadratic::<F, E>(tau, normalized_claim, h0, hinf);
    commit_field_els::<F, E, TR>(seed, &coeffs);
    st.rounds
        .push(crate::gkr::prover::SumcheckRoundCoefficients::Multilinear(
            coeffs,
        ));
    let r = draw_random_field_els::<F, E, TR>(seed, 1)[0];
    st.running_claim = evaluate_small_univariate_poly::<F, E, _>(&coeffs, &r);
    st.eq_prefactor = evaluate_eq_poly::<F, E>(&r, &tau);
    st.entries
        .push(EvaluationPointEntry::Coordinate { point: r });
    st.vars_bound += 1;
    r
}

/// One uniskip pass's transcript round: monomial conversion, the H-claim
/// self-check, commit/draw, the Horner claim update, and the Lagrange fold
/// weights of the drawn challenge.
#[allow(unused_variables)]
fn uniskip_transcript_round<F: PrimeField, E: FieldExtension<F> + Field, TR: Transcript<F, E>>(
    st: &mut ChainState<E>,
    q16: [E; 16],
    spans: &[(usize, usize)],
    prev_blocks: &[Vec<E>],
    omega16_f: F,
    seed: &mut TR::Seed,
    worker: &Worker,
) -> [E; 8] {
    use crate::gkr::prover::sumcheck_loop::windowed_mode::uniskip::*;

    let g = st.pass_idx;
    let coeffs = uniskip16_to_monomial::<F, E>(&q16, omega16_f);
    #[cfg(feature = "gkr_self_checks")]
    {
        // pass g binds vars 3g..3g+3: its claim identity uses the prev
        // point's blocks over those vars
        let eq8: [E; 8] = crate::gkr::sumcheck::eq_poly::make_eq_table_from_weight_blocks::<E>(
            &blocks_in(3 * g, 3 * g + 3, spans, prev_blocks),
            worker,
        )
        .try_into()
        .unwrap();
        assert_eq!(
            uniskip16_claim_from_monomial::<F, E>(&coeffs, &eq8, omega16_f),
            st.running_claim,
            "LSB uniskip chain: claim identity over H at pass {g}"
        );
    }
    commit_field_els::<F, E, TR>(seed, &coeffs);
    st.rounds
        .push(crate::gkr::prover::SumcheckRoundCoefficients::Uniskip(
            coeffs.to_vec(),
        ));
    let r = draw_random_field_els::<F, E, TR>(seed, 1)[0];
    st.running_claim = uniskip16_horner(&coeffs, &r);
    st.entries
        .push(EvaluationPointEntry::Uniskip { point: r, width: 3 });
    st.vars_bound += 3;
    st.pass_idx += 1;
    uniskip8_fold_weights::<F, E>(&r, omega16_f)
}

/// One window pass's three scalar bind rounds over its 27-cell accumulator;
/// returns the eq-tensor fold weights of the drawn challenges.
fn window_pass_rounds<F: PrimeField, E: FieldExtension<F> + Field, TR: Transcript<F, E>>(
    st: &mut ChainState<E>,
    acc27: [E; 27],
    spans: &[(usize, usize)],
    prev_blocks: &[Vec<E>],
    seed: &mut TR::Seed,
) -> [E; 8] {
    use windowed_mode::{
        bind_accumulator_27, bind_accumulator_9, evaluate_claim_from_intermediate_matrix_27,
        evaluate_claim_from_intermediate_matrix_9,
    };

    let v = st.vars_bound;
    let tau0 = scalar_coord(v, spans, prev_blocks);
    let tau1 = scalar_coord(v + 1, spans, prev_blocks);
    let tau2 = scalar_coord(v + 2, spans, prev_blocks);
    let eqf = |x: usize, t: &E| -> E {
        if x == 0 {
            let mut v = E::ONE;
            v.sub_assign(t);
            v
        } else {
            *t
        }
    };
    // matrix contraction layout: eq4[2*x1 + x2]
    let eq4: [E; 4] = core::array::from_fn(|i| {
        let mut v = eqf(i >> 1, &tau1);
        v.mul_assign(&eqf(i & 1, &tau2));
        v
    });
    let eq2: [E; 2] = core::array::from_fn(|i| eqf(i, &tau2));

    let e3 = evaluate_claim_from_intermediate_matrix_27(&eq4, &acc27);
    let r0 = scalar_chain_round::<F, E, TR>(st, tau0, e3[0], e3[2], seed);
    let acc9 = bind_accumulator_27(&acc27, &r0);
    let e3 = evaluate_claim_from_intermediate_matrix_9(&eq2, &acc9);
    let r1 = scalar_chain_round::<F, E, TR>(st, tau1, e3[0], e3[2], seed);
    let acc3 = bind_accumulator_9(&acc9, &r1);
    let r2 = scalar_chain_round::<F, E, TR>(st, tau2, acc3[0], acc3[2], seed);
    st.pass_idx += 1;

    core::array::from_fn(|i| {
        let mut v = eqf(i & 1, &r0);
        v.mul_assign(&eqf((i >> 1) & 1, &r1));
        v.mul_assign(&eqf((i >> 2) & 1, &r2));
        v
    })
}

/// After a fold: advance every tracker so the just-written region becomes
/// the input, with the next output sized by the FOLLOWING schedule step
/// (`live / 8` before another pass, `live / 2` before the tail's first
/// halving fold — which is also 0 once the live region is a single value).
fn step_trackers_for_next<E>(
    trackers: &mut [crate::gkr::prover::dimension_reduction::lsb_backward::FoldBufferTracker<E>],
    next_is_pass: bool,
) {
    let live = trackers[0].output_len();
    let next = if next_is_pass { live / 8 } else { live / 2 };
    for t in trackers.iter_mut() {
        t.step_to(next);
    }
}

/// The chain case (uniskip or windowed, per the validated schedule): the
/// INITIAL pass + its explicit fold, then [`chain_continue`] over the
/// remaining schedule steps, then the finals from the trackers. The
/// executor `C` is the backend's associated chain type; the polys are read
/// from storage here and handed to it as plain borrowed slices.
#[allow(clippy::too_many_arguments)]
fn same_size_chain_sumcheck<
    F: PrimeField + field::TwoAdicField,
    E: FieldExtension<F> + Field,
    TR: Transcript<F, E>,
    C: SameSizeChainOps<F, E>,
>(
    schedule: &[crate::gkr::prover_config::SumcheckStep],
    chain: &C,
    base_addrs: &[GKRAddress],
    ext_addrs: &[GKRAddress],
    claim: E,
    prev_entries: &[EvaluationPointEntry<E>],
    folding_steps: usize,
    gkr_storage: &GKRStorage<F, E>,
    fold_buffers: &mut [Box<[core::mem::MaybeUninit<E>]>],
    seed: &mut TR::Seed,
    worker: &Worker,
) -> SameSizeOutcome<E>
where
    [(); E::DEGREE]: Sized,
{
    use crate::gkr::prover::dimension_reduction::lsb_backward::FoldBufferTracker;
    use crate::gkr::prover_config::SumcheckStep;
    use windowed_mode::lsb_chain::*;

    let n = folding_steps;
    let omega16_f: F = ::fft::domain_generator_for_size::<F>(16);
    // the original layer inputs as plain borrowed slices, in slot order
    let base_polys: Vec<&[F]> = base_addrs
        .iter()
        .map(|a| {
            gkr_storage
                .try_get_base_poly(*a)
                .expect("chain sources must be present in storage")
        })
        .collect();
    let ext_polys: Vec<&[E]> = ext_addrs
        .iter()
        .map(|a| {
            gkr_storage
                .try_get_ext_poly(*a)
                .expect("chain sources must be present in storage")
        })
        .collect();
    let num_passes = schedule
        .iter()
        .filter(|s| {
            matches!(
                s,
                SumcheckStep::UniskipInitial { .. }
                    | SumcheckStep::UniskipContinuing { .. }
                    | SumcheckStep::WindowInitial { .. }
                    | SumcheckStep::WindowContinuing { .. }
            )
        })
        .count();
    let tail_rounds = n - 3 * num_passes;

    // previous point as per-entry weight blocks in VARIABLE order, plus each
    // block's variable span
    let prev_blocks: Vec<Vec<E>> = prev_entries
        .iter()
        .map(|e| e.eq_weight_block::<F>(omega16_f))
        .collect();
    let mut spans: Vec<(usize, usize)> = Vec::with_capacity(prev_blocks.len());
    let mut off = 0usize;
    for b in prev_blocks.iter() {
        let w = b.len().trailing_zeros() as usize;
        spans.push((off, w));
        off += w;
    }
    assert_eq!(off, n);

    // Suffix eq tables for every step of the schedule, built ONCE by
    // interleaved extension from the shortest suffix (each length is an
    // intermediate of the next longer one, so retention is free and no
    // contraction is ever needed): pass `g` reads the table over its HIGH
    // variables (suffix length `n - 3*(g+1)`), and the tail round binding
    // variable `v` reads the table over `v+1..n` (length `n - v - 1`).
    let mut needed = std::collections::BTreeSet::new();
    for g in 0..num_passes {
        needed.insert(n - 3 * (g + 1));
    }
    for t in 0..tail_rounds {
        needed.insert(tail_rounds - 1 - t);
    }
    let all_blocks: Vec<&[E]> = prev_blocks.iter().map(|b| &b[..]).collect();
    let suffix_tables =
        crate::gkr::sumcheck::eq_poly::SuffixTables::<E>::materialize(&all_blocks, &needed, worker);

    // one ping-pong fold tracker per input poly, in slot order
    assert_eq!(fold_buffers.len(), base_polys.len() + ext_polys.len());
    let first_out = 1usize << (n - 3);
    let mut trackers: Vec<FoldBufferTracker<E>> = fold_buffers
        .iter_mut()
        .map(|b| {
            FoldBufferTracker::new_with_first_output(b.as_mut_ptr() as *mut E, b.len(), first_out)
        })
        .collect();

    let mut st = ChainState {
        running_claim: claim,
        eq_prefactor: E::ONE,
        rounds: Vec::new(),
        entries: Vec::new(),
        vars_bound: 0,
        pass_idx: 0,
    };

    // ---- the INITIAL pass and its explicit fold (schedule[0..2]) ----
    let out_size = 1usize << (n - 3);
    let initial_suffix = suffix_tables.get(n - 3);
    let weights = match schedule[0] {
        SumcheckStep::UniskipInitial { window: 3 } => {
            let q16 = chain.uniskip_initial_pass(
                &base_polys,
                &ext_polys,
                initial_suffix,
                out_size,
                worker,
            );
            uniskip_transcript_round::<F, E, TR>(
                &mut st,
                q16,
                &spans,
                &prev_blocks,
                omega16_f,
                seed,
                worker,
            )
        }
        SumcheckStep::WindowInitial { window: 3 } => {
            let acc27 = chain.window_initial_pass(
                &base_polys,
                &ext_polys,
                initial_suffix,
                out_size,
                worker,
            );
            let w = window_pass_rounds::<F, E, TR>(&mut st, acc27, &spans, &prev_blocks, seed);
            st.pass_idx = 1;
            w
        }
        other => unreachable!("validated schedule cannot open with {other:?}"),
    };
    debug_assert!(matches!(
        schedule[1],
        SumcheckStep::FoldInitial { width: 3 }
    ));
    chain.fold_initial(&base_polys, &ext_polys, &weights, &mut trackers, worker);
    step_trackers_for_next(
        &mut trackers,
        !matches!(schedule.get(2), Some(SumcheckStep::Tail)),
    );

    // ---- the continuing rounds: walk the remaining schedule ----
    chain_continue::<F, E, TR, C>(
        chain,
        &schedule[2..],
        n,
        &mut st,
        &mut trackers,
        &suffix_tables,
        &spans,
        &prev_blocks,
        seed,
        worker,
    );
    assert_eq!(st.vars_bound, n, "the schedule must bind every variable");

    // finals: every tracker's live region is down to a single value
    let new_claims: BTreeMap<GKRAddress, E> = base_addrs
        .iter()
        .chain(ext_addrs.iter())
        .zip(trackers.iter())
        .map(|(addr, t)| {
            let s = unsafe { t.input_slice() };
            assert_eq!(s.len(), 1);
            (*addr, s[0])
        })
        .collect();

    SameSizeOutcome {
        rounds: st.rounds,
        point_entries: st.entries,
        new_claims,
    }
}

/// The chain's CONTINUING function: a plain loop over the remaining
/// schedule steps, dispatching per step — a continuing pass computes and
/// runs its transcript rounds (leaving its fold weights pending), the
/// explicit fold materializes them into the trackers, and the `Tail` step
/// binds every remaining variable with scalar rounds.
#[allow(clippy::too_many_arguments)]
fn chain_continue<
    F: PrimeField + field::TwoAdicField,
    E: FieldExtension<F> + Field,
    TR: Transcript<F, E>,
    C: SameSizeChainOps<F, E>,
>(
    chain: &C,
    remaining: &[crate::gkr::prover_config::SumcheckStep],
    folding_steps: usize,
    st: &mut ChainState<E>,
    trackers: &mut Vec<crate::gkr::prover::dimension_reduction::lsb_backward::FoldBufferTracker<E>>,
    suffix_tables: &crate::gkr::sumcheck::eq_poly::SuffixTables<E>,
    spans: &[(usize, usize)],
    prev_blocks: &[Vec<E>],
    seed: &mut TR::Seed,
    worker: &Worker,
) where
    [(); E::DEGREE]: Sized,
{
    use crate::gkr::prover_config::SumcheckStep;
    use windowed_mode::lsb_chain::*;

    let n = folding_steps;
    let omega16_f: F = ::fft::domain_generator_for_size::<F>(16);
    let mut pending_weights: Option<[E; 8]> = None;
    for (idx, step) in remaining.iter().enumerate() {
        match step {
            SumcheckStep::UniskipContinuing { window: 3 } => {
                let g = st.pass_idx;
                let out_size = 1usize << (n - 3 * (g + 1));
                let suffix = suffix_tables.get(n - 3 * (g + 1));
                let folded: Vec<&[E]> = trackers
                    .iter()
                    .map(|t| unsafe { t.input_slice() })
                    .collect();
                let q16 = chain.uniskip_continuing_pass(&folded, suffix, out_size, worker);
                pending_weights = Some(uniskip_transcript_round::<F, E, TR>(
                    st,
                    q16,
                    spans,
                    prev_blocks,
                    omega16_f,
                    seed,
                    worker,
                ));
            }
            SumcheckStep::WindowContinuing { window: 3 } => {
                let g = st.pass_idx;
                let out_size = 1usize << (n - 3 * (g + 1));
                let suffix = suffix_tables.get(n - 3 * (g + 1));
                let folded: Vec<&[E]> = trackers
                    .iter()
                    .map(|t| unsafe { t.input_slice() })
                    .collect();
                let acc27 = chain.window_continuing_pass(&folded, suffix, out_size, worker);
                pending_weights = Some(window_pass_rounds::<F, E, TR>(
                    st,
                    acc27,
                    spans,
                    prev_blocks,
                    seed,
                ));
            }
            SumcheckStep::FoldContinuing { width } => {
                assert_eq!(*width, 3, "the chain folds are width-3");
                let weights = pending_weights
                    .take()
                    .expect("a fold must follow its pass (validated)");
                chain.fold_continuing(&weights, trackers, worker);
                step_trackers_for_next(
                    trackers,
                    !matches!(remaining.get(idx + 1), Some(SumcheckStep::Tail)),
                );
            }
            SumcheckStep::Tail => {
                let tail_rounds = n - st.vars_bound;
                for _ in 0..tail_rounds {
                    let var = st.vars_bound;
                    // the round binding variable `var` weighs pairs with the
                    // suffix table over `var+1..n` — always available, no
                    // contraction
                    let tail_t = suffix_tables.get(n - var - 1);
                    let (h0, hinf) = chain.tail_round_message(trackers, tail_t, worker);
                    let tau = scalar_coord(var, spans, prev_blocks);
                    let r = scalar_chain_round::<F, E, TR>(st, tau, h0, hinf, seed);
                    tail_fold_trackers(trackers, &r, worker);
                    let pairs = trackers[0].output_len();
                    for t in trackers.iter_mut() {
                        t.step_to(pairs / 2);
                    }
                }
            }
            other => unreachable!("validated schedule cannot contain {other:?} here"),
        }
    }
}

/// Shared postlude of every same-size case: the at-point self-check, the
/// cached-relation dependency evaluations, the transcript commitment of the
/// claims, the next batching challenge, and the claim/point emission.
#[allow(clippy::too_many_arguments)]
fn finish_same_size_layer<
    F: PrimeField + field::TwoAdicField,
    E: FieldExtension<F> + Field,
    TR: Transcript<F, E>,
>(
    layer_idx: usize,
    layer: &GKRLayerDescription<F>,
    outcome: SameSizeOutcome<E>,
    folding_steps: usize,
    claim_point_entries: &mut BTreeMap<usize, Vec<crate::gkr::prover::EvaluationPointEntry<E>>>,
    claims_storage: &mut BTreeMap<usize, BTreeMap<GKRAddress, E>>,
    gkr_storage: &mut GKRStorage<F, E>,
    batching_challenge: &mut E,
    external_challenges: &GKRExternalChallenges<F, E>,
    lookup_challenges_multiplicative_part: E,
    seed: &mut TR::Seed,
    worker: &Worker,
) -> SumcheckIntermediateProofValues<F, E>
where
    [(); E::DEGREE]: Sized,
{
    use crate::gkr::sumcheck::eq_poly::make_eq_table_from_weight_blocks;

    let SameSizeOutcome {
        rounds,
        point_entries,
        mut new_claims,
    } = outcome;
    assert_eq!(
        point_entries.iter().map(|e| e.bound_vars()).sum::<usize>(),
        folding_steps,
        "the claim point must cover every bound variable"
    );

    // full block-tensor eq table over the OWN point: needed by the cached
    // relations (production) and the at-point self-check. For an all-scalar
    // point the 2-block tensor equals the plain LSB-first table.
    let need_full_eq = !layer.cached_relations.is_empty() || cfg!(feature = "gkr_self_checks");
    let full_eq: Option<Vec<E>> = need_full_eq.then(|| {
        let omega16_f: F = ::fft::domain_generator_for_size::<F>(16);
        let own_blocks: Vec<Vec<E>> = point_entries
            .iter()
            .map(|e| e.eq_weight_block::<F>(omega16_f))
            .collect();
        let refs: Vec<&[E]> = own_blocks.iter().map(|b| &b[..]).collect();
        make_eq_table_from_weight_blocks::<E>(&refs, worker)
    });

    #[cfg(feature = "gkr_self_checks")]
    {
        println!("Self-checking explicit at-point evaluations");
        let eq = full_eq.as_ref().unwrap();
        for (k, v) in new_claims.iter() {
            if let Some(poly) = gkr_storage.try_get_base_poly(*k) {
                let eval = evaluate_with_precomputed_eq(poly, &eq[..]);
                assert_eq!(eval, *v, "claim diverged for poly {k:?}");
            } else if let Some(poly) = gkr_storage.try_get_ext_poly(*k) {
                let eval = evaluate_with_precomputed_eq_ext(poly, &eq[..]);
                assert_eq!(eval, *v, "claim diverged for poly {k:?}");
            } else {
                unreachable!()
            }
        }
    }

    // snapshot the at-point evaluations to send in the proof before the
    // cached-relation handling extends `new_claims` with dependencies
    let final_step_evaluations: BTreeMap<GKRAddress, Vec<E>> =
        new_claims.iter().map(|(k, v)| (*k, vec![*v])).collect();
    let mut transcript_inputs: Vec<E> = new_claims.values().copied().collect();

    // cached relations: extra dependency claims evaluated at the own point
    let mut extra_evaluations_from_caching_relations = BTreeMap::new();
    for (cached_addr, relation) in layer.cached_relations.iter() {
        assert!(
            new_claims.contains_key(cached_addr),
            "Missing claim for cached address {:?}",
            cached_addr
        );
        for dep in relation.dependencies() {
            if new_claims.contains_key(&dep) {
                continue;
            }
            match dep {
                GKRAddress::BaseLayerWitness(_)
                | GKRAddress::BaseLayerMemory(_)
                | GKRAddress::Setup(_)
                | GKRAddress::InnerLayer { .. } => {
                    let eq = full_eq.as_ref().expect("built above");
                    let evaluation = if let Some(values) = gkr_storage.try_get_base_poly(dep) {
                        evaluate_with_precomputed_eq::<F, E>(values, &eq[..])
                    } else if let Some(values) = gkr_storage.try_get_ext_poly(dep) {
                        evaluate_with_precomputed_eq_ext::<E>(values, &eq[..])
                    } else {
                        panic!("Unknown poly at address {:?}", dep);
                    };
                    new_claims.insert(dep, evaluation);
                    extra_evaluations_from_caching_relations.insert(dep, evaluation);
                }
                _ => panic!(
                    "Unexpected dependency address {:?} for cached relation {:?}",
                    dep, cached_addr
                ),
            }
        }
    }
    if !extra_evaluations_from_caching_relations.is_empty() {
        transcript_inputs.extend(extra_evaluations_from_caching_relations.values().copied());
    }
    #[cfg(feature = "gkr_self_checks")]
    assert!(crate::gkr::prover::debug_utils::verify_cache_relations(
        layer,
        &new_claims,
        external_challenges,
        lookup_challenges_multiplicative_part,
    ));
    let _ = (external_challenges, lookup_challenges_multiplicative_part);

    // after all claims for the next layer are ready, draw the next batching
    // challenge
    commit_field_els::<F, E, TR>(seed, &transcript_inputs);
    let next_batching_challenge = draw_random_field_els::<F, E, TR>(seed, 1)[0];

    claims_storage.insert(layer_idx, new_claims);
    claim_point_entries.insert(layer_idx, point_entries);
    gkr_storage.purge_up_to_layer(layer_idx);
    *batching_challenge = next_batching_challenge;

    SumcheckIntermediateProofValues {
        sumcheck_num_rounds: folding_steps,
        internal_round_coefficients: rounds,
        final_step_evaluations,
        extra_evaluations_from_caching_relations,
        _marker: core::marker::PhantomData,
    }
}

fn run_sumcheck_loop<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    TR: Transcript<F, E>,
    const N: usize,
    const USE_BATCHING: bool,
>(
    collector: &KernelCollector<F, E>,
    initial_claim: E,
    prev_challenges: &[E],
    eq_poly: &[Box<[E]>],
    gkr_storage: &mut GKRStorage<F, E>,
    challenge_constants: &BatchedGKRTermDescriptionConstants<F, E>,
    folding_steps: usize,
    worker: &Worker,
    seed: &mut TR::Seed,
) -> (Vec<E>, Vec<[E; 4]>, BTreeMap<GKRAddress, [E; N]>, E)
where
    [(); E::DEGREE]: Sized,
{
    let use_batching = USE_BATCHING;
    if use_batching {
        println!("Running sumcheck loop in batched naive (LSB) mode");
    } else {
        println!("Running sumcheck loop in individual kernel (gate expression) mode");
    }

    let mut claim = initial_claim;
    let mut folding_challenges = Vec::with_capacity(folding_steps);
    let mut last_evaluations: BTreeMap<GKRAddress, [E; N]> = BTreeMap::new();

    let mut eq_prefactor = E::ONE;

    let max_acc_size = 1 << (folding_steps - 1);
    let mut accumulator_buffer = vec![[E::ZERO; 2]; max_acc_size];
    let mut intermediate_coeffs = Vec::with_capacity(folding_steps);

    let batched_description = if use_batching {
        collector.make_batched_description(challenge_constants, collector.layer)
    } else {
        Default::default()
    };

    // Every round - including the last one - now emits a univariate monomial and draws a
    // folding challenge. The last round's kernel evaluation produces the monomial form
    // `[G(0), G2]` (see `EXPLICIT_FORM == false` handling in the evaluators) while still
    // folding all input polys down to their line and recording `last_evaluations`, which the
    // callers use to fix the last coordinate at the freshly drawn challenge.
    for step in 0..folding_steps {
        let acc_size = 1 << (folding_steps - step - 1);
        let accumulator = &mut accumulator_buffer[..acc_size];
        if step > 0 {
            accumulator.fill([E::ZERO; 2]);
        }

        if use_batching {
            use crate::gkr::prover::sumcheck_loop::batch_evaluation::evaluate_batched_gkr_description;
            evaluate_batched_gkr_description(
                &batched_description,
                gkr_storage,
                step,
                &folding_challenges,
                accumulator,
                folding_steps,
                &mut last_evaluations,
                worker,
            );
        } else {
            collector.evaluate_kernels_over_storage(
                gkr_storage,
                step,
                &folding_challenges,
                accumulator,
                folding_steps,
                &mut last_evaluations,
                worker,
            );
        }

        let eq = &eq_poly[folding_steps - step - 1];

        assert_eq!(eq.len(), acc_size);

        let [c0, c2] = evaluate_constant_and_quadratic_coeffs_with_precomputed_eq::<F, E>(
            &accumulator,
            eq,
            worker,
        );

        let mut normalized_claim = claim;
        normalized_claim.mul_assign(&eq_prefactor.inverse().expect("eq prefactor non-zero"));

        let coeffs = output_univariate_monomial_form_max_quadratic::<F, E>(
            prev_challenges[step],
            normalized_claim,
            c0,
            c2,
        );

        #[cfg(feature = "gkr_self_checks")]
        {
            let s0 = evaluate_small_univariate_poly::<F, E, _>(&coeffs, &E::ZERO);
            let s1 = evaluate_small_univariate_poly::<F, E, _>(&coeffs, &E::ONE);
            let mut sum = s0;
            sum.add_assign(&s1);
            sum.mul_assign(&eq_prefactor);
            assert_eq!(
                sum, claim,
                "s(0) + s(1) != claim / eq_prefactor at folding step {}",
                step
            );
        }

        commit_field_els::<F, E, TR>(seed, &coeffs);
        intermediate_coeffs.push(coeffs);
        let folding_challenge = draw_random_field_els::<F, E, TR>(seed, 1)[0];

        let new_claim = evaluate_small_univariate_poly::<F, E, _>(&coeffs, &folding_challenge);

        claim = new_claim;
        eq_prefactor = evaluate_eq_poly::<F, E>(&folding_challenge, &prev_challenges[step]);

        folding_challenges.push(folding_challenge);
    }

    // normalize the claim to avoid prefactors sneaking in for our self-check outside
    let mut normalized_claim = claim;
    normalized_claim.mul_assign(&eq_prefactor.inverse().expect("eq prefactor non-zero"));

    (
        folding_challenges,
        intermediate_coeffs,
        last_evaluations,
        normalized_claim,
    )
}

#[inline(always)]
pub(crate) fn interpolate_linear<E: Field>(f0: E, f1: E, r: &E) -> E {
    let mut result = f1;
    result.sub_assign(&f0);
    result.mul_assign(r);
    result.add_assign(&f0);
    result
}
