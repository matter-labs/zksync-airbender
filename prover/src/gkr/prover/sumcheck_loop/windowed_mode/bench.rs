//! Benchmark driver for the windowed sumcheck variants. Not part of the prover
//! flow: it is invoked from `tests::gkr::windowed_bench` on a real (add/sub
//! family) circuit instance with a populated `GKRStorage`, and measures:
//!
//! * initial window of 3 over ALL term kinds, full-size scratch (one `[.; 27]`
//!   entry per source poly);
//! * the same with bounded scratch + Belady eviction (the "DAG" strategy) for
//!   several scratch capacities;
//! * split strategy: window of 3 over base*base and base*ext terms (+ all linear
//!   terms and the constant), with ext*ext terms evaluated by the classic
//!   per-round batched evaluator;
//! * the classic per-round batched evaluator over everything (baseline);
//! * the transition round (round 3 + folding everything into extension field);
//! * ext-only rounds processed with windows of size 1, 2 and 3.
//!
//! Correctness: windowed accumulators are cross-checked against each other
//! (bounded == full-size, bbbe + ee == all) and against the classic evaluator's
//! `[c0, c2]` round coefficients through the bind chain. The classic round-0
//! `c0` comparison relies on the witness being satisfying (the classic path
//! computes `G(0)` through the output polys, the windowed path through the gate
//! terms; they agree only on a satisfied trace).

use std::mem::MaybeUninit;

use super::bounded_scratch::*;
use super::full_size_scratch::extension_only_round::in_1_out_1::ExtensionOnlyRoundWindowIn1Out1;
use super::full_size_scratch::extension_only_round::in_1_out_3::ExtensionOnlyRoundWindowIn1Out3;
use super::full_size_scratch::extension_only_round::in_2_out_2::ExtensionOnlyRoundWindowIn2Out2;
use super::full_size_scratch::extension_only_round::in_3_out_1::ExtensionOnlyRoundWindowIn3Out1;
use super::full_size_scratch::extension_only_round::in_3_out_3::ExtensionOnlyRoundWindowIn3Out3;
use super::full_size_scratch::extension_only_round::{
    evaluate_extension_only_rounds_with_full_sized_scratch_parallel,
    ExtensionOnlyRoundImplementation,
};
use super::full_size_scratch::initial_round::evaluate_initial_with_full_sized_scratch_parallel;
use super::full_size_scratch::transition_round::in_3_out_1::TransitionRoundWindowIn3Out1;
use super::full_size_scratch::transition_round::in_3_out_3::TransitionRoundWindowIn3Out3;
use super::full_size_scratch::transition_round::{
    evaluate_transition_with_full_sized_scratch_parallel, TransitionRoundImplementation,
};
use super::full_size_scratch::{
    produce_descriptions_from_batched_description, BatchEvaluationCompactDescription,
};
use super::*;
use crate::gkr::prover::sumcheck_loop::batch_evaluation::{
    evaluate_batched_gkr_description, BatchedGKRDescription,
};

fn pseudo_challenge<F: PrimeField, E: FieldExtension<F> + Field>(i: u32) -> E {
    // arbitrary deterministic nonzero values; base-subfield points are fine for
    // benchmarking and for the exact-arithmetic cross-checks
    let v = 0x9E3779B9u32.wrapping_mul(i.wrapping_add(1)) >> 1;
    let v = if v == 0 { 42 } else { v };
    E::from_base(F::from_u32_with_reduction(v))
}

pub(crate) fn find_eq_with_len<E: Field>(tables: &[Box<[E]>], len: usize) -> &[E] {
    tables
        .iter()
        .find(|el| el.len() == len)
        .map(|el| &el[..])
        .expect("eq table with requested length")
}

fn reset_folding_intermediates<F: PrimeField, E: FieldExtension<F> + Field>(
    storage: &mut GKRStorage<F, E>,
) {
    for layer in storage.layers.iter_mut() {
        layer
            .intermediate_storage_for_folder_base_field_inputs
            .clear();
        layer
            .intermediate_storage_for_folder_extension_field_inputs
            .clear();
    }
}

/// bb + be + all linear terms + constant in the first part, ee-only in the second
fn split_batched_description<F: PrimeField, E: FieldExtension<F> + Field>(
    description: &BatchedGKRDescription<F, E>,
) -> (BatchedGKRDescription<F, E>, BatchedGKRDescription<F, E>) {
    let mut bbbe = description.clone();
    bbbe.quadratic_part_ext_by_ext = vec![];
    // outputs are ignored by the windowed evaluators; keep the field intact

    let mut ee = BatchedGKRDescription::<F, E>::default();
    ee.quadratic_part_ext_by_ext = description.quadratic_part_ext_by_ext.clone();

    (bbbe, ee)
}

pub(crate) fn collect_base_sources<'a, F: PrimeField, E: FieldExtension<F> + Field>(
    storage: &'a GKRStorage<F, E>,
    addresses: &[GKRAddress],
) -> Vec<DisjointAccessQuasiSlice<F, false>> {
    addresses
        .iter()
        .map(|el| {
            let slice = storage
                .try_get_base_poly(*el)
                .expect(&format!("must get a base field poly for address {:?}", el));
            DisjointAccessQuasiSlice::<_, false>::from_init_slice(slice)
        })
        .collect()
}

pub(crate) fn collect_ext_sources<'a, F: PrimeField, E: FieldExtension<F> + Field>(
    storage: &'a GKRStorage<F, E>,
    addresses: &[GKRAddress],
) -> Vec<DisjointAccessQuasiSlice<E, false>> {
    addresses
        .iter()
        .map(|el| {
            let slice = storage
                .try_get_ext_poly(*el)
                .expect(&format!("must get an ext field poly for address {:?}", el));
            DisjointAccessQuasiSlice::<_, false>::from_init_slice(slice)
        })
        .collect()
}

fn assert_acc_eq<E: Field>(a: &[E; 27], b: &[E; 27], what: &str) {
    for i in 0..27 {
        assert_eq!(
            a[i], b[i],
            "accumulator diverged at cell {} for {}",
            i, what
        );
    }
}

struct ClassicRoundsResult<E: Field> {
    // [c0, c2] per round
    coeffs: Vec<[E; 2]>,
    total: std::time::Duration,
}

/// Classic per-round batched evaluation of `rounds` rounds with fixed window
/// challenges, timing the accumulation + coefficient extraction (the per-round
/// work the windowed pass replaces).
fn run_classic_rounds<F: PrimeField, E: FieldExtension<F> + Field>(
    description: &BatchedGKRDescription<F, E>,
    storage: &mut GKRStorage<F, E>,
    window_challenges: &[E],
    rounds: usize,
    folding_steps: usize,
    eq_tables: &[Box<[E]>],
    accumulator_buffer: &mut Vec<[E; 2]>,
    worker: &Worker,
) -> ClassicRoundsResult<E> {
    reset_folding_intermediates(storage);
    let mut last_evaluations = std::collections::BTreeMap::<GKRAddress, [E; 2]>::new();
    let mut coeffs = vec![];
    let start = std::time::Instant::now();
    for step in 0..rounds {
        let acc_size = 1 << (folding_steps - step - 1);
        let accumulator = &mut accumulator_buffer[..acc_size];
        accumulator.fill([E::ZERO; 2]);

        evaluate_batched_gkr_description::<F, E, 2>(
            description,
            storage,
            step,
            &window_challenges[..step],
            accumulator,
            folding_steps,
            &mut last_evaluations,
            worker,
        );

        let one_table = [E::ONE];
        let eq = if acc_size == 1 {
            &one_table[..]
        } else {
            find_eq_with_len(eq_tables, acc_size)
        };
        let c = evaluate_constant_and_quadratic_coeffs_with_precomputed_eq::<F, E>(
            accumulator,
            eq,
            worker,
        );
        coeffs.push(c);
    }
    let total = start.elapsed();

    ClassicRoundsResult { coeffs, total }
}

fn time_ext_only_chain<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    I: ExtensionOnlyRoundImplementation<F, E>,
>(
    base_folding_buffers: &mut [Box<[MaybeUninit<E>]>],
    ext_folding_buffers: &mut [Box<[MaybeUninit<E>]>],
    description: &BatchEvaluationCompactDescription<F, E>,
    eq_tables: &[Box<[E]>],
    start_input_size_log2: usize,
    min_work_size: usize,
    worker: &Worker,
) -> (std::time::Duration, usize) {
    let mut chain_challenges: Vec<E> = (0..8).map(|i| pseudo_challenge::<F, E>(100 + i)).collect();
    let mut cur_log2 = start_input_size_log2;
    let mut rounds_processed = 0usize;

    let start = std::time::Instant::now();
    loop {
        let work_size = I::work_size_for_unfolded_input_size(cur_log2);
        if work_size < min_work_size {
            break;
        }
        let prefix = I::make_prefix_from_all_folding_challenges(&chain_challenges, worker);
        let eq = find_eq_with_len(eq_tables, work_size);

        let base_buffers: Vec<_> = base_folding_buffers
            .iter_mut()
            .map(|el| DisjointAccessQuasiSlice::<_, false>::from_uninit_slice_mut(el))
            .collect();
        let ext_buffers: Vec<_> = ext_folding_buffers
            .iter_mut()
            .map(|el| DisjointAccessQuasiSlice::<_, false>::from_uninit_slice_mut(el))
            .collect();

        let _acc = evaluate_extension_only_rounds_with_full_sized_scratch_parallel::<F, E, I>(
            base_buffers,
            ext_buffers,
            description,
            &prefix,
            eq,
            cur_log2,
            worker,
        );

        cur_log2 =
            I::folded_buffer_size_for_unfolded_input_size(cur_log2).trailing_zeros() as usize;
        rounds_processed += I::OUTPUT_WINDOW_SIZE;
        for i in 0..I::OUTPUT_WINDOW_SIZE {
            chain_challenges.push(pseudo_challenge::<F, E>(
                300 + (rounds_processed + i) as u32,
            ));
        }
    }
    (start.elapsed(), rounds_processed)
}

/// Micro-benchmark of the indirect cost of the parallel dispatch machinery:
/// entering `in_place_scope` with a single inline (sub-threshold) chunk, and a
/// full fan-out of empty spawned tasks. This is the per-pass floor the late
/// (tiny) sumcheck rounds pay regardless of arithmetic.
pub fn bench_scope_spawn_overhead(worker: &Worker) {
    use crate::gkr::PAR_THRESHOLD;

    // warmup
    for _ in 0..1000 {
        worker.scope_with_threshold(16, PAR_THRESHOLD, |_scope, _geometry| {});
    }

    let iters: u32 = 100_000;
    let now = std::time::Instant::now();
    for _ in 0..iters {
        worker.scope_with_threshold(16, PAR_THRESHOLD, |_scope, _geometry| {});
    }
    let inline_cost = now.elapsed() / iters;

    let iters_spawn: u32 = 20_000;
    let mut num_chunks = 0usize;
    let now = std::time::Instant::now();
    for _ in 0..iters_spawn {
        worker.scope_with_threshold(1 << 20, PAR_THRESHOLD, |scope, geometry| {
            num_chunks = geometry.len();
            for i in 0..geometry.len() {
                Worker::smart_spawn(scope, i == geometry.len() - 1, move |_| {});
            }
        });
    }
    let spawn_cost = now.elapsed() / iters_spawn;

    println!(
        "scope overhead: sub-threshold (1 inline chunk, no tasks): {:?}/pass; {} empty spawned tasks: {:?}/pass",
        inline_cost, num_chunks, spawn_cost,
    );
}

/// Univariate `[c0, c2]` triple-extraction for a 27-cell window accumulator
/// covering rounds `(s, s+1, s+2)`: round-s coefficients directly, then bind at
/// the round challenges to get rounds s+1 and s+2.
fn extract_window3_univariates<F: PrimeField, E: FieldExtension<F> + Field>(
    acc: &[E; 27],
    s: usize,
    prev_challenges: &[E],
    folding_challenges: &[E],
    worker: &Worker,
) -> [[E; 2]; 3] {
    let eq_prefix_4: [E; 4] = make_eq_poly_in_full::<E>(&prev_challenges[s + 1..s + 3], worker)
        .pop()
        .unwrap()
        .to_vec()
        .try_into()
        .unwrap();
    let eq_prefix_2: [E; 2] = make_eq_poly_in_full::<E>(&prev_challenges[s + 2..s + 3], worker)
        .pop()
        .unwrap()
        .to_vec()
        .try_into()
        .unwrap();

    let r0 = evaluate_claim_from_intermediate_matrix_27(&eq_prefix_4, acc);
    let acc_9 = bind_accumulator_27(acc, &folding_challenges[s]);
    let r1 = evaluate_claim_from_intermediate_matrix_9(&eq_prefix_2, &acc_9);
    let r2 = bind_accumulator_9(&acc_9, &folding_challenges[s + 1]);

    [[r0[0], r0[2]], [r1[0], r1[2]], [r2[0], r2[2]]]
}

/// Optional SoA + bracket-preserving replacement for the chain's initial pass
/// (BabyBear/Ext4 on aarch64 only; ignored otherwise).
pub struct SoaInitialProgram<'a, F: PrimeField, E: Field> {
    pub base_interp: &'a [bool],
    pub ext_interp: &'a [bool],
    pub forms: &'a [Vec<(FormOp<F>, u16)>],
    pub products: &'a [(u16, u16, E)],
    pub rest_steps: &'a [BenchStep<E>],
    /// expanded quadratic terms over the combined folded slot space
    /// (base-origin polys first, then ext), for the SoA transition and
    /// window-3 ext passes
    pub folded_quad: &'a [(u16, u16, E)],
    pub folded_lin: &'a [(u16, E)],
    pub additive_constant: E,
}

/// The complete windowed evaluation chain over all `folding_steps` rounds:
/// window-3 all-terms initial (rounds 0-2) -> transition in3out1 (round 3, fold
/// everything to ext) -> in1out3 bridge (rounds 4-6) -> in3out3 chain -> in3out1
/// bridge -> in1out1 tail. Returns per-round `[c0, c2]` coefficients (for
/// validation against the classic loop) and the total time; prints per-pass
/// timings.
pub fn run_windowed_full_chain<F: PrimeField, E: FieldExtension<F> + Field>(
    compact: &BatchEvaluationCompactDescription<F, E>,
    base_sources: &[DisjointAccessQuasiSlice<F, false>],
    ext_sources: &[DisjointAccessQuasiSlice<E, false>],
    base_folding_buffers: &mut Vec<Box<[MaybeUninit<E>]>>,
    ext_folding_buffers: &mut Vec<Box<[MaybeUninit<E>]>>,
    prev_challenges: &[E],
    folding_challenges: &[E],
    eq_tables: &[Box<[E]>],
    folding_steps: usize,
    verbose: bool,
    soa_initial: Option<&SoaInitialProgram<'_, F, E>>,
    worker: &Worker,
) -> (Vec<[E; 2]>, std::time::Duration) {
    assert!(folding_steps >= 10);
    assert_eq!(prev_challenges.len(), folding_steps);
    assert_eq!(folding_challenges.len(), folding_steps);
    let one_table = [E::ONE];
    let find_eq = |len: usize| -> &[E] {
        if len == 1 {
            &one_table[..]
        } else {
            find_eq_with_len(eq_tables, len)
        }
    };

    let w = folding_challenges;
    let mut per_round: Vec<[E; 2]> = Vec::with_capacity(folding_steps);
    let total_start = std::time::Instant::now();

    // rounds 0-2: initial window over everything
    let now = std::time::Instant::now();
    let _ = &soa_initial;
    let mut acc27_soa: Option<[E; 27]> = None;
    #[cfg(target_arch = "aarch64")]
    if const { neon::is_bb_pair::<F, E>() } {
        if let Some(prog) = soa_initial {
            acc27_soa = Some(evaluate_initial_soa_parallel(
                base_sources,
                ext_sources,
                prog.base_interp,
                prog.ext_interp,
                prog.forms,
                prog.products,
                prog.rest_steps,
                &prog.additive_constant,
                find_eq(1 << (folding_steps - 3)),
                folding_steps,
                worker,
            ));
        }
    }
    #[cfg(target_arch = "aarch64")]
    let soa_active = const { neon::is_bb_pair::<F, E>() } && soa_initial.is_some();
    #[cfg(not(target_arch = "aarch64"))]
    let soa_active = false;
    let _ = soa_active;
    let used_soa = acc27_soa.is_some();
    let acc27 = match acc27_soa {
        Some(acc) => acc,
        None => evaluate_initial_with_full_sized_scratch_parallel(
            base_sources.to_vec(),
            ext_sources.to_vec(),
            compact,
            find_eq(1 << (folding_steps - 3)),
            folding_steps,
            worker,
        ),
    };
    per_round.extend(extract_window3_univariates(
        &acc27,
        0,
        prev_challenges,
        w,
        worker,
    ));
    if verbose {
        println!(
            "  pass initial window-3 (rounds 0-2, {}) @2^{folding_steps}: {:?}",
            if used_soa { "SoA+brackets" } else { "expanded" },
            now.elapsed()
        );
    }

    // round 3: transition, folds everything into ext buffers
    let now = std::time::Instant::now();
    {
        type TI = TransitionRoundWindowIn3Out1;
        let prefix =
            <TI as TransitionRoundImplementation<F, E>>::make_prefix_from_all_folding_challenges(
                &w[..3],
                worker,
            );
        let work = <TI as TransitionRoundImplementation<F, E>>::work_size_for_unfolded_input_size(
            folding_steps,
        );
        let mut acc_opt: Option<[E; 2]> = None;
        #[cfg(target_arch = "aarch64")]
        if const { neon::is_bb_pair::<F, E>() } {
            if let Some(prog) = soa_initial {
                let base_ptrs: Vec<usize> = base_folding_buffers
                    .iter_mut()
                    .map(|el| el.as_mut_ptr() as usize)
                    .collect();
                let ext_ptrs: Vec<usize> = ext_folding_buffers
                    .iter_mut()
                    .map(|el| el.as_mut_ptr() as usize)
                    .collect();
                acc_opt = Some(evaluate_transition_soa_parallel(
                    base_sources,
                    ext_sources,
                    &base_ptrs,
                    &ext_ptrs,
                    prog.forms,
                    prog.products,
                    prog.folded_quad,
                    prog.folded_lin,
                    &prog.additive_constant,
                    &prefix,
                    find_eq(work),
                    folding_steps,
                    worker,
                ));
            }
        }
        let acc = match acc_opt {
            Some(acc) => acc,
            None => {
                let base_buffers: Vec<_> = base_folding_buffers
                    .iter_mut()
                    .map(|el| DisjointAccessQuasiSlice::<_, true>::from_uninit_slice_mut(el))
                    .collect();
                let ext_buffers: Vec<_> = ext_folding_buffers
                    .iter_mut()
                    .map(|el| DisjointAccessQuasiSlice::<_, true>::from_uninit_slice_mut(el))
                    .collect();
                evaluate_transition_with_full_sized_scratch_parallel::<F, E, TI>(
                    base_sources.to_vec(),
                    ext_sources.to_vec(),
                    base_buffers,
                    ext_buffers,
                    compact,
                    &prefix,
                    find_eq(work),
                    folding_steps,
                    worker,
                )
            }
        };
        per_round.push(acc);
    }
    if verbose {
        println!(
            "  pass transition in3out1 (round 3, {}) @2^{folding_steps}: {:?}",
            if soa_active { "SoA" } else { "AoS" },
            now.elapsed()
        );
    }

    let mut cur_log2 = folding_steps - 3;
    let mut next_round = 4;

    // generic ext-only pass runner over the (now folded) buffers
    macro_rules! ext_pass {
        ($impl:ty) => {{
            let now = std::time::Instant::now();
            let work = <$impl as ExtensionOnlyRoundImplementation<F, E>>::work_size_for_unfolded_input_size(cur_log2);
            let prefix = <$impl as ExtensionOnlyRoundImplementation<F, E>>::make_prefix_from_all_folding_challenges(
                &w[..next_round],
                worker,
            );
            let base_buffers: Vec<_> = base_folding_buffers
                .iter_mut()
                .map(|el| DisjointAccessQuasiSlice::<_, false>::from_uninit_slice_mut(el))
                .collect();
            let ext_buffers: Vec<_> = ext_folding_buffers
                .iter_mut()
                .map(|el| DisjointAccessQuasiSlice::<_, false>::from_uninit_slice_mut(el))
                .collect();
            let acc = evaluate_extension_only_rounds_with_full_sized_scratch_parallel::<F, E, $impl>(
                base_buffers,
                ext_buffers,
                compact,
                &prefix,
                find_eq(work),
                cur_log2,
                worker,
            );
            let took = now.elapsed();
            (acc, took)
        }};
    }

    // SoA window-3 pass over the folded ext buffers; falls back to the trait
    // executor for non-BB4 fields, tiny passes, or when no program is given
    macro_rules! soa_window3_pass {
        ($fold2:expr, $fold8:expr, $work:expr) => {{
            let mut result: Option<([E; 27], std::time::Duration)> = None;
            #[cfg(target_arch = "aarch64")]
            if const { neon::is_bb_pair::<F, E>() } {
                if let Some(prog) = soa_initial {
                    if $work >= 4 && $work % 4 == 0 {
                        let now = std::time::Instant::now();
                        let ptrs: Vec<usize> = base_folding_buffers
                            .iter_mut()
                            .chain(ext_folding_buffers.iter_mut())
                            .map(|el| el.as_mut_ptr() as usize)
                            .collect();
                        let fold2: Option<&E> = $fold2;
                        let fold8: Option<&[E; 8]> = $fold8;
                        let acc = evaluate_ext_window3_soa_parallel::<F, E>(
                            &ptrs,
                            fold2,
                            fold8,
                            prog.forms,
                            prog.products,
                            prog.folded_quad,
                            prog.folded_lin,
                            &prog.additive_constant,
                            find_eq($work),
                            cur_log2,
                            worker,
                        );
                        result = Some((acc, now.elapsed()));
                    }
                }
            }
            result
        }};
    }

    // rounds 4-6: bridge with one pending challenge, window of 3
    {
        type I13 = ExtensionOnlyRoundWindowIn1Out3;
        let work =
            <I13 as ExtensionOnlyRoundImplementation<F, E>>::work_size_for_unfolded_input_size(
                cur_log2,
            );
        let soa_result = soa_window3_pass!(Some(&w[next_round - 1]), None, work);
        let (acc, took) = match soa_result {
            Some(r) => r,
            None => ext_pass!(ExtensionOnlyRoundWindowIn1Out3),
        };
        per_round.extend(extract_window3_univariates(
            &acc,
            next_round,
            prev_challenges,
            w,
            worker,
        ));
        if verbose {
            println!("  pass ext in1out3 (rounds 4-6) @2^{cur_log2}: {:?}", took);
        }
        cur_log2 -= 1;
        next_round += 3;
    }

    // in3out3 chain
    while folding_steps - next_round >= 3 {
        type I33 = ExtensionOnlyRoundWindowIn3Out3;
        let work =
            <I33 as ExtensionOnlyRoundImplementation<F, E>>::work_size_for_unfolded_input_size(
                cur_log2,
            );
        let mut fold8_prefix_opt: Option<[E; 8]> = None;
        #[cfg(target_arch = "aarch64")]
        if const { neon::is_bb_pair::<F, E>() } {
            if soa_initial.is_some() && work >= 4 && work % 4 == 0 {
                fold8_prefix_opt = Some(
                    <I33 as ExtensionOnlyRoundImplementation<F, E>>::make_prefix_from_all_folding_challenges(
                        &w[..next_round],
                        worker,
                    ),
                );
            }
        }
        let soa_result = match fold8_prefix_opt.as_ref() {
            Some(p) => soa_window3_pass!(None, Some(p), work),
            None => None,
        };
        let (acc, took) = match soa_result {
            Some(r) => r,
            None => ext_pass!(ExtensionOnlyRoundWindowIn3Out3),
        };
        per_round.extend(extract_window3_univariates(
            &acc,
            next_round,
            prev_challenges,
            w,
            worker,
        ));
        if verbose {
            println!(
                "  pass ext in3out3 (rounds {}-{}) @2^{cur_log2}: {:?}",
                next_round,
                next_round + 2,
                took
            );
        }
        cur_log2 -= 3;
        next_round += 3;
    }

    // three challenges pending; bridge out with a window of 1
    if next_round < folding_steps {
        let (acc, took) = ext_pass!(ExtensionOnlyRoundWindowIn3Out1);
        per_round.push(acc);
        if verbose {
            println!(
                "  pass ext in3out1 (round {}) @2^{cur_log2}: {:?}",
                next_round, took
            );
        }
        cur_log2 -= 3;
        next_round += 1;
    }

    // in1out1 tail for whatever remains
    while next_round < folding_steps {
        let (acc, took) = ext_pass!(ExtensionOnlyRoundWindowIn1Out1);
        per_round.push(acc);
        if verbose {
            println!(
                "  pass ext in1out1 (round {}) @2^{cur_log2}: {:?}",
                next_round, took
            );
        }
        cur_log2 -= 1;
        next_round += 1;
    }

    assert_eq!(per_round.len(), folding_steps);
    (per_round, total_start.elapsed())
}

/// Variant 2 of the full chain: the transition uses `in 3, out 3` (fold to ext
/// while evaluating rounds 3-5 in a 27-cell window), which self-aligns the
/// pending-challenge count and removes the `in1out3` bridge entirely. For
/// `folding_steps` divisible by 3 the whole tail is pure `in3out3`.
pub fn run_windowed_full_chain_v2<F: PrimeField, E: FieldExtension<F> + Field>(
    compact: &BatchEvaluationCompactDescription<F, E>,
    base_sources: &[DisjointAccessQuasiSlice<F, false>],
    ext_sources: &[DisjointAccessQuasiSlice<E, false>],
    base_folding_buffers: &mut Vec<Box<[MaybeUninit<E>]>>,
    ext_folding_buffers: &mut Vec<Box<[MaybeUninit<E>]>>,
    prev_challenges: &[E],
    folding_challenges: &[E],
    eq_tables: &[Box<[E]>],
    folding_steps: usize,
    verbose: bool,
    worker: &Worker,
) -> (Vec<[E; 2]>, std::time::Duration) {
    assert!(folding_steps >= 10);
    let one_table = [E::ONE];
    let find_eq = |len: usize| -> &[E] {
        if len == 1 {
            &one_table[..]
        } else {
            find_eq_with_len(eq_tables, len)
        }
    };

    let w = folding_challenges;
    let mut per_round: Vec<[E; 2]> = Vec::with_capacity(folding_steps);
    let total_start = std::time::Instant::now();

    // rounds 0-2: initial window over everything
    let now = std::time::Instant::now();
    let acc27 = evaluate_initial_with_full_sized_scratch_parallel(
        base_sources.to_vec(),
        ext_sources.to_vec(),
        compact,
        find_eq(1 << (folding_steps - 3)),
        folding_steps,
        worker,
    );
    per_round.extend(extract_window3_univariates(
        &acc27,
        0,
        prev_challenges,
        w,
        worker,
    ));
    if verbose {
        println!(
            "  pass initial window-3 (rounds 0-2) @2^{folding_steps}: {:?}",
            now.elapsed()
        );
    }

    // rounds 3-5: in3out3 transition, folds everything into ext buffers
    let now = std::time::Instant::now();
    {
        type TI = TransitionRoundWindowIn3Out3;
        let prefix =
            <TI as TransitionRoundImplementation<F, E>>::make_prefix_from_all_folding_challenges(
                &w[..3],
                worker,
            );
        let work = <TI as TransitionRoundImplementation<F, E>>::work_size_for_unfolded_input_size(
            folding_steps,
        );
        let base_buffers: Vec<_> = base_folding_buffers
            .iter_mut()
            .map(|el| DisjointAccessQuasiSlice::<_, true>::from_uninit_slice_mut(el))
            .collect();
        let ext_buffers: Vec<_> = ext_folding_buffers
            .iter_mut()
            .map(|el| DisjointAccessQuasiSlice::<_, true>::from_uninit_slice_mut(el))
            .collect();
        let acc = evaluate_transition_with_full_sized_scratch_parallel::<F, E, TI>(
            base_sources.to_vec(),
            ext_sources.to_vec(),
            base_buffers,
            ext_buffers,
            compact,
            &prefix,
            find_eq(work),
            folding_steps,
            worker,
        );
        per_round.extend(extract_window3_univariates(
            &acc,
            3,
            prev_challenges,
            w,
            worker,
        ));
    }
    if verbose {
        println!(
            "  pass transition in3out3 (rounds 3-5) @2^{folding_steps}: {:?}",
            now.elapsed()
        );
    }

    let mut cur_log2 = folding_steps - 3;
    let mut next_round = 6;

    macro_rules! ext_pass_v2 {
        ($impl:ty) => {{
            let now = std::time::Instant::now();
            let work = <$impl as ExtensionOnlyRoundImplementation<F, E>>::work_size_for_unfolded_input_size(cur_log2);
            let prefix = <$impl as ExtensionOnlyRoundImplementation<F, E>>::make_prefix_from_all_folding_challenges(
                &w[..next_round],
                worker,
            );
            let base_buffers: Vec<_> = base_folding_buffers
                .iter_mut()
                .map(|el| DisjointAccessQuasiSlice::<_, false>::from_uninit_slice_mut(el))
                .collect();
            let ext_buffers: Vec<_> = ext_folding_buffers
                .iter_mut()
                .map(|el| DisjointAccessQuasiSlice::<_, false>::from_uninit_slice_mut(el))
                .collect();
            let acc = evaluate_extension_only_rounds_with_full_sized_scratch_parallel::<F, E, $impl>(
                base_buffers,
                ext_buffers,
                compact,
                &prefix,
                find_eq(work),
                cur_log2,
                worker,
            );
            let took = now.elapsed();
            (acc, took)
        }};
    }

    while folding_steps - next_round >= 3 {
        let (acc, took) = ext_pass_v2!(ExtensionOnlyRoundWindowIn3Out3);
        per_round.extend(extract_window3_univariates(
            &acc,
            next_round,
            prev_challenges,
            w,
            worker,
        ));
        if verbose {
            println!(
                "  pass ext in3out3 (rounds {}-{}) @2^{cur_log2}: {:?}",
                next_round,
                next_round + 2,
                took
            );
        }
        cur_log2 -= 3;
        next_round += 3;
    }

    if next_round < folding_steps {
        let (acc, took) = ext_pass_v2!(ExtensionOnlyRoundWindowIn3Out1);
        per_round.push(acc);
        if verbose {
            println!(
                "  pass ext in3out1 (round {}) @2^{cur_log2}: {:?}",
                next_round, took
            );
        }
        cur_log2 -= 3;
        next_round += 1;
    }

    while next_round < folding_steps {
        let (acc, took) = ext_pass_v2!(ExtensionOnlyRoundWindowIn1Out1);
        per_round.push(acc);
        if verbose {
            println!(
                "  pass ext in1out1 (round {}) @2^{cur_log2}: {:?}",
                next_round, took
            );
        }
        cur_log2 -= 1;
        next_round += 1;
    }

    assert_eq!(per_round.len(), folding_steps);
    (per_round, total_start.elapsed())
}

/// Step mirror used for the control-flow overhead measurement: same shape and
/// counts as the compact description's step list, but the "kernels" are
/// black-boxed so only iteration + match dispatch + operand-index reads remain.
#[derive(Clone, Copy)]
pub enum StubStep {
    Bb(u16, u16, u32),
    Be(u16, u16, u32),
    Ee(u16, u16, u32),
    LinB(u16, u32),
    LinE(u16, u32),
}

/// One inner-linear-form member of a preserved bracket.
#[derive(Clone, Copy)]
pub enum FormOp<F: PrimeField> {
    Add,
    Sub,
    Mul(F),
}

/// Expanded (monomial) step over the full scratch layout, used by the
/// bracket-preserving evaluator for everything that is not a preserved bracket.
#[derive(Clone, Copy)]
pub enum BenchStep<E: Field> {
    QuadBB { a: u16, b: u16, c: E },
    QuadBE { base: u16, ext: u16, c: E },
    QuadEE { a: u16, b: u16, c: E },
    LinB { i: u16, c: E },
    LinE { i: u16, c: E },
}

/// Reads/extrapolation plus (optionally) a stubbed step loop — measures the
/// non-arithmetic part of the initial-window row.
fn bench_initial_phase_split<F: PrimeField, E: FieldExtension<F> + Field>(
    base_field_inputs: &[DisjointAccessQuasiSlice<F, false>],
    ext_field_inputs: &[DisjointAccessQuasiSlice<E, false>],
    base_interp: &[bool],
    ext_interp: &[bool],
    stub_steps: Option<&[StubStep]>,
    input_size_log2: usize,
    worker: &Worker,
) -> u64 {
    use crate::gkr::PAR_THRESHOLD;
    let work_size = (1 << input_size_log2) / 8;
    let geometry = worker.get_geometry_with_threshold(work_size, PAR_THRESHOLD);
    let mut tokens = vec![0u64; geometry.num_chunks];

    worker.scope_with_threshold(work_size, PAR_THRESHOLD, |scope, geometry| {
        let mut it = tokens.iter_mut();
        for thread_idx in 0..geometry.num_chunks {
            let chunk_start = geometry.get_chunk_start_pos(thread_idx);
            let chunk_size = geometry.get_chunk_size(thread_idx);
            let base_field_inputs = base_field_inputs.to_vec();
            let ext_field_inputs = ext_field_inputs.to_vec();
            let dst = it.next().unwrap();

            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                let input_size = 1 << input_size_log2;
                let mut base_scratch = vec![[F::ZERO; 27]; base_field_inputs.len()];
                let mut ext_scratch = vec![[E::ZERO; 27]; ext_field_inputs.len()];
                let mut token = 0u64;
                for row in chunk_start..(chunk_start + chunk_size) {
                    for ((dst, src), interp) in base_scratch
                        .iter_mut()
                        .zip(base_field_inputs.iter())
                        .zip(base_interp.iter())
                    {
                        if *interp {
                            read_and_interpolate_field(dst, src, input_size, row);
                        } else {
                            read_without_interpolation(dst, src, input_size, row);
                        }
                    }
                    for ((dst, src), interp) in ext_scratch
                        .iter_mut()
                        .zip(ext_field_inputs.iter())
                        .zip(ext_interp.iter())
                    {
                        if *interp {
                            read_and_interpolate_field(dst, src, input_size, row);
                        } else {
                            read_without_interpolation(dst, src, input_size, row);
                        }
                    }
                    std::hint::black_box(&base_scratch);
                    std::hint::black_box(&ext_scratch);

                    if let Some(steps) = stub_steps {
                        for step in steps.iter() {
                            match *step {
                                StubStep::Bb(a, b, c) => {
                                    token = token
                                        .wrapping_add(std::hint::black_box(
                                            a as u64 + ((b as u64) << 8) + ((c as u64) << 16),
                                        ));
                                }
                                StubStep::Be(a, b, c) => {
                                    token = token
                                        .wrapping_add(std::hint::black_box(
                                            1 + a as u64 + ((b as u64) << 8) + ((c as u64) << 16),
                                        ));
                                }
                                StubStep::Ee(a, b, c) => {
                                    token = token
                                        .wrapping_add(std::hint::black_box(
                                            2 + a as u64 + ((b as u64) << 8) + ((c as u64) << 16),
                                        ));
                                }
                                StubStep::LinB(a, c) => {
                                    token = token.wrapping_add(std::hint::black_box(
                                        3 + a as u64 + ((c as u64) << 16),
                                    ));
                                }
                                StubStep::LinE(a, c) => {
                                    token = token.wrapping_add(std::hint::black_box(
                                        4 + a as u64 + ((c as u64) << 16),
                                    ));
                                }
                            }
                        }
                    }
                }
                *dst = token;
            })
        }
    });

    tokens.into_iter().fold(0u64, |a, b| a.wrapping_add(b))
}

/// Bracket-preserving evaluation of the initial window: distinct multi-member
/// inner linear forms are materialized once per row (CSE across gates), each
/// preserved product costs one monomial-shaped accumulation, and everything
/// else runs as expanded monomials. Matches the fully-expanded evaluator
/// exactly.
fn evaluate_initial_bracket_parallel<F: PrimeField, E: FieldExtension<F> + Field>(
    base_field_inputs: &[DisjointAccessQuasiSlice<F, false>],
    ext_field_inputs: &[DisjointAccessQuasiSlice<E, false>],
    base_interp: &[bool],
    ext_interp: &[bool],
    forms: &[Vec<(FormOp<F>, u16)>],
    products: &[(u16, u16, E)],
    rest_steps: &[BenchStep<E>],
    additive_constant: &E,
    precomputed_eq_suffix: &[E],
    input_size_log2: usize,
    worker: &Worker,
) -> [E; 27] {
    use crate::gkr::PAR_THRESHOLD;
    let work_size = (1 << input_size_log2) / 8;
    let geometry = worker.get_geometry_with_threshold(work_size, PAR_THRESHOLD);
    let mut acc_chunks = vec![[E::ZERO; 27]; geometry.num_chunks];

    worker.scope_with_threshold(work_size, PAR_THRESHOLD, |scope, geometry| {
        let mut it = acc_chunks.iter_mut();
        for thread_idx in 0..geometry.num_chunks {
            let chunk_start = geometry.get_chunk_start_pos(thread_idx);
            let chunk_size = geometry.get_chunk_size(thread_idx);
            let base_field_inputs = base_field_inputs.to_vec();
            let ext_field_inputs = ext_field_inputs.to_vec();
            let acc_dst = it.next().unwrap();

            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                let input_size = 1 << input_size_log2;
                let mut base_scratch = vec![[F::ZERO; 27]; base_field_inputs.len()];
                let mut ext_scratch = vec![[E::ZERO; 27]; ext_field_inputs.len()];
                let mut form_scratch = vec![[F::ZERO; 27]; forms.len()];
                let mut eval_scratch = [E::ZERO; 27];
                let mut accumulator = [E::ZERO; 27];

                for row in chunk_start..(chunk_start + chunk_size) {
                    let eq_prefactor = &precomputed_eq_suffix[row];
                    for ((dst, src), interp) in base_scratch
                        .iter_mut()
                        .zip(base_field_inputs.iter())
                        .zip(base_interp.iter())
                    {
                        if *interp {
                            read_and_interpolate_field(dst, src, input_size, row);
                        } else {
                            read_without_interpolation(dst, src, input_size, row);
                        }
                    }
                    for ((dst, src), interp) in ext_scratch
                        .iter_mut()
                        .zip(ext_field_inputs.iter())
                        .zip(ext_interp.iter())
                    {
                        if *interp {
                            read_and_interpolate_field(dst, src, input_size, row);
                        } else {
                            read_without_interpolation(dst, src, input_size, row);
                        }
                    }

                    // materialize the distinct inner linear forms
                    for (dst, members) in form_scratch.iter_mut().zip(forms.iter()) {
                        dst.fill(F::ZERO);
                        for (op, idx) in members.iter() {
                            let src = &base_scratch[*idx as usize];
                            #[cfg(target_arch = "aarch64")]
                            if const { neon::is_bb_pair::<F, E>() } {
                                unsafe {
                                    match op {
                                        FormOp::Add => neon::form_add_27(
                                            dst.as_mut_ptr() as *mut _,
                                            src.as_ptr() as *const _,
                                        ),
                                        FormOp::Sub => neon::form_sub_27(
                                            dst.as_mut_ptr() as *mut _,
                                            src.as_ptr() as *const _,
                                        ),
                                        FormOp::Mul(c) => neon::form_muladd_27(
                                            dst.as_mut_ptr() as *mut _,
                                            src.as_ptr() as *const _,
                                            *(c as *const F as *const _),
                                        ),
                                    }
                                }
                                continue;
                            }
                            match op {
                                FormOp::Add => {
                                    for i in 0..27 {
                                        dst[i].add_assign(&src[i]);
                                    }
                                }
                                FormOp::Sub => {
                                    for i in 0..27 {
                                        dst[i].sub_assign(&src[i]);
                                    }
                                }
                                FormOp::Mul(c) => {
                                    for i in 0..27 {
                                        let mut t = src[i];
                                        t.mul_assign(c);
                                        dst[i].add_assign(&t);
                                    }
                                }
                            }
                        }
                    }

                    eval_scratch.fill(E::ZERO);

                    #[cfg(target_arch = "aarch64")]
                    if const { neon::is_bb_pair::<F, E>() } {
                        // lazy path mirroring the expanded evaluator: preserved
                        // products and bb/linear-base monomials accumulate raw
                        // 64-bit lane products, cond-sub every 2 (see neon.rs)
                        let mut lazy_acc = [0u64; 27 * 4];
                        let mut lazy_products = 0usize;
                        macro_rules! lazy_tick {
                            () => {
                                lazy_products += 1;
                                if lazy_products == 2 {
                                    unsafe {
                                        neon::lazy_condsub_cells::<27>(lazy_acc.as_mut_ptr())
                                    };
                                    lazy_products = 0;
                                }
                            };
                        }
                        for (a, form, c) in products.iter() {
                            unsafe {
                                neon::lazy_quad_base_cells::<27>(
                                    lazy_acc.as_mut_ptr(),
                                    base_scratch[*a as usize].as_ptr() as *const _,
                                    form_scratch[*form as usize].as_ptr() as *const _,
                                    &*(c as *const E as *const _),
                                );
                            }
                            lazy_tick!();
                        }
                        for step in rest_steps.iter() {
                            match step {
                                BenchStep::QuadBB { a, b, c } => {
                                    unsafe {
                                        neon::lazy_quad_base_cells::<27>(
                                            lazy_acc.as_mut_ptr(),
                                            base_scratch[*a as usize].as_ptr() as *const _,
                                            base_scratch[*b as usize].as_ptr() as *const _,
                                            &*(c as *const E as *const _),
                                        );
                                    }
                                    lazy_tick!();
                                }
                                BenchStep::LinB { i, c } => {
                                    unsafe {
                                        neon::lazy_linear_base_27(
                                            lazy_acc.as_mut_ptr(),
                                            base_scratch[*i as usize].as_ptr() as *const _,
                                            &*(c as *const E as *const _),
                                        );
                                    }
                                    lazy_tick!();
                                }
                                BenchStep::QuadBE { base, ext, c } => {
                                    evaluate_quadratic_mixed(
                                        &mut eval_scratch,
                                        &ext_scratch[*ext as usize],
                                        &base_scratch[*base as usize],
                                        c,
                                    );
                                }
                                BenchStep::QuadEE { a, b, c } => {
                                    evaluate_quadratic_ext(
                                        &mut eval_scratch,
                                        &ext_scratch[*a as usize],
                                        &ext_scratch[*b as usize],
                                        c,
                                    );
                                }
                                BenchStep::LinE { i, c } => {
                                    evaluate_linear_ext(
                                        &mut eval_scratch,
                                        &ext_scratch[*i as usize],
                                        c,
                                    );
                                }
                            }
                        }
                        if additive_constant.is_zero() == false {
                            for i in 0..2 {
                                let offset = 9 * i;
                                for j in 0..2 {
                                    let offset = offset + 3 * j;
                                    for k in 0..2 {
                                        eval_scratch[offset + k].add_assign(additive_constant);
                                    }
                                }
                            }
                        }
                        let mut lazy_out = [E::ZERO; 27];
                        unsafe {
                            neon::lazy_finalize_cells::<27>(
                                lazy_acc.as_mut_ptr(),
                                lazy_out.as_mut_ptr() as *mut _,
                            );
                        }
                        for i in 0..27 {
                            eval_scratch[i].add_assign(&lazy_out[i]);
                        }
                        accumulate_scaled(&mut accumulator, &eval_scratch, eq_prefactor);
                        continue;
                    }

                    // generic reduced path
                    for (a, form, c) in products.iter() {
                        evaluate_quadratic_base(
                            &mut eval_scratch,
                            &base_scratch[*a as usize],
                            &form_scratch[*form as usize],
                            c,
                        );
                    }
                    for step in rest_steps.iter() {
                        match step {
                            BenchStep::QuadBB { a, b, c } => evaluate_quadratic_base(
                                &mut eval_scratch,
                                &base_scratch[*a as usize],
                                &base_scratch[*b as usize],
                                c,
                            ),
                            BenchStep::QuadBE { base, ext, c } => evaluate_quadratic_mixed(
                                &mut eval_scratch,
                                &ext_scratch[*ext as usize],
                                &base_scratch[*base as usize],
                                c,
                            ),
                            BenchStep::QuadEE { a, b, c } => evaluate_quadratic_ext(
                                &mut eval_scratch,
                                &ext_scratch[*a as usize],
                                &ext_scratch[*b as usize],
                                c,
                            ),
                            BenchStep::LinB { i, c } => evaluate_linear_base(
                                &mut eval_scratch,
                                &base_scratch[*i as usize],
                                c,
                            ),
                            BenchStep::LinE { i, c } => evaluate_linear_ext(
                                &mut eval_scratch,
                                &ext_scratch[*i as usize],
                                c,
                            ),
                        }
                    }
                    if additive_constant.is_zero() == false {
                        for i in 0..2 {
                            let offset = 9 * i;
                            for j in 0..2 {
                                let offset = offset + 3 * j;
                                for k in 0..2 {
                                    eval_scratch[offset + k].add_assign(additive_constant);
                                }
                            }
                        }
                    }
                    accumulate_scaled(&mut accumulator, &eval_scratch, eq_prefactor);
                }

                *acc_dst = accumulator;
            })
        }
    });

    let mut acc = acc_chunks.pop().unwrap();
    for el in acc_chunks.into_iter() {
        for i in 0..27 {
            acc[i].add_assign(&el[i]);
        }
    }

    acc
}

/// SoA row-blocked initial-window evaluator: 4 consecutive rows per NEON
/// vector. Reads are one `vld1q` per tap, extrapolation is vectorized subs,
/// and term evaluation vectorizes over the 4 rows (limb-major SoA for ext
/// values). BabyBear-specific; the type-id hook rejects other field pairs.
#[cfg(target_arch = "aarch64")]
pub(crate) fn evaluate_initial_soa_parallel<F: PrimeField, E: FieldExtension<F> + Field>(
    base_field_inputs: &[DisjointAccessQuasiSlice<F, false>],
    ext_field_inputs: &[DisjointAccessQuasiSlice<E, false>],
    base_interp: &[bool],
    ext_interp: &[bool],
    forms: &[Vec<(FormOp<F>, u16)>],
    products: &[(u16, u16, E)],
    steps: &[BenchStep<E>],
    additive_constant: &E,
    precomputed_eq_suffix: &[E],
    input_size_log2: usize,
    worker: &Worker,
) -> [E; 27] {
    use crate::gkr::PAR_THRESHOLD;
    use ::field::baby_bear::ext4::BabyBearExt4;

    if const { !neon::is_bb_pair::<F, E>() } {
        unreachable!("SoA variant is BabyBear/Ext4-specific");
    }

    let work_size = (1 << input_size_log2) / 8;
    assert_eq!(work_size % 4, 0);
    let num_blocks = work_size / 4;
    let geometry = worker.get_geometry_with_threshold(num_blocks, PAR_THRESHOLD / 4);
    let mut acc_chunks = vec![[E::ZERO; 27]; geometry.num_chunks];

    worker.scope_with_threshold(num_blocks, PAR_THRESHOLD / 4, |scope, geometry| {
        let mut it = acc_chunks.iter_mut();
        for thread_idx in 0..geometry.num_chunks {
            let chunk_start = geometry.get_chunk_start_pos(thread_idx) * 4;
            let chunk_size = geometry.get_chunk_size(thread_idx) * 4;
            let base_field_inputs = base_field_inputs.to_vec();
            let ext_field_inputs = ext_field_inputs.to_vec();
            let acc_dst = it.next().unwrap();

            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                let input_size = 1 << input_size_log2;
                let ec = |c: &E| -> &BabyBearExt4 { unsafe { &*(c as *const E as *const _) } };

                let mut base_grids = vec![[0u32; 27 * 4]; base_field_inputs.len()];
                let mut ext_grids = vec![[0u32; 27 * 16]; ext_field_inputs.len()];
                let mut form_grids = vec![[0u32; 27 * 4]; forms.len()];
                let mut lazy_acc = [0u64; 27 * 16];
                let mut lazy_out = [0u32; 27 * 16];
                let mut reduced = [0u32; 27 * 16];
                let mut acc_soa = [0u32; 27 * 16];
                let r11v = neon::soa_r11v();
                let const_bcast = unsafe { neon::soa_broadcast_ext(ec(additive_constant)) };
                let has_const = !additive_constant.is_zero();

                unsafe {
                    for row in (chunk_start..(chunk_start + chunk_size)).step_by(4) {
                        for ((grid, src), interp) in base_grids
                            .iter_mut()
                            .zip(base_field_inputs.iter())
                            .zip(base_interp.iter())
                        {
                            neon::soa_read_base_grid(
                                grid.as_mut_ptr(),
                                src.ptr as *const _,
                                input_size,
                                row,
                                *interp,
                            );
                        }
                        for ((grid, src), interp) in ext_grids
                            .iter_mut()
                            .zip(ext_field_inputs.iter())
                            .zip(ext_interp.iter())
                        {
                            neon::soa_read_ext_grid(
                                grid.as_mut_ptr(),
                                src.ptr as *const _,
                                input_size,
                                row,
                                *interp,
                            );
                        }

                        // materialize the preserved inner linear forms in SoA
                        for (grid, members) in form_grids.iter_mut().zip(forms.iter()) {
                            grid.fill(0);
                            for (op, idx) in members.iter() {
                                let src = base_grids[*idx as usize].as_ptr();
                                match op {
                                    FormOp::Add => neon::soa_form_add(grid.as_mut_ptr(), src),
                                    FormOp::Sub => neon::soa_form_sub(grid.as_mut_ptr(), src),
                                    FormOp::Mul(c) => neon::soa_form_muladd(
                                        grid.as_mut_ptr(),
                                        src,
                                        *(c as *const F as *const _),
                                    ),
                                }
                            }
                        }

                        let mut lazy_products = 0usize;
                        for (a, form, c) in products.iter() {
                            neon::soa_quad_bb_lazy::<27>(
                                lazy_acc.as_mut_ptr(),
                                base_grids[*a as usize].as_ptr(),
                                form_grids[*form as usize].as_ptr(),
                                ec(c),
                            );
                            lazy_products += 1;
                            if lazy_products == 2 {
                                neon::soa_lazy_condsub::<27>(lazy_acc.as_mut_ptr());
                                lazy_products = 0;
                            }
                        }
                        for step in steps.iter() {
                            match step {
                                BenchStep::QuadBB { a, b, c } => {
                                    neon::soa_quad_bb_lazy::<27>(
                                        lazy_acc.as_mut_ptr(),
                                        base_grids[*a as usize].as_ptr(),
                                        base_grids[*b as usize].as_ptr(),
                                        ec(c),
                                    );
                                    lazy_products += 1;
                                    if lazy_products == 2 {
                                        neon::soa_lazy_condsub::<27>(lazy_acc.as_mut_ptr());
                                        lazy_products = 0;
                                    }
                                }
                                BenchStep::LinB { i, c } => {
                                    neon::soa_lin_base_lazy(
                                        lazy_acc.as_mut_ptr(),
                                        base_grids[*i as usize].as_ptr(),
                                        ec(c),
                                    );
                                    lazy_products += 1;
                                    if lazy_products == 2 {
                                        neon::soa_lazy_condsub::<27>(lazy_acc.as_mut_ptr());
                                        lazy_products = 0;
                                    }
                                }
                                BenchStep::QuadBE { base, ext, c } => {
                                    let cb = neon::soa_broadcast_ext(ec(c));
                                    neon::soa_quad_be::<27>(
                                        reduced.as_mut_ptr(),
                                        ext_grids[*ext as usize].as_ptr(),
                                        base_grids[*base as usize].as_ptr(),
                                        &cb,
                                        r11v,
                                    );
                                }
                                BenchStep::QuadEE { a, b, c } => {
                                    let cb = neon::soa_broadcast_ext(ec(c));
                                    neon::soa_quad_ee(
                                        reduced.as_mut_ptr(),
                                        ext_grids[*a as usize].as_ptr(),
                                        ext_grids[*b as usize].as_ptr(),
                                        &cb,
                                        r11v,
                                    );
                                }
                                BenchStep::LinE { i, c } => {
                                    let cb = neon::soa_broadcast_ext(ec(c));
                                    neon::soa_lin_ext(
                                        reduced.as_mut_ptr(),
                                        ext_grids[*i as usize].as_ptr(),
                                        &cb,
                                        r11v,
                                    );
                                }
                            }
                        }
                        if has_const {
                            neon::soa_add_const(reduced.as_mut_ptr(), &const_bcast);
                        }

                        neon::soa_lazy_finalize::<27>(lazy_acc.as_mut_ptr(), lazy_out.as_mut_ptr());
                        let eq_soa = neon::soa_transpose_ext4(
                            precomputed_eq_suffix.as_ptr().add(row) as *const _,
                        );
                        neon::soa_apply_eq_and_accumulate::<27>(
                            acc_soa.as_mut_ptr(),
                            lazy_out.as_ptr(),
                            reduced.as_mut_ptr(),
                            &eq_soa,
                            r11v,
                        );
                    }

                    let mut out = [BabyBearExt4::ZERO; 27];
                    neon::soa_final_reduce_to_ext(acc_soa.as_ptr(), out.as_mut_ptr());
                    *acc_dst = *(&out as *const _ as *const [E; 27]);
                }
            })
        }
    });

    let mut acc = acc_chunks.pop().unwrap();
    for el in acc_chunks.into_iter() {
        for i in 0..27 {
            acc[i].add_assign(&el[i]);
        }
    }

    acc
}

/// SoA row-blocked transition round (in 3, out 1): 4 consecutive rows per
/// vector, lazy per-limb fold accumulation, folded values transposed back to
/// AoS for the buffer writes. BabyBear/Ext4-specific.
#[cfg(target_arch = "aarch64")]
pub(crate) fn evaluate_transition_soa_parallel<F: PrimeField, E: FieldExtension<F> + Field>(
    base_field_inputs: &[DisjointAccessQuasiSlice<F, false>],
    ext_field_inputs: &[DisjointAccessQuasiSlice<E, false>],
    base_buffer_ptrs: &[usize],
    ext_buffer_ptrs: &[usize],
    forms: &[Vec<(FormOp<F>, u16)>],
    products: &[(u16, u16, E)],
    folded_quad: &[(u16, u16, E)],
    folded_lin: &[(u16, E)],
    additive_constant: &E,
    prefix: &[E; 8],
    precomputed_eq_suffix: &[E],
    input_size_log2: usize,
    worker: &Worker,
) -> [E; 2] {
    use crate::gkr::PAR_THRESHOLD;
    use ::field::baby_bear::ext4::BabyBearExt4;

    if const { !neon::is_bb_pair::<F, E>() } {
        unreachable!("SoA variant is BabyBear/Ext4-specific");
    }

    let input_size = 1usize << input_size_log2;
    let tap_stride = input_size / 8;
    let half = tap_stride / 2;
    let work_size = half;
    assert_eq!(precomputed_eq_suffix.len(), work_size);
    let num_base = base_field_inputs.len();

    assert_eq!(work_size % 4, 0);
    let num_blocks = work_size / 4;
    let geometry = worker.get_geometry_with_threshold(num_blocks, PAR_THRESHOLD / 4);
    let mut acc_chunks = vec![[E::ZERO; 2]; geometry.num_chunks];

    worker.scope_with_threshold(num_blocks, PAR_THRESHOLD / 4, |scope, geometry| {
        let mut it = acc_chunks.iter_mut();
        for thread_idx in 0..geometry.num_chunks {
            let chunk_start = geometry.get_chunk_start_pos(thread_idx) * 4;
            let chunk_size = geometry.get_chunk_size(thread_idx) * 4;
            let base_field_inputs = base_field_inputs.to_vec();
            let ext_field_inputs = ext_field_inputs.to_vec();
            let base_buffer_ptrs = base_buffer_ptrs.to_vec();
            let ext_buffer_ptrs = ext_buffer_ptrs.to_vec();
            let acc_dst = it.next().unwrap();

            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                let ec = |c: &E| -> &BabyBearExt4 { unsafe { &*(c as *const E as *const _) } };
                let prefix_bb: &[BabyBearExt4; 8] =
                    unsafe { &*(prefix as *const [E; 8] as *const _) };
                let prefix_limbs = neon::soa_prefix_limbs(prefix_bb);
                let tables: [neon::SoaExtTable; 8] =
                    core::array::from_fn(|i| neon::SoaExtTable::new(&prefix_bb[i]));
                let r11v = neon::soa_r11v();
                let const_bcast = unsafe { neon::soa_broadcast_ext(ec(additive_constant)) };
                let has_const = !additive_constant.is_zero();
                let quad_terms: Vec<(u16, u16, [core::arch::aarch64::uint32x4_t; 4])> = folded_quad
                    .iter()
                    .map(|(a, b, c)| (*a, *b, unsafe { neon::soa_broadcast_ext(ec(c)) }))
                    .collect();
                let lin_terms: Vec<(u16, [core::arch::aarch64::uint32x4_t; 4])> = folded_lin
                    .iter()
                    .map(|(i, c)| (*i, unsafe { neon::soa_broadcast_ext(ec(c)) }))
                    .collect();

                let product_terms: Vec<(u16, u16, [core::arch::aarch64::uint32x4_t; 4])> =
                    products
                        .iter()
                        .map(|(a, f, c)| (*a, *f, unsafe { neon::soa_broadcast_ext(ec(c)) }))
                        .collect();

                // [2 cells][4 limbs][4 rows] per poly
                let mut pairs = vec![[0u32; 32]; num_base + ext_field_inputs.len()];
                let mut form_pairs = vec![[0u32; 32]; forms.len()];
                let mut eval2 = [0u32; 32];
                let mut acc2 = [0u32; 32];

                unsafe {
                    for row in (chunk_start..(chunk_start + chunk_size)).step_by(4) {
                        for (slot, src) in base_field_inputs.iter().enumerate() {
                            let v0 = neon::soa_fold8_base(
                                src.ptr as *const _,
                                &prefix_limbs,
                                tap_stride,
                                row,
                            );
                            let v1 = neon::soa_fold8_base(
                                src.ptr as *const _,
                                &prefix_limbs,
                                tap_stride,
                                row + half,
                            );
                            let dst = base_buffer_ptrs[slot] as *mut BabyBearExt4;
                            neon::soa_store_ext4(&v0, dst.add(row));
                            neon::soa_store_ext4(&v1, dst.add(row + half));
                            let d = neon::soa_sub_limbs(&v1, &v0);
                            neon::soa_store_cell(pairs[slot].as_mut_ptr(), &v0);
                            neon::soa_store_cell(pairs[slot].as_mut_ptr().add(16), &d);
                        }
                        for (idx, src) in ext_field_inputs.iter().enumerate() {
                            let slot = num_base + idx;
                            let v0 = neon::soa_fold8_ext(
                                src.ptr as *const _,
                                &tables,
                                tap_stride,
                                row,
                            );
                            let v1 = neon::soa_fold8_ext(
                                src.ptr as *const _,
                                &tables,
                                tap_stride,
                                row + half,
                            );
                            let dst = ext_buffer_ptrs[idx] as *mut BabyBearExt4;
                            neon::soa_store_ext4(&v0, dst.add(row));
                            neon::soa_store_ext4(&v1, dst.add(row + half));
                            let d = neon::soa_sub_limbs(&v1, &v0);
                            neon::soa_store_cell(pairs[slot].as_mut_ptr(), &v0);
                            neon::soa_store_cell(pairs[slot].as_mut_ptr().add(16), &d);
                        }

                        // materialize the preserved inner linear forms over the
                        // folded pairs (linearity holds for both cells)
                        for (grid, members) in form_pairs.iter_mut().zip(forms.iter()) {
                            grid.fill(0);
                            for (op, idx) in members.iter() {
                                let src = pairs[*idx as usize].as_ptr();
                                match op {
                                    FormOp::Add => {
                                        neon::soa_ext_form_add_n::<2>(grid.as_mut_ptr(), src)
                                    }
                                    FormOp::Sub => {
                                        neon::soa_ext_form_sub_n::<2>(grid.as_mut_ptr(), src)
                                    }
                                    FormOp::Mul(c) => neon::soa_ext_form_muladd_n::<2>(
                                        grid.as_mut_ptr(),
                                        src,
                                        *(c as *const F as *const _),
                                    ),
                                }
                            }
                        }
                        for (a, f, cb) in product_terms.iter() {
                            neon::soa_quad_ee_n::<2>(
                                eval2.as_mut_ptr(),
                                pairs[*a as usize].as_ptr(),
                                form_pairs[*f as usize].as_ptr(),
                                cb,
                                r11v,
                            );
                        }
                        for (a, b, cb) in quad_terms.iter() {
                            neon::soa_quad_ee_n::<2>(
                                eval2.as_mut_ptr(),
                                pairs[*a as usize].as_ptr(),
                                pairs[*b as usize].as_ptr(),
                                cb,
                                r11v,
                            );
                        }
                        for (i, cb) in lin_terms.iter() {
                            neon::soa_lin_ext_cell0(
                                eval2.as_mut_ptr(),
                                pairs[*i as usize].as_ptr(),
                                cb,
                                r11v,
                            );
                        }
                        if has_const {
                            neon::soa_add_const_cell0(eval2.as_mut_ptr(), &const_bcast);
                        }

                        let eq_soa = neon::soa_transpose_ext4(
                            precomputed_eq_suffix.as_ptr().add(row) as *const _,
                        );
                        neon::soa_apply_eq_and_accumulate_n::<2>(
                            acc2.as_mut_ptr(),
                            eval2.as_mut_ptr(),
                            &eq_soa,
                            r11v,
                        );
                    }

                    let mut out = [BabyBearExt4::ZERO; 2];
                    neon::soa_final_reduce_to_ext_n::<2>(acc2.as_ptr(), out.as_mut_ptr());
                    *acc_dst = *(&out as *const _ as *const [E; 2]);
                }
            })
        }
    });

    let mut acc = acc_chunks.pop().unwrap();
    for el in acc_chunks.into_iter() {
        for i in 0..2 {
            acc[i].add_assign(&el[i]);
        }
    }

    acc
}

/// SoA row-blocked window-3 ext pass: folds 1 pending challenge (in1out3) or 3
/// (in3out3) in SoA, fills the 27-cell grid per poly, evaluates and applies eq
/// per 4-row block. Buffers are ext AoS, written back in place.
#[cfg(target_arch = "aarch64")]
pub(crate) fn evaluate_ext_window3_soa_parallel<F: PrimeField, E: FieldExtension<F> + Field>(
    buffer_ptrs: &[usize], // combined slot order: base-origin polys then ext
    fold2_challenge: Option<&E>,
    fold8_prefix: Option<&[E; 8]>,
    forms: &[Vec<(FormOp<F>, u16)>],
    products: &[(u16, u16, E)],
    folded_quad: &[(u16, u16, E)],
    folded_lin: &[(u16, E)],
    additive_constant: &E,
    precomputed_eq_suffix: &[E],
    unfolded_input_size_log2: usize,
    worker: &Worker,
) -> [E; 27] {
    use crate::gkr::PAR_THRESHOLD;
    use ::field::baby_bear::ext4::BabyBearExt4;

    if const { !neon::is_bb_pair::<F, E>() } {
        unreachable!("SoA variant is BabyBear/Ext4-specific");
    }
    assert!(fold2_challenge.is_some() != fold8_prefix.is_some());

    let input_size = 1usize << unfolded_input_size_log2;
    let is_fold2 = fold2_challenge.is_some();
    // fold2: pairs at distance input/2, window over the folded input/2 domain
    // fold8: taps at stride input/8, window over the folded input/8 domain
    let (pair_stride, folded_size) = if is_fold2 {
        (input_size / 2, input_size / 2)
    } else {
        (input_size / 8, input_size / 8)
    };
    let corner_strides = [folded_size / 2, folded_size / 4, folded_size / 8];
    let work_size = folded_size / 8;
    assert_eq!(precomputed_eq_suffix.len(), work_size);
    assert!(work_size >= 4);

    assert_eq!(work_size % 4, 0);
    let num_blocks = work_size / 4;
    let geometry = worker.get_geometry_with_threshold(num_blocks, PAR_THRESHOLD / 4);
    let mut acc_chunks = vec![[E::ZERO; 27]; geometry.num_chunks];

    worker.scope_with_threshold(num_blocks, PAR_THRESHOLD / 4, |scope, geometry| {
        let mut it = acc_chunks.iter_mut();
        for thread_idx in 0..geometry.num_chunks {
            let chunk_start = geometry.get_chunk_start_pos(thread_idx) * 4;
            let chunk_size = geometry.get_chunk_size(thread_idx) * 4;
            let buffer_ptrs = buffer_ptrs.to_vec();
            let acc_dst = it.next().unwrap();

            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                let ec = |c: &E| -> &BabyBearExt4 { unsafe { &*(c as *const E as *const _) } };
                let r11v = neon::soa_r11v();
                let fold2_table = fold2_challenge.map(|c| neon::SoaExtTable::new(ec(c)));
                let fold8_tables: Option<[neon::SoaExtTable; 8]> = fold8_prefix.map(|p| {
                    let p: &[BabyBearExt4; 8] = unsafe { &*(p as *const [E; 8] as *const _) };
                    core::array::from_fn(|i| neon::SoaExtTable::new(&p[i]))
                });
                let const_bcast = unsafe { neon::soa_broadcast_ext(ec(additive_constant)) };
                let has_const = !additive_constant.is_zero();
                let quad_terms: Vec<(u16, u16, [core::arch::aarch64::uint32x4_t; 4])> = folded_quad
                    .iter()
                    .map(|(a, b, c)| (*a, *b, unsafe { neon::soa_broadcast_ext(ec(c)) }))
                    .collect();
                let lin_terms: Vec<(u16, [core::arch::aarch64::uint32x4_t; 4])> = folded_lin
                    .iter()
                    .map(|(i, c)| (*i, unsafe { neon::soa_broadcast_ext(ec(c)) }))
                    .collect();

                let product_terms: Vec<(u16, u16, [core::arch::aarch64::uint32x4_t; 4])> =
                    products
                        .iter()
                        .map(|(a, f, c)| (*a, *f, unsafe { neon::soa_broadcast_ext(ec(c)) }))
                        .collect();

                let mut grids = vec![[0u32; 27 * 16]; buffer_ptrs.len()];
                let mut form_grids = vec![[0u32; 27 * 16]; forms.len()];
                let mut eval27 = [0u32; 27 * 16];
                let mut acc27 = [0u32; 27 * 16];

                unsafe {
                    for row in (chunk_start..(chunk_start + chunk_size)).step_by(4) {
                        for (slot, ptr) in buffer_ptrs.iter().enumerate() {
                            let buf = *ptr as *mut BabyBearExt4;
                            let grid = grids[slot].as_mut_ptr();
                            for j in 0..8usize {
                                let idx = row
                                    + (j >> 2) * corner_strides[0]
                                    + ((j >> 1) & 1) * corner_strides[1]
                                    + (j & 1) * corner_strides[2];
                                let f = if let Some(t) = fold2_table.as_ref() {
                                    let v0 = neon::soa_transpose_ext4(buf.add(idx));
                                    let v1 = neon::soa_transpose_ext4(buf.add(idx + pair_stride));
                                    let d = neon::soa_sub_limbs(&v1, &v0);
                                    neon::soa_add_limbs(&v0, &t.apply(&d))
                                } else {
                                    neon::soa_fold8_ext(
                                        buf as *const _,
                                        fold8_tables.as_ref().unwrap(),
                                        pair_stride,
                                        idx,
                                    )
                                };
                                neon::soa_store_ext4(&f, buf.add(idx));
                                let cell = 9 * (j >> 2) + 3 * ((j >> 1) & 1) + (j & 1);
                                neon::soa_store_cell(grid.add(16 * cell), &f);
                            }
                            // interpolate the 19 infinity cells per limb
                            for x0 in 0..2usize {
                                let base = 9 * x0;
                                for x1 in 0..2usize {
                                    let off = base + 3 * x1;
                                    let a = neon::soa_load_cell(grid.add(16 * off));
                                    let b = neon::soa_load_cell(grid.add(16 * (off + 1)));
                                    neon::soa_store_cell(
                                        grid.add(16 * (off + 2)),
                                        &neon::soa_sub_limbs(&b, &a),
                                    );
                                }
                                for x2 in 0..3usize {
                                    let a = neon::soa_load_cell(grid.add(16 * (base + x2)));
                                    let b = neon::soa_load_cell(grid.add(16 * (base + 3 + x2)));
                                    neon::soa_store_cell(
                                        grid.add(16 * (base + 6 + x2)),
                                        &neon::soa_sub_limbs(&b, &a),
                                    );
                                }
                            }
                            for x1 in 0..3usize {
                                let off = 3 * x1;
                                for x2 in 0..3usize {
                                    let a = neon::soa_load_cell(grid.add(16 * (off + x2)));
                                    let b = neon::soa_load_cell(grid.add(16 * (9 + off + x2)));
                                    neon::soa_store_cell(
                                        grid.add(16 * (18 + off + x2)),
                                        &neon::soa_sub_limbs(&b, &a),
                                    );
                                }
                            }
                        }

                        for (grid, members) in form_grids.iter_mut().zip(forms.iter()) {
                            grid.fill(0);
                            for (op, idx) in members.iter() {
                                let src = grids[*idx as usize].as_ptr();
                                match op {
                                    FormOp::Add => {
                                        neon::soa_ext_form_add_n::<27>(grid.as_mut_ptr(), src)
                                    }
                                    FormOp::Sub => {
                                        neon::soa_ext_form_sub_n::<27>(grid.as_mut_ptr(), src)
                                    }
                                    FormOp::Mul(c) => neon::soa_ext_form_muladd_n::<27>(
                                        grid.as_mut_ptr(),
                                        src,
                                        *(c as *const F as *const _),
                                    ),
                                }
                            }
                        }
                        for (a, f, cb) in product_terms.iter() {
                            neon::soa_quad_ee_n::<27>(
                                eval27.as_mut_ptr(),
                                grids[*a as usize].as_ptr(),
                                form_grids[*f as usize].as_ptr(),
                                cb,
                                r11v,
                            );
                        }
                        for (a, b, cb) in quad_terms.iter() {
                            neon::soa_quad_ee_n::<27>(
                                eval27.as_mut_ptr(),
                                grids[*a as usize].as_ptr(),
                                grids[*b as usize].as_ptr(),
                                cb,
                                r11v,
                            );
                        }
                        for (i, cb) in lin_terms.iter() {
                            neon::soa_lin_ext(
                                eval27.as_mut_ptr(),
                                grids[*i as usize].as_ptr(),
                                cb,
                                r11v,
                            );
                        }
                        if has_const {
                            neon::soa_add_const(eval27.as_mut_ptr(), &const_bcast);
                        }

                        let eq_soa = neon::soa_transpose_ext4(
                            precomputed_eq_suffix.as_ptr().add(row) as *const _,
                        );
                        neon::soa_apply_eq_and_accumulate_n::<27>(
                            acc27.as_mut_ptr(),
                            eval27.as_mut_ptr(),
                            &eq_soa,
                            r11v,
                        );
                    }

                    let mut out = [BabyBearExt4::ZERO; 27];
                    neon::soa_final_reduce_to_ext_n::<27>(acc27.as_ptr(), out.as_mut_ptr());
                    *acc_dst = *(&out as *const _ as *const [E; 27]);
                }
            })
        }
    });

    let mut acc = acc_chunks.pop().unwrap();
    for el in acc_chunks.into_iter() {
        for i in 0..27 {
            acc[i].add_assign(&el[i]);
        }
    }

    acc
}

/// Owned SoA + bracket program for one layer, consumed by the production
/// windowed sumcheck loop (mirrors the program the bench driver builds inline).
pub(crate) struct OwnedSoaProgram<F: PrimeField, E: Field> {
    pub base_interp: Vec<bool>,
    pub ext_interp: Vec<bool>,
    pub forms: Vec<Vec<(FormOp<F>, u16)>>,
    pub products: Vec<(u16, u16, E)>,
    pub rest_steps: Vec<BenchStep<E>>,
    pub folded_quad: Vec<(u16, u16, E)>,
    pub folded_lin: Vec<(u16, E)>,
    pub additive_constant: E,
}

/// Build the SoA + bracket-preserving program for a layer: interpolation flags,
/// CSE'd multi-member bracket forms + preserved products (from the enforce
/// max-quadratic kernels), the bracket-subtracted expanded remainder, and the
/// folded-stage step lists over the combined slot space.
pub(crate) fn build_soa_program<F: PrimeField, E: FieldExtension<F> + Field>(
    description: &BatchedGKRDescription<F, E>,
    collector: &KernelCollector<F, E>,
    base_polys: &[GKRAddress],
    ext_polys: &[GKRAddress],
) -> OwnedSoaProgram<F, E> {
    use crate::gkr::prover::sumcheck_loop::kernel_collector::KernelVariant;
    use std::collections::BTreeSet;

    let bidx = |addr: &GKRAddress| base_polys.iter().position(|el| el == addr).unwrap() as u16;
    let eidx = |addr: &GKRAddress| ext_polys.iter().position(|el| el == addr).unwrap() as u16;

    let mut base_quad: BTreeSet<GKRAddress> = BTreeSet::new();
    let mut ext_quad: BTreeSet<GKRAddress> = BTreeSet::new();
    for (a, list) in description.quadratic_part_base_by_base.iter() {
        base_quad.insert(*a);
        for (b, _) in list.iter() {
            base_quad.insert(*b);
        }
    }
    for (a, list) in description.quadratic_part_base_by_ext.iter() {
        base_quad.insert(*a);
        for (b, _) in list.iter() {
            ext_quad.insert(*b);
        }
    }
    for (a, list) in description.quadratic_part_ext_by_ext.iter() {
        ext_quad.insert(*a);
        for (b, _) in list.iter() {
            ext_quad.insert(*b);
        }
    }
    let base_interp: Vec<bool> = base_polys.iter().map(|a| base_quad.contains(a)).collect();
    let ext_interp: Vec<bool> = ext_polys.iter().map(|a| ext_quad.contains(a)).collect();

    let mut forms: Vec<Vec<(FormOp<F>, u16)>> = vec![];
    let mut form_key_to_idx: BTreeMap<Vec<(u128, u16)>, u16> = BTreeMap::new();
    let mut products: Vec<(u16, u16, E)> = vec![];
    let mut subtract: BTreeMap<(GKRAddress, GKRAddress), E> = BTreeMap::new();

    for kernel in collector.kernels.iter() {
        let KernelVariant::EnforceSingleMaxQuadraticConstraint(rel, ch) = kernel else {
            continue;
        };
        let challenge = ch[0];
        for (a, bracket) in rel.relation.quadratic_terms.iter() {
            let members: Vec<(F, GKRAddress)> = bracket
                .iter()
                .filter(|(c, _)| !c.is_zero())
                .copied()
                .collect();
            if members.len() < 2 {
                continue;
            }
            for (c, b) in members.iter() {
                let pair = if *a <= *b { (*a, *b) } else { (*b, *a) };
                let mut contribution = challenge;
                contribution.mul_assign_by_base(c);
                subtract
                    .entry(pair)
                    .or_insert(E::ZERO)
                    .add_assign(&contribution);
            }
            let mut key: Vec<(u128, u16)> = members
                .iter()
                .map(|(c, b)| (c.as_u128_reduced(), bidx(b)))
                .collect();
            key.sort();
            let form_idx = *form_key_to_idx.entry(key).or_insert_with(|| {
                let ops: Vec<(FormOp<F>, u16)> = members
                    .iter()
                    .map(|(c, b)| {
                        let op = if *c == F::ONE {
                            FormOp::Add
                        } else if *c == F::MINUS_ONE {
                            FormOp::Sub
                        } else {
                            FormOp::Mul(*c)
                        };
                        (op, bidx(b))
                    })
                    .collect();
                forms.push(ops);
                (forms.len() - 1) as u16
            });
            products.push((bidx(a), form_idx, challenge));
        }
    }

    let mut rest_steps: Vec<BenchStep<E>> = vec![];
    for (a, list) in description.quadratic_part_base_by_base.iter() {
        for (b, c) in list.iter() {
            let mut c = *c;
            if let Some(sub) = subtract.get(&(*a, *b)) {
                c.sub_assign(sub);
            }
            if c.is_zero() {
                continue;
            }
            rest_steps.push(BenchStep::QuadBB {
                a: bidx(a),
                b: bidx(b),
                c,
            });
        }
    }
    for (a, list) in description.quadratic_part_base_by_ext.iter() {
        for (b, c) in list.iter() {
            rest_steps.push(BenchStep::QuadBE {
                base: bidx(a),
                ext: eidx(b),
                c: *c,
            });
        }
    }
    for (a, list) in description.quadratic_part_ext_by_ext.iter() {
        for (b, c) in list.iter() {
            rest_steps.push(BenchStep::QuadEE {
                a: eidx(a),
                b: eidx(b),
                c: *c,
            });
        }
    }
    for (a, c) in description.linear_part_base_by_everything.iter() {
        rest_steps.push(BenchStep::LinB { i: bidx(a), c: *c });
    }
    for (a, c) in description.linear_part_ext_by_everything.iter() {
        rest_steps.push(BenchStep::LinE { i: eidx(a), c: *c });
    }

    let nb = base_polys.len() as u16;
    let mut folded_quad: Vec<(u16, u16, E)> = vec![];
    for step in rest_steps.iter() {
        match step {
            BenchStep::QuadBB { a, b, c } => folded_quad.push((*a, *b, *c)),
            BenchStep::QuadBE { base, ext, c } => folded_quad.push((*base, nb + *ext, *c)),
            BenchStep::QuadEE { a, b, c } => folded_quad.push((nb + *a, nb + *b, *c)),
            _ => {}
        }
    }
    let mut folded_lin: Vec<(u16, E)> = vec![];
    for (a, c) in description.linear_part_base_by_everything.iter() {
        folded_lin.push((bidx(a), *c));
    }
    for (a, c) in description.linear_part_ext_by_everything.iter() {
        folded_lin.push((nb + eidx(a), *c));
    }

    OwnedSoaProgram {
        base_interp,
        ext_interp,
        forms,
        products,
        rest_steps,
        folded_quad,
        folded_lin,
        additive_constant: description.constant_term,
    }
}

/// Univariate-skip (k = 3) initial pass: each poly's 8 packed values per block
/// (top-3-bit strides, domain order j = 4*x0+2*x1+x2 on H = <w8>) are LDE'd to
/// the coset w16*H with size-8 NTTs; the bracketed program is evaluated on all
/// 16 points (packed linear terms and the constant are dense over the domain),
/// eq-weighted per 4-row block, and reduced to the `[E; 16]` evaluations of
/// the skipped-round univariate q on H u w16*H.
#[cfg(target_arch = "aarch64")]
fn evaluate_initial_uniskip_soa_parallel<F: PrimeField, E: FieldExtension<F> + Field>(
    base_field_inputs: &[DisjointAccessQuasiSlice<F, false>],
    ext_field_inputs: &[DisjointAccessQuasiSlice<E, false>],
    forms: &[Vec<(FormOp<F>, u16)>],
    products: &[(u16, u16, E)],
    rest_steps: &[BenchStep<E>],
    additive_constant: &E,
    lde_tables: &neon::SoaLde8Tables,
    precomputed_eq_suffix: &[E],
    input_size_log2: usize,
    worker: &Worker,
) -> [E; 16] {
    use crate::gkr::PAR_THRESHOLD;
    use ::field::baby_bear::ext4::BabyBearExt4;
    use core::arch::aarch64::{uint32x4_t, vld1q_u32, vst1q_u32};

    if const { !neon::is_bb_pair::<F, E>() } {
        unreachable!("uniskip variant is BabyBear/Ext4-specific");
    }

    let work_size = (1 << input_size_log2) / 8;
    assert_eq!(precomputed_eq_suffix.len(), work_size);
    assert_eq!(work_size % 4, 0);
    let num_blocks = work_size / 4;
    let geometry = worker.get_geometry_with_threshold(num_blocks, PAR_THRESHOLD / 4);
    let mut acc_chunks = vec![[E::ZERO; 16]; geometry.num_chunks];

    worker.scope_with_threshold(num_blocks, PAR_THRESHOLD / 4, |scope, geometry| {
        let mut it = acc_chunks.iter_mut();
        for thread_idx in 0..geometry.num_chunks {
            let chunk_start = geometry.get_chunk_start_pos(thread_idx) * 4;
            let chunk_size = geometry.get_chunk_size(thread_idx) * 4;
            let base_field_inputs = base_field_inputs.to_vec();
            let ext_field_inputs = ext_field_inputs.to_vec();
            let lde_tables = *lde_tables;
            let acc_dst = it.next().unwrap();

            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                let input_size = 1 << input_size_log2;
                let ec = |c: &E| -> &BabyBearExt4 { unsafe { &*(c as *const E as *const _) } };
                let r11v = neon::soa_r11v();
                let const_bcast = unsafe { neon::soa_broadcast_ext(ec(additive_constant)) };
                let has_const = !additive_constant.is_zero();

                // grids: cells 0..8 = H values (domain order), 8..16 = coset LDE
                let mut base_grids = vec![[0u32; 16 * 4]; base_field_inputs.len()];
                let mut ext_grids = vec![[0u32; 16 * 16]; ext_field_inputs.len()];
                let mut form_grids = vec![[0u32; 16 * 4]; forms.len()];
                let mut lazy_acc = [0u64; 16 * 16];
                let mut lazy_out = [0u32; 16 * 16];
                let mut reduced = [0u32; 16 * 16];
                let mut acc_soa = [0u32; 16 * 16];

                unsafe {
                    for row in (chunk_start..(chunk_start + chunk_size)).step_by(4) {
                        for (grid, src) in base_grids.iter_mut().zip(base_field_inputs.iter()) {
                            let h = neon::soa_read_base_block8(
                                src.ptr as *const _,
                                input_size,
                                row,
                            );
                            let coset = neon::soa_lde8(&h, &lde_tables);
                            for j in 0..8 {
                                vst1q_u32(grid.as_mut_ptr().add(4 * j), h[j]);
                                vst1q_u32(grid.as_mut_ptr().add(4 * (8 + j)), coset[j]);
                            }
                        }
                        for (grid, src) in ext_grids.iter_mut().zip(ext_field_inputs.iter()) {
                            let s0 = input_size / 2;
                            let s1 = input_size / 4;
                            let s2 = input_size / 8;
                            let base = src.ptr as *const BabyBearExt4;
                            for j in 0..8usize {
                                let idx =
                                    row + (j >> 2) * s0 + ((j >> 1) & 1) * s1 + (j & 1) * s2;
                                let limbs = neon::soa_transpose_ext4(base.add(idx));
                                neon::soa_store_cell(grid.as_mut_ptr().add(16 * j), &limbs);
                            }
                            for l in 0..4usize {
                                let h: [uint32x4_t; 8] = core::array::from_fn(|j| {
                                    vld1q_u32(grid.as_ptr().add(16 * j + 4 * l))
                                });
                                let coset = neon::soa_lde8(&h, &lde_tables);
                                for j in 0..8 {
                                    vst1q_u32(
                                        grid.as_mut_ptr().add(16 * (8 + j) + 4 * l),
                                        coset[j],
                                    );
                                }
                            }
                        }
                        // forms: materialize on the H half, then LDE like a poly
                        for (grid, members) in form_grids.iter_mut().zip(forms.iter()) {
                            grid[..32].fill(0);
                            for (op, idx) in members.iter() {
                                let src = base_grids[*idx as usize].as_ptr();
                                match op {
                                    FormOp::Add => {
                                        neon::soa_base_form_add_n::<8>(grid.as_mut_ptr(), src)
                                    }
                                    FormOp::Sub => {
                                        neon::soa_base_form_sub_n::<8>(grid.as_mut_ptr(), src)
                                    }
                                    FormOp::Mul(c) => neon::soa_base_form_muladd_n::<8>(
                                        grid.as_mut_ptr(),
                                        src,
                                        *(c as *const F as *const _),
                                    ),
                                }
                            }
                            let h: [uint32x4_t; 8] = core::array::from_fn(|j| {
                                vld1q_u32(grid.as_ptr().add(4 * j))
                            });
                            let coset = neon::soa_lde8(&h, &lde_tables);
                            for j in 0..8 {
                                vst1q_u32(grid.as_mut_ptr().add(4 * (8 + j)), coset[j]);
                            }
                        }

                        let mut lazy_products = 0usize;
                        macro_rules! lazy_tick {
                            () => {
                                lazy_products += 1;
                                if lazy_products == 2 {
                                    neon::soa_lazy_condsub::<16>(lazy_acc.as_mut_ptr());
                                    lazy_products = 0;
                                }
                            };
                        }
                        for (a, form, c) in products.iter() {
                            neon::soa_quad_bb_lazy::<16>(
                                lazy_acc.as_mut_ptr(),
                                base_grids[*a as usize].as_ptr(),
                                form_grids[*form as usize].as_ptr(),
                                ec(c),
                            );
                            lazy_tick!();
                        }
                        for step in rest_steps.iter() {
                            match step {
                                BenchStep::QuadBB { a, b, c } => {
                                    neon::soa_quad_bb_lazy::<16>(
                                        lazy_acc.as_mut_ptr(),
                                        base_grids[*a as usize].as_ptr(),
                                        base_grids[*b as usize].as_ptr(),
                                        ec(c),
                                    );
                                    lazy_tick!();
                                }
                                BenchStep::LinB { i, c } => {
                                    neon::soa_lin_base_all_n::<16>(
                                        lazy_acc.as_mut_ptr(),
                                        base_grids[*i as usize].as_ptr(),
                                        ec(c),
                                    );
                                    lazy_tick!();
                                }
                                BenchStep::QuadBE { base, ext, c } => {
                                    let cb = neon::soa_broadcast_ext(ec(c));
                                    neon::soa_quad_be::<16>(
                                        reduced.as_mut_ptr(),
                                        ext_grids[*ext as usize].as_ptr(),
                                        base_grids[*base as usize].as_ptr(),
                                        &cb,
                                        r11v,
                                    );
                                }
                                BenchStep::QuadEE { a, b, c } => {
                                    let cb = neon::soa_broadcast_ext(ec(c));
                                    neon::soa_quad_ee_n::<16>(
                                        reduced.as_mut_ptr(),
                                        ext_grids[*a as usize].as_ptr(),
                                        ext_grids[*b as usize].as_ptr(),
                                        &cb,
                                        r11v,
                                    );
                                }
                                BenchStep::LinE { i, c } => {
                                    let cb = neon::soa_broadcast_ext(ec(c));
                                    neon::soa_lin_ext_all_n::<16>(
                                        reduced.as_mut_ptr(),
                                        ext_grids[*i as usize].as_ptr(),
                                        &cb,
                                        r11v,
                                    );
                                }
                            }
                        }
                        if has_const {
                            neon::soa_add_const_all_n::<16>(reduced.as_mut_ptr(), &const_bcast);
                        }

                        neon::soa_lazy_finalize::<16>(lazy_acc.as_mut_ptr(), lazy_out.as_mut_ptr());
                        let eq_soa = neon::soa_transpose_ext4(
                            precomputed_eq_suffix.as_ptr().add(row) as *const _,
                        );
                        neon::soa_apply_eq_and_accumulate::<16>(
                            acc_soa.as_mut_ptr(),
                            lazy_out.as_ptr(),
                            reduced.as_mut_ptr(),
                            &eq_soa,
                            r11v,
                        );
                    }

                    let mut out = [BabyBearExt4::ZERO; 16];
                    neon::soa_final_reduce_to_ext_n::<16>(acc_soa.as_ptr(), out.as_mut_ptr());
                    *acc_dst = *(&out as *const _ as *const [E; 16]);
                }
            })
        }
    });

    let mut acc = acc_chunks.pop().unwrap();
    for el in acc_chunks.into_iter() {
        for i in 0..16 {
            acc[i].add_assign(&el[i]);
        }
    }

    acc
}

/// Univariate-skip k = 6 initial pass: 64 packed values per block LDE'd to the
/// coset with size-64 NTTs (radix-2 or radix-8 pipeline), bracketed program on
/// all 128 evaluation points.
#[cfg(target_arch = "aarch64")]
fn evaluate_initial_uniskip64_soa_parallel<F: PrimeField, E: FieldExtension<F> + Field>(
    base_field_inputs: &[DisjointAccessQuasiSlice<F, false>],
    ext_field_inputs: &[DisjointAccessQuasiSlice<E, false>],
    forms: &[Vec<(FormOp<F>, u16)>],
    products: &[(u16, u16, E)],
    rest_steps: &[BenchStep<E>],
    additive_constant: &E,
    lde_tables: &neon::SoaLde64Tables,
    use_radix8: bool,
    precomputed_eq_suffix: &[E],
    input_size_log2: usize,
    worker: &Worker,
) -> [E; 128] {
    use crate::gkr::PAR_THRESHOLD;
    use ::field::baby_bear::ext4::BabyBearExt4;
    use core::arch::aarch64::{uint32x4_t, vld1q_u32, vst1q_u32};

    if const { !neon::is_bb_pair::<F, E>() } {
        unreachable!("uniskip variant is BabyBear/Ext4-specific");
    }

    let work_size = (1 << input_size_log2) / 64;
    assert_eq!(precomputed_eq_suffix.len(), work_size);
    assert_eq!(work_size % 4, 0);
    let num_blocks = work_size / 4;
    let geometry = worker.get_geometry_with_threshold(num_blocks, PAR_THRESHOLD / 4);
    let mut acc_chunks = vec![[E::ZERO; 128]; geometry.num_chunks];

    worker.scope_with_threshold(num_blocks, PAR_THRESHOLD / 4, |scope, geometry| {
        let mut it = acc_chunks.iter_mut();
        for thread_idx in 0..geometry.num_chunks {
            let chunk_start = geometry.get_chunk_start_pos(thread_idx) * 4;
            let chunk_size = geometry.get_chunk_size(thread_idx) * 4;
            let base_field_inputs = base_field_inputs.to_vec();
            let ext_field_inputs = ext_field_inputs.to_vec();
            let lde_tables = *lde_tables;
            let acc_dst = it.next().unwrap();

            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                let input_size = 1 << input_size_log2;
                let ec = |c: &E| -> &BabyBearExt4 { unsafe { &*(c as *const E as *const _) } };
                let r11v = neon::soa_r11v();
                let const_bcast = unsafe { neon::soa_broadcast_ext(ec(additive_constant)) };
                let has_const = !additive_constant.is_zero();
                let lde = |h: &[uint32x4_t; 64]| -> [uint32x4_t; 64] {
                    unsafe {
                        if use_radix8 {
                            neon::soa_lde64_r8(h, &lde_tables)
                        } else {
                            neon::soa_lde64_r2(h, &lde_tables)
                        }
                    }
                };

                let mut base_grids = vec![[0u32; 128 * 4]; base_field_inputs.len()];
                let mut ext_grids = vec![[0u32; 128 * 16]; ext_field_inputs.len()];
                let mut form_grids = vec![[0u32; 128 * 4]; forms.len()];
                let mut lazy_acc = vec![0u64; 128 * 16];
                let mut lazy_out = vec![0u32; 128 * 16];
                let mut reduced = vec![0u32; 128 * 16];
                let mut acc_soa = vec![0u32; 128 * 16];

                unsafe {
                    for row in (chunk_start..(chunk_start + chunk_size)).step_by(4) {
                        for (grid, src) in base_grids.iter_mut().zip(base_field_inputs.iter()) {
                            let h = neon::soa_read_base_block64(
                                src.ptr as *const _,
                                input_size,
                                row,
                            );
                            let coset = lde(&h);
                            for j in 0..64 {
                                vst1q_u32(grid.as_mut_ptr().add(4 * j), h[j]);
                                vst1q_u32(grid.as_mut_ptr().add(4 * (64 + j)), coset[j]);
                            }
                        }
                        for (grid, src) in ext_grids.iter_mut().zip(ext_field_inputs.iter()) {
                            let step = input_size / 64;
                            let base = src.ptr as *const BabyBearExt4;
                            for j in 0..64usize {
                                let mut off = row;
                                for bit in 0..6 {
                                    if (j >> bit) & 1 == 1 {
                                        off += step << bit;
                                    }
                                }
                                let limbs = neon::soa_transpose_ext4(base.add(off));
                                neon::soa_store_cell(grid.as_mut_ptr().add(16 * j), &limbs);
                            }
                            for l in 0..4usize {
                                let h: [uint32x4_t; 64] = core::array::from_fn(|j| {
                                    vld1q_u32(grid.as_ptr().add(16 * j + 4 * l))
                                });
                                let coset = lde(&h);
                                for j in 0..64 {
                                    vst1q_u32(
                                        grid.as_mut_ptr().add(16 * (64 + j) + 4 * l),
                                        coset[j],
                                    );
                                }
                            }
                        }
                        for (grid, members) in form_grids.iter_mut().zip(forms.iter()) {
                            grid[..64 * 4].fill(0);
                            for (op, idx) in members.iter() {
                                let src = base_grids[*idx as usize].as_ptr();
                                match op {
                                    FormOp::Add => {
                                        neon::soa_base_form_add_n::<64>(grid.as_mut_ptr(), src)
                                    }
                                    FormOp::Sub => {
                                        neon::soa_base_form_sub_n::<64>(grid.as_mut_ptr(), src)
                                    }
                                    FormOp::Mul(c) => neon::soa_base_form_muladd_n::<64>(
                                        grid.as_mut_ptr(),
                                        src,
                                        *(c as *const F as *const _),
                                    ),
                                }
                            }
                            let h: [uint32x4_t; 64] = core::array::from_fn(|j| {
                                vld1q_u32(grid.as_ptr().add(4 * j))
                            });
                            let coset = lde(&h);
                            for j in 0..64 {
                                vst1q_u32(grid.as_mut_ptr().add(4 * (64 + j)), coset[j]);
                            }
                        }

                        let mut lazy_products = 0usize;
                        macro_rules! lazy_tick {
                            () => {
                                lazy_products += 1;
                                if lazy_products == 2 {
                                    neon::soa_lazy_condsub::<128>(lazy_acc.as_mut_ptr());
                                    lazy_products = 0;
                                }
                            };
                        }
                        for (a, form, c) in products.iter() {
                            neon::soa_quad_bb_lazy::<128>(
                                lazy_acc.as_mut_ptr(),
                                base_grids[*a as usize].as_ptr(),
                                form_grids[*form as usize].as_ptr(),
                                ec(c),
                            );
                            lazy_tick!();
                        }
                        for step in rest_steps.iter() {
                            match step {
                                BenchStep::QuadBB { a, b, c } => {
                                    neon::soa_quad_bb_lazy::<128>(
                                        lazy_acc.as_mut_ptr(),
                                        base_grids[*a as usize].as_ptr(),
                                        base_grids[*b as usize].as_ptr(),
                                        ec(c),
                                    );
                                    lazy_tick!();
                                }
                                BenchStep::LinB { i, c } => {
                                    neon::soa_lin_base_all_n::<128>(
                                        lazy_acc.as_mut_ptr(),
                                        base_grids[*i as usize].as_ptr(),
                                        ec(c),
                                    );
                                    lazy_tick!();
                                }
                                BenchStep::QuadBE { base, ext, c } => {
                                    let cb = neon::soa_broadcast_ext(ec(c));
                                    neon::soa_quad_be::<128>(
                                        reduced.as_mut_ptr(),
                                        ext_grids[*ext as usize].as_ptr(),
                                        base_grids[*base as usize].as_ptr(),
                                        &cb,
                                        r11v,
                                    );
                                }
                                BenchStep::QuadEE { a, b, c } => {
                                    let cb = neon::soa_broadcast_ext(ec(c));
                                    neon::soa_quad_ee_n::<128>(
                                        reduced.as_mut_ptr(),
                                        ext_grids[*a as usize].as_ptr(),
                                        ext_grids[*b as usize].as_ptr(),
                                        &cb,
                                        r11v,
                                    );
                                }
                                BenchStep::LinE { i, c } => {
                                    let cb = neon::soa_broadcast_ext(ec(c));
                                    neon::soa_lin_ext_all_n::<128>(
                                        reduced.as_mut_ptr(),
                                        ext_grids[*i as usize].as_ptr(),
                                        &cb,
                                        r11v,
                                    );
                                }
                            }
                        }
                        if has_const {
                            neon::soa_add_const_all_n::<128>(reduced.as_mut_ptr(), &const_bcast);
                        }

                        neon::soa_lazy_finalize::<128>(
                            lazy_acc.as_mut_ptr(),
                            lazy_out.as_mut_ptr(),
                        );
                        let eq_soa = neon::soa_transpose_ext4(
                            precomputed_eq_suffix.as_ptr().add(row) as *const _,
                        );
                        neon::soa_apply_eq_and_accumulate::<128>(
                            acc_soa.as_mut_ptr(),
                            lazy_out.as_ptr(),
                            reduced.as_mut_ptr(),
                            &eq_soa,
                            r11v,
                        );
                    }

                    let mut out = [BabyBearExt4::ZERO; 128];
                    neon::soa_final_reduce_to_ext_n::<128>(acc_soa.as_ptr(), out.as_mut_ptr());
                    *acc_dst = *(&out as *const _ as *const [E; 128]);
                }
            })
        }
    });

    let mut acc = acc_chunks.pop().unwrap();
    for el in acc_chunks.into_iter() {
        for i in 0..128 {
            acc[i].add_assign(&el[i]);
        }
    }

    acc
}

/// Slot-schedule step for the tiled uniskip evaluator. Base-pool indices
/// < `num_base` are real polys; >= `num_base` are bracket forms (materialized
/// from source taps on load, so forms do not pin their member grids).
#[derive(Clone)]
pub enum TiledStep<E: Field> {
    LoadBase { slot: u16, idx: u16 },
    LoadExt { slot: u16, idx: u16 },
    /// combine the form's members from their RESIDENT grids (all 128 cells --
    /// LDE is linear, so the coset half combines directly) into `slot`
    BuildForm { slot: u16, form: u16, member_slots: Vec<u16> },
    QuadBB { sa: u16, sb: u16, c: E },
    QuadBE { sb: u16, se: u16, c: E },
    QuadEE { sa: u16, sb: u16, c: E },
    LinB { slot: u16, c: E },
    LinE { slot: u16, c: E },
}

pub struct TiledStats {
    pub num_clusters: usize,
    pub isolated_ops: usize,
    pub peak_base_live: usize,
    pub peak_ext_live: usize,
    pub base_loads: usize,
    pub ext_loads: usize,
    pub distinct_base: usize,
    pub distinct_ext: usize,
}

/// Clustered min-scratch schedule over the BRACKETED op set (products +
/// remainder + linears), with forms as virtual base-pool operands.
fn produce_tiled_uniskip_schedule<F: PrimeField, E: FieldExtension<F> + Field>(
    forms: &[Vec<(FormOp<F>, u16)>],
    products: &[(u16, u16, E)],
    rest_steps: &[BenchStep<E>],
    num_base: usize,
    base_cap: usize,
    ext_cap: usize,
) -> (Vec<TiledStep<E>>, TiledStats) {
    use std::collections::{BTreeMap, BTreeSet};
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
    enum Opnd {
        B(u16),
        X(u16),
    }
    #[derive(Clone)]
    enum Op<E> {
        Quad(Opnd, Opnd, E),
        Lin(Opnd, E),
        /// materialize form f from its members
        Build(u16),
    }
    let nb = num_base as u16;
    let mut ops: Vec<Op<E>> = vec![];
    // form builds first in the op universe (scheduled by the greedy wherever
    // cheapest, but always before the first product that uses the form)
    let build_op_of_form: Vec<usize> = (0..forms.len()).map(|f| f).collect();
    for f in 0..forms.len() {
        ops.push(Op::Build(f as u16));
    }
    let _ = &build_op_of_form;
    for (a, f, c) in products.iter() {
        ops.push(Op::Quad(Opnd::B(*a), Opnd::B(nb + *f), *c));
    }
    for step in rest_steps.iter() {
        match step {
            BenchStep::QuadBB { a, b, c } => ops.push(Op::Quad(Opnd::B(*a), Opnd::B(*b), *c)),
            BenchStep::QuadBE { base, ext, c } => {
                ops.push(Op::Quad(Opnd::B(*base), Opnd::X(*ext), *c))
            }
            BenchStep::QuadEE { a, b, c } => ops.push(Op::Quad(Opnd::X(*a), Opnd::X(*b), *c)),
            BenchStep::LinB { i, c } => ops.push(Op::Lin(Opnd::B(*i), *c)),
            BenchStep::LinE { i, c } => ops.push(Op::Lin(Opnd::X(*i), *c)),
        }
    }
    // Build ops list ALL member polys plus the produced form as operands, so
    // clustering/liveness keep members resident through the build and the
    // form resident through its products.
    let operands_of = |op: &Op<E>| -> Vec<Opnd> {
        match op {
            Op::Quad(a, b, _) => vec![Some(*a), Some(*b)].into_iter().flatten().collect(),
            Op::Lin(a, _) => vec![*a],
            Op::Build(f) => {
                let mut v: Vec<Opnd> = forms[*f as usize]
                    .iter()
                    .map(|(_, m)| Opnd::B(*m))
                    .collect();
                v.push(Opnd::B(nb + *f));
                v
            }
        }
    };

    // union-find clustering
    let n = ops.len();
    let mut parent: Vec<usize> = (0..n).collect();
    fn find(p: &mut Vec<usize>, mut x: usize) -> usize {
        while p[x] != x {
            p[x] = p[p[x]];
            x = p[x];
        }
        x
    }
    let mut first: BTreeMap<Opnd, usize> = BTreeMap::new();
    for (pos, op) in ops.iter().enumerate() {
        for o in operands_of(op).iter() {
            if let Some(&f0) = first.get(o) {
                let (ra, rb) = (find(&mut parent, f0), find(&mut parent, pos));
                if ra != rb {
                    parent[ra] = rb;
                }
            } else {
                first.insert(*o, pos);
            }
        }
    }
    let mut clusters: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    for pos in 0..n {
        let r = find(&mut parent, pos);
        clusters.entry(r).or_default().push(pos);
    }
    let mut cluster_list: Vec<Vec<usize>> = clusters.into_values().collect();
    cluster_list.sort_by_key(|c| (c.len(), c[0]));
    let isolated = cluster_list.iter().filter(|c| c.len() == 1).count();

    // greedy order + peak-live
    let mut remaining: BTreeMap<Opnd, usize> = BTreeMap::new();
    for op in ops.iter() {
        for o in operands_of(op).iter() {
            *remaining.entry(*o).or_default() += 1;
        }
    }
    let mut order: Vec<usize> = Vec::with_capacity(n);
    let mut live: BTreeSet<Opnd> = BTreeSet::new();
    let mut rem = remaining.clone();
    let (mut peak_b, mut peak_x) = (0usize, 0usize);
    let mut form_built = vec![false; forms.len()];
    for cluster in cluster_list.iter() {
        let mut pending = cluster.clone();
        while !pending.is_empty() {
            let mut best = usize::MAX;
            let mut best_key = (usize::MAX, 0usize, usize::MAX);
            for (i, &pos) in pending.iter().enumerate() {
                // a product/linear referencing an unbuilt form is not yet
                // schedulable
                let uses_unbuilt_form = operands_of(&ops[pos]).iter().any(|o| {
                    matches!(o, Opnd::B(v) if *v >= nb && !form_built[(*v - nb) as usize])
                }) && !matches!(ops[pos], Op::Build(_));
                if uses_unbuilt_form {
                    continue;
                }
                let mut new_loads = 0usize;
                let mut new_uses = 0usize;
                for o in operands_of(&ops[pos]).iter() {
                    if !live.contains(o) {
                        new_loads += 1;
                        new_uses += rem[o];
                    }
                }
                let key = (new_loads, usize::MAX - new_uses, pos);
                if key < best_key {
                    best_key = key;
                    best = i;
                }
            }
            assert!(best != usize::MAX, "no schedulable op (form dependency cycle?)");
            let pos = pending.swap_remove(best);
            if let Op::Build(f) = ops[pos] {
                form_built[f as usize] = true;
            }
            for o in operands_of(&ops[pos]).iter() {
                live.insert(*o);
            }
            peak_b = peak_b.max(live.iter().filter(|o| matches!(o, Opnd::B(_))).count());
            peak_x = peak_x.max(live.iter().filter(|o| matches!(o, Opnd::X(_))).count());
            for o in operands_of(&ops[pos]).iter() {
                let r = rem.get_mut(o).unwrap();
                *r -= 1;
                if *r == 0 {
                    live.remove(o);
                }
            }
            order.push(pos);
        }
    }

    // Belady slot assignment
    let mut uses: BTreeMap<Opnd, Vec<usize>> = BTreeMap::new();
    for (pos, &p) in order.iter().enumerate() {
        for o in operands_of(&ops[p]).iter() {
            uses.entry(*o).or_default().push(pos);
        }
    }
    let mut cursor: BTreeMap<Opnd, usize> = uses.keys().map(|k| (*k, 0usize)).collect();
    struct Pool {
        resident: Vec<Option<u16>>,
        loc: std::collections::BTreeMap<u16, u16>,
        loads: usize,
    }
    let mut bp = Pool {
        resident: vec![None; base_cap],
        loc: BTreeMap::new(),
        loads: 0,
    };
    let mut xp = Pool {
        resident: vec![None; ext_cap],
        loc: BTreeMap::new(),
        loads: 0,
    };
    let mut steps: Vec<TiledStep<E>> = vec![];
    for &p in order.iter() {
        // Build ops are handled specially: members must be resident (loaded on
        // demand), then the form gets a fresh slot; forms are never reloadable
        // (that would require re-running the build), so at sane capacities the
        // Belady policy must keep them resident through their last product.
        if let Op::Build(f) = ops[p] {
            let members = &forms[f as usize];
            let mut member_slots: Vec<u16> = Vec::with_capacity(members.len());
            for (_, m) in members.iter() {
                let idx = *m;
                if let Some(&sl) = bp.loc.get(&idx) {
                    member_slots.push(sl);
                    continue;
                }
                let sl = if let Some(free) = bp.resident.iter().position(|e| e.is_none()) {
                    free as u16
                } else {
                    let mut vs = u16::MAX;
                    let mut vd = 0usize;
                    for (sn, r) in bp.resident.iter().enumerate() {
                        let r = r.unwrap();
                        // never evict another member of this build, and never
                        // evict a live form
                        if members.iter().any(|(_, mm)| *mm == r) || r >= nb {
                            continue;
                        }
                        let ro = Opnd::B(r);
                        let d = {
                            let l = &uses[&ro];
                            let c = cursor[&ro];
                            if c < l.len() {
                                l[c]
                            } else {
                                usize::MAX
                            }
                        };
                        if d >= vd {
                            vd = d;
                            vs = sn as u16;
                        }
                    }
                    assert!(vs != u16::MAX, "base capacity too small for form build");
                    let ev = bp.resident[vs as usize].take().unwrap();
                    bp.loc.remove(&ev);
                    vs
                };
                bp.resident[sl as usize] = Some(idx);
                bp.loc.insert(idx, sl);
                bp.loads += 1;
                steps.push(TiledStep::LoadBase { slot: sl, idx });
                member_slots.push(sl);
            }
            // slot for the form itself
            let form_operand = nb + f;
            let sl = if let Some(free) = bp.resident.iter().position(|e| e.is_none()) {
                free as u16
            } else {
                let mut vs = u16::MAX;
                let mut vd = 0usize;
                for (sn, r) in bp.resident.iter().enumerate() {
                    let r = r.unwrap();
                    if members.iter().any(|(_, mm)| *mm == r) || r >= nb {
                        continue;
                    }
                    let ro = Opnd::B(r);
                    let d = {
                        let l = &uses[&ro];
                        let c = cursor[&ro];
                        if c < l.len() {
                            l[c]
                        } else {
                            usize::MAX
                        }
                    };
                    if d >= vd {
                        vd = d;
                        vs = sn as u16;
                    }
                }
                assert!(vs != u16::MAX, "base capacity too small for form slot");
                let ev = bp.resident[vs as usize].take().unwrap();
                bp.loc.remove(&ev);
                vs
            };
            bp.resident[sl as usize] = Some(form_operand);
            bp.loc.insert(form_operand, sl);
            steps.push(TiledStep::BuildForm {
                slot: sl,
                form: f,
                member_slots,
            });
            for o in operands_of(&ops[p]).iter() {
                *cursor.get_mut(o).unwrap() += 1;
            }
            continue;
        }

        let operands = operands_of(&ops[p]);
        let mut slots: [u16; 2] = [0; 2];
        for (i, o) in operands.iter().enumerate() {
            let o = o;
            let (pool, is_b, idx) = match o {
                Opnd::B(v) => (&mut bp, true, *v),
                Opnd::X(v) => (&mut xp, false, *v),
            };
            if let Some(&sl) = pool.loc.get(&idx) {
                slots[i] = sl;
                continue;
            }
            assert!(
                !(is_b && idx >= nb),
                "form {} evicted before its last use; increase base capacity",
                idx - nb
            );
            let protected: Option<u16> = operands.get(1 - i).and_then(|other| match (o, other) {
                (Opnd::B(_), Opnd::B(v)) => Some(*v),
                (Opnd::X(_), Opnd::X(v)) => Some(*v),
                _ => None,
            });
            let sl = if let Some(free) = pool.resident.iter().position(|e| e.is_none()) {
                free as u16
            } else {
                let mut vs = u16::MAX;
                let mut vd = 0usize;
                for (sn, r) in pool.resident.iter().enumerate() {
                    let r = r.unwrap();
                    if Some(r) == protected {
                        continue;
                    }
                    // a live form cannot be re-materialized by a plain load
                    if is_b && r >= nb {
                        let ro = Opnd::B(r);
                        let l = &uses[&ro];
                        if cursor[&ro] < l.len() {
                            continue;
                        }
                    }
                    let ro = if is_b { Opnd::B(r) } else { Opnd::X(r) };
                    let d = {
                        let l = &uses[&ro];
                        let c = cursor[&ro];
                        if c < l.len() {
                            l[c]
                        } else {
                            usize::MAX
                        }
                    };
                    if d >= vd {
                        vd = d;
                        vs = sn as u16;
                    }
                }
                let ev = pool.resident[vs as usize].take().unwrap();
                pool.loc.remove(&ev);
                vs
            };
            pool.resident[sl as usize] = Some(idx);
            pool.loc.insert(idx, sl);
            pool.loads += 1;
            steps.push(if is_b {
                TiledStep::LoadBase { slot: sl, idx }
            } else {
                TiledStep::LoadExt { slot: sl, idx }
            });
            slots[i] = sl;
        }
        for o in operands.iter() {
            *cursor.get_mut(o).unwrap() += 1;
        }
        match &ops[p] {
            Op::Build(_) => unreachable!("handled above"),
            Op::Quad(a, b, c) => match (a, b) {
                (Opnd::B(_), Opnd::B(_)) => steps.push(TiledStep::QuadBB {
                    sa: slots[0],
                    sb: slots[1],
                    c: *c,
                }),
                (Opnd::B(_), Opnd::X(_)) => steps.push(TiledStep::QuadBE {
                    sb: slots[0],
                    se: slots[1],
                    c: *c,
                }),
                (Opnd::X(_), Opnd::X(_)) => steps.push(TiledStep::QuadEE {
                    sa: slots[0],
                    sb: slots[1],
                    c: *c,
                }),
                _ => unreachable!("BE ops are ordered base-first"),
            },
            Op::Lin(a, c) => match a {
                Opnd::B(_) => steps.push(TiledStep::LinB { slot: slots[0], c: *c }),
                Opnd::X(_) => steps.push(TiledStep::LinE { slot: slots[0], c: *c }),
            },
        }
    }

    let stats = TiledStats {
        num_clusters: cluster_list.len(),
        isolated_ops: isolated,
        peak_base_live: peak_b.max(2),
        peak_ext_live: peak_x.max(2),
        base_loads: bp.loads,
        ext_loads: xp.loads,
        distinct_base: uses.keys().filter(|o| matches!(o, Opnd::B(_))).count(),
        distinct_ext: uses.keys().filter(|o| matches!(o, Opnd::X(_))).count(),
    };
    (steps, stats)
}

/// Tiled k=6 uniskip initial pass: grids live in a bounded slot pool and are
/// (re)materialized on the schedule's Load steps, so only
/// `base_cap * 2KB + ext_cap * 8KB` of grid scratch is hot at any time.
/// Forms are materialized directly from source taps (member reads + combine
/// on H, then LDE), so they do not pin member grids.
#[cfg(target_arch = "aarch64")]
fn evaluate_initial_uniskip64_tiled_soa_parallel<F: PrimeField, E: FieldExtension<F> + Field>(
    base_field_inputs: &[DisjointAccessQuasiSlice<F, false>],
    ext_field_inputs: &[DisjointAccessQuasiSlice<E, false>],
    forms: &[Vec<(FormOp<F>, u16)>],
    schedule: &[TiledStep<E>],
    base_cap: usize,
    ext_cap: usize,
    additive_constant: &E,
    lde_tables: &neon::SoaLde64Tables,
    precomputed_eq_suffix: &[E],
    input_size_log2: usize,
    worker: &Worker,
) -> [E; 128] {
    use crate::gkr::PAR_THRESHOLD;
    use ::field::baby_bear::ext4::BabyBearExt4;
    use core::arch::aarch64::{uint32x4_t, vld1q_u32, vst1q_u32};

    if const { !neon::is_bb_pair::<F, E>() } {
        unreachable!("uniskip variant is BabyBear/Ext4-specific");
    }
    let num_base = base_field_inputs.len();
    let work_size = (1 << input_size_log2) / 64;
    assert_eq!(precomputed_eq_suffix.len(), work_size);
    assert_eq!(work_size % 4, 0);
    let num_blocks = work_size / 4;
    let geometry = worker.get_geometry_with_threshold(num_blocks, PAR_THRESHOLD / 4);
    let mut acc_chunks = vec![[E::ZERO; 128]; geometry.num_chunks];

    worker.scope_with_threshold(num_blocks, PAR_THRESHOLD / 4, |scope, geometry| {
        let mut it = acc_chunks.iter_mut();
        for thread_idx in 0..geometry.num_chunks {
            let chunk_start = geometry.get_chunk_start_pos(thread_idx) * 4;
            let chunk_size = geometry.get_chunk_size(thread_idx) * 4;
            let base_field_inputs = base_field_inputs.to_vec();
            let ext_field_inputs = ext_field_inputs.to_vec();
            let lde_tables = *lde_tables;
            let acc_dst = it.next().unwrap();

            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                let input_size = 1 << input_size_log2;
                let ec = |c: &E| -> &BabyBearExt4 { unsafe { &*(c as *const E as *const _) } };
                let r11v = neon::soa_r11v();
                let const_bcast = unsafe { neon::soa_broadcast_ext(ec(additive_constant)) };
                let has_const = !additive_constant.is_zero();

                let mut base_slots = vec![[0u32; 128 * 4]; base_cap];
                let mut ext_slots = vec![[0u32; 128 * 16]; ext_cap];
                let mut lazy_acc = vec![0u64; 128 * 16];
                let mut lazy_out = vec![0u32; 128 * 16];
                let mut reduced = vec![0u32; 128 * 16];
                let mut acc_soa = vec![0u32; 128 * 16];

                unsafe {
                    for row in (chunk_start..(chunk_start + chunk_size)).step_by(4) {
                        let mut lazy_products = 0usize;
                        macro_rules! lazy_tick {
                            () => {
                                lazy_products += 1;
                                if lazy_products == 2 {
                                    neon::soa_lazy_condsub::<128>(lazy_acc.as_mut_ptr());
                                    lazy_products = 0;
                                }
                            };
                        }
                        for step in schedule.iter() {
                            match step {
                                TiledStep::LoadBase { slot, idx } => {
                                    let grid = base_slots[*slot as usize].as_mut_ptr();
                                    let h = neon::soa_read_base_block64(
                                        base_field_inputs[*idx as usize].ptr as *const _,
                                        input_size,
                                        row,
                                    );
                                    let coset = neon::soa_lde64_r2(&h, &lde_tables);
                                    for j in 0..64 {
                                        vst1q_u32(grid.add(4 * j), h[j]);
                                        vst1q_u32(grid.add(4 * (64 + j)), coset[j]);
                                    }
                                }
                                TiledStep::BuildForm {
                                    slot,
                                    form,
                                    member_slots,
                                } => {
                                    // LDE is linear: combine members' full
                                    // 128-cell grids straight from L1 -- no
                                    // source reads, no form LDE
                                    let dst = base_slots[*slot as usize].as_mut_ptr();
                                    core::ptr::write_bytes(dst, 0, 128 * 4);
                                    for ((op, _), msl) in
                                        forms[*form as usize].iter().zip(member_slots.iter())
                                    {
                                        let src = base_slots[*msl as usize].as_ptr();
                                        match op {
                                            FormOp::Add => neon::soa_base_form_add_n::<128>(
                                                dst, src,
                                            ),
                                            FormOp::Sub => neon::soa_base_form_sub_n::<128>(
                                                dst, src,
                                            ),
                                            FormOp::Mul(c) => {
                                                neon::soa_base_form_muladd_n::<128>(
                                                    dst,
                                                    src,
                                                    *(c as *const F as *const _),
                                                )
                                            }
                                        }
                                    }
                                }
                                TiledStep::LoadExt { slot, idx } => {
                                    let grid = ext_slots[*slot as usize].as_mut_ptr();
                                    let step_sz = input_size / 64;
                                    let base = ext_field_inputs[*idx as usize].ptr
                                        as *const BabyBearExt4;
                                    for j in 0..64usize {
                                        let mut off = row;
                                        for bit in 0..6 {
                                            if (j >> bit) & 1 == 1 {
                                                off += step_sz << bit;
                                            }
                                        }
                                        let limbs = neon::soa_transpose_ext4(base.add(off));
                                        neon::soa_store_cell(grid.add(16 * j), &limbs);
                                    }
                                    for l in 0..4usize {
                                        let h: [uint32x4_t; 64] = core::array::from_fn(|j| {
                                            vld1q_u32(
                                                ext_slots[*slot as usize]
                                                    .as_ptr()
                                                    .add(16 * j + 4 * l),
                                            )
                                        });
                                        let coset = neon::soa_lde64_r2(&h, &lde_tables);
                                        for j in 0..64 {
                                            vst1q_u32(
                                                ext_slots[*slot as usize]
                                                    .as_mut_ptr()
                                                    .add(16 * (64 + j) + 4 * l),
                                                coset[j],
                                            );
                                        }
                                    }
                                }
                                TiledStep::QuadBB { sa, sb, c } => {
                                    neon::soa_quad_bb_lazy::<128>(
                                        lazy_acc.as_mut_ptr(),
                                        base_slots[*sa as usize].as_ptr(),
                                        base_slots[*sb as usize].as_ptr(),
                                        ec(c),
                                    );
                                    lazy_tick!();
                                }
                                TiledStep::LinB { slot, c } => {
                                    neon::soa_lin_base_all_n::<128>(
                                        lazy_acc.as_mut_ptr(),
                                        base_slots[*slot as usize].as_ptr(),
                                        ec(c),
                                    );
                                    lazy_tick!();
                                }
                                TiledStep::QuadBE { sb, se, c } => {
                                    let cb = neon::soa_broadcast_ext(ec(c));
                                    neon::soa_quad_be::<128>(
                                        reduced.as_mut_ptr(),
                                        ext_slots[*se as usize].as_ptr(),
                                        base_slots[*sb as usize].as_ptr(),
                                        &cb,
                                        r11v,
                                    );
                                }
                                TiledStep::QuadEE { sa, sb, c } => {
                                    let cb = neon::soa_broadcast_ext(ec(c));
                                    neon::soa_quad_ee_n::<128>(
                                        reduced.as_mut_ptr(),
                                        ext_slots[*sa as usize].as_ptr(),
                                        ext_slots[*sb as usize].as_ptr(),
                                        &cb,
                                        r11v,
                                    );
                                }
                                TiledStep::LinE { slot, c } => {
                                    let cb = neon::soa_broadcast_ext(ec(c));
                                    neon::soa_lin_ext_all_n::<128>(
                                        reduced.as_mut_ptr(),
                                        ext_slots[*slot as usize].as_ptr(),
                                        &cb,
                                        r11v,
                                    );
                                }
                            }
                        }
                        if has_const {
                            neon::soa_add_const_all_n::<128>(reduced.as_mut_ptr(), &const_bcast);
                        }
                        neon::soa_lazy_finalize::<128>(
                            lazy_acc.as_mut_ptr(),
                            lazy_out.as_mut_ptr(),
                        );
                        let eq_soa = neon::soa_transpose_ext4(
                            precomputed_eq_suffix.as_ptr().add(row) as *const _,
                        );
                        neon::soa_apply_eq_and_accumulate::<128>(
                            acc_soa.as_mut_ptr(),
                            lazy_out.as_ptr(),
                            reduced.as_mut_ptr(),
                            &eq_soa,
                            r11v,
                        );
                    }

                    let mut out = [BabyBearExt4::ZERO; 128];
                    neon::soa_final_reduce_to_ext_n::<128>(acc_soa.as_ptr(), out.as_mut_ptr());
                    *acc_dst = *(&out as *const _ as *const [E; 128]);
                }
            })
        }
    });

    let mut acc = acc_chunks.pop().unwrap();
    for el in acc_chunks.into_iter() {
        for i in 0..128 {
            acc[i].add_assign(&el[i]);
        }
    }

    acc
}

/// Entry point called from the test. `layer` must be a same-size (non
/// dimension-reducing) layer, typically layer 0, with `gkr_storage` populated by
/// the forward pass.
pub fn run_windowed_sumcheck_benchmarks<F: PrimeField, E: FieldExtension<F> + Field>(
    layer: &GKRLayerDescription<F>,
    layer_idx: usize,
    gkr_storage: &mut GKRStorage<F, E>,
    external_challenges: &GKRExternalChallenges<F, E>,
    lookup_challenges_multiplicative_part: E,
    lookup_challenges_additive_part: E,
    trace_len: usize,
    iters: usize,
    worker: &Worker,
) where
    [(); E::DEGREE]: Sized,
{
    assert!(trace_len.is_power_of_two());
    let folding_steps = trace_len.trailing_zeros() as usize;
    assert!(folding_steps >= 7);

    bench_scope_spawn_overhead(worker);

    let batching_challenge = pseudo_challenge::<F, E>(7);
    let collector = KernelCollector::from_layer(
        layer,
        layer_idx,
        batching_challenge,
        lookup_challenges_multiplicative_part,
        lookup_challenges_additive_part,
        &[],
        0,
    );
    let challenge_constants = BatchedGKRTermDescriptionConstants::<F, E> {
        external_challenges: *external_challenges,
        lookup_challenges_multiplicative_part,
        lookup_challenges_additive_part,
        _marker: core::marker::PhantomData,
    };
    let description = collector.make_batched_description(&challenge_constants, layer_idx);

    let num_bb: usize = description
        .quadratic_part_base_by_base
        .iter()
        .map(|(_, v)| v.len())
        .sum();
    let num_be: usize = description
        .quadratic_part_base_by_ext
        .iter()
        .map(|(_, v)| v.len())
        .sum();
    let num_ee: usize = description
        .quadratic_part_ext_by_ext
        .iter()
        .map(|(_, v)| v.len())
        .sum();
    println!("==== windowed sumcheck benchmark: layer {layer_idx}, trace 2^{folding_steps} ====");
    println!(
        "term counts: base*base = {}, base*ext = {}, ext*ext = {}, linear base = {}, linear ext = {}, outputs base = {}, outputs ext = {}",
        num_bb,
        num_be,
        num_ee,
        description.linear_part_base_by_everything.len(),
        description.linear_part_ext_by_everything.len(),
        description.outputs_in_base.len(),
        description.outputs_in_ext.len(),
    );

    let (desc_bbbe, desc_ee) = split_batched_description(&description);

    let (compact_all, base_polys_all, ext_polys_all) =
        produce_descriptions_from_batched_description(&description);
    let (compact_bbbe, base_polys_bbbe, ext_polys_bbbe) =
        produce_descriptions_from_batched_description(&desc_bbbe);
    let (compact_ee, base_polys_ee, ext_polys_ee) =
        produce_descriptions_from_batched_description(&desc_ee);
    assert!(base_polys_ee.is_empty());

    println!(
        "distinct sources: all = {} base + {} ext; bb/be part = {} base + {} ext; ee part = {} ext",
        base_polys_all.len(),
        ext_polys_all.len(),
        base_polys_bbbe.len(),
        ext_polys_bbbe.len(),
        ext_polys_ee.len(),
    );

    let prev_challenges: Vec<E> = (0..folding_steps)
        .map(|i| pseudo_challenge::<F, E>(1000 + i as u32))
        .collect();
    let eq_tables = make_eq_poly_in_full::<E>(&prev_challenges, worker);

    // fixed folding challenges for every round (the first three are the
    // in-window challenges, the fourth the transition-round challenge)
    let window_challenges: Vec<E> = (0..folding_steps as u32)
        .map(|i| pseudo_challenge::<F, E>(2000 + i))
        .collect();

    let eq_suffix_initial = find_eq_with_len(&eq_tables, trace_len / 8);

    // ---------------- variant A: window 3, all terms, full-size scratch ----------------
    let base_sources_all = collect_base_sources(gkr_storage, &base_polys_all);
    let ext_sources_all = collect_ext_sources(gkr_storage, &ext_polys_all);

    let mut acc_all = [E::ZERO; 27];
    let mut best_a = std::time::Duration::MAX;
    for _ in 0..iters {
        let now = std::time::Instant::now();
        acc_all = evaluate_initial_with_full_sized_scratch_parallel(
            base_sources_all.clone(),
            ext_sources_all.clone(),
            &compact_all,
            eq_suffix_initial,
            folding_steps,
            worker,
        );
        best_a = best_a.min(now.elapsed());
    }
    println!(
        "[A] window-3 rounds 0-2, ALL terms, full-size scratch: {:?}",
        best_a
    );

    // ---------------- phase split: reads vs control flow vs compute ----------------
    let (base_interp, ext_interp, forms, products, rest_steps, folded_quad, folded_lin) = {
        // interpolation flags recomputed from the description (mirrors
        // produce_descriptions_from_batched_description)
        use std::collections::BTreeSet;
        let mut base_quad: BTreeSet<GKRAddress> = BTreeSet::new();
        let mut ext_quad: BTreeSet<GKRAddress> = BTreeSet::new();
        for (a, list) in description.quadratic_part_base_by_base.iter() {
            base_quad.insert(*a);
            for (b, _) in list.iter() {
                base_quad.insert(*b);
            }
        }
        for (a, list) in description.quadratic_part_base_by_ext.iter() {
            base_quad.insert(*a);
            for (b, _) in list.iter() {
                ext_quad.insert(*b);
            }
        }
        for (a, list) in description.quadratic_part_ext_by_ext.iter() {
            ext_quad.insert(*a);
            for (b, _) in list.iter() {
                ext_quad.insert(*b);
            }
        }
        let base_interp: Vec<bool> = base_polys_all.iter().map(|a| base_quad.contains(a)).collect();
        let ext_interp: Vec<bool> = ext_polys_all.iter().map(|a| ext_quad.contains(a)).collect();

        let bidx = |addr: &GKRAddress| base_polys_all.iter().position(|el| el == addr).unwrap() as u16;
        let eidx = |addr: &GKRAddress| ext_polys_all.iter().position(|el| el == addr).unwrap() as u16;

        let mut stub_steps: Vec<StubStep> = vec![];
        let mut ci = 0u32;
        for (a, list) in description.quadratic_part_base_by_base.iter() {
            for (b, _) in list.iter() {
                stub_steps.push(StubStep::Bb(bidx(a), bidx(b), ci));
                ci += 1;
            }
        }
        for (a, list) in description.quadratic_part_base_by_ext.iter() {
            for (b, _) in list.iter() {
                stub_steps.push(StubStep::Be(bidx(a), eidx(b), ci));
                ci += 1;
            }
        }
        for (a, list) in description.quadratic_part_ext_by_ext.iter() {
            for (b, _) in list.iter() {
                stub_steps.push(StubStep::Ee(eidx(a), eidx(b), ci));
                ci += 1;
            }
        }
        for (a, _) in description.linear_part_base_by_everything.iter() {
            stub_steps.push(StubStep::LinB(bidx(a), ci));
            ci += 1;
        }
        for (a, _) in description.linear_part_ext_by_everything.iter() {
            stub_steps.push(StubStep::LinE(eidx(a), ci));
            ci += 1;
        }

        let mut best_reads = std::time::Duration::MAX;
        let mut best_stub = std::time::Duration::MAX;
        let mut token = 0u64;
        for _ in 0..iters {
            let now = std::time::Instant::now();
            token = token.wrapping_add(bench_initial_phase_split(
                &base_sources_all,
                &ext_sources_all,
                &base_interp,
                &ext_interp,
                None,
                folding_steps,
                worker,
            ));
            best_reads = best_reads.min(now.elapsed());
            let now = std::time::Instant::now();
            token = token.wrapping_add(bench_initial_phase_split(
                &base_sources_all,
                &ext_sources_all,
                &base_interp,
                &ext_interp,
                Some(&stub_steps),
                folding_steps,
                worker,
            ));
            best_stub = best_stub.min(now.elapsed());
        }
        std::hint::black_box(token);
        println!(
            "[P] initial-window phase split: fill+extrapolate {:?}; +stubbed dispatch ({} steps) {:?}; full [A] {:?} -> control flow ~{:?}, compute ~{:?}",
            best_reads,
            stub_steps.len(),
            best_stub,
            best_a,
            best_stub.saturating_sub(best_reads),
            best_a.saturating_sub(best_stub),
        );

        // finer split: reads without extrapolation, and base-only / ext-only
        let no_interp_base = vec![false; base_interp.len()];
        let no_interp_ext = vec![false; ext_interp.len()];
        let mut best_reads_no_interp = std::time::Duration::MAX;
        let mut best_reads_base_only = std::time::Duration::MAX;
        let mut best_reads_ext_only = std::time::Duration::MAX;
        let mut token = 0u64;
        for _ in 0..iters {
            let now = std::time::Instant::now();
            token = token.wrapping_add(bench_initial_phase_split(
                &base_sources_all,
                &ext_sources_all,
                &no_interp_base,
                &no_interp_ext,
                None,
                folding_steps,
                worker,
            ));
            best_reads_no_interp = best_reads_no_interp.min(now.elapsed());
            let now = std::time::Instant::now();
            token = token.wrapping_add(bench_initial_phase_split::<F, E>(
                &base_sources_all,
                &[],
                &base_interp,
                &[],
                None,
                folding_steps,
                worker,
            ));
            best_reads_base_only = best_reads_base_only.min(now.elapsed());
            let now = std::time::Instant::now();
            token = token.wrapping_add(bench_initial_phase_split::<F, E>(
                &[],
                &ext_sources_all,
                &[],
                &ext_interp,
                None,
                folding_steps,
                worker,
            ));
            best_reads_ext_only = best_reads_ext_only.min(now.elapsed());
        }
        std::hint::black_box(token);
        println!(
            "[P2] fill breakdown: raw reads (8 cells, no extrapolation) {:?}; extrapolation ~{:?}; base polys only {:?}; ext polys only {:?}",
            best_reads_no_interp,
            best_reads.saturating_sub(best_reads_no_interp),
            best_reads_base_only,
            best_reads_ext_only,
        );

        // ---------------- bracket-preserving initial window ----------------
        use crate::gkr::prover::sumcheck_loop::kernel_collector::KernelVariant;

        let mut forms: Vec<Vec<(FormOp<F>, u16)>> = vec![];
        let mut form_key_to_idx: BTreeMap<Vec<(u128, u16)>, u16> = BTreeMap::new();
        let mut products: Vec<(u16, u16, E)> = vec![];
        let mut subtract: BTreeMap<(GKRAddress, GKRAddress), E> = BTreeMap::new();
        let mut preserved_monomials = 0usize;

        for kernel in collector.kernels.iter() {
            let KernelVariant::EnforceSingleMaxQuadraticConstraint(rel, ch) = kernel else {
                continue;
            };
            let challenge = ch[0];
            for (a, bracket) in rel.relation.quadratic_terms.iter() {
                let members: Vec<(F, GKRAddress)> = bracket
                    .iter()
                    .filter(|(c, _)| !c.is_zero())
                    .copied()
                    .collect();
                if members.len() < 2 {
                    continue;
                }
                preserved_monomials += members.len();
                for (c, b) in members.iter() {
                    let pair = if *a <= *b { (*a, *b) } else { (*b, *a) };
                    let mut contribution = challenge;
                    contribution.mul_assign_by_base(c);
                    subtract
                        .entry(pair)
                        .or_insert(E::ZERO)
                        .add_assign(&contribution);
                }
                let mut key: Vec<(u128, u16)> = members
                    .iter()
                    .map(|(c, b)| (c.as_u128_reduced(), bidx(b)))
                    .collect();
                key.sort();
                let form_idx = *form_key_to_idx.entry(key).or_insert_with(|| {
                    let ops: Vec<(FormOp<F>, u16)> = members
                        .iter()
                        .map(|(c, b)| {
                            let op = if *c == F::ONE {
                                FormOp::Add
                            } else if *c == F::MINUS_ONE {
                                FormOp::Sub
                            } else {
                                FormOp::Mul(*c)
                            };
                            (op, bidx(b))
                        })
                        .collect();
                    forms.push(ops);
                    (forms.len() - 1) as u16
                });
                products.push((bidx(a), form_idx, challenge));
            }
        }

        // expanded remainder: subtract the preserved brackets' contributions
        let mut rest_steps: Vec<BenchStep<E>> = vec![];
        let mut removed = 0usize;
        for (a, list) in description.quadratic_part_base_by_base.iter() {
            for (b, c) in list.iter() {
                let mut c = *c;
                if let Some(sub) = subtract.get(&(*a, *b)) {
                    c.sub_assign(sub);
                }
                if c.is_zero() {
                    removed += 1;
                    continue;
                }
                rest_steps.push(BenchStep::QuadBB {
                    a: bidx(a),
                    b: bidx(b),
                    c,
                });
            }
        }
        for (a, list) in description.quadratic_part_base_by_ext.iter() {
            for (b, c) in list.iter() {
                rest_steps.push(BenchStep::QuadBE {
                    base: bidx(a),
                    ext: eidx(b),
                    c: *c,
                });
            }
        }
        for (a, list) in description.quadratic_part_ext_by_ext.iter() {
            for (b, c) in list.iter() {
                rest_steps.push(BenchStep::QuadEE {
                    a: eidx(a),
                    b: eidx(b),
                    c: *c,
                });
            }
        }
        for (a, c) in description.linear_part_base_by_everything.iter() {
            rest_steps.push(BenchStep::LinB { i: bidx(a), c: *c });
        }
        for (a, c) in description.linear_part_ext_by_everything.iter() {
            rest_steps.push(BenchStep::LinE { i: eidx(a), c: *c });
        }

        let total_members: usize = forms.iter().map(|f| f.len()).sum();
        println!(
            "bracket program: {} preserved products over {} distinct forms ({} members), {} expanded monomials removed ({} preserved), rest steps {}",
            products.len(),
            forms.len(),
            total_members,
            removed,
            preserved_monomials,
            rest_steps.len(),
        );

        let mut acc_bracket = [E::ZERO; 27];
        let mut best_bracket = std::time::Duration::MAX;
        for _ in 0..iters {
            let now = std::time::Instant::now();
            acc_bracket = evaluate_initial_bracket_parallel(
                &base_sources_all,
                &ext_sources_all,
                &base_interp,
                &ext_interp,
                &forms,
                &products,
                &rest_steps,
                &description.constant_term,
                eq_suffix_initial,
                folding_steps,
                worker,
            );
            best_bracket = best_bracket.min(now.elapsed());
        }
        assert_acc_eq(&acc_bracket, &acc_all, "bracket-preserving vs expanded");
        println!(
            "[BR] window-3 rounds 0-2, bracket-preserving max-quad gates: {:?} (expanded [A]: {:?})",
            best_bracket, best_a,
        );

        // ---------------- SoA row-blocked evaluator ----------------
        #[cfg(target_arch = "aarch64")]
        {
            let mut full_steps: Vec<BenchStep<E>> = vec![];
            for (a, list) in description.quadratic_part_base_by_base.iter() {
                for (b, c) in list.iter() {
                    full_steps.push(BenchStep::QuadBB {
                        a: bidx(a),
                        b: bidx(b),
                        c: *c,
                    });
                }
            }
            for (a, list) in description.quadratic_part_base_by_ext.iter() {
                for (b, c) in list.iter() {
                    full_steps.push(BenchStep::QuadBE {
                        base: bidx(a),
                        ext: eidx(b),
                        c: *c,
                    });
                }
            }
            for (a, list) in description.quadratic_part_ext_by_ext.iter() {
                for (b, c) in list.iter() {
                    full_steps.push(BenchStep::QuadEE {
                        a: eidx(a),
                        b: eidx(b),
                        c: *c,
                    });
                }
            }
            for (a, c) in description.linear_part_base_by_everything.iter() {
                full_steps.push(BenchStep::LinB { i: bidx(a), c: *c });
            }
            for (a, c) in description.linear_part_ext_by_everything.iter() {
                full_steps.push(BenchStep::LinE { i: eidx(a), c: *c });
            }

            let mut acc_soa_variant = [E::ZERO; 27];
            let mut best_soa = std::time::Duration::MAX;
            for _ in 0..iters {
                let now = std::time::Instant::now();
                acc_soa_variant = evaluate_initial_soa_parallel(
                    &base_sources_all,
                    &ext_sources_all,
                    &base_interp,
                    &ext_interp,
                    &[],
                    &[],
                    &full_steps,
                    &description.constant_term,
                    eq_suffix_initial,
                    folding_steps,
                    worker,
                );
                best_soa = best_soa.min(now.elapsed());
            }
            assert_acc_eq(&acc_soa_variant, &acc_all, "SoA row-blocked vs expanded");
            println!(
                "[S] window-3 rounds 0-2, SoA row-blocked (4 rows/vector): {:?} (expanded [A]: {:?}, bracket [BR]: {:?})",
                best_soa, best_a, best_bracket,
            );

            // SoA + bracket-preserving combined
            let mut acc_sb = [E::ZERO; 27];
            let mut best_sb = std::time::Duration::MAX;
            for _ in 0..iters {
                let now = std::time::Instant::now();
                acc_sb = evaluate_initial_soa_parallel(
                    &base_sources_all,
                    &ext_sources_all,
                    &base_interp,
                    &ext_interp,
                    &forms,
                    &products,
                    &rest_steps,
                    &description.constant_term,
                    eq_suffix_initial,
                    folding_steps,
                    worker,
                );
                best_sb = best_sb.min(now.elapsed());
            }
            assert_acc_eq(&acc_sb, &acc_all, "SoA + brackets vs expanded");
            println!(
                "[SB] window-3 rounds 0-2, SoA + bracket-preserving: {:?} (SoA expanded [S]: {:?})",
                best_sb, best_soa,
            );

            // ---------------- uniskip (k = 3) initial round ----------------
            {
                use ::field::baby_bear::base::BabyBearField;
                let omega16_bb = ::fft::domain_generator_for_size::<BabyBearField>(16);
                let mut omega8_bb = omega16_bb;
                omega8_bb.square();
                let lde_tables = neon::SoaLde8Tables::new(omega8_bb, omega16_bb);

                let mut acc_u = [E::ZERO; 16];
                let mut best_u = std::time::Duration::MAX;
                for _ in 0..iters {
                    let now = std::time::Instant::now();
                    acc_u = evaluate_initial_uniskip_soa_parallel(
                        &base_sources_all,
                        &ext_sources_all,
                        &forms,
                        &products,
                        &rest_steps,
                        &description.constant_term,
                        &lde_tables,
                        eq_suffix_initial,
                        folding_steps,
                        worker,
                    );
                    best_u = best_u.min(now.elapsed());
                }

                // H-identity: the eq-weighted sum of q over H must equal the
                // eq-weighted sum of the window accumulator's binary cells
                let eq8 = make_eq_poly_in_full::<E>(&prev_challenges[..3], worker)
                    .pop()
                    .unwrap();
                let mut lhs = E::ZERO;
                let mut rhs = E::ZERO;
                for j in 0..8usize {
                    let mut t = eq8[j];
                    t.mul_assign(&acc_u[j]);
                    lhs.add_assign(&t);
                    let cell = 9 * (j >> 2) + 3 * ((j >> 1) & 1) + (j & 1);
                    let mut t = eq8[j];
                    t.mul_assign(&acc_all[cell]);
                    rhs.add_assign(&t);
                }
                assert_eq!(lhs, rhs, "uniskip H-domain eq-weighted sum vs window accumulator");
                println!(
                    "[U] uniskip k=3 initial (16-point q, bracketed): {:?} (window-3 SoA+brackets [SB]: {:?})",
                    best_u, best_sb,
                );
                println!("validation: uniskip q matches window accumulator on the H domain");

                // -------- uniskip k=6, size-64 NTT (radix-2 vs radix-8) --------
                let omega128_bb = ::fft::domain_generator_for_size::<BabyBearField>(128);
                let mut omega64_bb = omega128_bb;
                omega64_bb.square();
                let lde64_tables = neon::SoaLde64Tables::new(omega64_bb, omega128_bb);
                let eq_suffix_64 = find_eq_with_len(&eq_tables, trace_len / 64);

                // standalone NTT micro-benchmark
                {
                    use core::arch::aarch64::{uint32x4_t, vdupq_n_u32};
                    let dummy: [uint32x4_t; 64] =
                        core::array::from_fn(|i| unsafe { vdupq_n_u32(i as u32 + 1) });
                    let iters_ntt = 200_000u32;
                    let now = std::time::Instant::now();
                    let mut sink = dummy;
                    for _ in 0..iters_ntt {
                        sink = unsafe { neon::soa_lde64_r2(&sink, &lde64_tables) };
                    }
                    std::hint::black_box(&sink);
                    let t_r2 = now.elapsed() / iters_ntt;
                    let now = std::time::Instant::now();
                    let mut sink = dummy;
                    for _ in 0..iters_ntt {
                        sink = unsafe { neon::soa_lde64_r8(&sink, &lde64_tables) };
                    }
                    std::hint::black_box(&sink);
                    let t_r8 = now.elapsed() / iters_ntt;
                    println!(
                        "[NTT64] lde64 micro: radix-2 {:?}/call, radix-8 {:?}/call (4 lanes each)",
                        t_r2, t_r8
                    );
                }

                let mut acc_u64_r2 = [E::ZERO; 128];
                let mut best_u64_r2 = std::time::Duration::MAX;
                for _ in 0..iters {
                    let now = std::time::Instant::now();
                    acc_u64_r2 = evaluate_initial_uniskip64_soa_parallel(
                        &base_sources_all,
                        &ext_sources_all,
                        &forms,
                        &products,
                        &rest_steps,
                        &description.constant_term,
                        &lde64_tables,
                        false,
                        eq_suffix_64,
                        folding_steps,
                        worker,
                    );
                    best_u64_r2 = best_u64_r2.min(now.elapsed());
                }
                let mut acc_u64_r8 = [E::ZERO; 128];
                let mut best_u64_r8 = std::time::Duration::MAX;
                for _ in 0..iters {
                    let now = std::time::Instant::now();
                    acc_u64_r8 = evaluate_initial_uniskip64_soa_parallel(
                        &base_sources_all,
                        &ext_sources_all,
                        &forms,
                        &products,
                        &rest_steps,
                        &description.constant_term,
                        &lde64_tables,
                        true,
                        eq_suffix_64,
                        folding_steps,
                        worker,
                    );
                    best_u64_r8 = best_u64_r8.min(now.elapsed());
                }
                for i in 0..128 {
                    assert_eq!(
                        acc_u64_r2[i], acc_u64_r8[i],
                        "radix-2 vs radix-8 accumulator divergence at point {}",
                        i
                    );
                }
                // claim identity: eq6-weighted sum over H64 must equal the
                // eq3-weighted sum over H8 (both equal the full-cube claim)
                let eq64 = make_eq_poly_in_full::<E>(&prev_challenges[..6], worker)
                    .pop()
                    .unwrap();
                let mut lhs64 = E::ZERO;
                for j in 0..64usize {
                    let mut t = eq64[j];
                    t.mul_assign(&acc_u64_r2[j]);
                    lhs64.add_assign(&t);
                }
                assert_eq!(lhs64, lhs, "uniskip k=6 H-domain claim vs k=3");
                println!(
                    "[U64] uniskip k=6 initial (128-point q, bracketed): radix-2 {:?}, radix-8 {:?} (k=3 [U]: {:?}, window [SB]: {:?})",
                    best_u64_r2, best_u64_r8, best_u, best_sb,
                );
                println!("validation: k=6 radix variants bit-identical; H64 claim matches k=3");

                // -------- tiled k=6: clustered schedule, bounded slot pools --------
                let (_, tstats) = produce_tiled_uniskip_schedule::<F, E>(
                    &forms,
                    &products,
                    &rest_steps,
                    base_polys_all.len(),
                    64,
                    8,
                );
                println!(
                    "[U64T] bracketed DAG: {} clusters, {} isolated; zero-recompute capacity {} base(+forms) / {} ext slots",
                    tstats.num_clusters,
                    tstats.isolated_ops,
                    tstats.peak_base_live,
                    tstats.peak_ext_live,
                );
                for (bcap, ecap) in [
                    (tstats.peak_base_live, tstats.peak_ext_live),
                    (tstats.peak_base_live + 4, tstats.peak_ext_live + 2),
                ] {
                    let (schedule, st) = produce_tiled_uniskip_schedule::<F, E>(
                        &forms,
                        &products,
                        &rest_steps,
                        base_polys_all.len(),
                        bcap,
                        ecap,
                    );
                    let mut acc_t = [E::ZERO; 128];
                    let mut best_t64 = std::time::Duration::MAX;
                    for _ in 0..iters {
                        let now = std::time::Instant::now();
                        acc_t = evaluate_initial_uniskip64_tiled_soa_parallel(
                            &base_sources_all,
                            &ext_sources_all,
                            &forms,
                            &schedule,
                            bcap,
                            ecap,
                            &description.constant_term,
                            &lde64_tables,
                            eq_suffix_64,
                            folding_steps,
                            worker,
                        );
                        best_t64 = best_t64.min(now.elapsed());
                    }
                    for i in 0..128 {
                        assert_eq!(
                            acc_t[i], acc_u64_r2[i],
                            "tiled k=6 accumulator divergence at point {}",
                            i
                        );
                    }
                    println!(
                        "[U64T] tiled k=6 {}b/{}e slots (grid loads {} base / {} distinct, {} ext): {:?} (untiled [U64]: {:?}, k=3 [U]: {:?}, [SB]: {:?})",
                        bcap,
                        ecap,
                        st.base_loads,
                        st.distinct_base,
                        st.ext_loads,
                        best_t64,
                        best_u64_r2,
                        best_u,
                        best_sb,
                    );
                }
                println!("validation: tiled k=6 accumulator bit-identical to untiled");

                // ---- LSB-binding artificial test (contiguous taps, SoA engine) ----
                {
                    use super::lsb_bench::{
                        self, LsbLdeAny, PH_ALL, PH_EXT, PH_FILL_BASE, PH_FILL_EXT, PH_FORMS,
                        PH_LAZY,
                    };

                    // eq split for the LSB convention.
                    //
                    // The MSB phases weight trace index i with
                    //   W(i) = eq8[top 3 bits of i] * eqs[low 21 bits of i]
                    // and both factors are eq tables, i.e. products of one
                    // factor per BIT. A per-bit product can be regrouped around
                    // any bit boundary, in particular around the LOW k bits:
                    //
                    //     i (24 bits):  [ suffix bits (row) | low k bits (j) ]
                    //     W(i)       =        T_k[row]      *     w_k[j]
                    //
                    // so the LSB evaluators can use w_k as the window weight
                    // and T_k as the per-row suffix table while producing the
                    // SAME total claim as the MSB phases -- that is what the
                    // cross-family `lhs` assertions below rely on. Extraction:
                    // w_k[j] = eqs[j]/eqs[0] strips the suffix part off the
                    // low-bit entries, and T_k[row] regains the eq8 factor for
                    // the top 3 bits plus the remaining eqs bits.
                    let eqs = eq_suffix_initial;
                    let inv0 = eqs[0].inverse().expect("eq entry invertible");
                    let normed = |j: usize| {
                        let mut t = eqs[j];
                        t.mul_assign(&inv0);
                        t
                    };
                    let w3_lsb: Vec<E> = (0..8).map(normed).collect();
                    let w6_lsb: Vec<E> = (0..64).map(normed).collect();
                    let rows8 = trace_len / 8;
                    let sub8 = rows8 / 8;
                    let t8: Vec<E> = (0..rows8)
                        .map(|row| {
                            let mut t = eq8[row / sub8];
                            t.mul_assign(&eqs[(row % sub8) * 8]);
                            t
                        })
                        .collect();
                    let rows64 = trace_len / 64;
                    let sub64 = rows64 / 8;
                    let t64: Vec<E> = (0..rows64)
                        .map(|row| {
                            let mut t = eq8[row / sub64];
                            t.mul_assign(&eqs[(row % sub64) * 64]);
                            t
                        })
                        .collect();

                    let lsb8_tables =
                        LsbLdeAny::K8(neon::LsbLde8Tables::new(omega8_bb, omega16_bb));
                    let lsb64_tables =
                        LsbLdeAny::K64(neon::LsbLde64Tables::new(omega64_bb, omega128_bb));

                    // canonical vs partially-reduced NTT8 micro-benchmark
                    {
                        use core::arch::aarch64::vdupq_n_u32;
                        let LsbLdeAny::K8(ref t8m) = lsb8_tables else {
                            unreachable!()
                        };
                        let dummy = [unsafe { vdupq_n_u32(1) }, unsafe { vdupq_n_u32(2) }];
                        let iters_ntt = 2_000_000u32;
                        let now = std::time::Instant::now();
                        let mut sink = dummy;
                        for _ in 0..iters_ntt {
                            sink = unsafe { neon::lsb_lde8_base(sink, t8m) };
                        }
                        std::hint::black_box(&sink);
                        let t_canon = now.elapsed() / iters_ntt;
                        let now = std::time::Instant::now();
                        let mut sink = dummy;
                        for _ in 0..iters_ntt {
                            sink = unsafe { neon::lsb_lde8_base_lazy(sink, t8m) };
                        }
                        std::hint::black_box(&sink);
                        let t_lazy = now.elapsed() / iters_ntt;
                        let t8mat = neon::LsbLde8MatTables::new(omega8_bb, omega16_bb);
                        let now = std::time::Instant::now();
                        let mut sink = dummy;
                        for _ in 0..iters_ntt {
                            sink = unsafe { neon::lsb_lde8_base_mat(sink, &t8mat) };
                        }
                        std::hint::black_box(&sink);
                        let t_mat = now.elapsed() / iters_ntt;
                        println!(
                            "[NTT8] lsb lde8 micro: canonical {:?}/call, partially-reduced {:?}/call, lagrange-matrix {:?}/call (8 cells each)",
                            t_canon, t_lazy, t_mat
                        );
                    }

                    // zero-reload bounded schedule (bracketed op set, forms
                    // built from resident members)
                    let (lsb_schedule, lsb_stats) = produce_tiled_uniskip_schedule::<F, E>(
                        &forms,
                        &products,
                        &rest_steps,
                        base_polys_all.len(),
                        tstats.peak_base_live,
                        tstats.peak_ext_live,
                    );

                    macro_rules! time_runs {
                        ($n:expr, $body:expr) => {{
                            let mut best = std::time::Duration::MAX;
                            let mut result = None;
                            for _ in 0..$n {
                                let now = std::time::Instant::now();
                                let r = $body;
                                best = best.min(now.elapsed());
                                result = Some(r);
                            }
                            (result.unwrap(), best)
                        }};
                    }
                    macro_rules! lsb_full {
                        ($ng:literal, $nbin:literal, $out:literal, $u:literal, $tables:expr, $t:expr, $rows:expr, $mask:expr) => {
                            lsb_bench::lsb_soa_full_parallel::<F, E, $ng, $nbin, $out, $u>(
                                &base_sources_all,
                                &ext_sources_all,
                                &base_interp,
                                &ext_interp,
                                $tables,
                                &forms,
                                &products,
                                &rest_steps,
                                &description.constant_term,
                                $t,
                                $rows,
                                worker,
                                $mask,
                            )
                        };
                    }
                    macro_rules! lsb_bounded {
                        ($ng:literal, $nbin:literal, $out:literal, $tables:expr, $t:expr, $rows:expr) => {
                            lsb_bench::lsb_soa_bounded_parallel::<F, E, $ng, $nbin, $out>(
                                &base_sources_all,
                                &ext_sources_all,
                                $tables,
                                &forms,
                                &lsb_schedule,
                                tstats.peak_base_live,
                                tstats.peak_ext_live,
                                &description.constant_term,
                                $t,
                                $rows,
                                worker,
                            )
                        };
                    }

                    let (acc_lw3, best_lw3) =
                        time_runs!(iters, lsb_full!(7, 2, 27, 1, None, &t8, rows8, PH_ALL));
                    let (acc_lw3b, best_lw3b) =
                        time_runs!(iters, lsb_bounded!(7, 2, 27, None, &t8, rows8));
                    let (acc_lu8, best_lu8) = time_runs!(
                        iters,
                        lsb_full!(4, 4, 16, 1, Some(&lsb8_tables), &t8, rows8, PH_ALL)
                    );
                    let (acc_lu8b, best_lu8b) =
                        time_runs!(iters, lsb_bounded!(4, 4, 16, Some(&lsb8_tables), &t8, rows8));
                    let lsb8_mat_tables =
                        LsbLdeAny::K8Mat(neon::LsbLde8MatTables::new(omega8_bb, omega16_bb));
                    let (acc_lu8m, best_lu8m) = time_runs!(
                        iters,
                        lsb_full!(4, 4, 16, 1, Some(&lsb8_mat_tables), &t8, rows8, PH_ALL)
                    );
                    let (acc_lu8m_x2, best_lu8m_x2) = time_runs!(
                        iters,
                        lsb_full!(4, 4, 16, 2, Some(&lsb8_mat_tables), &t8, rows8, PH_ALL)
                    );
                    let (acc_lu64, best_lu64) = time_runs!(
                        iters,
                        lsb_full!(32, 32, 128, 1, Some(&lsb64_tables), &t64, rows64, PH_ALL)
                    );
                    let (acc_lu64b, best_lu64b) = time_runs!(
                        iters,
                        lsb_bounded!(32, 32, 128, Some(&lsb64_tables), &t64, rows64)
                    );

                    // row-unrolled variants (outer-loop analog of the MSB
                    // 4-row vectorization)
                    let (acc_lw3_x2, best_lw3_x2) =
                        time_runs!(iters, lsb_full!(7, 2, 27, 2, None, &t8, rows8, PH_ALL));
                    let (acc_lw3_x4, best_lw3_x4) =
                        time_runs!(iters, lsb_full!(7, 2, 27, 4, None, &t8, rows8, PH_ALL));
                    let (acc_lu8_x2, best_lu8_x2) = time_runs!(
                        iters,
                        lsb_full!(4, 4, 16, 2, Some(&lsb8_tables), &t8, rows8, PH_ALL)
                    );
                    let (acc_lu8_x4, best_lu8_x4) = time_runs!(
                        iters,
                        lsb_full!(4, 4, 16, 4, Some(&lsb8_tables), &t8, rows8, PH_ALL)
                    );
                    let (acc_lu64_x2, best_lu64_x2) = time_runs!(
                        iters,
                        lsb_full!(32, 32, 128, 2, Some(&lsb64_tables), &t64, rows64, PH_ALL)
                    );
                    let (acc_lu64_x4, best_lu64_x4) = time_runs!(
                        iters,
                        lsb_full!(32, 32, 128, 4, Some(&lsb64_tables), &t64, rows64, PH_ALL)
                    );

                    // validations: the eq-weighted claim is layout-independent
                    let claim_of = |weights: &[E], cells: &[E]| {
                        let mut s = E::ZERO;
                        for (w, c) in weights.iter().zip(cells.iter()) {
                            let mut t = *w;
                            t.mul_assign(c);
                            s.add_assign(&t);
                        }
                        s
                    };
                    assert_eq!(
                        claim_of(&w3_lsb, &acc_lw3[..8]),
                        lhs,
                        "LSB window-3 claim vs MSB full-cube claim"
                    );
                    assert_eq!(
                        claim_of(&w3_lsb, &acc_lu8[..8]),
                        lhs,
                        "LSB uniskip k=3 claim vs MSB full-cube claim"
                    );
                    assert_eq!(
                        claim_of(&w6_lsb, &acc_lu64[..64]),
                        lhs,
                        "LSB uniskip k=6 claim vs MSB full-cube claim"
                    );
                    for j in 0..8 {
                        assert_eq!(
                            acc_lw3[j], acc_lu8[j],
                            "LSB window-3 binary cell {} vs uniskip H cell",
                            j
                        );
                    }
                    assert_eq!(acc_lw3b, acc_lw3, "LSB window-3 bounded vs full");
                    assert_eq!(acc_lu8b, acc_lu8, "LSB uniskip k=3 bounded vs full");
                    assert_eq!(acc_lu64b, acc_lu64, "LSB uniskip k=6 bounded vs full");
                    assert_eq!(acc_lw3_x2, acc_lw3, "LSB window-3 x2 vs x1");
                    assert_eq!(acc_lw3_x4, acc_lw3, "LSB window-3 x4 vs x1");
                    assert_eq!(acc_lu8_x2, acc_lu8, "LSB uniskip k=3 x2 vs x1");
                    assert_eq!(acc_lu8m, acc_lu8, "LSB uniskip k=3 matrix-LDE vs NTT");
                    assert_eq!(acc_lu8m_x2, acc_lu8, "LSB uniskip k=3 matrix-LDE x2 vs NTT");
                    assert_eq!(acc_lu8_x4, acc_lu8, "LSB uniskip k=3 x4 vs x1");
                    assert_eq!(acc_lu64_x2, acc_lu64, "LSB uniskip k=6 x2 vs x1");
                    assert_eq!(acc_lu64_x4, acc_lu64, "LSB uniskip k=6 x4 vs x1");

                    println!(
                        "[LSB-W3] window-3 LSB SoA engine: full {:?} (x2 {:?}, x4 {:?}), bounded {:?} ({}b/{}e slots, {} base loads / {} distinct) (MSB SoA+brackets [SB]: {:?})",
                        best_lw3,
                        best_lw3_x2,
                        best_lw3_x4,
                        best_lw3b,
                        tstats.peak_base_live,
                        tstats.peak_ext_live,
                        lsb_stats.base_loads,
                        lsb_stats.distinct_base,
                        best_sb,
                    );
                    println!(
                        "[LSB-U8] uniskip k=3 LSB SoA engine: full {:?} (x2 {:?}, x4 {:?}), bounded {:?} (MSB SoA [U]: {:?})",
                        best_lu8, best_lu8_x2, best_lu8_x4, best_lu8b, best_u,
                    );
                    println!(
                        "[LSB-U8M] uniskip k=3 LSB, lagrange-matrix LDE: full {:?} (x2 {:?}) (NTT-LDE full: {:?}, x2: {:?})",
                        best_lu8m, best_lu8m_x2, best_lu8, best_lu8_x2,
                    );
                    println!(
                        "[LSB-U64] uniskip k=6 LSB SoA engine: full {:?} (x2 {:?}, x4 {:?}), bounded {:?} (MSB SoA [U64] r2: {:?})",
                        best_lu64, best_lu64_x2, best_lu64_x4, best_lu64b, best_u64_r2,
                    );
                    println!(
                        "validation: LSB claims match the MSB full-cube claim; window-3 binary cells == uniskip k=3 H cells; bounded and x2/x4 bit-identical to full"
                    );

                    // phase split: cumulative masks, reported as deltas
                    macro_rules! split_report {
                        ($label:expr, $ng:literal, $nbin:literal, $out:literal, $tables:expr, $t:expr, $rows:expr) => {{
                            let cum = [
                                PH_FILL_BASE,
                                PH_FILL_BASE | PH_FILL_EXT,
                                PH_FILL_BASE | PH_FILL_EXT | PH_FORMS,
                                PH_FILL_BASE | PH_FILL_EXT | PH_FORMS | PH_LAZY,
                                PH_FILL_BASE | PH_FILL_EXT | PH_FORMS | PH_LAZY | PH_EXT,
                                PH_ALL,
                            ];
                            let mut times: Vec<std::time::Duration> = vec![];
                            for m in cum {
                                let (_, t) = time_runs!(
                                    2,
                                    lsb_full!($ng, $nbin, $out, 1, $tables, $t, $rows, m)
                                );
                                times.push(t);
                            }
                            let d = |i: usize| {
                                if i == 0 {
                                    times[0]
                                } else {
                                    times[i].saturating_sub(times[i - 1])
                                }
                            };
                            println!(
                                "[LSB-SPLIT] {}: fill-base {:?}, fill-ext {:?}, forms {:?}, bb-lazy {:?}, ext-terms {:?}, eq+acc {:?} (full {:?})",
                                $label,
                                d(0),
                                d(1),
                                d(2),
                                d(3),
                                d(4),
                                d(5),
                                times[5],
                            );
                        }};
                    }
                    split_report!("window-3", 7, 2, 27, None, &t8, rows8);
                    split_report!("uniskip k=3", 4, 4, 16, Some(&lsb8_tables), &t8, rows8);
                    split_report!("uniskip k=6", 32, 32, 128, Some(&lsb64_tables), &t64, rows64);

                    // ---- full 24-round chain of width-3 uniskip passes ----
                    //
                    // Artificial (fixed-challenge, no transcript) protocol on
                    // bit-reversed witness columns. Notation:
                    //
                    //   G(..)     the circuit's quadratic gate polynomial: at one
                    //             point of the boolean cube it combines every
                    //             column's value there:
                    //             sum coeff*col_a*col_b (+ linear terms + const).
                    //   i         24-bit trace index; bit v of i IS boolean
                    //             variable v. LSB binding: pass g eliminates the
                    //             three lowest remaining bits (vars 3g..3g+2),
                    //             so i = row*8 + j with j in 0..8 and `row` the
                    //             surviving high bits.
                    //   H, gH     the size-8 subgroup <w8> and its coset g*H
                    //             (g = w16). Boolean assignment j of a row is
                    //             identified with the point u_j = w8^j of H.
                    //   packed    for a fixed row, a column's 8 values
                    //   poly      {col[8*row+j]} are the evaluation form of a
                    //             degree-<8 univariate P_row with P_row(u_j) =
                    //             col[8*row+j]; the LDE in the evaluators
                    //             extends it to the coset points.
                    //   q_g(X)    the pass's packed sum-polynomial
                    //               q_g(X) = sum_row T_g(row) * G(packed at X)
                    //             deg q_g <= 14 (G quadratic in degree-7 packed
                    //             polys), so its 16 values on H u gH pin it down.
                    //   W(i)      the eq weight, one factor per bit:
                    //             W(i) = prod_v f_v(bit_v(i)). Because it is a
                    //             per-bit product it splits around ANY bit group:
                    //               W(i) = w3_g[j] * T_g(row)
                    //             with w3_g over the 3 dying bits, T_g the rest.
                    //   r_g       the pass challenge. Folding = evaluating every
                    //             packed poly at r_g:
                    //               folded[row] = P_row(r_g)
                    //                           = sum_j L_j(r_g) * col[8row+j].
                    //
                    // One pass, pictorially (columns shrink 8x):
                    //
                    //   col: [ v0 .. v7 | v8 .. v15 | ... ]   8 values per row
                    //           row 0       row 1
                    //     |
                    //     | evaluate: q_g at the 16 points of H u gH
                    //     | claim:    sum_j w3_g[j] * q_g(u_j)
                    //     | fold(r_g):
                    //     v
                    //   col':[ P_0(r_g) | P_1(r_g) | ... ]    1 value per row
                    //
                    // The chain telescopes, which is the entire validation:
                    //
                    //   q_g(r_g) = sum_row  T_g(row)   * G(folded row values)
                    //            = sum_row',j w3_{g+1}[j]*T_{g+1}(row') * G(..)
                    //            = sum_j w3_{g+1}[j] * q_{g+1}(u_j)
                    //
                    // (first step: definition of the fold; second: W splits per
                    // bit; third: definition of q_{g+1}.) So the NEXT pass's
                    // weighted H-values must reproduce the PREVIOUS pass's q
                    // interpolated (degree-15 barycentric) at its challenge --
                    // any error in the fold, the LDE, the eq tables or the term
                    // evaluation breaks it. After the last fold every column is
                    // a single value and the identity degenerates to
                    // G(final values) == q_7(r_7).
                    //
                    // Why eq is (nearly) free here: uniskip keeps the eq factor
                    // of the three skipped variables OUT of the packed
                    // polynomial. The prover only multiplies each row's G-value
                    // by the scalar suffix weight T_g(row) (one ext multiply
                    // per row, `soa_apply_eq_*`); the window part w3_g touches
                    // only the 8 H-values of q_g when the claim is formed --
                    // verifier-side work, 8 multiplies per PASS. The kernels
                    // never see eq inside the 16-point term evaluation, which
                    // is why "eq+acc" is 27-66ms of the 1.4s chain in
                    // [LSB-SPLIT].
                    {
                        use ::field::baby_bear::base::BabyBearField;
                        let nbits = folding_steps;
                        let nb = base_sources_all.len();
                        let ne = ext_sources_all.len();
                        let num_passes = nbits / 3;
                        assert_eq!(nbits % 3, 0);

                        // bit-reversed column copies (one-time, outside timing)
                        let t_setup = std::time::Instant::now();
                        let mut base_cols_rev: Vec<Vec<F>> =
                            (0..nb).map(|_| vec![F::ZERO; trace_len]).collect();
                        let mut ext_cols_rev: Vec<Vec<E>> =
                            (0..ne).map(|_| vec![E::ZERO; trace_len]).collect();
                        {
                            let src_b: Vec<usize> =
                                base_sources_all.iter().map(|s| s.ptr as usize).collect();
                            let dst_b: Vec<usize> = base_cols_rev
                                .iter_mut()
                                .map(|c| c.as_mut_ptr() as usize)
                                .collect();
                            let src_e: Vec<usize> =
                                ext_sources_all.iter().map(|s| s.ptr as usize).collect();
                            let dst_e: Vec<usize> = ext_cols_rev
                                .iter_mut()
                                .map(|c| c.as_mut_ptr() as usize)
                                .collect();
                            let total_cols = nb + ne;
                            worker.scope_with_threshold(total_cols, 1, |scope, geometry| {
                                for thread_idx in 0..geometry.num_chunks {
                                    let cs = geometry.get_chunk_start_pos(thread_idx);
                                    let cl = geometry.get_chunk_size(thread_idx);
                                    let src_b = src_b.clone();
                                    let dst_b = dst_b.clone();
                                    let src_e = src_e.clone();
                                    let dst_e = dst_e.clone();
                                    Worker::smart_spawn(
                                        scope,
                                        thread_idx == geometry.len() - 1,
                                        move |_| unsafe {
                                            let shift = 32 - nbits;
                                            for c in cs..(cs + cl) {
                                                if c < nb {
                                                    let sp = src_b[c] as *const F;
                                                    let dp = dst_b[c] as *mut F;
                                                    for i in 0..trace_len {
                                                        let j = (i as u32).reverse_bits()
                                                            as usize
                                                            >> shift;
                                                        *dp.add(i) = *sp.add(j);
                                                    }
                                                } else {
                                                    let sp = src_e[c - nb] as *const E;
                                                    let dp = dst_e[c - nb] as *mut E;
                                                    for i in 0..trace_len {
                                                        let j = (i as u32).reverse_bits()
                                                            as usize
                                                            >> shift;
                                                        *dp.add(i) = *sp.add(j);
                                                    }
                                                }
                                            }
                                        },
                                    )
                                }
                            });
                        }
                        let brev_base_sources: Vec<_> = base_cols_rev
                            .iter()
                            .map(|c| DisjointAccessQuasiSlice::<_, false>::from_init_slice(&c[..]))
                            .collect();
                        let brev_ext_sources: Vec<_> = ext_cols_rev
                            .iter()
                            .map(|c| DisjointAccessQuasiSlice::<_, false>::from_init_slice(&c[..]))
                            .collect();

                        // artificial per-variable eq factors + per-pass challenges
                        let mut seed = 0xC0FFEEu64;
                        let mut pe = || -> E {
                            let mut limbs = [BabyBearField::ZERO; 4];
                            for l in limbs.iter_mut() {
                                seed = seed
                                    .wrapping_mul(6364136223846793005)
                                    .wrapping_add(1442695040888963407);
                                *l = BabyBearField::from_u32_with_reduction((seed >> 33) as u32);
                            }
                            let v =
                                ::field::baby_bear::ext4::BabyBearExt4::from_array_of_base(limbs);
                            unsafe { *(&v as *const _ as *const E) }
                        };
                        let chall: Vec<E> = (0..nbits).map(|_| pe()).collect();
                        let rs: Vec<E> = (0..num_passes).map(|_| pe()).collect();
                        let fac = |v: usize, bit: usize| -> E {
                            if bit == 1 {
                                chall[v]
                            } else {
                                let mut t = E::ONE;
                                t.sub_assign(&chall[v]);
                                t
                            }
                        };
                        let w3g: Vec<[E; 8]> = (0..num_passes)
                            .map(|g| {
                                core::array::from_fn(|j| {
                                    let mut t = E::ONE;
                                    for b in 0..3 {
                                        t.mul_assign(&fac(3 * g + b, (j >> b) & 1));
                                    }
                                    t
                                })
                            })
                            .collect();
                        let tgs: Vec<Vec<E>> = (0..num_passes)
                            .map(|g| {
                                let rem = nbits - 3 * (g + 1);
                                let mut t = vec![E::ONE; 1 << rem];
                                for b in 0..rem {
                                    let half = 1usize << b;
                                    let (f0, f1) = (fac(3 * (g + 1) + b, 0), fac(3 * (g + 1) + b, 1));
                                    for i in 0..half {
                                        let mut hi = t[i];
                                        hi.mul_assign(&f1);
                                        t[i + half] = hi;
                                        t[i].mul_assign(&f0);
                                    }
                                }
                                t
                            })
                            .collect();

                        // 16 evaluation points and interpolation helpers
                        let u_pts: [E; 16] = core::array::from_fn(|idx| {
                            let mut u = if idx < 8 {
                                omega8_bb.pow(idx as u32)
                            } else {
                                let mut t = omega16_bb;
                                t.mul_assign(&omega8_bb.pow((idx - 8) as u32));
                                t
                            };
                            let uf = unsafe { *(&u as *const _ as *const F) };
                            let _ = &mut u;
                            E::from_base(uf)
                        });
                        let denom_inv: [E; 16] = core::array::from_fn(|j| {
                            let mut d = E::ONE;
                            for k in 0..16 {
                                if k != j {
                                    let mut t = u_pts[j];
                                    t.sub_assign(&u_pts[k]);
                                    d.mul_assign(&t);
                                }
                            }
                            d.inverse().expect("distinct points")
                        });
                        let interp_at = |q: &[E; 16], r: &E| -> E {
                            let mut pre = [E::ONE; 17];
                            for k in 0..16 {
                                let mut t = *r;
                                t.sub_assign(&u_pts[k]);
                                let mut p = pre[k];
                                p.mul_assign(&t);
                                pre[k + 1] = p;
                            }
                            let mut suf = [E::ONE; 17];
                            for k in (0..16).rev() {
                                let mut t = *r;
                                t.sub_assign(&u_pts[k]);
                                let mut p = suf[k + 1];
                                p.mul_assign(&t);
                                suf[k] = p;
                            }
                            let mut acc = E::ZERO;
                            for j in 0..16 {
                                let mut t = q[j];
                                t.mul_assign(&pre[j]);
                                t.mul_assign(&suf[j + 1]);
                                t.mul_assign(&denom_inv[j]);
                                acc.add_assign(&t);
                            }
                            acc
                        };
                        let eighth_bb = BabyBearField::from_u32_with_reduction(8)
                            .inverse()
                            .unwrap();
                        let l8_at = |r: &E| -> [E; 8] {
                            let mut z = r.pow(8);
                            z.sub_assign(&E::ONE);
                            core::array::from_fn(|j| {
                                let uj_bb = omega8_bb.pow(j as u32);
                                let uj = E::from_base(unsafe { *(&uj_bb as *const _ as *const F) });
                                let mut denom = *r;
                                denom.sub_assign(&uj);
                                let mut w = z;
                                w.mul_assign(&uj);
                                w.mul_assign(&denom.inverse().expect("r not in H"));
                                w.mul_assign_by_base(unsafe {
                                    &*(&eighth_bb as *const _ as *const F)
                                });
                                w
                            })
                        };

                        // ---- monomial-form verifier (the "updated" verifier) ----
                        //
                        // PROVER extra work: the 16 evaluation points H u gH
                        // form exactly the size-16 subgroup <w16> (gamma = w16,
                        // gamma^2 = w8; eval idx < 8 sits at w16^(2*idx), idx
                        // >= 8 at w16^(2*(idx-8)+1)), so the prover converts
                        // q's 16 values to monomial coefficients C_0..C_15
                        // with one 16-point inverse DFT and sends THOSE.
                        let sixteenth = BabyBearField::from_u32_with_reduction(16)
                            .inverse()
                            .unwrap();
                        let omega16_inv = omega16_bb.inverse().unwrap();
                        let exp_of =
                            |idx: usize| -> usize { if idx < 8 { 2 * idx } else { 2 * (idx - 8) + 1 } };
                        let to_monomial = |q: &[E; 16]| -> [E; 16] {
                            core::array::from_fn(|m| {
                                let mut acc = E::ZERO;
                                for idx in 0..16 {
                                    let tw = omega16_inv.pow((exp_of(idx) * m % 16) as u32);
                                    let mut t = q[idx];
                                    t.mul_assign_by_base(unsafe {
                                        &*(&tw as *const _ as *const F)
                                    });
                                    acc.add_assign(&t);
                                }
                                acc.mul_assign_by_base(unsafe {
                                    &*(&sixteenth as *const _ as *const F)
                                });
                                acc
                            })
                        };
                        // VERIFIER claim check, fully unrolled:
                        //   claim == sum_{j<8} Eq_j * q(w8^j)
                        //         == sum_{t<8} (C_t + C_{t+8}) * W_t
                        // where W_t = sum_j Eq_j * w8^(j*t) -- only t < 8
                        // exist because w8^8 = 1 makes W periodic in t -- and
                        // W_0 = sum_j Eq_j = 1 (eq sums to one over the cube),
                        // so the t = 0 term costs no multiply. Base-field
                        // twiddles, no inversions, no per-point Horner.
                        let verifier_claim = |c: &[E; 16], eq8: &[E; 8]| -> E {
                            let folded: [E; 8] = core::array::from_fn(|t| {
                                let mut v = c[t];
                                v.add_assign(&c[t + 8]);
                                v
                            });
                            let w: [E; 8] = core::array::from_fn(|t| {
                                let mut acc = E::ZERO;
                                for j in 0..8 {
                                    let tw = omega8_bb.pow((j * t % 8) as u32);
                                    let mut v = eq8[j];
                                    v.mul_assign_by_base(unsafe {
                                        &*(&tw as *const _ as *const F)
                                    });
                                    acc.add_assign(&v);
                                }
                                acc
                            });
                            assert_eq!(w[0], E::ONE, "eq table must sum to 1");
                            let mut claim = folded[0]; // W_0 = 1
                            for t in 1..8 {
                                let mut v = folded[t];
                                v.mul_assign(&w[t]);
                                claim.add_assign(&v);
                            }
                            claim
                        };
                        // VERIFIER next-claim: plain Horner over C_15..C_0.
                        let horner16 = |c: &[E; 16], r: &E| -> E {
                            let mut acc = c[15];
                            for m in (0..15).rev() {
                                acc.mul_assign(r);
                                acc.add_assign(&c[m]);
                            }
                            acc
                        };
                        // VERIFIER fold weights, inversion-free product form:
                        //   L_j(r) = [prod_{k!=j} (r - w8^k)] * D_j,
                        //   D_j = 1/prod_{k!=j} (w8^j - w8^k)
                        // The D_j are DOMAIN constants (base field, inverted
                        // once at setup); at runtime only prefix/suffix
                        // products of (r - w8^k) are needed.
                        let d_consts: [E; 8] = core::array::from_fn(|j| {
                            let mut d = BabyBearField::ONE;
                            for k in 0..8 {
                                if k != j {
                                    let mut t = omega8_bb.pow(j as u32);
                                    t.sub_assign(&omega8_bb.pow(k as u32));
                                    d.mul_assign(&t);
                                }
                            }
                            let dinv = d.inverse().unwrap();
                            E::from_base(unsafe { *(&dinv as *const _ as *const F) })
                        });
                        let l8_product_form = |r: &E| -> [E; 8] {
                            let diffs: [E; 8] = core::array::from_fn(|k| {
                                let uk = omega8_bb.pow(k as u32);
                                let mut t = *r;
                                t.sub_assign(&E::from_base(unsafe {
                                    *(&uk as *const _ as *const F)
                                }));
                                t
                            });
                            let mut pre = [E::ONE; 9];
                            for k in 0..8 {
                                let mut p = pre[k];
                                p.mul_assign(&diffs[k]);
                                pre[k + 1] = p;
                            }
                            let mut suf = [E::ONE; 9];
                            for k in (0..8).rev() {
                                let mut p = suf[k + 1];
                                p.mul_assign(&diffs[k]);
                                suf[k] = p;
                            }
                            core::array::from_fn(|j| {
                                let mut v = pre[j];
                                v.mul_assign(&suf[j + 1]);
                                v.mul_assign(&d_consts[j]);
                                v
                            })
                        };

                        // folded term lists over the combined slot space
                        let nbu = nb as u16;
                        let mut chain_quads: Vec<(u16, u16, E)> = vec![];
                        let mut chain_lins: Vec<(u16, E)> = vec![];
                        for step in rest_steps.iter() {
                            match step {
                                BenchStep::QuadBB { a, b, c } => chain_quads.push((*a, *b, *c)),
                                BenchStep::QuadBE { base, ext, c } => {
                                    chain_quads.push((*base, nbu + *ext, *c))
                                }
                                BenchStep::QuadEE { a, b, c } => {
                                    chain_quads.push((nbu + *a, nbu + *b, *c))
                                }
                                BenchStep::LinB { i, c } => chain_lins.push((*i, *c)),
                                BenchStep::LinE { i, c } => chain_lins.push((nbu + *i, *c)),
                            }
                        }
                        let t_setup = t_setup.elapsed();

                        {
                            // SoA fold kernels must agree bitwise with the AoS ones
                            let lw0 = l8_at(&rs[0]);
                            let n_check = 1usize << (nbits - 3);
                            let mut a = vec![E::ZERO; n_check];
                            let mut b = vec![E::ZERO; n_check];
                            lsb_bench::lsb_fold_base_parallel::<F, E>(
                                base_cols_rev[0].as_ptr() as *const u8,
                                &mut a,
                                &lw0,
                                worker,
                            );
                            lsb_bench::lsb_fold_base_soa_parallel::<F, E>(
                                base_cols_rev[0].as_ptr() as *const u8,
                                &mut b,
                                &lw0,
                                worker,
                            );
                            assert_eq!(a, b, "SoA base fold vs AoS");
                            lsb_bench::lsb_fold_ext_parallel::<E>(
                                ext_cols_rev[0].as_ptr() as *const u8,
                                &mut a,
                                &lw0,
                                worker,
                            );
                            lsb_bench::lsb_fold_ext_soa_parallel::<E>(
                                ext_cols_rev[0].as_ptr() as *const u8,
                                &mut b,
                                &lw0,
                                worker,
                            );
                            assert_eq!(a, b, "SoA ext fold vs AoS");
                        }

                        let mut eval_times = vec![std::time::Duration::ZERO; num_passes];
                        let mut fold_times = vec![std::time::Duration::ZERO; num_passes];
                        let mut best_total = std::time::Duration::MAX;
                        // pre-allocated pass-1 folding buffers (like the MSB
                        // chain's ext_folding_buffers -- not part of the timing)
                        let mut pass1_bufs: Vec<Vec<E>> = (0..(nb + ne))
                            .map(|_| vec![E::ZERO; 1usize << (nbits - 3)])
                            .collect();
                        for _iteration in 0..2 {
                            let t_total = std::time::Instant::now();
                            let mut q_prev_at_r: Option<E> = None;
                            let mut combined: Vec<Vec<E>> = Vec::new();
                            for g in 0..num_passes {
                                let out_size = 1usize << (nbits - 3 * g - 3);
                                let t0 = std::time::Instant::now();
                                let q: [E; 16] = if g == 0 {
                                    lsb_bench::lsb_soa_full_parallel::<F, E, 4, 4, 16, 2>(
                                        &brev_base_sources,
                                        &brev_ext_sources,
                                        &base_interp,
                                        &ext_interp,
                                        Some(&lsb8_mat_tables),
                                        &forms,
                                        &products,
                                        &rest_steps,
                                        &description.constant_term,
                                        &tgs[0],
                                        out_size,
                                        worker,
                                        PH_ALL,
                                    )
                                } else {
                                    let cur: &Vec<Vec<E>> =
                                        if g == 1 { &pass1_bufs } else { &combined };
                                    let srcs: Vec<DisjointAccessQuasiSlice<E, false>> = cur
                                        .iter()
                                        .map(|c| {
                                            DisjointAccessQuasiSlice::<_, false>::from_init_slice(
                                                &c[..],
                                            )
                                        })
                                        .collect();
                                    if out_size % 2 == 0 {
                                        lsb_bench::lsb_uniskip_ext_pass_parallel::<F, E, 2>(
                                            &srcs,
                                            &forms,
                                            &products,
                                            &chain_quads,
                                            &chain_lins,
                                            &description.constant_term,
                                            &lsb8_mat_tables,
                                            &tgs[g],
                                            out_size,
                                            worker,
                                        )
                                    } else {
                                        lsb_bench::lsb_uniskip_ext_pass_parallel::<F, E, 1>(
                                            &srcs,
                                            &forms,
                                            &products,
                                            &chain_quads,
                                            &chain_lins,
                                            &description.constant_term,
                                            &lsb8_mat_tables,
                                            &tgs[g],
                                            out_size,
                                            worker,
                                        )
                                    }
                                };
                                eval_times[g] = t0.elapsed();
                                // prover-side: convert q to monomial form;
                                // everything the verifier does below uses ONLY
                                // the coefficients
                                let coeffs = to_monomial(&q);
                                assert_eq!(coeffs[15], E::ZERO, "deg(q) <= 14");
                                if let Some(expected) = q_prev_at_r {
                                    // evaluation-form reference check
                                    let mut claim = E::ZERO;
                                    for j in 0..8 {
                                        let mut t = w3g[g][j];
                                        t.mul_assign(&q[j]);
                                        claim.add_assign(&t);
                                    }
                                    assert_eq!(
                                        claim, expected,
                                        "chain claim mismatch entering pass {}",
                                        g
                                    );
                                    // monomial-form VERIFIER check (fold +
                                    // DFT8 + dot; no barycentric, no
                                    // inversions)
                                    assert_eq!(
                                        verifier_claim(&coeffs, &w3g[g]),
                                        expected,
                                        "monomial verifier claim at pass {}",
                                        g
                                    );
                                }
                                // verifier next-claim via Horner; must agree
                                // with the barycentric evaluation of q's
                                // 16-value form
                                let q_r = horner16(&coeffs, &rs[g]);
                                assert_eq!(
                                    q_r,
                                    interp_at(&q, &rs[g]),
                                    "Horner vs barycentric q(r) at pass {}",
                                    g
                                );
                                q_prev_at_r = Some(q_r);
                                // verifier fold weights: inversion-free
                                // product form == barycentric form
                                let lw = l8_product_form(&rs[g]);
                                assert_eq!(
                                    lw,
                                    l8_at(&rs[g]),
                                    "product-form fold weights at pass {}",
                                    g
                                );
                                let t1 = std::time::Instant::now();
                                if g == 0 {
                                    for (i, col) in base_cols_rev.iter().enumerate() {
                                        lsb_bench::lsb_fold_base_soa_parallel::<F, E>(
                                            col.as_ptr() as *const u8,
                                            &mut pass1_bufs[i],
                                            &lw,
                                            worker,
                                        );
                                    }
                                    for (i, col) in ext_cols_rev.iter().enumerate() {
                                        lsb_bench::lsb_fold_ext_soa_parallel::<E>(
                                            col.as_ptr() as *const u8,
                                            &mut pass1_bufs[nb + i],
                                            &lw,
                                            worker,
                                        );
                                    }
                                } else {
                                    let cur: &Vec<Vec<E>> =
                                        if g == 1 { &pass1_bufs } else { &combined };
                                    let mut next: Vec<Vec<E>> = Vec::with_capacity(cur.len());
                                    for col in cur.iter() {
                                        let mut dstv = vec![E::ZERO; out_size];
                                        if out_size % 4 == 0 {
                                            lsb_bench::lsb_fold_ext_soa_parallel::<E>(
                                                col.as_ptr() as *const u8,
                                                &mut dstv,
                                                &lw,
                                                worker,
                                            );
                                        } else {
                                            lsb_bench::lsb_fold_ext_parallel::<E>(
                                                col.as_ptr() as *const u8,
                                                &mut dstv,
                                                &lw,
                                                worker,
                                            );
                                        }
                                        next.push(dstv);
                                    }
                                    combined = next;
                                }
                                fold_times[g] = t1.elapsed();
                            }
                            // final identity: G(final values) == q_last(r_last)
                            let final_vals: Vec<E> = combined.iter().map(|c| c[0]).collect();
                            let mut g_val = description.constant_term;
                            for (a, f, c) in products.iter() {
                                let mut form_val = E::ZERO;
                                for (op, m) in forms[*f as usize].iter() {
                                    match op {
                                        FormOp::Add => {
                                            form_val.add_assign(&final_vals[*m as usize]);
                                        }
                                        FormOp::Sub => {
                                            form_val.sub_assign(&final_vals[*m as usize]);
                                        }
                                        FormOp::Mul(cf) => {
                                            let mut t = final_vals[*m as usize];
                                            t.mul_assign_by_base(cf);
                                            form_val.add_assign(&t);
                                        }
                                    }
                                }
                                let mut t = final_vals[*a as usize];
                                t.mul_assign(&form_val);
                                t.mul_assign(c);
                                g_val.add_assign(&t);
                            }
                            for (a, b, c) in chain_quads.iter() {
                                let mut t = final_vals[*a as usize];
                                t.mul_assign(&final_vals[*b as usize]);
                                t.mul_assign(c);
                                g_val.add_assign(&t);
                            }
                            for (i, c) in chain_lins.iter() {
                                let mut t = final_vals[*i as usize];
                                t.mul_assign(c);
                                g_val.add_assign(&t);
                            }
                            assert_eq!(
                                g_val,
                                q_prev_at_r.unwrap(),
                                "final G identity vs interpolated q(r)"
                            );
                            best_total = best_total.min(t_total.elapsed());
                        }

                        let mut head = std::time::Duration::ZERO;
                        let mut tail = std::time::Duration::ZERO;
                        for g in 0..num_passes {
                            let d = eval_times[g] + fold_times[g];
                            if g < 4 {
                                head += d;
                            } else {
                                tail += d;
                            }
                            println!(
                                "[LSB-CHAIN] pass {} (size 2^{:>2}): eval {:?}, fold {:?}",
                                g,
                                nbits - 3 * g,
                                eval_times[g],
                                fold_times[g],
                            );
                        }
                        println!(
                            "[LSB-CHAIN] full 24-var chain of width-3 uniskip passes: total {:?} (to 2^12: {:?}, tail 2^12->1: {:?}; one-time bitrev+setup {:?})",
                            best_total, head, tail, t_setup,
                        );
                        println!(
                            "validation: every pass claim chains via interpolated q(r); final G(folded values) == q(r); monomial-form verifier (coeff fold + DFT8 + Horner + product-form fold weights) agrees on every pass"
                        );

                        // ---- fused variant: pass-0 fold merged into pass-1 ----
                        let mut f_eval = vec![std::time::Duration::ZERO; num_passes];
                        let mut f_fold = vec![std::time::Duration::ZERO; num_passes];
                        let mut best_total_f = std::time::Duration::MAX;
                        let mut fpass1_bufs: Vec<Vec<E>> = (0..(nb + ne))
                            .map(|_| vec![E::ZERO; 1usize << (nbits - 3)])
                            .collect();
                        for _iteration in 0..2 {
                            let t_total = std::time::Instant::now();
                            let t0 = std::time::Instant::now();
                            let q0 = lsb_bench::lsb_soa_full_parallel::<F, E, 4, 4, 16, 2>(
                                &brev_base_sources,
                                &brev_ext_sources,
                                &base_interp,
                                &ext_interp,
                                Some(&lsb8_mat_tables),
                                &forms,
                                &products,
                                &rest_steps,
                                &description.constant_term,
                                &tgs[0],
                                1usize << (nbits - 3),
                                worker,
                                PH_ALL,
                            );
                            f_eval[0] = t0.elapsed();
                            let mut q_prev_at_r = interp_at(&q0, &rs[0]);
                            let lw0 = l8_at(&rs[0]);
                            let base_addrs: Vec<usize> = base_cols_rev
                                .iter()
                                .map(|c| c.as_ptr() as usize)
                                .collect();
                            let ext_addrs: Vec<usize> =
                                ext_cols_rev.iter().map(|c| c.as_ptr() as usize).collect();
                            let fold_addrs: Vec<usize> = fpass1_bufs
                                .iter_mut()
                                .map(|c| c.as_mut_ptr() as usize)
                                .collect();
                            let t1 = std::time::Instant::now();
                            let q1 = lsb_bench::lsb_fold_and_ext_pass_parallel::<F, E>(
                                &base_addrs,
                                &ext_addrs,
                                &fold_addrs,
                                &lw0,
                                &forms,
                                &products,
                                &chain_quads,
                                &chain_lins,
                                &description.constant_term,
                                &lsb8_mat_tables,
                                &tgs[1],
                                worker,
                            );
                            f_eval[1] = t1.elapsed(); // includes the pass-0 fold
                            {
                                let mut claim = E::ZERO;
                                for j in 0..8 {
                                    let mut t = w3g[1][j];
                                    t.mul_assign(&q1[j]);
                                    claim.add_assign(&t);
                                }
                                assert_eq!(claim, q_prev_at_r, "fused pass-1 claim");
                            }
                            q_prev_at_r = interp_at(&q1, &rs[1]);
                            let mut fcombined: Vec<Vec<E>> = Vec::new();
                            for g in 2..num_passes {
                                let in_size = 1usize << (nbits - 3 * g);
                                let lwg = l8_at(&rs[g - 1]);
                                let tf = std::time::Instant::now();
                                let cur: &Vec<Vec<E>> =
                                    if g == 2 { &fpass1_bufs } else { &fcombined };
                                let mut next: Vec<Vec<E>> = Vec::with_capacity(cur.len());
                                for col in cur.iter() {
                                    let mut dstv = vec![E::ZERO; in_size];
                                    if in_size % 4 == 0 {
                                        lsb_bench::lsb_fold_ext_soa_parallel::<E>(
                                            col.as_ptr() as *const u8,
                                            &mut dstv,
                                            &lwg,
                                            worker,
                                        );
                                    } else {
                                        lsb_bench::lsb_fold_ext_parallel::<E>(
                                            col.as_ptr() as *const u8,
                                            &mut dstv,
                                            &lwg,
                                            worker,
                                        );
                                    }
                                    next.push(dstv);
                                }
                                fcombined = next;
                                f_fold[g - 1] = tf.elapsed();
                                let te = std::time::Instant::now();
                                let srcs: Vec<DisjointAccessQuasiSlice<E, false>> = fcombined
                                    .iter()
                                    .map(|c| {
                                        DisjointAccessQuasiSlice::<_, false>::from_init_slice(
                                            &c[..],
                                        )
                                    })
                                    .collect();
                                let rows_g = in_size / 8;
                                let q: [E; 16] = if rows_g % 2 == 0 && rows_g >= 2 {
                                    lsb_bench::lsb_uniskip_ext_pass_parallel::<F, E, 2>(
                                        &srcs,
                                        &forms,
                                        &products,
                                        &chain_quads,
                                        &chain_lins,
                                        &description.constant_term,
                                        &lsb8_mat_tables,
                                        &tgs[g],
                                        rows_g,
                                        worker,
                                    )
                                } else {
                                    lsb_bench::lsb_uniskip_ext_pass_parallel::<F, E, 1>(
                                        &srcs,
                                        &forms,
                                        &products,
                                        &chain_quads,
                                        &chain_lins,
                                        &description.constant_term,
                                        &lsb8_mat_tables,
                                        &tgs[g],
                                        rows_g,
                                        worker,
                                    )
                                };
                                f_eval[g] = te.elapsed();
                                let mut claim = E::ZERO;
                                for j in 0..8 {
                                    let mut t = w3g[g][j];
                                    t.mul_assign(&q[j]);
                                    claim.add_assign(&t);
                                }
                                assert_eq!(
                                    claim, q_prev_at_r,
                                    "fused chain claim mismatch entering pass {}",
                                    g
                                );
                                q_prev_at_r = interp_at(&q, &rs[g]);
                            }
                            // last fold to single values + final identity
                            let lw_last = l8_at(&rs[num_passes - 1]);
                            let tf = std::time::Instant::now();
                            let mut finals: Vec<E> = Vec::with_capacity(fcombined.len());
                            for col in fcombined.iter() {
                                let mut dstv = vec![E::ZERO; 1];
                                lsb_bench::lsb_fold_ext_parallel::<E>(
                                    col.as_ptr() as *const u8,
                                    &mut dstv,
                                    &lw_last,
                                    worker,
                                );
                                finals.push(dstv[0]);
                            }
                            f_fold[num_passes - 1] = tf.elapsed();
                            let mut g_val = description.constant_term;
                            for (a, f, c) in products.iter() {
                                let mut form_val = E::ZERO;
                                for (op, m) in forms[*f as usize].iter() {
                                    match op {
                                        FormOp::Add => {
                                            form_val.add_assign(&finals[*m as usize]);
                                        }
                                        FormOp::Sub => {
                                            form_val.sub_assign(&finals[*m as usize]);
                                        }
                                        FormOp::Mul(cf) => {
                                            let mut t = finals[*m as usize];
                                            t.mul_assign_by_base(cf);
                                            form_val.add_assign(&t);
                                        }
                                    }
                                }
                                let mut t = finals[*a as usize];
                                t.mul_assign(&form_val);
                                t.mul_assign(c);
                                g_val.add_assign(&t);
                            }
                            for (a, b, c) in chain_quads.iter() {
                                let mut t = finals[*a as usize];
                                t.mul_assign(&finals[*b as usize]);
                                t.mul_assign(c);
                                g_val.add_assign(&t);
                            }
                            for (i, c) in chain_lins.iter() {
                                let mut t = finals[*i as usize];
                                t.mul_assign(c);
                                g_val.add_assign(&t);
                            }
                            assert_eq!(g_val, q_prev_at_r, "fused final G identity");
                            best_total_f = best_total_f.min(t_total.elapsed());
                        }
                        for g in 0..num_passes {
                            println!(
                                "[LSB-CHAIN-F] pass {} (size 2^{:>2}): eval {:?}, fold {:?}{}",
                                g,
                                nbits - 3 * g,
                                f_eval[g],
                                f_fold[g],
                                if g == 1 { "  (eval includes fused pass-0 fold)" } else { "" },
                            );
                        }
                        println!(
                            "[LSB-CHAIN-F] fused chain total {:?} (unfused: {:?})",
                            best_total_f, best_total,
                        );
                        println!(
                            "validation: fused chain claims + final G identity hold"
                        );
                    }
                }
            }
        }

        // expanded steps over the combined folded slot space (all polys ext
        // after the transition; base-origin slots first)
        let nb = base_polys_all.len() as u16;
        // bracket-subtracted remainder over the combined folded slot space:
        // the preserved products (forms) carry the rest of the quadratic terms
        let mut folded_quad: Vec<(u16, u16, E)> = vec![];
        for step in rest_steps.iter() {
            match step {
                BenchStep::QuadBB { a, b, c } => folded_quad.push((*a, *b, *c)),
                BenchStep::QuadBE { base, ext, c } => {
                    folded_quad.push((*base, nb + *ext, *c))
                }
                BenchStep::QuadEE { a, b, c } => {
                    folded_quad.push((nb + *a, nb + *b, *c))
                }
                _ => {}
            }
        }
        let mut folded_lin: Vec<(u16, E)> = vec![];
        for (a, c) in description.linear_part_base_by_everything.iter() {
            folded_lin.push((bidx(a), *c));
        }
        for (a, c) in description.linear_part_ext_by_everything.iter() {
            folded_lin.push((nb + eidx(a), *c));
        }

        (base_interp, ext_interp, forms, products, rest_steps, folded_quad, folded_lin)
    };

    // ---------------- variant B: bounded scratch (Belady) ----------------
    for (bcap, ecap) in [(4usize, 2usize), (8, 4), (16, 8), (32, 16)] {
        let bcap = bcap.min(base_polys_all.len().max(2));
        let ecap = ecap.min(ext_polys_all.len().max(2));
        let (bounded, b_srcs, e_srcs) =
            produce_bounded_scratch_description(&description, bcap, ecap);
        assert_eq!(b_srcs, base_polys_all);
        assert_eq!(e_srcs, ext_polys_all);

        let mut acc = [E::ZERO; 27];
        let mut best = std::time::Duration::MAX;
        for _ in 0..iters {
            let now = std::time::Instant::now();
            acc = evaluate_initial_with_bounded_scratch_parallel(
                base_sources_all.clone(),
                ext_sources_all.clone(),
                &bounded,
                eq_suffix_initial,
                folding_steps,
                worker,
            );
            best = best.min(now.elapsed());
        }
        assert_acc_eq(&acc, &acc_all, "bounded scratch vs full-size scratch");
        println!(
            "[B] window-3 rounds 0-2, ALL terms, bounded scratch {}b/{}e slots (loads: {} base / {} distinct, {} ext / {} distinct): {:?}",
            bcap,
            ecap,
            bounded.num_base_loads,
            bounded.num_distinct_base,
            bounded.num_ext_loads,
            bounded.num_distinct_ext,
            best,
        );
    }

    // ---------------- variant B2: clustered-DAG bounded scratch ----------------
    {
        use super::bounded_scratch::produce_clustered_scratch_description;
        let (_d, _b, _e, stats) =
            produce_clustered_scratch_description(&description, 16, 8);
        println!(
            "[B2] evaluation DAG: {} clusters (sizes {:?}{}), {} isolated gates; zero-reload capacity: {} base / {} ext slots",
            stats.num_clusters,
            &stats.cluster_sizes[..stats.cluster_sizes.len().min(6)],
            if stats.cluster_sizes.len() > 6 { ", ..." } else { "" },
            stats.isolated_ops,
            stats.peak_base_live,
            stats.peak_ext_live,
        );
        for (bcap, ecap) in [
            (stats.peak_base_live, stats.peak_ext_live),
            (16usize, 8usize),
            (12, 6),
            (8, 4),
            (6, 3),
            (4, 2),
        ] {
            let bcap = bcap.max(2).min(base_polys_all.len().max(2));
            let ecap = ecap.max(2).min(ext_polys_all.len().max(2));
            let (clustered, b_srcs, e_srcs, _) =
                produce_clustered_scratch_description(&description, bcap, ecap);
            assert_eq!(b_srcs, base_polys_all);
            assert_eq!(e_srcs, ext_polys_all);
            let mut acc = [E::ZERO; 27];
            let mut best = std::time::Duration::MAX;
            for _ in 0..iters {
                let now = std::time::Instant::now();
                acc = evaluate_initial_with_bounded_scratch_parallel(
                    base_sources_all.clone(),
                    ext_sources_all.clone(),
                    &clustered,
                    eq_suffix_initial,
                    folding_steps,
                    worker,
                );
                best = best.min(now.elapsed());
            }
            assert_acc_eq(&acc, &acc_all, "clustered bounded scratch vs full-size");
            println!(
                "[B2] clustered {}b/{}e slots (loads: {} base / {} distinct, {} ext / {} distinct): {:?}",
                bcap,
                ecap,
                clustered.num_base_loads,
                clustered.num_distinct_base,
                clustered.num_ext_loads,
                clustered.num_distinct_ext,
                best,
            );
        }
    }

    // ---------------- variant C: split bb/be window + classic ee rounds ----------------
    let base_sources_bbbe = collect_base_sources(gkr_storage, &base_polys_bbbe);
    let ext_sources_bbbe = collect_ext_sources(gkr_storage, &ext_polys_bbbe);

    let mut acc_bbbe = [E::ZERO; 27];
    let mut best_c_window = std::time::Duration::MAX;
    for _ in 0..iters {
        let now = std::time::Instant::now();
        acc_bbbe = evaluate_initial_with_full_sized_scratch_parallel(
            base_sources_bbbe.clone(),
            ext_sources_bbbe.clone(),
            &compact_bbbe,
            eq_suffix_initial,
            folding_steps,
            worker,
        );
        best_c_window = best_c_window.min(now.elapsed());
    }

    // bounded-scratch flavor of the same window
    let mut best_c_window_bounded = std::time::Duration::MAX;
    {
        let (bounded, _, _) =
            produce_bounded_scratch_description(&desc_bbbe, 16, 8.min(ext_polys_bbbe.len().max(2)));
        let mut acc = [E::ZERO; 27];
        for _ in 0..iters {
            let now = std::time::Instant::now();
            acc = evaluate_initial_with_bounded_scratch_parallel(
                base_sources_bbbe.clone(),
                ext_sources_bbbe.clone(),
                &bounded,
                eq_suffix_initial,
                folding_steps,
                worker,
            );
            best_c_window_bounded = best_c_window_bounded.min(now.elapsed());
        }
        assert_acc_eq(
            &acc,
            &acc_bbbe,
            "bounded bbbe window vs full-size bbbe window",
        );
    }

    // window over ee-only terms: used for the split-identity check
    let ext_sources_ee = collect_ext_sources(gkr_storage, &ext_polys_ee);
    let acc_ee_window = evaluate_initial_with_full_sized_scratch_parallel(
        vec![],
        ext_sources_ee.clone(),
        &compact_ee,
        eq_suffix_initial,
        folding_steps,
        worker,
    );
    {
        let mut sum = acc_bbbe;
        for i in 0..27 {
            sum[i].add_assign(&acc_ee_window[i]);
        }
        assert_acc_eq(
            &sum,
            &acc_all,
            "bbbe window + ee window == all-terms window",
        );
    }

    // classic evaluation of the ee-only part for rounds 0..3
    let mut accumulator_buffer = vec![[E::ZERO; 2]; 1 << (folding_steps - 1)];
    let mut best_c_classic_ee = std::time::Duration::MAX;
    for _ in 0..iters {
        let res = run_classic_rounds(
            &desc_ee,
            gkr_storage,
            &window_challenges[..3],
            3,
            folding_steps,
            &eq_tables,
            &mut accumulator_buffer,
            worker,
        );
        best_c_classic_ee = best_c_classic_ee.min(res.total);
    }
    println!(
        "[C] window-3 rounds 0-2, bb+be+linear terms only, full-size scratch: {:?} (+ bounded 16b/8e flavor: {:?}); classic ee-only rounds 0-2: {:?}; split total: {:?}",
        best_c_window,
        best_c_window_bounded,
        best_c_classic_ee,
        best_c_window + best_c_classic_ee,
    );

    // ---------------- variant D: classic all-terms rounds 0..3 (baseline + validation) ----------------
    let mut best_d = std::time::Duration::MAX;
    let mut classic_all = None;
    for _ in 0..iters {
        let res = run_classic_rounds(
            &description,
            gkr_storage,
            &window_challenges[..3],
            3,
            folding_steps,
            &eq_tables,
            &mut accumulator_buffer,
            worker,
        );
        best_d = best_d.min(res.total);
        classic_all = Some(res.coeffs);
    }
    let classic_all = classic_all.unwrap();
    println!(
        "[D] classic per-round batched evaluation, ALL terms, rounds 0-2: {:?}",
        best_d
    );

    // validation of the window accumulator against the classic rounds through the bind chain
    {
        let eq_prefix_4: [E; 4] = make_eq_poly_in_full::<E>(&prev_challenges[1..3], worker)
            .pop()
            .unwrap()
            .to_vec()
            .try_into()
            .unwrap();
        let eq_prefix_2: [E; 2] = make_eq_poly_in_full::<E>(&prev_challenges[2..3], worker)
            .pop()
            .unwrap()
            .to_vec()
            .try_into()
            .unwrap();

        let round_0 = evaluate_claim_from_intermediate_matrix_27(&eq_prefix_4, &acc_all);
        assert_eq!(round_0[0], classic_all[0][0], "round 0: G(0) vs classic c0");
        assert_eq!(
            round_0[2], classic_all[0][1],
            "round 0: G_inf vs classic c2"
        );

        let acc_9 = bind_accumulator_27(&acc_all, &window_challenges[0]);
        let round_1 = evaluate_claim_from_intermediate_matrix_9(&eq_prefix_2, &acc_9);
        assert_eq!(round_1[0], classic_all[1][0], "round 1: G(0) vs classic c0");
        assert_eq!(
            round_1[2], classic_all[1][1],
            "round 1: G_inf vs classic c2"
        );

        let round_2 = bind_accumulator_9(&acc_9, &window_challenges[1]);
        assert_eq!(round_2[0], classic_all[2][0], "round 2: G(0) vs classic c0");
        assert_eq!(
            round_2[2], classic_all[2][1],
            "round 2: G_inf vs classic c2"
        );

        println!(
            "validation: window accumulator matches classic rounds 0-2 through the bind chain"
        );
    }

    // ---------------- transition round (round 3 + fold everything to ext) ----------------
    let buffer_size = trace_len / 8;
    let mut base_folding_buffers: Vec<Box<[MaybeUninit<E>]>> = base_polys_all
        .iter()
        .map(|_| Box::new_uninit_slice(buffer_size))
        .collect();
    let mut ext_folding_buffers: Vec<Box<[MaybeUninit<E>]>> = ext_polys_all
        .iter()
        .map(|_| Box::new_uninit_slice(buffer_size))
        .collect();
    println!(
        "transition folding buffers: {} polys x 2^{} ext elements (~{} GiB)",
        base_polys_all.len() + ext_polys_all.len(),
        buffer_size.trailing_zeros(),
        (base_polys_all.len() + ext_polys_all.len()) * buffer_size * core::mem::size_of::<E>()
            / (1 << 30),
    );

    type TI = TransitionRoundWindowIn3Out1;
    let transition_prefix =
        <TI as TransitionRoundImplementation<F, E>>::make_prefix_from_all_folding_challenges(
            &window_challenges[..3],
            worker,
        );
    let transition_work =
        <TI as TransitionRoundImplementation<F, E>>::work_size_for_unfolded_input_size(
            folding_steps,
        );
    let eq_suffix_transition = find_eq_with_len(&eq_tables, transition_work);

    let mut run_transition = |base_folding_buffers: &mut Vec<Box<[MaybeUninit<E>]>>,
                              ext_folding_buffers: &mut Vec<Box<[MaybeUninit<E>]>>|
     -> ([E; 2], std::time::Duration) {
        let base_buffers: Vec<_> = base_folding_buffers
            .iter_mut()
            .map(|el| DisjointAccessQuasiSlice::<_, true>::from_uninit_slice_mut(el))
            .collect();
        let ext_buffers: Vec<_> = ext_folding_buffers
            .iter_mut()
            .map(|el| DisjointAccessQuasiSlice::<_, true>::from_uninit_slice_mut(el))
            .collect();
        let now = std::time::Instant::now();
        let acc = evaluate_transition_with_full_sized_scratch_parallel::<F, E, TI>(
            base_sources_all.clone(),
            ext_sources_all.clone(),
            base_buffers,
            ext_buffers,
            &compact_all,
            &transition_prefix,
            eq_suffix_transition,
            folding_steps,
            worker,
        );
        (acc, now.elapsed())
    };

    let mut best_t = std::time::Duration::MAX;
    let mut transition_acc = [E::ZERO; 2];
    for _ in 0..iters {
        let (acc, took) = run_transition(&mut base_folding_buffers, &mut ext_folding_buffers);
        transition_acc = acc;
        best_t = best_t.min(took);
    }
    println!(
        "[T] transition round 3 (in 3, out 1; folds all polys to ext): {:?}",
        best_t
    );

    // validate transition against the classic step-3 coefficients
    {
        reset_folding_intermediates(gkr_storage);
        let res = run_classic_rounds(
            &description,
            gkr_storage,
            &window_challenges[..3],
            4,
            folding_steps,
            &eq_tables,
            &mut accumulator_buffer,
            worker,
        );
        assert_eq!(
            transition_acc[0], res.coeffs[3][0],
            "transition round: G(0) vs classic c0"
        );
        assert_eq!(
            transition_acc[1], res.coeffs[3][1],
            "transition round: G_inf vs classic c2"
        );
        println!("validation: transition round matches classic round 3");
    }
    drop(accumulator_buffer);

    // ---------------- SoA transition round ----------------
    #[cfg(target_arch = "aarch64")]
    {
        let base_ptrs: Vec<usize> = base_folding_buffers
            .iter_mut()
            .map(|el| el.as_mut_ptr() as usize)
            .collect();
        let ext_ptrs: Vec<usize> = ext_folding_buffers
            .iter_mut()
            .map(|el| el.as_mut_ptr() as usize)
            .collect();
        let mut acc_ts = [E::ZERO; 2];
        let mut best_ts = std::time::Duration::MAX;
        for _ in 0..iters {
            let now = std::time::Instant::now();
            acc_ts = evaluate_transition_soa_parallel(
                &base_sources_all,
                &ext_sources_all,
                &base_ptrs,
                &ext_ptrs,
                &forms,
                &products,
                &folded_quad,
                &folded_lin,
                &description.constant_term,
                &transition_prefix,
                eq_suffix_transition,
                folding_steps,
                worker,
            );
            best_ts = best_ts.min(now.elapsed());
        }
        assert_eq!(acc_ts[0], transition_acc[0], "SoA transition: G(0)");
        assert_eq!(acc_ts[1], transition_acc[1], "SoA transition: G_inf");
        println!(
            "[TS] SoA transition round 3 (in 3, out 1): {:?} (AoS [T]: {:?})",
            best_ts, best_t,
        );
    }

    // ---------------- transition with Lagrange fold weights (uniskip wiring) ----------------
    #[cfg(target_arch = "aarch64")]
    {
        use ::field::baby_bear::base::BabyBearField;
        let omega16_bb = ::fft::domain_generator_for_size::<BabyBearField>(16);
        let mut omega8_bb = omega16_bb;
        omega8_bb.square();

        // L_j(r) = (r^8 - 1) * u_j / (8 (r - u_j)) for u_j in H = <w8>
        let r = window_challenges[0];
        let mut z = r.pow(8);
        z.sub_assign(&E::ONE);
        let eighth_bb = BabyBearField::from_u32_with_reduction(8).inverse().unwrap();
        let lagrange: [E; 8] = core::array::from_fn(|j| {
            let uj_bb = omega8_bb.pow(j as u32);
            let uj = E::from_base(unsafe { *(&uj_bb as *const _ as *const F) });
            let mut denom = r;
            denom.sub_assign(&uj);
            let mut w = z;
            w.mul_assign(&uj);
            w.mul_assign(&denom.inverse().expect("r not in H"));
            w.mul_assign_by_base(unsafe { &*(&eighth_bb as *const _ as *const F) });
            w
        });

        let base_ptrs: Vec<usize> = base_folding_buffers
            .iter_mut()
            .map(|el| el.as_mut_ptr() as usize)
            .collect();
        let ext_ptrs: Vec<usize> = ext_folding_buffers
            .iter_mut()
            .map(|el| el.as_mut_ptr() as usize)
            .collect();
        let now = std::time::Instant::now();
        let _acc_t = evaluate_transition_soa_parallel(
            &base_sources_all,
            &ext_sources_all,
            &base_ptrs,
            &ext_ptrs,
            &forms,
            &products,
            &folded_quad,
            &folded_lin,
            &description.constant_term,
            &lagrange,
            eq_suffix_transition,
            folding_steps,
            worker,
        );
        let t_time = now.elapsed();

        // spot-check the Lagrange fold: buffer values must equal the packed
        // poly evaluated at r
        let src0 = &base_sources_all[0];
        for pos in [0usize, 12345] {
            let mut expected = E::ZERO;
            for j in 0..8usize {
                let stride = trace_len / 8;
                let v = src0.read(pos + j * stride);
                let mut t = lagrange[j];
                t.mul_assign_by_base(&v);
                expected.add_assign(&t);
            }
            let got = unsafe { base_folding_buffers[0][pos].assume_init() };
            assert_eq!(got, expected, "Lagrange fold mismatch at {}", pos);
        }
        println!(
            "[UT] transition with Lagrange fold weights (uniskip wiring): {:?} (eq-fold [TS] above)",
            t_time
        );
        println!("validation: Lagrange fold matches direct packed-poly evaluation at r");
    }

    // ---------------- merged transition + in1out3 experiment ----------------
    // Reference: buffers currently hold fold-by-(w0..w2); run one in1out3 pass
    // on them to get the rounds-4-6 accumulator + folded-by-w3 buffers.
    {
        use super::full_size_scratch::merged_transition::evaluate_merged_transition_in1out3_parallel;
        type I13 = ExtensionOnlyRoundWindowIn1Out3;

        let cur_log2 = folding_steps - 3;
        let i13_work =
            <I13 as ExtensionOnlyRoundImplementation<F, E>>::work_size_for_unfolded_input_size(
                cur_log2,
            );
        let i13_prefix =
            <I13 as ExtensionOnlyRoundImplementation<F, E>>::make_prefix_from_all_folding_challenges(
                &window_challenges[..4],
                worker,
            );
        let eq_suffix_i13 = find_eq_with_len(&eq_tables, i13_work);

        let mut run_i13 = |base_folding_buffers: &mut Vec<Box<[MaybeUninit<E>]>>,
                           ext_folding_buffers: &mut Vec<Box<[MaybeUninit<E>]>>|
         -> ([E; 27], std::time::Duration) {
            let base_buffers: Vec<_> = base_folding_buffers
                .iter_mut()
                .map(|el| DisjointAccessQuasiSlice::<_, false>::from_uninit_slice_mut(el))
                .collect();
            let ext_buffers: Vec<_> = ext_folding_buffers
                .iter_mut()
                .map(|el| DisjointAccessQuasiSlice::<_, false>::from_uninit_slice_mut(el))
                .collect();
            let now = std::time::Instant::now();
            let acc = evaluate_extension_only_rounds_with_full_sized_scratch_parallel::<F, E, I13>(
                base_buffers,
                ext_buffers,
                &compact_all,
                &i13_prefix,
                eq_suffix_i13,
                cur_log2,
                worker,
            );
            (acc, now.elapsed())
        };

        // time the separate in1out3 (needs fresh transition output each iter
        // because the pass folds in place)
        let mut best_i13 = std::time::Duration::MAX;
        let mut acc27_ref = [E::ZERO; 27];
        for i in 0..iters {
            if i > 0 {
                let _ = run_transition(&mut base_folding_buffers, &mut ext_folding_buffers);
            }
            let (acc, took) = run_i13(&mut base_folding_buffers, &mut ext_folding_buffers);
            acc27_ref = acc;
            best_i13 = best_i13.min(took);
        }

        // snapshot the folded-by-w3 buffer halves for validation
        let half = buffer_size / 2;
        let snapshot: Vec<Vec<E>> = base_folding_buffers
            .iter()
            .chain(ext_folding_buffers.iter())
            .map(|el| (0..half).map(|i| unsafe { el[i].assume_init() }).collect())
            .collect();

        // merged pass setup
        let eq_mid = make_eq_poly_in_full::<E>(&prev_challenges[4..7], worker)
            .pop()
            .unwrap();
        let eq_suffix_merged = find_eq_with_len(&eq_tables, i13_work);
        assert_eq!(eq_suffix_merged.len(), 1 << (folding_steps - 7));

        let mut best_merged = std::time::Duration::MAX;
        let mut acc2_m = [E::ZERO; 2];
        let mut acc27_m = [E::ZERO; 27];
        for _ in 0..iters {
            let base_buffers: Vec<_> = base_folding_buffers
                .iter_mut()
                .map(|el| DisjointAccessQuasiSlice::<_, true>::from_uninit_slice_mut(el))
                .collect();
            let ext_buffers: Vec<_> = ext_folding_buffers
                .iter_mut()
                .map(|el| DisjointAccessQuasiSlice::<_, true>::from_uninit_slice_mut(el))
                .collect();
            let now = std::time::Instant::now();
            let (a2, a27) = evaluate_merged_transition_in1out3_parallel(
                base_sources_all.clone(),
                ext_sources_all.clone(),
                base_buffers,
                ext_buffers,
                &compact_all,
                &transition_prefix,
                &window_challenges[3],
                &eq_mid,
                eq_suffix_merged,
                folding_steps,
                worker,
            );
            best_merged = best_merged.min(now.elapsed());
            acc2_m = a2;
            acc27_m = a27;
        }

        assert_eq!(acc2_m[0], transition_acc[0], "merged: round-3 G(0)");
        assert_eq!(acc2_m[1], transition_acc[1], "merged: round-3 G_inf");
        for i in 0..27 {
            assert_eq!(acc27_m[i], acc27_ref[i], "merged: rounds 4-6 cell {}", i);
        }
        for (poly_idx, expected) in snapshot.iter().enumerate() {
            let buf = if poly_idx < base_folding_buffers.len() {
                &base_folding_buffers[poly_idx]
            } else {
                &ext_folding_buffers[poly_idx - base_folding_buffers.len()]
            };
            for i in 0..half {
                let got = unsafe { buf[i].assume_init() };
                assert_eq!(got, expected[i], "merged: buffer {} at {}", poly_idx, i);
            }
        }
        println!("validation: merged pass matches transition acc, in1out3 acc and folded buffers");
        println!(
            "[M] merged transition+in1out3 (rounds 3-6, fused fold): {:?} vs separate {:?} + {:?} = {:?}",
            best_merged,
            best_t,
            best_i13,
            best_t + best_i13,
        );
    }

    // ---------------- ext-only rounds: windows of 1 / 2 / 3 ----------------
    // Chains are timing-only at this scale (the window-2/3 chains fold dummy
    // pending challenges); impl correctness is covered by the synthetic test.
    let ext_state_log2 = buffer_size.trailing_zeros() as usize;
    let min_work_size = 32;

    let (w1_time, w1_rounds) = {
        run_transition(&mut base_folding_buffers, &mut ext_folding_buffers);
        time_ext_only_chain::<F, E, ExtensionOnlyRoundWindowIn1Out1>(
            &mut base_folding_buffers,
            &mut ext_folding_buffers,
            &compact_all,
            &eq_tables,
            ext_state_log2,
            min_work_size,
            worker,
        )
    };
    println!(
        "[E1] ext-only rounds, window 1: {} rounds in {:?}",
        w1_rounds, w1_time
    );

    let (w2_time, w2_rounds) = {
        run_transition(&mut base_folding_buffers, &mut ext_folding_buffers);
        time_ext_only_chain::<F, E, ExtensionOnlyRoundWindowIn2Out2>(
            &mut base_folding_buffers,
            &mut ext_folding_buffers,
            &compact_all,
            &eq_tables,
            ext_state_log2,
            min_work_size,
            worker,
        )
    };
    println!(
        "[E2] ext-only rounds, window 2: {} rounds in {:?}",
        w2_rounds, w2_time
    );

    let (w3_time, w3_rounds) = {
        run_transition(&mut base_folding_buffers, &mut ext_folding_buffers);
        time_ext_only_chain::<F, E, ExtensionOnlyRoundWindowIn3Out3>(
            &mut base_folding_buffers,
            &mut ext_folding_buffers,
            &compact_all,
            &eq_tables,
            ext_state_log2,
            min_work_size,
            worker,
        )
    };
    println!(
        "[E3] ext-only rounds, window 3: {} rounds in {:?}",
        w3_rounds, w3_time
    );

    // ---------------- full windowed chain vs naive per-round loop ----------------
    println!("full chain: window-3 initial -> transition in3out1 -> in1out3 -> in3out3... -> in3out1 -> in1out1");
    let soa_prog = SoaInitialProgram {
        base_interp: &base_interp,
        ext_interp: &ext_interp,
        forms: &forms,
        products: &products,
        rest_steps: &rest_steps,
        folded_quad: &folded_quad,
        folded_lin: &folded_lin,
        additive_constant: description.constant_term,
    };
    let mut best_chain = std::time::Duration::MAX;
    let mut chain_rounds = None;
    for iter in 0..iters {
        let (rounds, took) = run_windowed_full_chain(
            &compact_all,
            &base_sources_all,
            &ext_sources_all,
            &mut base_folding_buffers,
            &mut ext_folding_buffers,
            &prev_challenges,
            &window_challenges,
            &eq_tables,
            folding_steps,
            iter == iters - 1,
            Some(&soa_prog),
            worker,
        );
        best_chain = best_chain.min(took);
        chain_rounds = Some(rounds);
    }
    let chain_rounds = chain_rounds.unwrap();
    println!(
        "[F] full windowed chain, all {} rounds: {:?}",
        folding_steps, best_chain
    );

    let mut best_chain_v2 = std::time::Duration::MAX;
    let mut chain_v2_rounds = None;
    for iter in 0..iters {
        let (rounds, took) = run_windowed_full_chain_v2(
            &compact_all,
            &base_sources_all,
            &ext_sources_all,
            &mut base_folding_buffers,
            &mut ext_folding_buffers,
            &prev_challenges,
            &window_challenges,
            &eq_tables,
            folding_steps,
            iter == iters - 1,
            worker,
        );
        best_chain_v2 = best_chain_v2.min(took);
        chain_v2_rounds = Some(rounds);
    }
    let chain_v2_rounds = chain_v2_rounds.unwrap();
    println!(
        "[F2] full windowed chain v2 (in3out3 transition), all {} rounds: {:?}",
        folding_steps, best_chain_v2
    );

    let mut accumulator_buffer = vec![[E::ZERO; 2]; 1 << (folding_steps - 1)];
    let mut best_naive = std::time::Duration::MAX;
    let mut naive_rounds = None;
    for _ in 0..iters {
        let res = run_classic_rounds(
            &description,
            gkr_storage,
            &window_challenges,
            folding_steps,
            folding_steps,
            &eq_tables,
            &mut accumulator_buffer,
            worker,
        );
        best_naive = best_naive.min(res.total);
        naive_rounds = Some(res.coeffs);
    }
    let naive_rounds = naive_rounds.unwrap();
    println!(
        "[N] naive per-round loop, all {} rounds: {:?}",
        folding_steps, best_naive
    );

    for (i, (a, b)) in chain_rounds.iter().zip(naive_rounds.iter()).enumerate() {
        assert_eq!(
            a[0], b[0],
            "round {}: G(0) diverged between chain and naive",
            i
        );
        assert_eq!(
            a[1], b[1],
            "round {}: G_inf diverged between chain and naive",
            i
        );
    }
    for (i, (a, b)) in chain_v2_rounds.iter().zip(naive_rounds.iter()).enumerate() {
        assert_eq!(
            a[0], b[0],
            "round {}: G(0) diverged between chain v2 and naive",
            i
        );
        assert_eq!(
            a[1], b[1],
            "round {}: G_inf diverged between chain v2 and naive",
            i
        );
    }
    println!(
        "validation: both windowed chains match the naive per-round loop on all {} rounds",
        folding_steps
    );
    drop(accumulator_buffer);

    println!("==== summary ====");
    println!(
        "initial 3 rounds:  window-3 all-terms full scratch  {:?}",
        best_a
    );
    println!(
        "                   split (bb/be window + classic ee) {:?}",
        best_c_window + best_c_classic_ee
    );
    println!(
        "                   classic per-round baseline        {:?}",
        best_d
    );
    println!(
        "round 3 + fold:    transition in3out1                {:?}",
        best_t
    );
    println!(
        "ext-only rounds:   w1 {:?} ({} rounds), w2 {:?} ({} rounds), w3 {:?} ({} rounds)",
        w1_time, w1_rounds, w2_time, w2_rounds, w3_time, w3_rounds
    );
    println!(
        "full sumcheck:     windowed chain (in3out1 trans.)   {:?}",
        best_chain
    );
    println!(
        "                   windowed chain (in3out3 trans.)   {:?}",
        best_chain_v2
    );
    println!(
        "                   naive per-round loop              {:?}",
        best_naive
    );
}

#[cfg(test)]
mod synthetic_tests {
    use super::*;
    use ::field::baby_bear::base::BabyBearField;
    use ::field::baby_bear::ext4::BabyBearExt4;

    type F = BabyBearField;
    type E = BabyBearExt4;

    fn pseudo_base(seed: &mut u64) -> F {
        *seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        F::from_u32_with_reduction((*seed >> 33) as u32)
    }

    fn pseudo_ext(seed: &mut u64) -> E {
        E::from_array_of_base(core::array::from_fn(|_| pseudo_base(seed)))
    }

    /// value of a poly at window coords in {0, 1, 2=inf}^W (top W variables),
    /// remaining variables fixed at `row`
    fn grid_value<T: Field, const W: usize>(
        poly: &[T],
        size: usize,
        row: usize,
        coords: [usize; W],
    ) -> T {
        // enumerate binary corners with signs induced by the inf-coordinates
        let mut result = T::ZERO;
        let num_corners = 1usize << W;
        'corner: for corner in 0..num_corners {
            let mut sign_negative = false;
            let mut offset = row;
            for var in 0..W {
                let stride = size >> (var + 1);
                let bit = (corner >> (W - 1 - var)) & 1;
                match coords[var] {
                    0 => {
                        if bit == 1 {
                            continue 'corner;
                        }
                    }
                    1 => {
                        if bit == 0 {
                            continue 'corner;
                        }
                        offset += stride;
                    }
                    2 => {
                        if bit == 1 {
                            offset += stride;
                        } else {
                            sign_negative = !sign_negative;
                        }
                    }
                    _ => unreachable!(),
                }
            }
            let v = poly[offset];
            if sign_negative {
                result.sub_assign(&v);
            } else {
                result.add_assign(&v);
            }
        }
        result
    }

    fn cell_coords<const W: usize>(cell: usize) -> [usize; W] {
        let mut coords = [0usize; W];
        let mut c = cell;
        for i in (0..W).rev() {
            coords[i] = c % 3;
            c /= 3;
        }
        coords
    }

    fn is_binary<const W: usize>(coords: &[usize; W]) -> bool {
        coords.iter().all(|el| *el < 2)
    }

    struct SyntheticInstance {
        base_polys: Vec<Vec<F>>,
        ext_polys: Vec<Vec<E>>,
        description: BatchedGKRDescription<F, E>,
    }

    fn make_instance(size: usize, seed: &mut u64) -> SyntheticInstance {
        let num_base = 4;
        let num_ext = 3;
        let base_polys: Vec<Vec<F>> = (0..num_base)
            .map(|_| (0..size).map(|_| pseudo_base(seed)).collect())
            .collect();
        let ext_polys: Vec<Vec<E>> = (0..num_ext)
            .map(|_| (0..size).map(|_| pseudo_ext(seed)).collect())
            .collect();

        let baddr = |i: usize| GKRAddress::InnerLayer {
            layer: 0,
            offset: i,
        };
        let eaddr = |i: usize| GKRAddress::InnerLayer {
            layer: 0,
            offset: num_base + i,
        };

        let mut description = BatchedGKRDescription::<F, E>::default();
        description.quadratic_part_base_by_base = vec![
            (
                baddr(0),
                vec![(baddr(1), pseudo_ext(seed)), (baddr(2), pseudo_ext(seed))],
            ),
            (baddr(1), vec![(baddr(3), pseudo_ext(seed))]),
        ];
        description.quadratic_part_base_by_ext = vec![
            (baddr(0), vec![(eaddr(0), pseudo_ext(seed))]),
            (baddr(3), vec![(eaddr(1), pseudo_ext(seed))]),
        ];
        description.quadratic_part_ext_by_ext = vec![
            (eaddr(0), vec![(eaddr(1), pseudo_ext(seed))]),
            (eaddr(1), vec![(eaddr(2), pseudo_ext(seed))]),
        ];
        description.linear_part_base_by_everything =
            vec![(baddr(2), pseudo_ext(seed)), (baddr(3), pseudo_ext(seed))];
        description.linear_part_ext_by_everything = vec![(eaddr(2), pseudo_ext(seed))];
        description.constant_term = pseudo_ext(seed);

        SyntheticInstance {
            base_polys,
            ext_polys,
            description,
        }
    }

    /// brute-force 27-cell accumulator for the initial window over raw sources
    fn reference_initial_accumulator(
        inst: &SyntheticInstance,
        eq_suffix: &[E],
        size: usize,
    ) -> [E; 27] {
        let num_base = inst.base_polys.len();
        let bidx = |addr: &GKRAddress| match addr {
            GKRAddress::InnerLayer { offset, .. } => *offset as usize,
            _ => unreachable!(),
        };
        let eidx = |addr: &GKRAddress| match addr {
            GKRAddress::InnerLayer { offset, .. } => *offset as usize - num_base,
            _ => unreachable!(),
        };

        let mut acc = [E::ZERO; 27];
        for row in 0..size / 8 {
            for cell in 0..27 {
                let coords = cell_coords::<3>(cell);
                let mut val = E::ZERO;
                for (a, list) in inst.description.quadratic_part_base_by_base.iter() {
                    let ag = grid_value::<F, 3>(&inst.base_polys[bidx(a)], size, row, coords);
                    for (b, c) in list.iter() {
                        let bg = grid_value::<F, 3>(&inst.base_polys[bidx(b)], size, row, coords);
                        let mut t = ag;
                        t.mul_assign(&bg);
                        let mut term = *c;
                        term.mul_assign_by_base(&t);
                        val.add_assign(&term);
                    }
                }
                for (a, list) in inst.description.quadratic_part_base_by_ext.iter() {
                    let ag = grid_value::<F, 3>(&inst.base_polys[bidx(a)], size, row, coords);
                    for (b, c) in list.iter() {
                        let bg = grid_value::<E, 3>(&inst.ext_polys[eidx(b)], size, row, coords);
                        let mut t = bg;
                        t.mul_assign_by_base(&ag);
                        t.mul_assign(c);
                        val.add_assign(&t);
                    }
                }
                for (a, list) in inst.description.quadratic_part_ext_by_ext.iter() {
                    let ag = grid_value::<E, 3>(&inst.ext_polys[eidx(a)], size, row, coords);
                    for (b, c) in list.iter() {
                        let bg = grid_value::<E, 3>(&inst.ext_polys[eidx(b)], size, row, coords);
                        let mut t = ag;
                        t.mul_assign(&bg);
                        t.mul_assign(c);
                        val.add_assign(&t);
                    }
                }
                if is_binary(&coords) {
                    for (a, c) in inst.description.linear_part_base_by_everything.iter() {
                        let ag = grid_value::<F, 3>(&inst.base_polys[bidx(a)], size, row, coords);
                        let mut t = *c;
                        t.mul_assign_by_base(&ag);
                        val.add_assign(&t);
                    }
                    for (a, c) in inst.description.linear_part_ext_by_everything.iter() {
                        let ag = grid_value::<E, 3>(&inst.ext_polys[eidx(a)], size, row, coords);
                        let mut t = *c;
                        t.mul_assign(&ag);
                        val.add_assign(&t);
                    }
                    val.add_assign(&inst.description.constant_term);
                }
                val.mul_assign(&eq_suffix[row]);
                acc[cell].add_assign(&val);
            }
        }
        acc
    }

    #[test]
    fn initial_window_matches_reference() {
        let worker = Worker::new_with_num_threads(1);
        let mut seed = 42u64;
        const SIZE_LOG2: usize = 7;
        let size = 1 << SIZE_LOG2;
        let inst = make_instance(size, &mut seed);

        let suffix_challenges: Vec<E> = (0..SIZE_LOG2 - 3).map(|_| pseudo_ext(&mut seed)).collect();
        let eq_suffix = make_eq_poly_in_full::<E>(&suffix_challenges, &worker)
            .pop()
            .unwrap();
        assert_eq!(eq_suffix.len(), size / 8);

        let reference = reference_initial_accumulator(&inst, &eq_suffix, size);

        let (compact, base_addrs, ext_addrs) =
            produce_descriptions_from_batched_description(&inst.description);
        assert_eq!(base_addrs.len(), inst.base_polys.len());
        assert_eq!(ext_addrs.len(), inst.ext_polys.len());

        let base_sources: Vec<_> = inst
            .base_polys
            .iter()
            .map(|el| DisjointAccessQuasiSlice::<_, false>::from_init_slice(&el[..]))
            .collect();
        let ext_sources: Vec<_> = inst
            .ext_polys
            .iter()
            .map(|el| DisjointAccessQuasiSlice::<_, false>::from_init_slice(&el[..]))
            .collect();

        let acc_full = evaluate_initial_with_full_sized_scratch_parallel(
            base_sources.clone(),
            ext_sources.clone(),
            &compact,
            &eq_suffix,
            SIZE_LOG2,
            &worker,
        );
        assert_acc_eq(&acc_full, &reference, "full-size scratch vs brute force");

        for (bcap, ecap) in [(2usize, 2usize), (3, 2), (4, 3)] {
            let (bounded, _, _) =
                produce_bounded_scratch_description(&inst.description, bcap, ecap);
            let acc_bounded = evaluate_initial_with_bounded_scratch_parallel(
                base_sources.clone(),
                ext_sources.clone(),
                &bounded,
                &eq_suffix,
                SIZE_LOG2,
                &worker,
            );
            assert_acc_eq(
                &acc_bounded,
                &reference,
                &format!("bounded scratch ({bcap}/{ecap}) vs brute force"),
            );
        }

        // split identity: bb/be window + ee window == all
        let (desc_bbbe, desc_ee) = split_batched_description(&inst.description);
        let (compact_bbbe, bbbe_base, bbbe_ext) =
            produce_descriptions_from_batched_description(&desc_bbbe);
        let (compact_ee, ee_base, ee_ext) = produce_descriptions_from_batched_description(&desc_ee);
        assert!(ee_base.is_empty());
        let bbbe_base_sources: Vec<_> = bbbe_base
            .iter()
            .map(|a| match a {
                GKRAddress::InnerLayer { offset, .. } => {
                    DisjointAccessQuasiSlice::<_, false>::from_init_slice(
                        &inst.base_polys[*offset as usize][..],
                    )
                }
                _ => unreachable!(),
            })
            .collect();
        let num_base = inst.base_polys.len();
        let bbbe_ext_sources: Vec<_> = bbbe_ext
            .iter()
            .map(|a| match a {
                GKRAddress::InnerLayer { offset, .. } => {
                    DisjointAccessQuasiSlice::<_, false>::from_init_slice(
                        &inst.ext_polys[*offset as usize - num_base][..],
                    )
                }
                _ => unreachable!(),
            })
            .collect();
        let ee_ext_sources: Vec<_> = ee_ext
            .iter()
            .map(|a| match a {
                GKRAddress::InnerLayer { offset, .. } => {
                    DisjointAccessQuasiSlice::<_, false>::from_init_slice(
                        &inst.ext_polys[*offset as usize - num_base][..],
                    )
                }
                _ => unreachable!(),
            })
            .collect();

        let acc_bbbe = evaluate_initial_with_full_sized_scratch_parallel(
            bbbe_base_sources,
            bbbe_ext_sources,
            &compact_bbbe,
            &eq_suffix,
            SIZE_LOG2,
            &worker,
        );
        let acc_ee = evaluate_initial_with_full_sized_scratch_parallel(
            vec![],
            ee_ext_sources,
            &compact_ee,
            &eq_suffix,
            SIZE_LOG2,
            &worker,
        );
        let mut sum = acc_bbbe;
        for i in 0..27 {
            sum[i].add_assign(&acc_ee[i]);
        }
        assert_acc_eq(&sum, &reference, "bbbe + ee windows vs brute force");
    }

    /// fold the top `w` variables of `poly` at the given challenges
    fn fold_top_vars<T: Field>(poly: &[T], challenges: &[T]) -> Vec<T> {
        let mut current = poly.to_vec();
        for c in challenges.iter() {
            let half = current.len() / 2;
            let mut next = Vec::with_capacity(half);
            for i in 0..half {
                let mut t = current[half + i];
                t.sub_assign(&current[i]);
                t.mul_assign(c);
                t.add_assign(&current[i]);
                next.push(t);
            }
            current = next;
        }
        current
    }

    /// brute-force 3^W accumulator for an ext-only pass: the pass folds the
    /// pending challenges as it reads and accumulates the grid over the next W
    /// variables of an ee-only + linear-ext + constant description
    fn reference_ext_only_accumulator<const W: usize, const CELLS: usize>(
        ext_polys: &[Vec<E>],
        description: &BatchedGKRDescription<F, E>,
        num_base: usize,
        pending: &[E],
        eq_suffix: &[E],
    ) -> [E; CELLS] {
        assert_eq!(CELLS, 3usize.pow(W as u32));
        let folded: Vec<Vec<E>> = ext_polys
            .iter()
            .map(|el| fold_top_vars(&el[..], pending))
            .collect();
        let size = folded[0].len();
        let rows = size >> W;
        assert_eq!(eq_suffix.len(), rows);

        let eidx = |addr: &GKRAddress| match addr {
            GKRAddress::InnerLayer { offset, .. } => *offset as usize - num_base,
            _ => unreachable!(),
        };

        let mut acc = [E::ZERO; CELLS];
        for row in 0..rows {
            for cell in 0..CELLS {
                let coords = cell_coords::<W>(cell);
                let mut val = E::ZERO;
                for (a, list) in description.quadratic_part_ext_by_ext.iter() {
                    let ag = grid_value::<E, W>(&folded[eidx(a)], size, row, coords);
                    for (b, c) in list.iter() {
                        let bg = grid_value::<E, W>(&folded[eidx(b)], size, row, coords);
                        let mut t = ag;
                        t.mul_assign(&bg);
                        t.mul_assign(c);
                        val.add_assign(&t);
                    }
                }
                if is_binary(&coords) {
                    for (a, c) in description.linear_part_ext_by_everything.iter() {
                        let ag = grid_value::<E, W>(&folded[eidx(a)], size, row, coords);
                        let mut t = *c;
                        t.mul_assign(&ag);
                        val.add_assign(&t);
                    }
                    val.add_assign(&description.constant_term);
                }
                val.mul_assign(&eq_suffix[row]);
                acc[cell].add_assign(&val);
            }
        }
        acc
    }

    fn run_ext_only_pass<I: ExtensionOnlyRoundImplementation<F, E>>(
        ext_polys: &[Vec<E>],
        compact: &BatchEvaluationCompactDescription<F, E>,
        pending: &[E],
        eq_suffix: &[E],
        size_log2: usize,
        worker: &Worker,
    ) -> I::AccumulatorOutput {
        // the pass folds in place: work on copies presented as folding buffers
        let mut copies: Vec<Vec<E>> = ext_polys.iter().cloned().collect();
        let buffers: Vec<_> = copies
            .iter_mut()
            .map(|el| DisjointAccessQuasiSlice::<_, false>::from_init_slice_mut(&mut el[..]))
            .collect();
        let prefix = I::make_prefix_from_all_folding_challenges(pending, worker);
        evaluate_extension_only_rounds_with_full_sized_scratch_parallel::<F, E, I>(
            vec![],
            buffers,
            compact,
            &prefix,
            eq_suffix,
            size_log2,
            worker,
        )
    }

    #[test]
    fn uniskip_initial_matches_reference() {
        use ::field::baby_bear::base::BabyBearField;

        let worker = Worker::new_with_num_threads(1);
        let mut seed = 4242u64;
        const SIZE_LOG2: usize = 8;
        let size = 1 << SIZE_LOG2;
        let inst = make_instance(size, &mut seed);
        let num_base = inst.base_polys.len();

        let omega16 = ::fft::domain_generator_for_size::<BabyBearField>(16);
        let mut omega8 = omega16;
        omega8.square();
        let lde_tables = super::super::neon::SoaLde8Tables::new(omega8, omega16);

        // all-expanded steps over the instance description
        let bidx = |a: &GKRAddress| match a {
            GKRAddress::InnerLayer { offset, .. } => *offset as u16,
            _ => unreachable!(),
        };
        let eidx = |a: &GKRAddress| match a {
            GKRAddress::InnerLayer { offset, .. } => (*offset - num_base) as u16,
            _ => unreachable!(),
        };
        let mut steps: Vec<BenchStep<E>> = vec![];
        for (a, list) in inst.description.quadratic_part_base_by_base.iter() {
            for (b, c) in list.iter() {
                steps.push(BenchStep::QuadBB { a: bidx(a), b: bidx(b), c: *c });
            }
        }
        for (a, list) in inst.description.quadratic_part_base_by_ext.iter() {
            for (b, c) in list.iter() {
                steps.push(BenchStep::QuadBE { base: bidx(a), ext: eidx(b), c: *c });
            }
        }
        for (a, list) in inst.description.quadratic_part_ext_by_ext.iter() {
            for (b, c) in list.iter() {
                steps.push(BenchStep::QuadEE { a: eidx(a), b: eidx(b), c: *c });
            }
        }
        for (a, c) in inst.description.linear_part_base_by_everything.iter() {
            steps.push(BenchStep::LinB { i: bidx(a), c: *c });
        }
        for (a, c) in inst.description.linear_part_ext_by_everything.iter() {
            steps.push(BenchStep::LinE { i: eidx(a), c: *c });
        }

        let work = size / 8;
        let suffix_challenges: Vec<E> = (0..(work.trailing_zeros() as usize))
            .map(|_| pseudo_ext(&mut seed))
            .collect();
        let eq_suffix = make_eq_poly_in_full::<E>(&suffix_challenges, &worker)
            .pop()
            .unwrap();

        let base_sources: Vec<_> = inst
            .base_polys
            .iter()
            .map(|el| DisjointAccessQuasiSlice::<_, false>::from_init_slice(&el[..]))
            .collect();
        let ext_sources: Vec<_> = inst
            .ext_polys
            .iter()
            .map(|el| DisjointAccessQuasiSlice::<_, false>::from_init_slice(&el[..]))
            .collect();

        let acc = evaluate_initial_uniskip_soa_parallel::<F, E>(
            &base_sources,
            &ext_sources,
            &[],
            &[],
            &steps,
            &inst.description.constant_term,
            &lde_tables,
            &eq_suffix,
            SIZE_LOG2,
            &worker,
        );

        // scalar reference: per block, interpolate each poly's 8 packed values
        // (inverse DFT with base roots) and evaluate q at all 16 domain points
        let omega8_inv = omega8.inverse().unwrap();
        let eighth = BabyBearField::from_u32_with_reduction(8).inverse().unwrap();
        let f_of = |v: BabyBearField| -> F { unsafe { *(&v as *const _ as *const F) } };

        // domain points: u_j = omega8^j (j<8), then omega16 * omega8^(j-8)
        let point = |idx: usize| -> BabyBearField {
            if idx < 8 {
                omega8.pow(idx as u32)
            } else {
                let mut t = omega16;
                t.mul_assign(&omega8.pow((idx - 8) as u32));
                t
            }
        };

        // coefficients of the packed poly from 8 E-values (base-field roots)
        let coeffs_from = |vals: &[E; 8]| -> [E; 8] {
            core::array::from_fn(|i| {
                let mut acc = E::ZERO;
                for j in 0..8 {
                    let mut t = vals[j];
                    let w = omega8_inv.pow((i * j % 8) as u32);
                    t.mul_assign_by_base(&f_of(w));
                    acc.add_assign(&t);
                }
                acc.mul_assign_by_base(&f_of(eighth));
                acc
            })
        };
        let eval_at = |c: &[E; 8], x: BabyBearField| -> E {
            let mut acc = E::ZERO;
            for i in (0..8).rev() {
                acc.mul_assign_by_base(&f_of(x));
                acc.add_assign(&c[i]);
            }
            acc
        };

        let stride = size / 8;
        let mut reference = [E::ZERO; 16];
        for row in 0..work {
            // packed values per poly at the 16 points
            let mut packed: Vec<[E; 16]> = vec![[E::ZERO; 16]; num_base + inst.ext_polys.len()];
            for (slot, poly) in inst.base_polys.iter().enumerate() {
                let vals: [E; 8] =
                    core::array::from_fn(|j| E::from_base(poly[row + j * stride]));
                let c = coeffs_from(&vals);
                for idx in 0..16 {
                    packed[slot][idx] = eval_at(&c, point(idx));
                }
            }
            for (k, poly) in inst.ext_polys.iter().enumerate() {
                let vals: [E; 8] = core::array::from_fn(|j| poly[row + j * stride]);
                let c = coeffs_from(&vals);
                for idx in 0..16 {
                    packed[num_base + k][idx] = eval_at(&c, point(idx));
                }
            }
            for idx in 0..16 {
                let mut val = E::ZERO;
                for step in steps.iter() {
                    match step {
                        BenchStep::QuadBB { a, b, c } => {
                            let mut t = packed[*a as usize][idx];
                            t.mul_assign(&packed[*b as usize][idx]);
                            t.mul_assign(c);
                            val.add_assign(&t);
                        }
                        BenchStep::QuadBE { base, ext, c } => {
                            let mut t = packed[*base as usize][idx];
                            t.mul_assign(&packed[num_base + *ext as usize][idx]);
                            t.mul_assign(c);
                            val.add_assign(&t);
                        }
                        BenchStep::QuadEE { a, b, c } => {
                            let mut t = packed[num_base + *a as usize][idx];
                            t.mul_assign(&packed[num_base + *b as usize][idx]);
                            t.mul_assign(c);
                            val.add_assign(&t);
                        }
                        BenchStep::LinB { i, c } => {
                            let mut t = packed[*i as usize][idx];
                            t.mul_assign(c);
                            val.add_assign(&t);
                        }
                        BenchStep::LinE { i, c } => {
                            let mut t = packed[num_base + *i as usize][idx];
                            t.mul_assign(c);
                            val.add_assign(&t);
                        }
                    }
                }
                val.add_assign(&inst.description.constant_term);
                val.mul_assign(&eq_suffix[row]);
                reference[idx].add_assign(&val);
            }
        }

        for idx in 0..16 {
            assert_eq!(acc[idx], reference[idx], "uniskip q mismatch at point {}", idx);
        }
    }

    #[test]
    fn transition_round_matches_reference() {
        use super::super::full_size_scratch::transition_round::evaluate_transition_with_full_sized_scratch_parallel;

        let worker = Worker::new_with_num_threads(1);
        let mut seed = 777u64;
        const SIZE_LOG2: usize = 8;
        let size = 1 << SIZE_LOG2;
        let inst = make_instance(size, &mut seed);

        let pending: Vec<E> = (0..3).map(|_| pseudo_ext(&mut seed)).collect();

        let (compact, base_addrs, ext_addrs) =
            produce_descriptions_from_batched_description(&inst.description);
        assert_eq!(base_addrs.len(), inst.base_polys.len());
        assert_eq!(ext_addrs.len(), inst.ext_polys.len());

        type TI = TransitionRoundWindowIn3Out1;
        let work = <TI as TransitionRoundImplementation<F, E>>::work_size_for_unfolded_input_size(
            SIZE_LOG2,
        );
        assert_eq!(work, size / 16);
        let suffix_challenges: Vec<E> = (0..(work.trailing_zeros() as usize))
            .map(|_| pseudo_ext(&mut seed))
            .collect();
        let eq_suffix = make_eq_poly_in_full::<E>(&suffix_challenges, &worker)
            .pop()
            .unwrap();

        let prefix =
            <TI as TransitionRoundImplementation<F, E>>::make_prefix_from_all_folding_challenges(
                &pending, &worker,
            );

        let base_sources: Vec<_> = inst
            .base_polys
            .iter()
            .map(|el| DisjointAccessQuasiSlice::<_, false>::from_init_slice(&el[..]))
            .collect();
        let ext_sources: Vec<_> = inst
            .ext_polys
            .iter()
            .map(|el| DisjointAccessQuasiSlice::<_, false>::from_init_slice(&el[..]))
            .collect();

        let buffer_size = size / 8;
        let mut base_buffers_mem: Vec<Box<[std::mem::MaybeUninit<E>]>> = inst
            .base_polys
            .iter()
            .map(|_| Box::new_uninit_slice(buffer_size))
            .collect();
        let mut ext_buffers_mem: Vec<Box<[std::mem::MaybeUninit<E>]>> = inst
            .ext_polys
            .iter()
            .map(|_| Box::new_uninit_slice(buffer_size))
            .collect();
        let base_buffers: Vec<_> = base_buffers_mem
            .iter_mut()
            .map(|el| DisjointAccessQuasiSlice::<_, true>::from_uninit_slice_mut(el))
            .collect();
        let ext_buffers: Vec<_> = ext_buffers_mem
            .iter_mut()
            .map(|el| DisjointAccessQuasiSlice::<_, true>::from_uninit_slice_mut(el))
            .collect();

        let acc = evaluate_transition_with_full_sized_scratch_parallel::<F, E, TI>(
            base_sources,
            ext_sources,
            base_buffers,
            ext_buffers,
            &compact,
            &prefix,
            &eq_suffix,
            SIZE_LOG2,
            &worker,
        );

        // reference: fold everything by the pending challenges, then a W=1 pass
        let num_base = inst.base_polys.len();
        let folded_base: Vec<Vec<E>> = inst
            .base_polys
            .iter()
            .map(|el| {
                let lifted: Vec<E> = el.iter().map(|v| E::from_base(*v)).collect();
                fold_top_vars(&lifted, &pending)
            })
            .collect();
        let folded_ext: Vec<Vec<E>> = inst
            .ext_polys
            .iter()
            .map(|el| fold_top_vars(&el[..], &pending))
            .collect();

        // check the write-back buffers hold the folded values
        for (mem, expected) in base_buffers_mem.iter().zip(folded_base.iter()) {
            for i in 0..buffer_size {
                let got = unsafe { mem[i].assume_init() };
                assert_eq!(got, expected[i], "base folding buffer at {}", i);
            }
        }
        for (mem, expected) in ext_buffers_mem.iter().zip(folded_ext.iter()) {
            for i in 0..buffer_size {
                let got = unsafe { mem[i].assume_init() };
                assert_eq!(got, expected[i], "ext folding buffer at {}", i);
            }
        }

        let folded_size = buffer_size;
        let get_grid = |addr: &GKRAddress, row: usize, coord: usize| -> E {
            let offset = match addr {
                GKRAddress::InnerLayer { offset, .. } => *offset,
                _ => unreachable!(),
            };
            let poly: &Vec<E> = if offset < num_base {
                &folded_base[offset]
            } else {
                &folded_ext[offset - num_base]
            };
            grid_value::<E, 1>(&poly[..], folded_size, row, [coord])
        };

        let mut reference = [E::ZERO; 2];
        for row in 0..work {
            for (slot, coord) in [(0usize, 0usize), (1, 2)] {
                let mut val = E::ZERO;
                for part in [
                    &inst.description.quadratic_part_base_by_base,
                    &inst.description.quadratic_part_base_by_ext,
                    &inst.description.quadratic_part_ext_by_ext,
                ] {
                    for (a, list) in part.iter() {
                        let ag = get_grid(a, row, coord);
                        for (b, c) in list.iter() {
                            let bg = get_grid(b, row, coord);
                            let mut t = ag;
                            t.mul_assign(&bg);
                            t.mul_assign(c);
                            val.add_assign(&t);
                        }
                    }
                }
                if coord == 0 {
                    for (a, c) in inst.description.linear_part_base_by_everything.iter() {
                        let mut t = *c;
                        t.mul_assign(&get_grid(a, row, 0));
                        val.add_assign(&t);
                    }
                    for (a, c) in inst.description.linear_part_ext_by_everything.iter() {
                        let mut t = *c;
                        t.mul_assign(&get_grid(a, row, 0));
                        val.add_assign(&t);
                    }
                    val.add_assign(&inst.description.constant_term);
                }
                val.mul_assign(&eq_suffix[row]);
                reference[slot].add_assign(&val);
            }
        }

        assert_eq!(acc[0], reference[0], "transition G(0)");
        assert_eq!(acc[1], reference[1], "transition G_inf");

        // also cover the in3out3 transition (fold + 27-cell window in one pass)
        {
            type T3 = TransitionRoundWindowIn3Out3;
            let work =
                <T3 as TransitionRoundImplementation<F, E>>::work_size_for_unfolded_input_size(
                    SIZE_LOG2,
                );
            assert_eq!(work, size / 64);
            let suffix_challenges: Vec<E> = (0..(work.trailing_zeros() as usize))
                .map(|_| pseudo_ext(&mut seed))
                .collect();
            let eq_suffix = make_eq_poly_in_full::<E>(&suffix_challenges, &worker)
                .pop()
                .unwrap();
            let prefix = <T3 as TransitionRoundImplementation<F, E>>::make_prefix_from_all_folding_challenges(
                &pending, &worker,
            );

            let base_sources: Vec<_> = inst
                .base_polys
                .iter()
                .map(|el| DisjointAccessQuasiSlice::<_, false>::from_init_slice(&el[..]))
                .collect();
            let ext_sources: Vec<_> = inst
                .ext_polys
                .iter()
                .map(|el| DisjointAccessQuasiSlice::<_, false>::from_init_slice(&el[..]))
                .collect();
            let mut base_buffers_mem: Vec<Box<[std::mem::MaybeUninit<E>]>> = inst
                .base_polys
                .iter()
                .map(|_| Box::new_uninit_slice(buffer_size))
                .collect();
            let mut ext_buffers_mem: Vec<Box<[std::mem::MaybeUninit<E>]>> = inst
                .ext_polys
                .iter()
                .map(|_| Box::new_uninit_slice(buffer_size))
                .collect();
            let base_buffers: Vec<_> = base_buffers_mem
                .iter_mut()
                .map(|el| DisjointAccessQuasiSlice::<_, true>::from_uninit_slice_mut(el))
                .collect();
            let ext_buffers: Vec<_> = ext_buffers_mem
                .iter_mut()
                .map(|el| DisjointAccessQuasiSlice::<_, true>::from_uninit_slice_mut(el))
                .collect();

            let acc = evaluate_transition_with_full_sized_scratch_parallel::<F, E, T3>(
                base_sources,
                ext_sources,
                base_buffers,
                ext_buffers,
                &compact,
                &prefix,
                &eq_suffix,
                SIZE_LOG2,
                &worker,
            );

            let get_grid_3 = |addr: &GKRAddress, row: usize, coords: [usize; 3]| -> E {
                let offset = match addr {
                    GKRAddress::InnerLayer { offset, .. } => *offset,
                    _ => unreachable!(),
                };
                let poly: &Vec<E> = if offset < num_base {
                    &folded_base[offset]
                } else {
                    &folded_ext[offset - num_base]
                };
                grid_value::<E, 3>(&poly[..], folded_size, row, coords)
            };

            let mut reference = [E::ZERO; 27];
            for row in 0..work {
                for cell in 0..27 {
                    let coords = cell_coords::<3>(cell);
                    let mut val = E::ZERO;
                    for part in [
                        &inst.description.quadratic_part_base_by_base,
                        &inst.description.quadratic_part_base_by_ext,
                        &inst.description.quadratic_part_ext_by_ext,
                    ] {
                        for (a, list) in part.iter() {
                            let ag = get_grid_3(a, row, coords);
                            for (b, c) in list.iter() {
                                let bg = get_grid_3(b, row, coords);
                                let mut t = ag;
                                t.mul_assign(&bg);
                                t.mul_assign(c);
                                val.add_assign(&t);
                            }
                        }
                    }
                    if is_binary(&coords) {
                        for (a, c) in inst.description.linear_part_base_by_everything.iter() {
                            let mut t = *c;
                            t.mul_assign(&get_grid_3(a, row, coords));
                            val.add_assign(&t);
                        }
                        for (a, c) in inst.description.linear_part_ext_by_everything.iter() {
                            let mut t = *c;
                            t.mul_assign(&get_grid_3(a, row, coords));
                            val.add_assign(&t);
                        }
                        val.add_assign(&inst.description.constant_term);
                    }
                    val.mul_assign(&eq_suffix[row]);
                    reference[cell].add_assign(&val);
                }
            }
            for i in 0..27 {
                assert_eq!(acc[i], reference[i], "transition in3out3: cell {}", i);
            }
        }
    }

    #[test]
    fn ext_only_windows_match_reference() {
        let worker = Worker::new_with_num_threads(1);
        let mut seed = 123u64;
        const SIZE_LOG2: usize = 8;
        let size = 1 << SIZE_LOG2;

        // ee-only instance: 3 ext polys, no base
        let num_base = 0usize;
        let ext_polys: Vec<Vec<E>> = (0..3)
            .map(|_| (0..size).map(|_| pseudo_ext(&mut seed)).collect())
            .collect();
        let eaddr = |i: usize| GKRAddress::InnerLayer {
            layer: 0,
            offset: i,
        };
        let mut description = BatchedGKRDescription::<F, E>::default();
        description.quadratic_part_ext_by_ext = vec![
            (eaddr(0), vec![(eaddr(1), pseudo_ext(&mut seed))]),
            (eaddr(1), vec![(eaddr(2), pseudo_ext(&mut seed))]),
        ];
        description.linear_part_ext_by_everything = vec![(eaddr(2), pseudo_ext(&mut seed))];
        description.constant_term = pseudo_ext(&mut seed);

        let (compact, base_addrs, ext_addrs) =
            produce_descriptions_from_batched_description(&description);
        assert!(base_addrs.is_empty());
        assert_eq!(ext_addrs.len(), 3);

        // window 1
        {
            let pending: Vec<E> = vec![pseudo_ext(&mut seed)];
            let work = <ExtensionOnlyRoundWindowIn1Out1 as ExtensionOnlyRoundImplementation<
                F,
                E,
            >>::work_size_for_unfolded_input_size(SIZE_LOG2);
            assert_eq!(work, size / 4);
            let suffix_challenges: Vec<E> = (0..(work.trailing_zeros() as usize))
                .map(|_| pseudo_ext(&mut seed))
                .collect();
            let eq_suffix = make_eq_poly_in_full::<E>(&suffix_challenges, &worker)
                .pop()
                .unwrap();

            let acc = run_ext_only_pass::<ExtensionOnlyRoundWindowIn1Out1>(
                &ext_polys, &compact, &pending, &eq_suffix, SIZE_LOG2, &worker,
            );
            let reference = reference_ext_only_accumulator::<1, 3>(
                &ext_polys,
                &description,
                num_base,
                &pending,
                &eq_suffix,
            );
            // in1out1 accumulator layout is [G(0), G_inf]; reference cells are {0,1,inf}
            assert_eq!(acc[0], reference[0], "w1: G(0)");
            assert_eq!(acc[1], reference[2], "w1: G_inf");
        }

        // window 2
        {
            let pending: Vec<E> = (0..2).map(|_| pseudo_ext(&mut seed)).collect();
            let work = <ExtensionOnlyRoundWindowIn2Out2 as ExtensionOnlyRoundImplementation<
                F,
                E,
            >>::work_size_for_unfolded_input_size(SIZE_LOG2);
            assert_eq!(work, size / 16);
            let suffix_challenges: Vec<E> = (0..(work.trailing_zeros() as usize))
                .map(|_| pseudo_ext(&mut seed))
                .collect();
            let eq_suffix = make_eq_poly_in_full::<E>(&suffix_challenges, &worker)
                .pop()
                .unwrap();

            let acc = run_ext_only_pass::<ExtensionOnlyRoundWindowIn2Out2>(
                &ext_polys, &compact, &pending, &eq_suffix, SIZE_LOG2, &worker,
            );
            let reference = reference_ext_only_accumulator::<2, 9>(
                &ext_polys,
                &description,
                num_base,
                &pending,
                &eq_suffix,
            );
            for i in 0..9 {
                assert_eq!(acc[i], reference[i], "w2: cell {}", i);
            }
        }

        // window 3
        {
            let pending: Vec<E> = (0..3).map(|_| pseudo_ext(&mut seed)).collect();
            let work = <ExtensionOnlyRoundWindowIn3Out3 as ExtensionOnlyRoundImplementation<
                F,
                E,
            >>::work_size_for_unfolded_input_size(SIZE_LOG2);
            assert_eq!(work, size / 64);
            let suffix_challenges: Vec<E> = (0..(work.trailing_zeros() as usize))
                .map(|_| pseudo_ext(&mut seed))
                .collect();
            let eq_suffix = make_eq_poly_in_full::<E>(&suffix_challenges, &worker)
                .pop()
                .unwrap();

            let acc = run_ext_only_pass::<ExtensionOnlyRoundWindowIn3Out3>(
                &ext_polys, &compact, &pending, &eq_suffix, SIZE_LOG2, &worker,
            );
            let reference = reference_ext_only_accumulator::<3, 27>(
                &ext_polys,
                &description,
                num_base,
                &pending,
                &eq_suffix,
            );
            for i in 0..27 {
                assert_eq!(acc[i], reference[i], "w3: cell {}", i);
            }
        }

        // bridge in: fold 1 pending challenge, open a window of 3
        {
            let pending: Vec<E> = vec![pseudo_ext(&mut seed)];
            let work = <ExtensionOnlyRoundWindowIn1Out3 as ExtensionOnlyRoundImplementation<
                F,
                E,
            >>::work_size_for_unfolded_input_size(SIZE_LOG2);
            assert_eq!(work, size / 16);
            let suffix_challenges: Vec<E> = (0..(work.trailing_zeros() as usize))
                .map(|_| pseudo_ext(&mut seed))
                .collect();
            let eq_suffix = make_eq_poly_in_full::<E>(&suffix_challenges, &worker)
                .pop()
                .unwrap();

            let acc = run_ext_only_pass::<ExtensionOnlyRoundWindowIn1Out3>(
                &ext_polys, &compact, &pending, &eq_suffix, SIZE_LOG2, &worker,
            );
            let reference = reference_ext_only_accumulator::<3, 27>(
                &ext_polys,
                &description,
                num_base,
                &pending,
                &eq_suffix,
            );
            for i in 0..27 {
                assert_eq!(acc[i], reference[i], "in1out3: cell {}", i);
            }
        }

        // bridge out: fold 3 pending challenges, window of 1
        {
            let pending: Vec<E> = (0..3).map(|_| pseudo_ext(&mut seed)).collect();
            let work = <ExtensionOnlyRoundWindowIn3Out1 as ExtensionOnlyRoundImplementation<
                F,
                E,
            >>::work_size_for_unfolded_input_size(SIZE_LOG2);
            assert_eq!(work, size / 16);
            let suffix_challenges: Vec<E> = (0..(work.trailing_zeros() as usize))
                .map(|_| pseudo_ext(&mut seed))
                .collect();
            let eq_suffix = make_eq_poly_in_full::<E>(&suffix_challenges, &worker)
                .pop()
                .unwrap();

            let acc = run_ext_only_pass::<ExtensionOnlyRoundWindowIn3Out1>(
                &ext_polys, &compact, &pending, &eq_suffix, SIZE_LOG2, &worker,
            );
            let reference = reference_ext_only_accumulator::<1, 3>(
                &ext_polys,
                &description,
                num_base,
                &pending,
                &eq_suffix,
            );
            assert_eq!(acc[0], reference[0], "in3out1: G(0)");
            assert_eq!(acc[1], reference[2], "in3out1: G_inf");
        }
    }
}
