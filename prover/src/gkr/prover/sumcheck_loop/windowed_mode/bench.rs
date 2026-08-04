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
use super::full_size_scratch::extension_only_round::in_3_out_1::ExtensionOnlyRoundWindowIn3Out1;
use super::full_size_scratch::extension_only_round::in_2_out_2::ExtensionOnlyRoundWindowIn2Out2;
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

fn find_eq_with_len<E: Field>(tables: &[Box<[E]>], len: usize) -> &[E] {
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

fn collect_base_sources<'a, F: PrimeField, E: FieldExtension<F> + Field>(
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

fn collect_ext_sources<'a, F: PrimeField, E: FieldExtension<F> + Field>(
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
        assert_eq!(a[i], b[i], "accumulator diverged at cell {} for {}", i, what);
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

        cur_log2 = I::folded_buffer_size_for_unfolded_input_size(cur_log2)
            .trailing_zeros() as usize;
        rounds_processed += I::OUTPUT_WINDOW_SIZE;
        for i in 0..I::OUTPUT_WINDOW_SIZE {
            chain_challenges.push(pseudo_challenge::<F, E>(300 + (rounds_processed + i) as u32));
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
    let eq_prefix_4: [E; 4] =
        make_eq_poly_in_full::<E>(&prev_challenges[s + 1..s + 3], worker)
            .pop()
            .unwrap()
            .to_vec()
            .try_into()
            .unwrap();
    let eq_prefix_2: [E; 2] =
        make_eq_poly_in_full::<E>(&prev_challenges[s + 2..s + 3], worker)
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
        println!("  pass initial window-3 (rounds 0-2) @2^{folding_steps}: {:?}", now.elapsed());
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
        let work =
            <TI as TransitionRoundImplementation<F, E>>::work_size_for_unfolded_input_size(
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
        per_round.push(acc);
    }
    if verbose {
        println!("  pass transition in3out1 (round 3) @2^{folding_steps}: {:?}", now.elapsed());
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

    // rounds 4-6: bridge with one pending challenge, window of 3
    {
        let (acc, took) = ext_pass!(ExtensionOnlyRoundWindowIn1Out3);
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
        let (acc, took) = ext_pass!(ExtensionOnlyRoundWindowIn3Out3);
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
            println!("  pass ext in3out1 (round {}) @2^{cur_log2}: {:?}", next_round, took);
        }
        cur_log2 -= 3;
        next_round += 1;
    }

    // in1out1 tail for whatever remains
    while next_round < folding_steps {
        let (acc, took) = ext_pass!(ExtensionOnlyRoundWindowIn1Out1);
        per_round.push(acc);
        if verbose {
            println!("  pass ext in1out1 (round {}) @2^{cur_log2}: {:?}", next_round, took);
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
        println!("  pass initial window-3 (rounds 0-2) @2^{folding_steps}: {:?}", now.elapsed());
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
        let work =
            <TI as TransitionRoundImplementation<F, E>>::work_size_for_unfolded_input_size(
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
        println!("  pass transition in3out3 (rounds 3-5) @2^{folding_steps}: {:?}", now.elapsed());
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
            println!("  pass ext in3out1 (round {}) @2^{cur_log2}: {:?}", next_round, took);
        }
        cur_log2 -= 3;
        next_round += 1;
    }

    while next_round < folding_steps {
        let (acc, took) = ext_pass_v2!(ExtensionOnlyRoundWindowIn1Out1);
        per_round.push(acc);
        if verbose {
            println!("  pass ext in1out1 (round {}) @2^{cur_log2}: {:?}", next_round, took);
        }
        cur_log2 -= 1;
        next_round += 1;
    }

    assert_eq!(per_round.len(), folding_steps);
    (per_round, total_start.elapsed())
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
    println!("[A] window-3 rounds 0-2, ALL terms, full-size scratch: {:?}", best_a);

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
        let (bounded, _, _) = produce_bounded_scratch_description(&desc_bbbe, 16, 8.min(ext_polys_bbbe.len().max(2)));
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
        assert_acc_eq(&acc, &acc_bbbe, "bounded bbbe window vs full-size bbbe window");
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
        assert_acc_eq(&sum, &acc_all, "bbbe window + ee window == all-terms window");
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
    println!("[D] classic per-round batched evaluation, ALL terms, rounds 0-2: {:?}", best_d);

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
        assert_eq!(round_0[2], classic_all[0][1], "round 0: G_inf vs classic c2");

        let acc_9 = bind_accumulator_27(&acc_all, &window_challenges[0]);
        let round_1 = evaluate_claim_from_intermediate_matrix_9(&eq_prefix_2, &acc_9);
        assert_eq!(round_1[0], classic_all[1][0], "round 1: G(0) vs classic c0");
        assert_eq!(round_1[2], classic_all[1][1], "round 1: G_inf vs classic c2");

        let round_2 = bind_accumulator_9(&acc_9, &window_challenges[1]);
        assert_eq!(round_2[0], classic_all[2][0], "round 2: G(0) vs classic c0");
        assert_eq!(round_2[2], classic_all[2][1], "round 2: G_inf vs classic c2");

        println!("validation: window accumulator matches classic rounds 0-2 through the bind chain");
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
    println!("[T] transition round 3 (in 3, out 1; folds all polys to ext): {:?}", best_t);

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
    println!("[E1] ext-only rounds, window 1: {} rounds in {:?}", w1_rounds, w1_time);

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
    println!("[E2] ext-only rounds, window 2: {} rounds in {:?}", w2_rounds, w2_time);

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
    println!("[E3] ext-only rounds, window 3: {} rounds in {:?}", w3_rounds, w3_time);

    // ---------------- full windowed chain vs naive per-round loop ----------------
    println!("full chain: window-3 initial -> transition in3out1 -> in1out3 -> in3out3... -> in3out1 -> in1out1");
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
            worker,
        );
        best_chain = best_chain.min(took);
        chain_rounds = Some(rounds);
    }
    let chain_rounds = chain_rounds.unwrap();
    println!("[F] full windowed chain, all {} rounds: {:?}", folding_steps, best_chain);

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
    println!("[N] naive per-round loop, all {} rounds: {:?}", folding_steps, best_naive);

    for (i, (a, b)) in chain_rounds.iter().zip(naive_rounds.iter()).enumerate() {
        assert_eq!(a[0], b[0], "round {}: G(0) diverged between chain and naive", i);
        assert_eq!(a[1], b[1], "round {}: G_inf diverged between chain and naive", i);
    }
    for (i, (a, b)) in chain_v2_rounds.iter().zip(naive_rounds.iter()).enumerate() {
        assert_eq!(a[0], b[0], "round {}: G(0) diverged between chain v2 and naive", i);
        assert_eq!(a[1], b[1], "round {}: G_inf diverged between chain v2 and naive", i);
    }
    println!(
        "validation: both windowed chains match the naive per-round loop on all {} rounds",
        folding_steps
    );
    drop(accumulator_buffer);

    println!("==== summary ====");
    println!("initial 3 rounds:  window-3 all-terms full scratch  {:?}", best_a);
    println!("                   split (bb/be window + classic ee) {:?}", best_c_window + best_c_classic_ee);
    println!("                   classic per-round baseline        {:?}", best_d);
    println!("round 3 + fold:    transition in3out1                {:?}", best_t);
    println!(
        "ext-only rounds:   w1 {:?} ({} rounds), w2 {:?} ({} rounds), w3 {:?} ({} rounds)",
        w1_time, w1_rounds, w2_time, w2_rounds, w3_time, w3_rounds
    );
    println!("full sumcheck:     windowed chain (in3out1 trans.)   {:?}", best_chain);
    println!("                   windowed chain (in3out3 trans.)   {:?}", best_chain_v2);
    println!("                   naive per-round loop              {:?}", best_naive);
}

#[cfg(test)]
mod synthetic_tests {
    use super::*;
    use ::field::baby_bear::base::BabyBearField;
    use ::field::baby_bear::ext4::BabyBearExt4;

    type F = BabyBearField;
    type E = BabyBearExt4;

    fn pseudo_base(seed: &mut u64) -> F {
        *seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
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

        let baddr = |i: usize| GKRAddress::InnerLayer { layer: 0, offset: i };
        let eaddr = |i: usize| GKRAddress::InnerLayer {
            layer: 0,
            offset: num_base + i,
        };

        let mut description = BatchedGKRDescription::<F, E>::default();
        description.quadratic_part_base_by_base = vec![
            (baddr(0), vec![(baddr(1), pseudo_ext(seed)), (baddr(2), pseudo_ext(seed))]),
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
        let (compact_ee, ee_base, ee_ext) =
            produce_descriptions_from_batched_description(&desc_ee);
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
        let work =
            <TI as TransitionRoundImplementation<F, E>>::work_size_for_unfolded_input_size(
                SIZE_LOG2,
            );
        assert_eq!(work, size / 16);
        let suffix_challenges: Vec<E> = (0..(work.trailing_zeros() as usize))
            .map(|_| pseudo_ext(&mut seed))
            .collect();
        let eq_suffix = make_eq_poly_in_full::<E>(&suffix_challenges, &worker)
            .pop()
            .unwrap();

        let prefix = <TI as TransitionRoundImplementation<F, E>>::make_prefix_from_all_folding_challenges(
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
        let eaddr = |i: usize| GKRAddress::InnerLayer { layer: 0, offset: i };
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
            let work =
                <ExtensionOnlyRoundWindowIn1Out1 as ExtensionOnlyRoundImplementation<F, E>>::work_size_for_unfolded_input_size(SIZE_LOG2);
            assert_eq!(work, size / 4);
            let suffix_challenges: Vec<E> =
                (0..(work.trailing_zeros() as usize)).map(|_| pseudo_ext(&mut seed)).collect();
            let eq_suffix = make_eq_poly_in_full::<E>(&suffix_challenges, &worker)
                .pop()
                .unwrap();

            let acc = run_ext_only_pass::<ExtensionOnlyRoundWindowIn1Out1>(
                &ext_polys,
                &compact,
                &pending,
                &eq_suffix,
                SIZE_LOG2,
                &worker,
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
            let work =
                <ExtensionOnlyRoundWindowIn2Out2 as ExtensionOnlyRoundImplementation<F, E>>::work_size_for_unfolded_input_size(SIZE_LOG2);
            assert_eq!(work, size / 16);
            let suffix_challenges: Vec<E> =
                (0..(work.trailing_zeros() as usize)).map(|_| pseudo_ext(&mut seed)).collect();
            let eq_suffix = make_eq_poly_in_full::<E>(&suffix_challenges, &worker)
                .pop()
                .unwrap();

            let acc = run_ext_only_pass::<ExtensionOnlyRoundWindowIn2Out2>(
                &ext_polys,
                &compact,
                &pending,
                &eq_suffix,
                SIZE_LOG2,
                &worker,
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
            let work =
                <ExtensionOnlyRoundWindowIn3Out3 as ExtensionOnlyRoundImplementation<F, E>>::work_size_for_unfolded_input_size(SIZE_LOG2);
            assert_eq!(work, size / 64);
            let suffix_challenges: Vec<E> =
                (0..(work.trailing_zeros() as usize)).map(|_| pseudo_ext(&mut seed)).collect();
            let eq_suffix = make_eq_poly_in_full::<E>(&suffix_challenges, &worker)
                .pop()
                .unwrap();

            let acc = run_ext_only_pass::<ExtensionOnlyRoundWindowIn3Out3>(
                &ext_polys,
                &compact,
                &pending,
                &eq_suffix,
                SIZE_LOG2,
                &worker,
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
            let work =
                <ExtensionOnlyRoundWindowIn1Out3 as ExtensionOnlyRoundImplementation<F, E>>::work_size_for_unfolded_input_size(SIZE_LOG2);
            assert_eq!(work, size / 16);
            let suffix_challenges: Vec<E> =
                (0..(work.trailing_zeros() as usize)).map(|_| pseudo_ext(&mut seed)).collect();
            let eq_suffix = make_eq_poly_in_full::<E>(&suffix_challenges, &worker)
                .pop()
                .unwrap();

            let acc = run_ext_only_pass::<ExtensionOnlyRoundWindowIn1Out3>(
                &ext_polys,
                &compact,
                &pending,
                &eq_suffix,
                SIZE_LOG2,
                &worker,
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
            let work =
                <ExtensionOnlyRoundWindowIn3Out1 as ExtensionOnlyRoundImplementation<F, E>>::work_size_for_unfolded_input_size(SIZE_LOG2);
            assert_eq!(work, size / 16);
            let suffix_challenges: Vec<E> =
                (0..(work.trailing_zeros() as usize)).map(|_| pseudo_ext(&mut seed)).collect();
            let eq_suffix = make_eq_poly_in_full::<E>(&suffix_challenges, &worker)
                .pop()
                .unwrap();

            let acc = run_ext_only_pass::<ExtensionOnlyRoundWindowIn3Out1>(
                &ext_polys,
                &compact,
                &pending,
                &eq_suffix,
                SIZE_LOG2,
                &worker,
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
