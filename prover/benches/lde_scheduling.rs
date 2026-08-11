#![feature(allocator_api)]
//! Backend scheduling benchmark for the in-memory LDE commitments: naive
//! scheduling (parallel-over-polys, or sequential cosets each with one
//! barrier-per-stage parallel NTT) vs the work-stealing backend (flat
//! poly×coset grid of serial fused coset FFTs on the worker's rayon pool).
//!
//! The headline shape mirrors the packed unified Proth120 circuit — FEW packed
//! polynomials (7) with a LARGE LDE factor (32) — scaled down in message size so
//! it fits a workstation. Run with:
//!   `cargo bench -p prover --bench lde_scheduling`

use field::{
    baby_bear::base::BabyBearField, Field, FieldExtension, PrimeField, Proth120, Rand, TwoAdicField,
};
use prover::fft::Twiddles;
use prover::gkr::prover::{Backend, NaiveBackend, WorkStealingBackend};
use std::alloc::Global;
use std::time::Instant;
use worker::Worker;

fn rand_cols<F: Rand>(num: usize, n: usize) -> Vec<Vec<F>> {
    let mut rng = rand::rng();
    (0..num)
        .map(|_| (0..n).map(|_| F::random_element(&mut rng)).collect())
        .collect()
}

fn median<T, S: FnMut() -> T, F: FnMut(T)>(k: usize, mut setup: S, mut f: F) -> f64 {
    let mut times = Vec::with_capacity(k);
    for _ in 0..k {
        let input = setup();
        let t0 = Instant::now();
        f(input);
        times.push(t0.elapsed().as_secs_f64());
    }
    times.sort_by(|a, b| a.partial_cmp(b).unwrap());
    times[k / 2]
}

fn bench_packed_shape<F: PrimeField + TwoAdicField + Rand>(
    name: &str,
    num_polys: usize,
    log_n: usize,
    lde_factor: usize,
    worker: &Worker,
    k: usize,
) {
    let n = 1usize << log_n;
    let twiddles = Twiddles::<F, Global>::new(n, worker);
    let monomials: Vec<Vec<F>> = rand_cols(num_polys, n);

    println!(
        "\n== {name}: {num_polys} polys x 2^{log_n}, LDE {lde_factor} ({} coset tasks, {} GiB output) ==",
        num_polys * lde_factor,
        (num_polys * lde_factor * n * core::mem::size_of::<F>()) as f64 / (1u64 << 30) as f64
    );

    let t = median(
        k,
        || monomials.clone(),
        |m| {
            let cosets = Backend::<F, F>::lde_packed_monomials_into_cosets(
                &NaiveBackend,
                m,
                &twiddles,
                lde_factor,
                worker,
            );
            std::hint::black_box(cosets);
        },
    );
    println!("  naive (seq cosets x parallel NTT)   {:>9.1} ms", t * 1e3);

    let t = median(
        k,
        || monomials.clone(),
        |m| {
            let cosets = Backend::<F, F>::lde_packed_monomials_into_cosets(
                &WorkStealingBackend,
                m,
                &twiddles,
                lde_factor,
                worker,
            );
            std::hint::black_box(cosets);
        },
    );
    println!("  work-stealing (planned grid)        {:>9.1} ms", t * 1e3);
}

fn bench_multi_col_shape<F: PrimeField + TwoAdicField + Rand>(
    name: &str,
    num_cols: usize,
    log_n: usize,
    lde_factor: usize,
    worker: &Worker,
    k: usize,
) {
    let n = 1usize << log_n;
    let twiddles = Twiddles::<F, Global>::new(n, worker);
    let cols: Vec<Vec<F>> = rand_cols(num_cols, n);
    let col_refs: Vec<&[F]> = cols.iter().map(|c| &c[..]).collect();

    println!(
        "\n== {name}: {num_cols} hypercube cols x 2^{log_n}, LDE {lde_factor} ({} coset tasks) ==",
        num_cols * lde_factor
    );

    let t = median(
        k,
        || (),
        |_| {
            let cosets = Backend::<F, F>::lde_multiple_polys_from_hypercubes(
                &NaiveBackend,
                &col_refs,
                &twiddles,
                lde_factor,
                worker,
            );
            std::hint::black_box(cosets);
        },
    );
    println!("  naive (parallel over polys only)    {:>9.1} ms", t * 1e3);

    let t = median(
        k,
        || (),
        |_| {
            let cosets = Backend::<F, F>::lde_multiple_polys_from_hypercubes(
                &WorkStealingBackend,
                &col_refs,
                &twiddles,
                lde_factor,
                worker,
            );
            std::hint::black_box(cosets);
        },
    );
    println!("  work-stealing (flat poly x coset)   {:>9.1} ms", t * 1e3);
}

fn main() {
    // Remote-run overrides (no recompile needed):
    //   BENCH_THREADS   — cap the worker pool (default: all cores)
    //   FULL_SIZE_LDE   — LDE factor of the 2^26 full-size shape (default 4;
    //                     production 32 needs ~224 GiB of codeword RAM)
    let env_usize =
        |name: &str| -> Option<usize> { std::env::var(name).ok().and_then(|v| v.parse().ok()) };
    let worker = match env_usize("BENCH_THREADS") {
        Some(t) => Worker::new_with_num_threads(t),
        None => Worker::new(),
    };
    let full_size_lde = env_usize("FULL_SIZE_LDE").unwrap_or(4);
    println!("host cores: {}", worker.get_num_cores());

    // The unified packed Proth120 shape (7 packed polys, LDE 32), message scaled
    // from 2^26 down to workstation sizes.
    bench_packed_shape::<Proth120>("Proth120 packed-unified shape", 7, 20, 32, &worker, 3);
    bench_packed_shape::<Proth120>("Proth120 packed-unified shape", 7, 22, 32, &worker, 3);

    // The REAL packed-unified message size (2^26). The production LDE factor of
    // 32 needs ~224 GiB of codeword, so locally the LDE is capped at 4 (28 GiB);
    // per-coset cost is identical to production, only the task count differs.
    bench_packed_shape::<Proth120>(
        "Proth120 packed-unified FULL-SIZE",
        7,
        26,
        full_size_lde,
        &worker,
        1,
    );

    // UNDERSUBSCRIBED wide-field grid (tasks < threads): the planner switches to
    // the parallel-within-task mode (each Proth120 FFT worker-parallel, nested on
    // the same pool) instead of leaving threads idle.
    bench_packed_shape::<Proth120>("Proth120 undersubscribed", 7, 24, 2, &worker, 3);

    // A family-circuit base commit at production size: many columns, LDE 2.
    bench_multi_col_shape::<BabyBearField>("BabyBear family shape", 32, 24, 2, &worker, 3);
    // Few columns, moderate LDE (worst case for parallel-over-polys).
    bench_multi_col_shape::<BabyBearField>("BabyBear few-cols shape", 4, 22, 8, &worker, 3);
}
