//! Per-stage kernels of the non-GKR prover pipeline at production sizes, each
//! reported with its effective memory bandwidth so it can be compared against
//! the machine roofline from the `bw` section.
//!
//! Stage list (Proth120, production packed-unified shape 2^26):
//!   * scaled copy (split-powers)         — 1r + 1w streaming
//!   * bit-reversal permutation           — ~1r + 1w scattered
//!   * serial DIT NTT                     — log n passes of 2r + 2w over n/2 pairs
//!   * full seq-fused coset pipeline      — sum of the above
//!   * hypercube -> monomial transform    — (log n - ~1) passes of 1r + 1w over n/2
//!     (copied kernel: butterflies of `sub_assign` only, no multiplies — the
//!     FFT-like stage the task notes as benefiting from generic FFT work)

use super::{gbps, median};
use field::{Field, PrimeField, Proth120, Rand, TwoAdicField};
use std::alloc::Global;
use std::time::Instant;
use worker::Worker;

/// Copy of `prover`'s `multivariate_hypercube_evals_into_coeffs` (kept in sync
/// manually; the prover crate is deliberately not a dependency here). Butterfly
/// network over `size_log2` stages of `sub_assign` with stride n/2 .. 2, plus a
/// final in-pair pass.
fn hypercube_evals_into_coeffs<F: Field>(input: &mut [F], size_log2: u32) {
    assert_eq!(input.len(), 1usize << size_log2);
    let len = 1usize << size_log2;

    let mut stride = len / 2;
    let mut iterations = len / 2;

    for _round in 1..size_log2 {
        let mut i = 0;
        while i < len {
            for _ in 0..iterations {
                let lhs = input[i];
                input[i + stride].sub_assign(&lhs);
                i += 1;
            }
            i += iterations;
        }
        stride /= 2;
        iterations /= 2;
    }

    for pair in input.chunks_exact_mut(2) {
        let (a, b) = pair.split_at_mut(1);
        b[0].sub_assign(&a[0]);
    }
}

pub fn bench_stages(worker: &Worker) {
    type F = Proth120;
    let log_n = 24u32; // per-coset FFT cost is what matters; 2^24 keeps runs fast.
    let n = 1usize << log_n;
    let el = core::mem::size_of::<F>();
    let bytes = n * el;

    let mut rng = rand::rng();
    let input: Vec<F> = (0..n).map(|_| F::random_element(&mut rng)).collect();
    let twiddles: Vec<F, Global> =
        fft::precompute_all_twiddles_for_fft_serial::<F, Global, false>(n);
    let offset = fft::domain_generator_for_size::<F>((n * 2) as u64);

    println!("\n== stage kernels: Proth120 2^{log_n} ({} MiB/poly), SERIAL ==", bytes >> 20);

    // scaled copy
    let t = median(
        5,
        || (),
        |_| {
            let powers = fft::SplitPowers::new(offset, n);
            let mut out: Vec<F> = Vec::with_capacity(n);
            #[allow(clippy::uninit_vec)]
            unsafe {
                out.set_len(n)
            };
            fft::scaled_copy_sequential(&input, Some(&powers), &mut out);
            std::hint::black_box(out);
        },
    );
    println!(
        "  scaled copy               {:>9.1} ms  ({:>6.1} GB/s of {} touched)",
        t * 1e3,
        gbps(2 * bytes, t),
        "2x"
    );

    // bitreverse
    let t = median(
        5,
        || input.clone(),
        |mut v| {
            fft::bitreverse_enumeration_inplace(&mut v);
            std::hint::black_box(v);
        },
    );
    println!(
        "  bitreverse (in-place)     {:>9.1} ms  ({:>6.1} GB/s of {} touched)",
        t * 1e3,
        gbps(2 * bytes, t),
        "2x"
    );

    // serial DIT NTT: log n stages, each streaming the whole array (r+w)
    let t = median(
        5,
        || {
            let mut v = input.clone();
            fft::bitreverse_enumeration_inplace(&mut v);
            v
        },
        |mut v| {
            fft::naive::serial_ct_ntt_bitreversed_to_natural(&mut v, log_n, &twiddles[..n / 2]);
            std::hint::black_box(v);
        },
    );
    println!(
        "  serial DIT NTT            {:>9.1} ms  ({:>6.1} GB/s of {}x touched)",
        t * 1e3,
        gbps(2 * bytes * log_n as usize, t),
        2 * log_n
    );

    // full fused coset pipeline
    let t = median(
        5,
        || (),
        |_| {
            let v = fft::lde_coset_natural_seq_fused(&input, offset, &twiddles);
            std::hint::black_box(v);
        },
    );
    println!(
        "  seq-fused coset pipeline  {:>9.1} ms  ({:>6.1} GB/s of {}x touched)",
        t * 1e3,
        gbps((2 * log_n as usize + 4) * bytes, t),
        2 * log_n + 4
    );

    // hypercube -> monomial (bitreverse + sub-butterfly network)
    let t = median(
        5,
        || input.clone(),
        |mut v| {
            fft::bitreverse_enumeration_inplace(&mut v);
            hypercube_evals_into_coeffs(&mut v, log_n);
            std::hint::black_box(v);
        },
    );
    println!(
        "  hypercube->monomial       {:>9.1} ms  ({:>6.1} GB/s of {}x touched)",
        t * 1e3,
        gbps((2 + 2 * log_n as usize) * bytes, t),
        2 + 2 * log_n
    );

    // The production grid: 88 concurrent serial coset FFTs (7 polys x LDE) —
    // aggregate effective bandwidth of the whole machine on the NTT stage.
    let tasks = worker.get_num_cores();
    println!(
        "\n== aggregate: {tasks} concurrent serial fused coset pipelines (one per core) =="
    );
    let inputs: Vec<Vec<F>> = (0..8)
        .map(|_| (0..n).map(|_| F::random_element(&mut rng)).collect())
        .collect();
    let t = {
        use worker::rayon::prelude::*;
        let t0 = Instant::now();
        worker.pool.install(|| {
            (0..tasks).into_par_iter().for_each(|i| {
                let v =
                    fft::lde_coset_natural_seq_fused(&inputs[i % inputs.len()], offset, &twiddles);
                std::hint::black_box(v);
            });
        });
        t0.elapsed().as_secs_f64()
    };
    let total_bytes = tasks * (2 * log_n as usize + 4) * bytes;
    println!(
        "  {tasks} fused (DIT) pipelines  {:>9.1} ms  (aggregate {:>6.1} GB/s effective)",
        t * 1e3,
        gbps(total_bytes, t),
    );

    // Same aggregate with the FOUR-STEP pipeline: ~5 full-array passes instead
    // of log n — serially it loses on compute, but in the bandwidth-bound
    // aggregate regime the ~5x traffic reduction should dominate.
    let omega = fft::domain_generator_for_size::<F>(n as u64);
    let t = {
        use worker::rayon::prelude::*;
        let t0 = Instant::now();
        worker.pool.install(|| {
            (0..tasks).into_par_iter().for_each(|i| {
                let mut scratch: Vec<F> = Vec::new();
                let v = fft::fft_natural_to_natural_four_step(
                    &inputs[i % inputs.len()],
                    offset,
                    omega,
                    &twiddles,
                    &mut scratch,
                );
                std::hint::black_box(v);
            });
        });
        t0.elapsed().as_secs_f64()
    };
    println!(
        "  {tasks} FOUR-STEP pipelines    {:>9.1} ms  (~10x traffic/task vs {}x)",
        t * 1e3,
        2 * log_n + 4
    );
}
