#![feature(allocator_api)]
//! Hand-rolled NTT/LDE micro-benchmarks (no criterion: each measured section is
//! hundreds of ms at the large sizes, so a median-of-k loop is both faster and
//! easier to read than a statistical harness).
//!
//! Measures, per field (BabyBear base 4B, BabyBearExt4 16B, Proth120 16B) and per
//! size, the passes making up one serial LDE coset:
//!   copy, distribute_powers (offset scaling), bit-reversal, DIT NTT
//!   (bitreversed->natural), and the whole pipeline; plus the worker-parallel NTT
//!   at several thread counts.
//!
//! Run with: `cargo bench -p fft --bench ntt -- [filter]`
//!   filter `serial` = serial passes only, `parallel` = parallel NTT only.

use fft::*;
use field::{
    baby_bear::{base::BabyBearField, ext4::BabyBearExt4},
    Field, FieldExtension, PrimeField, Proth120, Rand, TwoAdicField,
};
use std::alloc::Global;
use std::time::Instant;
use worker::Worker;

/// Median wall time of `k` runs of `f` (each run gets a fresh `setup()` value).
fn median_time<T, S: FnMut() -> T, F: FnMut(T)>(k: usize, mut setup: S, mut f: F) -> f64 {
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

fn rand_vec<E: Rand>(n: usize) -> Vec<E> {
    let mut rng = rand::rng();
    (0..n).map(|_| E::random_element(&mut rng)).collect()
}

fn bench_field<F: PrimeField + TwoAdicField + Rand>(name: &str, log_sizes: &[u32], filter: &str) {
    let worker = Worker::new();
    for &log_n in log_sizes {
        let n = 1usize << log_n;
        let twiddles: Vec<F, Global> = precompute_all_twiddles_for_fft_serial::<F, Global, false>(n);
        let offset = domain_generator_for_size::<F>((n * 2) as u64);
        let input: Vec<F> = rand_vec(n);
        let k = if log_n >= 24 { 5 } else { 9 };

        let el_bytes = core::mem::size_of::<F>();
        let mb = (n * el_bytes) as f64 / (1 << 20) as f64;
        println!("\n== {name} 2^{log_n} ({mb:.0} MiB/poly, {el_bytes} B/el) ==");

        if filter.is_empty() || filter == "serial" {
            let t = median_time(
                k,
                || (),
                |_| {
                    let v = input.clone();
                    std::hint::black_box(v);
                },
            );
            println!("  copy (to_vec)              {:>9.3} ms", t * 1e3);

            let t = median_time(
                k,
                || input.clone(),
                |mut v| {
                    distribute_powers_serial(&mut v, F::ONE, offset);
                    std::hint::black_box(v);
                },
            );
            println!("  distribute_powers_serial   {:>9.3} ms", t * 1e3);

            let t = median_time(
                k,
                || input.clone(),
                |mut v| {
                    bitreverse_enumeration_inplace(&mut v);
                    std::hint::black_box(v);
                },
            );
            println!("  bitreverse_inplace         {:>9.3} ms", t * 1e3);

            let t = median_time(
                k,
                || {
                    let mut v = input.clone();
                    bitreverse_enumeration_inplace(&mut v);
                    v
                },
                |mut v| {
                    fft::naive::serial_ct_ntt_bitreversed_to_natural(&mut v, log_n, &twiddles);
                    std::hint::black_box(v);
                },
            );
            println!("  serial DIT ntt (br->nat)   {:>9.3} ms", t * 1e3);

            let t = median_time(
                k,
                || (),
                |_| {
                    // the exact serial coset pipeline of the LDE
                    let mut v = input.clone();
                    distribute_powers_serial(&mut v, F::ONE, offset);
                    bitreverse_enumeration_inplace(&mut v);
                    fft::naive::serial_ct_ntt_bitreversed_to_natural(&mut v, log_n, &twiddles);
                    std::hint::black_box(v);
                },
            );
            println!("  FULL serial coset pipeline {:>9.3} ms", t * 1e3);

            let t = median_time(
                k,
                || input.clone(),
                |mut v| {
                    fft::naive::cache_friendly_ntt_natural_to_bitreversed(&mut v, log_n, &twiddles);
                    std::hint::black_box(v);
                },
            );
            println!("  cache_friendly DIF (ifft)  {:>9.3} ms", t * 1e3);

            let omega = domain_generator_for_size::<F>(n as u64);
            let mut scratch: Vec<F> = Vec::new();
            let t = median_time(
                k,
                || (),
                |_| {
                    let v = fft::fft_natural_to_natural_four_step(
                        &input, offset, omega, &twiddles, &mut scratch,
                    );
                    std::hint::black_box(v);
                },
            );
            println!("  FOUR-STEP coset pipeline   {:>9.3} ms", t * 1e3);

            let t = median_time(
                k,
                || (),
                |_| {
                    let v = fft::lde_coset_natural_fused(&input, offset, &twiddles);
                    std::hint::black_box(v);
                },
            );
            println!("  FUSED coset pipeline       {:>9.3} ms", t * 1e3);

            let t = median_time(
                k,
                || (),
                |_| {
                    let v = fft::lde_coset_natural_seq_fused(&input, offset, &twiddles);
                    std::hint::black_box(v);
                },
            );
            println!("  SEQ-FUSED coset pipeline   {:>9.3} ms", t * 1e3);
        }

        if filter.is_empty() || filter == "parallel" {
            // thread ladder adapted to the host: powers of two + typical P-core /
            // socket counts, capped at (and always including) the core count
            let cores = worker.get_num_cores();
            let mut ladder: Vec<usize> = [2usize, 4, 8, 12, 16, 24, 32, 44, 64, 88]
                .into_iter()
                .filter(|&t| t < cores)
                .collect();
            ladder.push(cores);
            for threads in ladder {
                let w = Worker::new_with_num_threads(threads);
                let t = median_time(
                    k,
                    || {
                        let mut v = input.clone();
                        bitreverse_enumeration_inplace(&mut v);
                        v
                    },
                    |mut v| {
                        fft::naive::parallel_ct_ntt_bitreversed_to_natural(
                            &mut v, log_n, &twiddles, &w,
                        );
                        std::hint::black_box(v);
                    },
                );
                println!("  parallel ntt {threads:>3} threads   {:>9.3} ms", t * 1e3);
            }
        }
    }
}

fn bench_ext(filter: &str) {
    // BabyBearExt4 over BabyBear twiddles (the intermediate-oracle LDE shape).
    type F = BabyBearField;
    type E = BabyBearExt4;
    let log_sizes = [20u32, 22];
    for &log_n in &log_sizes {
        let n = 1usize << log_n;
        let twiddles: Vec<F, Global> = precompute_all_twiddles_for_fft_serial::<F, Global, false>(n);
        let offset = domain_generator_for_size::<F>((n * 2) as u64);
        let input: Vec<E> = rand_vec(n);
        let k = 7;
        println!(
            "\n== BabyBearExt4 2^{log_n} ({} MiB/poly) ==",
            (n * core::mem::size_of::<E>()) >> 20
        );
        if filter.is_empty() || filter == "serial" {
            let t = median_time(
                k,
                || (),
                |_| {
                    let mut v = input.clone();
                    distribute_powers_serial(&mut v, F::ONE, offset);
                    bitreverse_enumeration_inplace(&mut v);
                    fft::naive::serial_ct_ntt_bitreversed_to_natural(&mut v, log_n, &twiddles);
                    std::hint::black_box(v);
                },
            );
            println!("  FULL serial coset pipeline {:>9.3} ms", t * 1e3);

            let omega = domain_generator_for_size::<F>(n as u64);
            let mut scratch: Vec<E> = Vec::new();
            let t = median_time(
                k,
                || (),
                |_| {
                    let v = fft::fft_natural_to_natural_four_step(
                        &input, offset, omega, &twiddles, &mut scratch,
                    );
                    std::hint::black_box(v);
                },
            );
            println!("  FOUR-STEP coset pipeline   {:>9.3} ms", t * 1e3);

            let t = median_time(
                k,
                || (),
                |_| {
                    let v = fft::lde_coset_natural_fused(&input, offset, &twiddles);
                    std::hint::black_box(v);
                },
            );
            println!("  FUSED coset pipeline       {:>9.3} ms", t * 1e3);
        }
    }
}

fn main() {
    // cargo bench passes `--bench` (and possibly other flags); only recognize
    // our own section names and ignore everything else.
    let filter = std::env::args()
        .skip(1)
        .find(|a| a == "serial" || a == "parallel")
        .unwrap_or_default();
    println!("host cores: {}", Worker::new().get_num_cores());
    bench_field::<BabyBearField>("BabyBear", &[18, 20, 22, 24], &filter);
    bench_field::<Proth120>("Proth120", &[18, 20, 22, 24], &filter);
    bench_ext(&filter);
}
