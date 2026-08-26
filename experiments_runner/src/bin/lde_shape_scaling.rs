//! WHIR intermediate-oracle LDE shape experiment.
//!
//! `ws_lde_single_poly_from_monomial_form` parallelizes over COSETS
//! (`(0..lde_factor).into_par_iter()`), so for a fixed output-domain size the
//! work granularity degrades as the polynomial shrinks: a 2^24 poly at lde
//! 2^7 is 128 big NTT tasks, while a 2^8 poly at lde 2^23 is 8.4M tiny
//! 256-point tasks (per-task scheduling + one boxed allocation each). This
//! bin times `Backend::lde_ext_poly_from_monomial_form` (the exact production
//! entry the Proth120 packed prover uses for intermediate WHIR oracles)
//! across shapes with a constant output size.
//!
//! Usage: `lde_shape_scaling [--out-log2 31] [--polys 24,20,16,12,8] [--threads N]`
//! (poly p is committed at lde 2^(out_log2 - p)). Output domain 2^31 needs
//! ~34 GB per shape (allocated and freed per shape).
#![feature(allocator_api)]

use prover::fft::Twiddles;
use prover::field::{Proth120, PrimeField};
use prover::gkr::prover::{Backend, Proth120WorkStealingLazyBackend};
use prover::worker::Worker;

fn main() {
    let mut out_log2 = 31usize;
    let mut polys: Vec<usize> = vec![24, 20, 16, 12, 8];
    let mut threads: Option<usize> = None;

    let mut it = std::env::args().skip(1);
    while let Some(arg) = it.next() {
        let mut value =
            |name: &str| -> String { it.next().unwrap_or_else(|| panic!("{name} needs a value")) };
        match arg.as_str() {
            "--out-log2" => out_log2 = value("--out-log2").parse().expect("--out-log2"),
            "--polys" => {
                polys = value("--polys")
                    .split(',')
                    .map(|s| s.trim().parse().expect("--polys"))
                    .collect()
            }
            "--threads" => threads = Some(value("--threads").parse().expect("--threads")),
            other => panic!("unknown argument `{other}`"),
        }
    }

    let worker = match threads {
        Some(n) => Worker::new_with_num_threads(n),
        None => Worker::new(),
    };
    let backend = Proth120WorkStealingLazyBackend;

    println!(
        "ext-LDE shape scaling: output domain 2^{out_log2}, {} threads",
        worker.num_cores
    );
    println!("poly_log2,lde_log2,cosets,seconds,gpoints_per_s");

    for &p in &polys {
        assert!(p <= out_log2);
        let lde_log2 = out_log2 - p;
        let n = 1usize << p;

        // Deterministic pseudo-random monomial coefficients.
        let mut state = 0x243F6A8885A308D3u64 ^ (p as u64);
        let poly: Vec<Proth120> = (0..n)
            .map(|_| {
                state = state
                    .wrapping_mul(6364136223846793005)
                    .wrapping_add(1442695040888963407);
                Proth120::from_u128_with_reduction(state as u128)
            })
            .collect();

        let twiddles: Twiddles<Proth120, std::alloc::Global> = Twiddles::new(n.max(2), &worker);

        let start = std::time::Instant::now();
        let cosets = <Proth120WorkStealingLazyBackend as Backend<Proth120, Proth120>>::
            lde_ext_poly_from_monomial_form(
                &backend,
                &poly,
                &twiddles,
                1usize << lde_log2,
                &worker,
            );
        let el = start.elapsed().as_secs_f64();
        assert_eq!(cosets.len(), 1usize << lde_log2);
        // keep the result alive through the timer, then free it (untimed)
        let checksum = cosets[0].0[0];
        drop(cosets);
        let _ = checksum;

        let total_points = (1u128 << out_log2) as f64;
        println!(
            "{p},{lde_log2},{},{el:.3},{:.3}",
            1u64 << lde_log2,
            total_points / el / 1.0e9
        );
    }
}
