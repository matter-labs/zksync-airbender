//! WHIR intermediate-oracle LDE shape experiment.
//!
//! `ws_lde_single_poly_from_monomial_form` parallelizes over COSETS
//! (`(0..lde_factor).into_par_iter()`), so for a fixed output-domain size the
//! work granularity degrades as the polynomial shrinks: a 2^24 poly at lde
//! 2^7 is 128 big NTT tasks, while a 2^8 poly at lde 2^23 is 8.4M tiny
//! 256-point tasks (per-task scheduling + one boxed allocation each). This
//! bin times `Backend::lde_ext_poly_from_monomial_form` (the exact production
//! entry the Proth120 packed prover uses for intermediate WHIR oracles)
//! against the continuous-buffer entry
//! `Backend::lde_ext_poly_from_monomial_form_continuous` (single allocation,
//! bounded coset-group task grid) across shapes with a constant output size.
//! When both modes run, a few (coset, index) samples plus coset offsets are
//! cross-checked so the speed comparison is also a correctness check.
//!
//! Usage: `lde_shape_scaling [--out-log2 31] [--polys 24,20,16,12,8]
//! [--threads N] [--mode boxed|continuous|both]`
//! (poly p is committed at lde 2^(out_log2 - p)). Output domain 2^31 needs
//! ~32 GB per mode (allocated and freed per shape).
#![feature(allocator_api)]

use prover::fft::Twiddles;
use prover::field::{PrimeField, Proth120};
use prover::gkr::prover::{Backend, Proth120WorkStealingLazyBackend};
use prover::worker::Worker;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Boxed,
    Continuous,
    Both,
}

fn main() {
    let mut out_log2 = 31usize;
    let mut polys: Vec<usize> = vec![24, 20, 16, 12, 8];
    let mut threads: Option<usize> = None;
    let mut mode = Mode::Both;

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
            "--mode" => {
                mode = match value("--mode").as_str() {
                    "boxed" => Mode::Boxed,
                    "continuous" => Mode::Continuous,
                    "both" => Mode::Both,
                    other => panic!("unknown mode `{other}`"),
                }
            }
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
    println!("mode,poly_log2,lde_log2,cosets,seconds,gpoints_per_s");

    let total_points = (1u128 << out_log2) as f64;

    for &p in &polys {
        assert!(p <= out_log2);
        let lde_log2 = out_log2 - p;
        let lde_factor = 1usize << lde_log2;
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

        // Sample positions for the boxed-vs-continuous cross-check.
        let mut sample_state = 0x9E3779B97F4A7C15u64 ^ (p as u64);
        let samples: Vec<(usize, usize)> = (0..8)
            .map(|_| {
                sample_state = sample_state
                    .wrapping_mul(6364136223846793005)
                    .wrapping_add(1442695040888963407);
                let coset = (sample_state >> 32) as usize % lde_factor;
                let idx = (sample_state & 0xFFFF_FFFF) as usize % n;
                (coset, idx)
            })
            .collect();
        let mut boxed_samples: Option<Vec<(Proth120, Proth120)>> = None;

        if mode != Mode::Continuous {
            let start = std::time::Instant::now();
            let cosets = <Proth120WorkStealingLazyBackend as Backend<Proth120, Proth120>>::
                lde_ext_poly_from_monomial_form(
                    &backend,
                    &poly,
                    &twiddles,
                    lde_factor,
                    &worker,
                );
            let el = start.elapsed().as_secs_f64();
            assert_eq!(cosets.len(), lde_factor);
            boxed_samples = Some(
                samples
                    .iter()
                    .map(|&(c, i)| (cosets[c].0[i], cosets[c].1))
                    .collect(),
            );
            println!(
                "boxed,{p},{lde_log2},{lde_factor},{el:.3},{:.3}",
                total_points / el / 1.0e9
            );
            drop(cosets); // untimed: freeing lde_factor boxes can itself be slow
        }

        if mode != Mode::Boxed {
            let start = std::time::Instant::now();
            let (buffer, offsets) = <Proth120WorkStealingLazyBackend as Backend<
                Proth120,
                Proth120,
            >>::lde_ext_poly_from_monomial_form_continuous(
                &backend, &poly, &twiddles, lde_factor, &worker,
            );
            let el = start.elapsed().as_secs_f64();
            assert_eq!(buffer.len(), lde_factor << p);
            assert_eq!(offsets.len(), lde_factor);
            if let Some(expected) = &boxed_samples {
                for (&(c, i), &(value, offset)) in samples.iter().zip(expected.iter()) {
                    assert_eq!(
                        buffer[(c << p) + i],
                        value,
                        "value mismatch at coset {c} idx {i}"
                    );
                    assert_eq!(offsets[c], offset, "offset mismatch at coset {c}");
                }
                println!(
                    "# cross-check ok: {} samples + offsets match boxed",
                    samples.len()
                );
            }
            println!(
                "continuous,{p},{lde_log2},{lde_factor},{el:.3},{:.3}",
                total_points / el / 1.0e9
            );
            drop(buffer);
        }
    }
}
