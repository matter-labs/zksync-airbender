//! Keccak PoW-grind thread-scaling experiment.
//!
//! Runs the PRODUCTION `Keccak256Transcript::search_pow` (the exact function
//! the Proth120 WHIR rounds grind with) at a fixed difficulty from FIXED
//! transcript seeds across a ladder of worker thread counts. The search scans
//! nonce stripes for the global minimum valid nonce, so for a fixed seed the
//! total hash work is identical at every thread count — wall time should
//! scale as 1/threads if the grind is compute-bound and NUMA-clean.
//!
//! Build for the external x86-64 box:
//!
//! ```text
//! cargo zigbuild -p experiments_runner --bin pow_scaling --release \
//!     --target x86_64-unknown-linux-gnu.2.17
//! ```
//!
//! Usage: `pow_scaling [--bits 30] [--threads 16,32,64,96,128,160,192] [--seeds 2]`
//! Prints CSV (`threads,seed,nonce,seconds,mh_per_s`) followed by a scaling
//! summary against the smallest thread count.

use prover::field::Proth120;
use prover::transcript::{Keccak256Transcript, Transcript};
use worker::Worker;

type Tr = Keccak256Transcript;
type Seed = <Tr as Transcript<Proth120, Proth120>>::Seed;

fn fixed_seed(tag: u32) -> Seed {
    // A fixed "initial point": deterministic transcript state per tag.
    <Tr as Transcript<Proth120, Proth120>>::commit_initial_u32(&[
        0x504f_5721, // "POW!"
        0x6772_696e, // "grin"
        0x6421_0000, // "d!"
        tag,
    ])
}

fn main() {
    let mut bits = 30u32;
    let mut threads_list: Vec<usize> = vec![16, 32, 64, 96, 128, 160, 192];
    let mut num_seeds = 2usize;

    let mut it = std::env::args().skip(1);
    while let Some(arg) = it.next() {
        let mut value =
            |name: &str| -> String { it.next().unwrap_or_else(|| panic!("{name} needs a value")) };
        match arg.as_str() {
            "--bits" => bits = value("--bits").parse().expect("--bits"),
            "--threads" => {
                threads_list = value("--threads")
                    .split(',')
                    .map(|s| s.trim().parse().expect("--threads"))
                    .collect()
            }
            "--seeds" => num_seeds = value("--seeds").parse().expect("--seeds"),
            other => panic!("unknown argument `{other}`"),
        }
    }

    let max_threads = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(usize::MAX);
    threads_list.retain(|&t| {
        let ok = t <= max_threads && t <= Worker::MAX_WORKER_SIZE;
        if !ok {
            eprintln!("skipping {t} threads (machine has {max_threads})");
        }
        ok
    });

    let seeds: Vec<Seed> = (0..num_seeds as u32).map(fixed_seed).collect();

    println!(
        "keccak search_pow scaling: {bits}-bit difficulty, {} fixed seed(s), threads {threads_list:?}"
    , seeds.len());
    println!("threads,seed,nonce,seconds,mh_per_s");

    // (threads -> summed seconds over seeds)
    let mut totals: Vec<(usize, f64)> = Vec::new();
    for &t in &threads_list {
        let worker = Worker::new_with_num_threads(t);
        // One untimed warmup grind at low difficulty spins the pool up.
        let _ = <Tr as Transcript<Proth120, Proth120>>::search_pow(&seeds[0], 16, &worker);

        let mut total = 0.0f64;
        for (i, seed) in seeds.iter().enumerate() {
            let start = std::time::Instant::now();
            let (_seed_out, nonce) =
                <Tr as Transcript<Proth120, Proth120>>::search_pow(seed, bits, &worker);
            let el = start.elapsed().as_secs_f64();
            total += el;
            // Total hashes scanned across all stripes ~= winning nonce.
            println!("{t},{i},{nonce},{el:.3},{:.2}", nonce as f64 / el / 1.0e6);
        }
        totals.push((t, total));
    }

    let (base_threads, base_total) = totals[0];
    println!("\nscaling summary (vs {base_threads} threads):");
    println!("threads,total_seconds,speedup,ideal_speedup,parallel_efficiency_%");
    for &(t, total) in &totals {
        let speedup = base_total / total;
        let ideal = t as f64 / base_threads as f64;
        println!(
            "{t},{total:.3},{speedup:.2},{ideal:.2},{:.1}",
            100.0 * speedup / ideal
        );
    }
}
