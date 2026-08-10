#![feature(allocator_api)]
//! Experiment harness for prover performance work. Depends only on the leaf
//! crates (`field`/`fft`/`worker`) so a release rebuild is seconds, and it
//! cross-compiles standalone for remote benchmark machines.
//!
//! Sections (select by argv, default = all):
//!   `bw`     — machine memory-bandwidth roofline (single-thread + all-threads
//!              read / write / copy / triad over multi-GiB buffers).
//!   `field`  — Proth120 arithmetic micro-benches (latency chains + throughput)
//!              incl. the experimental special-form Montgomery multiplication.
//!   `stages` — the non-GKR prover stage kernels at production sizes, each
//!              reported as effective GB/s against the measured roofline.
//!
//! Env knobs: `BENCH_THREADS` caps the worker pool.

use field::{Field, FieldExtension, PrimeField, Proth120, Rand, TwoAdicField};
use std::alloc::Global;
use std::time::Instant;
use worker::Worker;

mod ifma;
mod proth_adx;
mod proth_opt;
mod stages;

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

fn gbps(bytes: usize, seconds: f64) -> f64 {
    bytes as f64 / seconds / 1e9
}

// ---------------------------------------------------------------------------
// bw: memory bandwidth roofline
// ---------------------------------------------------------------------------

fn bench_bw(worker: &Worker) {
    // 8 GiB working set: far beyond any cache level.
    const BYTES: usize = 8 << 30;
    let n = BYTES / 8;
    // NUMA-aware first touch: allocate uninitialized and FILL IN PARALLEL with
    // the same chunk->thread mapping the benchmark loops use, so each page is
    // owned by the node that will access it. (A serial `vec![1; n]` puts all
    // 8 GiB on one node and measures cross-socket contention instead of the
    // machine's aggregate bandwidth.)
    let mut a: Vec<u64> = Vec::with_capacity(n);
    let mut b: Vec<u64> = Vec::with_capacity(n);
    #[allow(clippy::uninit_vec)]
    unsafe {
        a.set_len(n);
        b.set_len(n);
    }
    parallel_over_chunks_mut(&mut a, worker, |chunk| {
        for x in chunk.iter_mut() {
            *x = 1;
        }
    });
    parallel_over_chunks_mut(&mut b, worker, |chunk| {
        for x in chunk.iter_mut() {
            *x = 2;
        }
    });

    println!("\n== memory bandwidth roofline (8 GiB buffers) ==");

    // single-thread streaming read (sum)
    let t = median(
        3,
        || (),
        |_| {
            let mut acc = 0u64;
            for &x in a.iter() {
                acc = acc.wrapping_add(x);
            }
            std::hint::black_box(acc);
        },
    );
    println!("  1-thread read             {:>8.1} GB/s", gbps(BYTES, t));

    // all-threads streaming read
    let t = median(
        3,
        || (),
        |_| {
            let acc = parallel_over_chunks(&a, worker, |chunk| {
                let mut acc = 0u64;
                for &x in chunk.iter() {
                    acc = acc.wrapping_add(x);
                }
                acc
            });
            std::hint::black_box(acc);
        },
    );
    println!("  all-thread read           {:>8.1} GB/s", gbps(BYTES, t));

    // all-threads write (fill)
    let t = median(
        3,
        || (),
        |_| {
            parallel_over_chunks_mut(&mut a, worker, |chunk| {
                for x in chunk.iter_mut() {
                    *x = 3;
                }
            });
        },
    );
    println!("  all-thread write          {:>8.1} GB/s", gbps(BYTES, t));

    // all-threads copy b -> a (2 bytes of traffic per byte copied: read + write;
    // report as touched bytes = 2x)
    let t = median(
        3,
        || (),
        |_| {
            let src = &b;
            parallel_copy(src, &mut a, worker);
        },
    );
    println!(
        "  all-thread copy (r+w)     {:>8.1} GB/s",
        gbps(2 * BYTES, t)
    );

    // all-threads triad a[i] = a[i] * k + b[i] over u64 (3 accesses per elem)
    let t = median(
        3,
        || (),
        |_| {
            let src = &b;
            parallel_triad(src, &mut a, worker);
        },
    );
    println!(
        "  all-thread triad (2r+1w)  {:>8.1} GB/s",
        gbps(3 * BYTES, t)
    );
    drop(a);
    drop(b);
}

fn parallel_over_chunks<T: Sync, R: Send + std::iter::Sum>(
    data: &[T],
    worker: &Worker,
    f: impl Fn(&[T]) -> R + Sync,
) -> R {
    use worker::rayon::prelude::*;
    let chunk = data.len().div_ceil(worker.get_num_cores());
    worker
        .pool
        .install(|| data.par_chunks(chunk).map(|c| f(c)).sum())
}

fn parallel_over_chunks_mut<T: Send>(
    data: &mut [T],
    worker: &Worker,
    f: impl Fn(&mut [T]) + Sync,
) {
    use worker::rayon::prelude::*;
    let chunk = data.len().div_ceil(worker.get_num_cores());
    worker
        .pool
        .install(|| data.par_chunks_mut(chunk).for_each(|c| f(c)));
}

fn parallel_copy(src: &[u64], dst: &mut [u64], worker: &Worker) {
    use worker::rayon::prelude::*;
    let chunk = src.len().div_ceil(worker.get_num_cores());
    worker.pool.install(|| {
        dst.par_chunks_mut(chunk)
            .zip(src.par_chunks(chunk))
            .for_each(|(d, s)| d.copy_from_slice(s));
    });
}

fn parallel_triad(src: &[u64], dst: &mut [u64], worker: &Worker) {
    use worker::rayon::prelude::*;
    let chunk = src.len().div_ceil(worker.get_num_cores());
    worker.pool.install(|| {
        dst.par_chunks_mut(chunk)
            .zip(src.par_chunks(chunk))
            .for_each(|(d, s)| {
                for (x, &y) in d.iter_mut().zip(s.iter()) {
                    *x = x.wrapping_mul(3).wrapping_add(y);
                }
            });
    });
}

// ---------------------------------------------------------------------------
// field: Proth120 arithmetic micro-benches
// ---------------------------------------------------------------------------

fn bench_field() {
    let mut rng = rand::rng();
    println!("\n== Proth120 arithmetic ==");

    // Latency: dependent multiplication chain.
    let n_lat = 1u64 << 24;
    let mut x = Proth120::random_element(&mut rng);
    let y = Proth120::random_element(&mut rng);
    let t0 = Instant::now();
    for _ in 0..n_lat {
        x.mul_assign(&y);
    }
    std::hint::black_box(x);
    let t = t0.elapsed().as_secs_f64();
    println!(
        "  mul latency (dep chain)     {:>7.2} ns/op",
        t / n_lat as f64 * 1e9
    );

    // Throughput: 8 independent chains.
    let mut xs: [Proth120; 8] = core::array::from_fn(|_| Proth120::random_element(&mut rng));
    let t0 = Instant::now();
    for _ in 0..(n_lat / 8) {
        for x in xs.iter_mut() {
            x.mul_assign(&y);
        }
    }
    std::hint::black_box(&xs);
    let t = t0.elapsed().as_secs_f64();
    println!(
        "  mul throughput (8 chains)   {:>7.2} ns/op",
        t / n_lat as f64 * 1e9
    );

    // Experimental special-form Montgomery mul: p = 7*2^120 + 1 means
    // p == 1 (mod 2^64), so the reduction pass needs no real multiplies.
    let mut x2 = proth_opt::OptProth(x_raw(&mut rng));
    let y2 = proth_opt::OptProth(x_raw(&mut rng));
    let t0 = Instant::now();
    for _ in 0..n_lat {
        x2.mul_assign_opt(&y2);
    }
    std::hint::black_box(&x2);
    let t = t0.elapsed().as_secs_f64();
    println!(
        "  OPT mul latency             {:>7.2} ns/op",
        t / n_lat as f64 * 1e9
    );

    let mut xs2: [proth_opt::OptProth; 8] =
        core::array::from_fn(|_| proth_opt::OptProth(x_raw(&mut rng)));
    let t0 = Instant::now();
    for _ in 0..(n_lat / 8) {
        for x in xs2.iter_mut() {
            x.mul_assign_opt(&y2);
        }
    }
    std::hint::black_box(&xs2);
    let t = t0.elapsed().as_secs_f64();
    println!(
        "  OPT mul throughput          {:>7.2} ns/op",
        t / n_lat as f64 * 1e9
    );

    // add latency chain for context
    let mut x3 = Proth120::random_element(&mut rng);
    let y3 = Proth120::random_element(&mut rng);
    let t0 = Instant::now();
    for _ in 0..n_lat {
        x3.add_assign(&y3);
    }
    std::hint::black_box(x3);
    let t = t0.elapsed().as_secs_f64();
    println!(
        "  add latency (dep chain)     {:>7.2} ns/op",
        t / n_lat as f64 * 1e9
    );

    proth_opt::self_check();
    println!("  (opt mul self-check vs reference: OK)");

    // BMI2 mulx + ADX adcx/adox inline-asm variant (x86-64 only).
    #[cfg(target_arch = "x86_64")]
    {
        proth_adx::self_check();
        println!("  (adx mul self-check vs reference: OK)");

        let mut xa = x_raw(&mut rng);
        let ya = x_raw(&mut rng);
        let t0 = Instant::now();
        for _ in 0..n_lat {
            xa = proth_adx::imp::mont_mul_adx(xa, ya);
        }
        std::hint::black_box(xa);
        let t = t0.elapsed().as_secs_f64();
        println!(
            "  ADX mul latency             {:>7.2} ns/op",
            t / n_lat as f64 * 1e9
        );

        let mut xs3: [u128; 8] = core::array::from_fn(|_| x_raw(&mut rng));
        let t0 = Instant::now();
        for _ in 0..(n_lat / 8) {
            for x in xs3.iter_mut() {
                *x = proth_adx::imp::mont_mul_adx(*x, ya);
            }
        }
        std::hint::black_box(&xs3);
        let t = t0.elapsed().as_secs_f64();
        println!(
            "  ADX mul throughput          {:>7.2} ns/op",
            t / n_lat as f64 * 1e9
        );
    }
}

fn x_raw(rng: &mut impl rand::Rng) -> u128 {
    Proth120::random_element(rng).raw_u128_value()
}

// ---------------------------------------------------------------------------
// hash: Blake2s (as used by the BabyBear Merkle trees) throughput roofline
// ---------------------------------------------------------------------------

/// Measures the machine's Blake2s hashing roofline with the EXACT primitives
/// the `Blake2sU32MerkleTreeWithCap` uses: `compress_two_to_one` (node layers,
/// one 64-B block per node) and a chained `absorb` (leaf hashing, one 64-B
/// block per 16 u32 words of leaf data), both in the tree's default
/// REDUCED-round mode and in full-round mode. Reported as Mhash/s and GB/s of
/// hashed payload; the all-thread numbers are the machine's hashing bound for
/// Merkle-tree construction.
fn bench_hash(worker: &Worker) {
    use blake2s_u32::{Blake2sState, BLAKE2S_BLOCK_SIZE_U32_WORDS, BLAKE2S_DIGEST_SIZE_U32_WORDS};
    use worker::rayon::prelude::*;

    println!("\n== Blake2s hashing roofline (merkle-tree primitives) ==");

    const N: usize = 1 << 22; // compressions per measurement
    let block: [u32; BLAKE2S_BLOCK_SIZE_U32_WORDS] = core::array::from_fn(|i| i as u32);

    fn compress_chain<const REDUCED: bool>(
        n: usize,
        seed: &[u32; BLAKE2S_BLOCK_SIZE_U32_WORDS],
    ) -> [u32; BLAKE2S_DIGEST_SIZE_U32_WORDS] {
        // dependent chain: digest feeds half of the next block — matches the
        // serial dependency of one tree PATH, and (run in parallel over many
        // chains) the throughput shape of layer construction.
        let mut block = *seed;
        let mut dst = [0u32; BLAKE2S_DIGEST_SIZE_U32_WORDS];
        for _ in 0..n {
            Blake2sState::compress_two_to_one::<REDUCED>(&block, &mut dst);
            block[..BLAKE2S_DIGEST_SIZE_U32_WORDS].copy_from_slice(&dst);
        }
        dst
    }

    fn absorb_chain<const REDUCED: bool>(
        n: usize,
        seed: &[u32; BLAKE2S_BLOCK_SIZE_U32_WORDS],
    ) -> [u32; BLAKE2S_DIGEST_SIZE_U32_WORDS] {
        // long-message absorb: the leaf-hashing shape (state carried across
        // blocks, no re-init) — independent blocks, throughput-bound.
        let mut hasher = Blake2sState::new();
        let mut dst = [0u32; BLAKE2S_DIGEST_SIZE_U32_WORDS];
        for _ in 0..n - 1 {
            hasher.absorb::<REDUCED>(seed);
        }
        hasher.absorb_final_block::<REDUCED>(seed, BLAKE2S_BLOCK_SIZE_U32_WORDS, &mut dst);
        dst
    }

    let bytes = N * 64;
    let threads = worker.get_num_cores();

    // 1-thread
    let t0 = Instant::now();
    std::hint::black_box(compress_chain::<true>(N, &block));
    let t = t0.elapsed().as_secs_f64();
    println!(
        "  1-thread compress (reduced)  {:>7.1} Mh/s  {:>6.2} GB/s",
        N as f64 / t / 1e6,
        gbps(bytes, t)
    );

    let t0 = Instant::now();
    std::hint::black_box(compress_chain::<false>(N, &block));
    let t = t0.elapsed().as_secs_f64();
    println!(
        "  1-thread compress (full)     {:>7.1} Mh/s  {:>6.2} GB/s",
        N as f64 / t / 1e6,
        gbps(bytes, t)
    );

    let t0 = Instant::now();
    std::hint::black_box(absorb_chain::<true>(N, &block));
    let t = t0.elapsed().as_secs_f64();
    println!(
        "  1-thread absorb   (reduced)  {:>7.1} Mh/s  {:>6.2} GB/s",
        N as f64 / t / 1e6,
        gbps(bytes, t)
    );

    // all threads: independent chains, aggregate throughput
    let t0 = Instant::now();
    worker.pool.install(|| {
        (0..threads).into_par_iter().for_each(|i| {
            let mut seed = block;
            seed[0] ^= i as u32;
            std::hint::black_box(compress_chain::<true>(N, &seed));
        });
    });
    let t = t0.elapsed().as_secs_f64();
    println!(
        "  {threads}-thread compress (reduced) {:>8.1} Mh/s  {:>6.1} GB/s",
        (N * threads) as f64 / t / 1e6,
        gbps(bytes * threads, t)
    );

    let t0 = Instant::now();
    worker.pool.install(|| {
        (0..threads).into_par_iter().for_each(|i| {
            let mut seed = block;
            seed[0] ^= i as u32;
            std::hint::black_box(absorb_chain::<true>(N, &seed));
        });
    });
    let t = t0.elapsed().as_secs_f64();
    println!(
        "  {threads}-thread absorb   (reduced) {:>8.1} Mh/s  {:>6.1} GB/s",
        (N * threads) as f64 / t / 1e6,
        gbps(bytes * threads, t)
    );
}

// ---------------------------------------------------------------------------

fn bench_ifma(worker: &Worker) {
    println!("\n== IFMA (avx512, vpmadd52) Proth120 NTT draft ==");
    #[cfg(all(target_arch = "x86_64", target_feature = "avx512ifma"))]
    {
        ifma::self_check(12);
        ifma::self_check(16);
        ifma::self_check_six_step::<ifma::IfmaK>(12);
        ifma::self_check_six_step::<ifma::IfmaK>(16);
        println!("  (self-checks incl. six-step vs scalar reference: OK)");

        let log_n = 24u32;
        let n = 1usize << log_n;
        let mut rng = rand::rng();
        let input: Vec<Proth120> = (0..n).map(|_| Proth120::random_element(&mut rng)).collect();
        let tw: Vec<Proth120, Global> =
            fft::precompute_all_twiddles_for_fft_serial::<Proth120, Global, false>(n);
        let tw52 = ifma::convert_twiddles(&tw[..n / 2]);
        println!("  converting 2^{log_n} input to limb planes...");
        let planes = ifma::Planes::from_proth(&input);

        let t = median(
            3,
            || input.clone(),
            |mut v| {
                fft::naive::serial_ct_ntt_bitreversed_to_natural(&mut v, log_n, &tw[..n / 2]);
                std::hint::black_box(v);
            },
        );
        println!("  scalar DIT NTT 2^{log_n} serial   {:>9.1} ms", t * 1e3);

        let t = median(
            3,
            || planes.clone(),
            |mut p| {
                ifma::ifma_ntt_bitreversed_to_natural(&mut p, log_n, &tw52);
                std::hint::black_box(p);
            },
        );
        println!("  IFMA   DIT NTT 2^{log_n} serial   {:>9.1} ms", t * 1e3);

        // aggregate: one NTT per core (the work-stealing grid regime). Each task
        // clones its input inside the timed region for both variants (note the
        // limb planes are 1.5x larger than the packed u128 form: 24 B/elem).
        use worker::rayon::prelude::*;
        let tasks = worker.get_num_cores();
        let t0 = Instant::now();
        worker.pool.install(|| {
            (0..tasks).into_par_iter().for_each(|_| {
                let mut v = input.clone();
                fft::naive::serial_ct_ntt_bitreversed_to_natural(&mut v, log_n, &tw[..n / 2]);
                std::hint::black_box(v);
            });
        });
        let t = t0.elapsed().as_secs_f64();
        println!("  {tasks} concurrent scalar NTTs    {:>9.1} ms", t * 1e3);

        let t0 = Instant::now();
        worker.pool.install(|| {
            (0..tasks).into_par_iter().for_each(|_| {
                let mut p = planes.clone();
                ifma::ifma_ntt_bitreversed_to_natural(&mut p, log_n, &tw52);
                std::hint::black_box(p);
            });
        });
        let t = t0.elapsed().as_secs_f64();
        println!("  {tasks} concurrent IFMA NTTs      {:>9.1} ms", t * 1e3);

        // ---- six-step variants (natural -> natural, out-of-place; the input
        // planes / Proth vec are shared read-only across tasks) ----
        println!("\n  -- six-step (natural->natural) --");
        let tables = ifma::build_six_step_tables(log_n);
        let omega = fft::domain_generator_for_size::<Proth120>(1u64 << log_n);

        // naive scalar four/six-step (u128 field ops), offset = 1
        let t = median(
            3,
            || (),
            |_| {
                let mut scratch: Vec<Proth120> = Vec::new();
                let v = fft::fft_natural_to_natural_four_step(
                    &input,
                    Proth120::ONE,
                    omega,
                    &tw,
                    &mut scratch,
                );
                std::hint::black_box(v);
            },
        );
        println!("  naive six-step 2^{log_n} serial   {:>9.1} ms", t * 1e3);

        let t = median(
            3,
            || (),
            |_| {
                let v = ifma::six_step_ntt::<ifma::IfmaK>(&planes, log_n, &tw52, &tables);
                std::hint::black_box(v);
            },
        );
        println!("  IFMA  six-step 2^{log_n} serial   {:>9.1} ms", t * 1e3);

        let t0 = Instant::now();
        worker.pool.install(|| {
            (0..tasks).into_par_iter().for_each(|_| {
                let mut scratch: Vec<Proth120> = Vec::new();
                let v = fft::fft_natural_to_natural_four_step(
                    &input,
                    Proth120::ONE,
                    omega,
                    &tw,
                    &mut scratch,
                );
                std::hint::black_box(v);
            });
        });
        let t = t0.elapsed().as_secs_f64();
        println!("  {tasks} concurrent naive six-step {:>9.1} ms", t * 1e3);

        let t0 = Instant::now();
        worker.pool.install(|| {
            (0..tasks).into_par_iter().for_each(|_| {
                let v = ifma::six_step_ntt::<ifma::IfmaK>(&planes, log_n, &tw52, &tables);
                std::hint::black_box(v);
            });
        });
        let t = t0.elapsed().as_secs_f64();
        println!("  {tasks} concurrent IFMA six-step  {:>9.1} ms", t * 1e3);
    }
    #[cfg(not(all(target_arch = "x86_64", target_feature = "avx512ifma")))]
    {
        let _ = worker;
        // Validate the 52-bit-domain arithmetic + six-step layout via the
        // portable scalar kernel.
        ifma::self_check(10);
        ifma::self_check_six_step::<ifma::ScalarK>(10);
        ifma::self_check_six_step::<ifma::ScalarK>(14);
        println!("  avx512ifma not compiled in — scalar-kernel self-checks only (OK)");
    }
}

fn bench_lde(worker: &Worker) {
    println!("\n== realistic LDE grid: 7 polys x 2^26, LDE 32 (prover schedule) ==");
    #[cfg(all(target_arch = "x86_64", target_feature = "avx512ifma"))]
    {
        use worker::rayon::prelude::*;

        ifma::self_check_lde::<ifma::IfmaK>(12);
        ifma::self_check_lde::<ifma::IfmaLazyK>(12);
        ifma::self_check_lde::<ifma::IfmaLazyK>(16);
        println!("  (LDE-task self-checks: strict + lazy OK)");

        let log_n = 26u32;
        let n = 1usize << log_n;
        let lde_factor = 32usize;
        let num_polys = 7usize;

        println!("  generating {num_polys} random 2^{log_n} polys + twiddles...");
        let mut rng = rand::rng();
        let polys: Vec<Vec<Proth120>> = (0..num_polys)
            .map(|_| (0..n).map(|_| Proth120::random_element(&mut rng)).collect())
            .collect();
        let tw: Vec<Proth120, Global> =
            fft::precompute_all_twiddles_for_fft_serial::<Proth120, Global, false>(n);
        let tw52 = ifma::convert_twiddles(&tw[..n / 2]);
        let tables = ifma::build_six_step_tables(log_n);
        let root = fft::domain_generator_for_size::<Proth120>((n * lde_factor) as u64);
        let offsets: Vec<Proth120> = {
            let mut v = Vec::with_capacity(lde_factor);
            let mut cur = Proth120::ONE;
            for _ in 0..lde_factor {
                v.push(cur);
                cur.mul_assign(&root);
            }
            v
        };

        // ---- serial single-coset diagnostics (coset 1, offset != 1) ----
        println!("\n  -- serial single-coset 2^{log_n} diagnostics --");
        let t = median(
            1,
            || (),
            |_| {
                let v = fft::lde_coset_natural_seq_fused(&polys[0], offsets[1], &tw);
                std::hint::black_box(v);
            },
        );
        println!("  seq-fused (DIT) baseline        {:>9.1} ms", t * 1e3);

        let t = median(
            1,
            || (),
            |_| {
                let v = fft::proth120_lazy::lde_coset_lazy(&polys[0], offsets[1], &tw);
                std::hint::black_box(v);
            },
        );
        println!("  seq-fused LAZY (<2p, DIT)       {:>9.1} ms", t * 1e3);

        let t = median(
            1,
            || (),
            |_| {
                let v = fft::proth120_lazy::lde_coset_lazy_r4(&polys[0], offsets[1], &tw);
                std::hint::black_box(v);
            },
        );
        println!("  seq-fused LAZY radix-4          {:>9.1} ms", t * 1e3);

        let t = median(
            1,
            || (),
            |_| {
                let v = fft::proth120_lazy::lde_coset_lazy_r8(&polys[0], offsets[1], &tw);
                std::hint::black_box(v);
            },
        );
        println!("  seq-fused LAZY radix-8          {:>9.1} ms", t * 1e3);

        let omega = fft::domain_generator_for_size::<Proth120>(n as u64);
        let t = median(
            1,
            || (),
            |_| {
                let mut scratch: Vec<Proth120> = Vec::new();
                let v = fft::fft_natural_to_natural_four_step(
                    &polys[0],
                    offsets[1],
                    omega,
                    &tw,
                    &mut scratch,
                );
                std::hint::black_box(v);
            },
        );
        println!("  naive six-step                  {:>9.1} ms", t * 1e3);

        let t = median(
            1,
            || (),
            |_| {
                let mut scratch: Vec<Proth120> = Vec::new();
                let v = fft::fft_natural_to_natural_four_step_r4(
                    &polys[0],
                    offsets[1],
                    omega,
                    &tw,
                    &mut scratch,
                );
                std::hint::black_box(v);
            },
        );
        println!("  naive six-step radix-4          {:>9.1} ms", t * 1e3);

        let t = median(
            1,
            || (),
            |_| {
                let mut scratch: Vec<Proth120> = Vec::new();
                let v = fft::fft_natural_to_natural_four_step_r8(
                    &polys[0],
                    offsets[1],
                    omega,
                    &tw,
                    &mut scratch,
                );
                std::hint::black_box(v);
            },
        );
        println!("  naive six-step radix-8          {:>9.1} ms", t * 1e3);

        let mut st = ifma::StageTimes::default();
        let t0 = Instant::now();
        let v = ifma::lde_coset_six_step::<ifma::IfmaLazyK>(
            &polys[0],
            offsets[1],
            log_n,
            &tw52,
            &tables,
            Some(&mut st),
        );
        let t = t0.elapsed().as_secs_f64();
        std::hint::black_box(v);
        println!("  IFMA-lazy six-step              {:>9.1} ms, stages:", t * 1e3);
        let n1 = tables.n1;
        let n2 = tables.n2;
        println!(
            "    gather+convert+scale  {:>8.1} ms   (block {}x{} = {} KiB/8-row block)",
            st.gather_scale_in * 1e3,
            n1,
            n2,
            n2 * 8 * 8 * 3 / 1024,
        );
        println!("    phase-A NTT (rows N2) {:>8.1} ms", st.phase_a_ntt * 1e3);
        println!("    twiddle correction    {:>8.1} ms", st.twiddle_correction * 1e3);
        println!("    relayout (8x8 tiles)  {:>8.1} ms", st.relayout * 1e3);
        println!("    phase-B NTT (rows N1) {:>8.1} ms", st.phase_b_ntt * 1e3);
        println!("    scatter+convert out   {:>8.1} ms", st.scatter_out * 1e3);

        // compute bound: measure mul8 throughput and model the NTT phases
        let t_mul8 = {
            let mut buf = ifma::Planes {
                l0: vec![1; 1 << 13],
                l1: vec![0; 1 << 13],
                l2: vec![0; 1 << 13],
            };
            let s = ifma::to_mont52(12345);
            let reps = 2000usize;
            let t0 = Instant::now();
            for _ in 0..reps {
                for j in (0..(1usize << 13)).step_by(8) {
                    unsafe {
                        use ifma::Kernel8;
                        let v = ifma::IfmaLazyK::load(
                            buf.l0.as_ptr().add(j),
                            buf.l1.as_ptr().add(j),
                            buf.l2.as_ptr().add(j),
                        );
                        let v = ifma::IfmaLazyK::mul_broadcast(v, &s);
                        ifma::IfmaLazyK::store(
                            v,
                            buf.l0.as_mut_ptr().add(j),
                            buf.l1.as_mut_ptr().add(j),
                            buf.l2.as_mut_ptr().add(j),
                        );
                    }
                }
            }
            t0.elapsed().as_secs_f64() / (reps * (1 << 13) / 8) as f64
        };
        // butterflies per transform: n/2 * (log_n2 + log_n1); each = ~1 mul8/8 lanes
        let bf_vec_ops = (n / 2 / 8) * log_n as usize;
        let tw_vec_ops = 2 * n / 8;
        let conv_vec_ops = 2 * n / 8;
        println!(
            "    [model] mul8 = {:.2} ns; NTT-mul bound = {:.0} ms, +twiddle/conv = {:.0} ms",
            t_mul8 * 1e9,
            bf_vec_ops as f64 * t_mul8 * 1e3,
            (bf_vec_ops + tw_vec_ops + conv_vec_ops) as f64 * t_mul8 * 1e3,
        );

        // ---- the grid: 7 polys x 8 cosets = 56 tasks over 88 cores ----
        let tasks: Vec<(usize, usize)> = (0..num_polys)
            .flat_map(|p| (0..lde_factor).map(move |c| (p, c)))
            .collect();
        println!("\n  -- grid: {} tasks over {} cores --", tasks.len(), worker.get_num_cores());

        let t0 = Instant::now();
        worker.pool.install(|| {
            tasks.par_iter().for_each(|&(p, c)| {
                let v = fft::lde_coset_natural_seq_fused(&polys[p], offsets[c], &tw);
                std::hint::black_box(v);
            });
        });
        println!("  seq-fused (DIT) grid            {:>9.1} ms", t0.elapsed().as_secs_f64() * 1e3);

        let t0 = Instant::now();
        worker.pool.install(|| {
            tasks.par_iter().for_each(|&(p, c)| {
                let v = fft::proth120_lazy::lde_coset_lazy(&polys[p], offsets[c], &tw);
                std::hint::black_box(v);
            });
        });
        println!("  seq-fused LAZY grid             {:>9.1} ms", t0.elapsed().as_secs_f64() * 1e3);

        let t0 = Instant::now();
        worker.pool.install(|| {
            tasks.par_iter().for_each(|&(p, c)| {
                let v = fft::proth120_lazy::lde_coset_lazy_r4(&polys[p], offsets[c], &tw);
                std::hint::black_box(v);
            });
        });
        println!("  seq-fused LAZY r4 grid          {:>9.1} ms", t0.elapsed().as_secs_f64() * 1e3);

        let t0 = Instant::now();
        worker.pool.install(|| {
            tasks.par_iter().for_each(|&(p, c)| {
                let v = fft::proth120_lazy::lde_coset_lazy_r8(&polys[p], offsets[c], &tw);
                std::hint::black_box(v);
            });
        });
        println!("  seq-fused LAZY r8 grid          {:>9.1} ms", t0.elapsed().as_secs_f64() * 1e3);

        let t0 = Instant::now();
        worker.pool.install(|| {
            tasks.par_iter().for_each(|&(p, c)| {
                let mut scratch: Vec<Proth120> = Vec::new();
                let v = fft::fft_natural_to_natural_four_step(
                    &polys[p],
                    offsets[c],
                    omega,
                    &tw,
                    &mut scratch,
                );
                std::hint::black_box(v);
            });
        });
        println!("  naive six-step grid             {:>9.1} ms", t0.elapsed().as_secs_f64() * 1e3);

        let t0 = Instant::now();
        worker.pool.install(|| {
            tasks.par_iter().for_each(|&(p, c)| {
                let mut scratch: Vec<Proth120> = Vec::new();
                let v = fft::fft_natural_to_natural_four_step_r4(
                    &polys[p],
                    offsets[c],
                    omega,
                    &tw,
                    &mut scratch,
                );
                std::hint::black_box(v);
            });
        });
        println!("  naive six-step r4 grid          {:>9.1} ms", t0.elapsed().as_secs_f64() * 1e3);

        let t0 = Instant::now();
        worker.pool.install(|| {
            tasks.par_iter().for_each(|&(p, c)| {
                let mut scratch: Vec<Proth120> = Vec::new();
                let v = fft::fft_natural_to_natural_four_step_r8(
                    &polys[p],
                    offsets[c],
                    omega,
                    &tw,
                    &mut scratch,
                );
                std::hint::black_box(v);
            });
        });
        println!("  naive six-step r8 grid          {:>9.1} ms", t0.elapsed().as_secs_f64() * 1e3);

        let t0 = Instant::now();
        worker.pool.install(|| {
            tasks.par_iter().for_each(|&(p, c)| {
                let v = ifma::lde_coset_six_step::<ifma::IfmaLazyK>(
                    &polys[p],
                    offsets[c],
                    log_n,
                    &tw52,
                    &tables,
                    None,
                );
                std::hint::black_box(v);
            });
        });
        println!("  IFMA-lazy six-step grid         {:>9.1} ms", t0.elapsed().as_secs_f64() * 1e3);
    }
    #[cfg(not(all(target_arch = "x86_64", target_feature = "avx512ifma")))]
    {
        let _ = worker;
        ifma::self_check_lde::<ifma::ScalarK>(12);
        ifma::self_check_lde::<ifma::ScalarLazyK>(12);
        ifma::self_check_lde::<ifma::ScalarLazyK>(14);
        println!("  avx512ifma not compiled in — scalar LDE-task self-checks only (OK)");
    }
}

fn main() {
    let filter = std::env::args()
        .skip(1)
        .find(|a| {
            a == "bw" || a == "field" || a == "stages" || a == "ifma" || a == "lde" || a == "hash"
        })
        .unwrap_or_default();
    let worker = match std::env::var("BENCH_THREADS")
        .ok()
        .and_then(|v| v.parse().ok())
    {
        Some(t) => Worker::new_with_num_threads(t),
        None => Worker::new(),
    };
    println!("host cores: {}", worker.get_num_cores());

    if filter.is_empty() || filter == "bw" {
        bench_bw(&worker);
    }
    if filter.is_empty() || filter == "field" {
        bench_field();
    }
    if filter.is_empty() || filter == "stages" {
        stages::bench_stages(&worker);
    }
    if filter.is_empty() || filter == "hash" {
        bench_hash(&worker);
    }
    if filter.is_empty() || filter == "ifma" {
        bench_ifma(&worker);
    }
    if filter.is_empty() || filter == "lde" {
        bench_lde(&worker);
    }
}
