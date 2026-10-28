//! STAGE PROBE (aarch64, BabyBear/Ext4): where the time of the non-sumcheck
//! prover stages goes — base-commitment LDE vs Merkle tree, the WHIR
//! intermediate-oracle LDE vs tree, and the forward-layer relation
//! archetypes — each placed against this machine's measured page-fault,
//! write, read and copy ceilings, so every stage can be labelled "fault
//! tax", "bandwidth" or "compute".
//!
//! No proof is produced and nothing outside this module changes. `#[ignore]`d,
//! env-driven:
//!
//! ```text
//! STAGE_LOG2=23 STAGE_THREADS=8 STAGE_COLS=61 STAGE_SECTIONS=mem,lde,tree,whir,fwd \
//!   <test-binary> --ignored --nocapture --exact gkr::prover::stage_probe::stage_probe
//! ```
//!
//! Env: `STAGE_LOG2` (trace length log2, default 23), `STAGE_THREADS`
//! (default 8), `STAGE_COLS` (base commitment columns, default 61),
//! `STAGE_SECTIONS` (comma list of `mem,lde,tree,whir,fwd`, default all),
//! `STAGE_REPS` (default 2; every rep is printed, the first is the cold one).

use crate::gkr::prover::backend::{Backend, DefaultBabyBearBackend, ExtCoeffConversion};
use crate::merkle_trees::{ColumnMajorMerkleTreeConstructor, DefaultTreeConstructor};
use blake2s_u32::{Blake2sState, BLAKE2S_BLOCK_SIZE_U32_WORDS, BLAKE2S_DIGEST_SIZE_U32_WORDS};
use field::baby_bear::{base::BabyBearField, ext4::BabyBearExt4};
use field::{Field, FieldExtension, PrimeField};
use std::hint::black_box;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};
use worker::Worker;

type BB = BabyBearField;
type E4 = BabyBearExt4;

const P: u64 = 0x7800_0001;
const CAP: usize = 64;

fn env_usize(name: &str, default: usize) -> usize {
    std::env::var(name)
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(default)
}

fn splitmix(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// `items` tasks over `threads` OS threads, dynamically claimed.
fn par_for(items: usize, threads: usize, f: impl Fn(usize) + Sync) {
    let next = AtomicUsize::new(0);
    std::thread::scope(|s| {
        for _ in 0..threads.min(items).max(1) {
            let next = &next;
            let f = &f;
            s.spawn(move || loop {
                let i = next.fetch_add(1, Ordering::Relaxed);
                if i >= items {
                    break;
                }
                f(i);
            });
        }
    });
}

/// Static row chunks over `threads` OS threads (the prover's `apply_row_wise`
/// shape).
fn par_rows(n: usize, threads: usize, f: impl Fn(usize, usize) + Sync) {
    let chunk = n.div_ceil(threads).max(1);
    std::thread::scope(|s| {
        let mut start = 0;
        while start < n {
            let end = (start + chunk).min(n);
            let f = &f;
            s.spawn(move || f(start, end));
            start = end;
        }
    });
}

fn par_fill<T: Send, const K: usize>(
    dst: &mut [T],
    seed: u64,
    threads: usize,
    make: impl Fn([u32; K]) -> T + Sync,
) {
    let chunk = dst.len().div_ceil(threads).max(1);
    std::thread::scope(|s| {
        for (i, part) in dst.chunks_mut(chunk).enumerate() {
            let make = &make;
            s.spawn(move || {
                let mut st = seed ^ ((i as u64 + 1) << 40);
                for el in part.iter_mut() {
                    let limbs: [u32; K] = core::array::from_fn(|_| (splitmix(&mut st) % P) as u32);
                    *el = make(limbs);
                }
            });
        }
    });
}

fn random_base_polys(count: usize, len: usize, threads: usize, seed: u64) -> Vec<Vec<BB>> {
    (0..count)
        .map(|i| {
            let mut v = vec![BB::ZERO; len];
            par_fill::<BB, 1>(&mut v, seed ^ (i as u64 * 0x1234_5678_9ABC), threads, |l| {
                BB::new(l[0])
            });
            v
        })
        .collect()
}

fn random_ext_poly(len: usize, threads: usize, seed: u64) -> Vec<E4> {
    let mut v = vec![E4::ZERO; len];
    par_fill::<E4, 4>(&mut v, seed, threads, |l| {
        E4::from_array_of_base(l.map(BB::new))
    });
    v
}

fn gbs(bytes: usize, d: Duration) -> f64 {
    bytes as f64 / d.as_secs_f64() / 1e9
}

fn fresh_u32(n: usize) -> Vec<u32> {
    let mut v: Vec<u32> = Vec::with_capacity(n);
    #[allow(clippy::uninit_vec)]
    unsafe {
        v.set_len(n)
    };
    v
}

fn fresh_e4(n: usize) -> Vec<E4> {
    let mut v: Vec<E4> = Vec::with_capacity(n);
    #[allow(clippy::uninit_vec)]
    unsafe {
        v.set_len(n)
    };
    v
}

/// Sequential store pass over a u32 buffer (what an LDE output pass does to
/// a fresh page: one write per line, no read).
fn write_pass(v: &mut [u32], tag: u32) {
    for (i, x) in v.iter_mut().enumerate() {
        *x = (i as u32) ^ tag;
    }
}

fn read_pass(v: &[u32]) -> u64 {
    let mut acc = [0u64; 8];
    for ch in v.chunks_exact(8) {
        for k in 0..8 {
            acc[k] = acc[k].wrapping_add(ch[k] as u64);
        }
    }
    acc.iter().fold(0u64, |a, b| a.wrapping_add(*b))
}

// -------------------------------------------------------------------------
// mem: fault tax and bandwidth ceilings
// -------------------------------------------------------------------------

fn section_mem(n: usize, cols: usize, threads: usize) {
    println!(
        "\n== mem: page-fault tax and bandwidth ceilings (2^{} u32 buffers)",
        n.trailing_zeros()
    );
    let bufs = cols * 3; // what one base-commit part allocates: monomials + 2 cosets per column
    let bytes = bufs * n * 4;

    // 1. fresh allocation + first write (fault tax), parallel over buffers
    let t = Instant::now();
    let mut v: Vec<Vec<u32>> = (0..bufs).map(|_| fresh_u32(n)).collect();
    let t_alloc = t.elapsed();
    let t = Instant::now();
    {
        let ptrs: Vec<usize> = v.iter_mut().map(|b| b.as_mut_ptr() as usize).collect();
        par_for(bufs, threads, |i| unsafe {
            let s = core::slice::from_raw_parts_mut(ptrs[i] as *mut u32, n);
            write_pass(s, i as u32);
        });
    }
    let t_fault = t.elapsed();
    println!(
        "[mem] {bufs} fresh buffers ({:.2} GB): alloc {:.1?}, first-write (faults) {:.3?} = {:.1} GB/s at {threads} thr",
        bytes as f64 / 1e9,
        t_alloc,
        t_fault,
        gbs(bytes, t_fault)
    );

    // 2. second write pass over the now-faulted pages: write bandwidth
    let t = Instant::now();
    {
        let ptrs: Vec<usize> = v.iter_mut().map(|b| b.as_mut_ptr() as usize).collect();
        par_for(bufs, threads, |i| unsafe {
            let s = core::slice::from_raw_parts_mut(ptrs[i] as *mut u32, n);
            write_pass(s, !(i as u32));
        });
    }
    let t_write = t.elapsed();
    println!(
        "[mem] write pass (faulted): {:.3?} = {:.1} GB/s",
        t_write,
        gbs(bytes, t_write)
    );

    // 3. read pass
    let t = Instant::now();
    {
        let sum = AtomicUsize::new(0);
        par_for(bufs, threads, |i| {
            let s = read_pass(&v[i]);
            sum.fetch_add(s as usize, Ordering::Relaxed);
        });
        black_box(sum.load(Ordering::Relaxed));
    }
    let t_read = t.elapsed();
    println!(
        "[mem] read pass: {:.3?} = {:.1} GB/s",
        t_read,
        gbs(bytes, t_read)
    );

    // 4. copy pass (first half -> second half, both faulted)
    let half = bufs / 2;
    let t = Instant::now();
    {
        let (a, b) = v.split_at_mut(half);
        let srcs: Vec<usize> = a.iter().map(|x| x.as_ptr() as usize).collect();
        let dsts: Vec<usize> = b.iter_mut().map(|x| x.as_mut_ptr() as usize).collect();
        par_for(half, threads, |i| unsafe {
            let s = core::slice::from_raw_parts(srcs[i] as *const u32, n);
            let d = core::slice::from_raw_parts_mut(dsts[i] as *mut u32, n);
            d.copy_from_slice(s);
        });
    }
    let t_copy = t.elapsed();
    println!(
        "[mem] copy pass ({} buffers, read+write {:.2} GB): {:.3?} = {:.1} GB/s moved",
        half,
        (half * n * 4 * 2) as f64 / 1e9,
        t_copy,
        gbs(half * n * 4 * 2, t_copy)
    );

    // 5. copy into FRESH destinations (the `to_vec()` of the LDE phase 1)
    let t = Instant::now();
    {
        let srcs: Vec<usize> = v[..half].iter().map(|x| x.as_ptr() as usize).collect();
        let outs: Vec<std::sync::Mutex<Option<Vec<u32>>>> =
            (0..half).map(|_| std::sync::Mutex::new(None)).collect();
        par_for(half, threads, |i| unsafe {
            let s = core::slice::from_raw_parts(srcs[i] as *const u32, n);
            *outs[i].lock().unwrap() = Some(s.to_vec());
        });
        let t_fresh_copy = t.elapsed();
        println!(
            "[mem] to_vec into fresh buffers ({} x {:.0} MB): {:.3?} = {:.1} GB/s moved",
            half,
            (n * 4) as f64 / 1e6,
            t_fresh_copy,
            gbs(half * n * 4 * 2, t_fresh_copy)
        );
        let t = Instant::now();
        drop(outs);
        println!("[mem] drop of those {half} buffers: {:.3?}", t.elapsed());
    }

    // 6. single-thread fault + write reference on 8 buffers
    let k = 8.min(bufs);
    let t = Instant::now();
    let mut single: Vec<Vec<u32>> = (0..k).map(|_| fresh_u32(n)).collect();
    for (i, b) in single.iter_mut().enumerate() {
        write_pass(b, i as u32);
    }
    let t_s_fault = t.elapsed();
    let t = Instant::now();
    for (i, b) in single.iter_mut().enumerate() {
        write_pass(b, !(i as u32));
    }
    let t_s_write = t.elapsed();
    println!(
        "[mem] 1 thread, {k} buffers: first-write {:.3?} = {:.1} GB/s, re-write {:.3?} = {:.1} GB/s",
        t_s_fault,
        gbs(k * n * 4, t_s_fault),
        t_s_write,
        gbs(k * n * 4, t_s_write)
    );
    drop(single);

    let t = Instant::now();
    drop(v);
    println!("[mem] drop of the {bufs} buffers: {:.3?}", t.elapsed());
}

// -------------------------------------------------------------------------
// lde + tree: the base commitment part
// -------------------------------------------------------------------------

fn section_lde_tree(
    log2: usize,
    cols: usize,
    threads: usize,
    reps: usize,
    do_lde: bool,
    do_tree: bool,
    worker: &Worker,
) {
    let n = 1usize << log2;
    let lde = 2usize;
    println!("\n== lde/tree: base commitment part, {cols} cols 2^{log2}, lde {lde}, 2 values/leaf");
    let backend = DefaultBabyBearBackend::default();
    let tw = backend.make_twiddles(n * lde, worker);
    let pool = crate::allocation_pool::default_pool_for::<BB, E4>();
    let polys = random_base_polys(cols, n, threads, 0x5151);
    let refs: Vec<&[BB]> = polys.iter().map(|p| &p[..]).collect();

    let mut last = None;
    if do_lde {
        for rep in 0..reps {
            let t = Instant::now();
            let out = backend.lde_multiple_polys_from_hypercubes(&refs, &tw, lde, &*pool, worker);
            let d = t.elapsed();
            println!(
                "[lde] full lde_multiple_polys_from_hypercubes rep {rep}: {:.3?} ({:.1} ms/col, {:.1} GB/s of output)",
                d,
                d.as_secs_f64() * 1e3 / cols as f64,
                gbs(cols * lde * n * 4, d)
            );
            if rep == 0 {
                let t = Instant::now();
                drop(last.take());
                let _ = t;
            }
            last = Some(out);
        }

        // phase 1 alone: to_vec + NEON hypercube->monomial per column (as ws_lde does)
        {
            use worker::rayon::prelude::*;
            let t = Instant::now();
            let monomials: Vec<Vec<BB>> = worker.pool.install(|| {
                refs.par_iter()
                    .map(|col| {
                        let mut v = col.to_vec();
                        crate::gkr::whir::hypercube_to_monomial::multivariate_hypercube_evals_into_coeffs_neon_bb(&mut v, log2 as u32);
                        v
                    })
                    .collect()
            });
            let d1 = t.elapsed();
            println!(
                "[lde] phase 1 (to_vec + neon hypercube->monomial, fresh buffers): {:.3?} ({:.1} ms/col)",
                d1,
                d1.as_secs_f64() * 1e3 / cols as f64
            );
            // phase 1 into already-faulted buffers
            let mut monos2 = monomials.clone();
            let t = Instant::now();
            worker.pool.install(|| {
                monos2.par_iter_mut().zip(refs.par_iter()).for_each(|(dst, col)| {
                    dst.copy_from_slice(col);
                    crate::gkr::whir::hypercube_to_monomial::multivariate_hypercube_evals_into_coeffs_neon_bb(dst, log2 as u32);
                });
            });
            let d1b = t.elapsed();
            println!(
                "[lde] phase 1 into faulted buffers: {:.3?} ({:.1} ms/col) -> fault share {:.3?}",
                d1b,
                d1b.as_secs_f64() * 1e3 / cols as f64,
                d1.saturating_sub(d1b)
            );
            // the transform alone (in place, warm)
            let t = Instant::now();
            worker.pool.install(|| {
                monos2.par_iter_mut().for_each(|dst| {
                    crate::gkr::whir::hypercube_to_monomial::multivariate_hypercube_evals_into_coeffs_neon_bb(dst, log2 as u32);
                });
            });
            let d1c = t.elapsed();
            println!(
                "[lde] phase 1 transform only (in place): {:.3?} ({:.1} ms/col)",
                d1c,
                d1c.as_secs_f64() * 1e3 / cols as f64
            );
            drop(monos2);

            // phase 2 alone: 2*cols serial NEON coset tasks on the pool
            let next_root = fft::domain_generator_for_size::<BB>((n * lde) as u64);
            let root_powers = fft::materialize_powers_serial_starting_with_one::<
                BB,
                std::alloc::Global,
            >(next_root, lde);
            let plain_tw = &tw.plain.forward_twiddles[..];
            let ext = &tw.forward_ext;
            let t = Instant::now();
            let cosets: Vec<Vec<BB>> = worker.pool.install(|| {
                (0..lde * cols)
                    .into_par_iter()
                    .map(|task| {
                        let coset = task / cols;
                        let col = task % cols;
                        fft::baby_bear_neon::lde_coset_neon(
                            &monomials[col],
                            root_powers[coset],
                            plain_tw,
                            ext,
                        )
                    })
                    .collect()
            });
            let d2 = t.elapsed();
            println!(
                "[lde] phase 2 ({} serial neon coset tasks, fresh output each): {:.3?} ({:.1} ms/task)",
                lde * cols,
                d2,
                d2.as_secs_f64() * 1e3 / (lde * cols) as f64
            );
            let t = Instant::now();
            drop(cosets);
            println!("[lde] drop of phase-2 output: {:.3?}", t.elapsed());

            // phase 2 pieces, 1 thread, one column, warm
            let m0 = &monomials[0];
            let t = Instant::now();
            let one = fft::baby_bear_neon::lde_coset_neon(m0, root_powers[1], plain_tw, ext);
            let d_task = t.elapsed();
            let t = Instant::now();
            let mut f = fresh_u32(n);
            write_pass(&mut f, 7);
            let d_fault = t.elapsed();
            let mut br = one.clone();
            let t = Instant::now();
            fft::bitreverse_enumeration_inplace(&mut br);
            let d_br = t.elapsed();
            for q in [6u32, 7, 8, 9] {
                let mut b2 = one.clone();
                let t = Instant::now();
                fft::bitreverse_enumeration_inplace_blocked_q(&mut b2, q);
                let d = t.elapsed();
                black_box(&b2);
                let mut e2 = vec![E4::ZERO; n / 2];
                par_fill::<E4, 4>(&mut e2, 0x33, threads, |l| {
                    E4::from_array_of_base(l.map(BB::new))
                });
                let t = Instant::now();
                fft::bitreverse_enumeration_inplace_blocked_q(&mut e2, q);
                let d_e = t.elapsed();
                black_box(&e2);
                println!(
                    "[lde] blocked bit-reverse q={q}: 2^{log2} u32 {:.1?}, 2^{} ext4 {:.1?}",
                    d,
                    log2 - 1,
                    d_e
                );
            }
            {
                let mut e1 = vec![E4::ZERO; n / 2];
                par_fill::<E4, 4>(&mut e1, 0x33, threads, |l| {
                    E4::from_array_of_base(l.map(BB::new))
                });
                let t = Instant::now();
                fft::bitreverse_enumeration_inplace(&mut e1);
                println!(
                    "[lde] old bit-reverse 2^{} ext4 {:.1?}",
                    log2 - 1,
                    t.elapsed()
                );
            }
            let t = Instant::now();
            let one_warm = fft::baby_bear_neon::lde_coset_neon(m0, root_powers[1], plain_tw, ext);
            let d_task2 = t.elapsed();
            black_box(&one_warm);
            println!(
                "[lde] 1 thread, one coset task: {:.1?} / {:.1?} (two runs); of which fresh-buffer first write {:.1?}, scalar bit-reverse of 2^{log2} {:.1?}",
                d_task, d_task2, d_fault, d_br
            );
            drop(f);
            drop(br);
            drop(one);

            // phase 2 scaling: `threads` tasks at once vs 1
            let k = threads.min(cols);
            let t = Instant::now();
            let outs: Vec<Vec<BB>> = worker.pool.install(|| {
                (0..k)
                    .into_par_iter()
                    .map(|c| {
                        fft::baby_bear_neon::lde_coset_neon(
                            &monomials[c],
                            root_powers[1],
                            plain_tw,
                            ext,
                        )
                    })
                    .collect()
            });
            let d_k = t.elapsed();
            println!(
                "[lde] {k} coset tasks concurrently: {:.1?} wall = {:.2}x one serial task",
                d_k,
                d_k.as_secs_f64() / d_task2.as_secs_f64()
            );
            drop(outs);
            drop(monomials);
        }
    }

    if do_tree {
        let evals = match last.take() {
            Some(e) => e,
            None => backend.lde_multiple_polys_from_hypercubes(&refs, &tw, lde, &*pool, worker),
        };
        let src: Vec<Vec<&[BB]>> = evals
            .iter()
            .map(|coset| coset.iter().map(|c| c.as_contiguous().unwrap()).collect())
            .collect();
        let src_ref: Vec<&[&[BB]]> = src.iter().map(|c| &c[..]).collect();
        for rep in 0..reps {
            let t = Instant::now();
            let tree = DefaultTreeConstructor::construct_from_cosets::<BB, _>(
                &src_ref, 2, CAP, true, true, false, worker,
            );
            let d = t.elapsed();
            black_box(&tree);
            let leaves = lde * n / 2;
            let leaf_words = cols * 2;
            let blocks = leaf_words.div_ceil(BLAKE2S_BLOCK_SIZE_U32_WORDS);
            println!(
                "[tree] base tree rep {rep}: {:.3?} for {} leaves x {} words ({} blocks/leaf) = {:.1} ns/leaf/thread, {:.1} ns/compression/thread; reads {:.1} GB/s",
                d,
                leaves,
                leaf_words,
                blocks,
                d.as_secs_f64() * 1e9 * threads as f64 / leaves as f64,
                d.as_secs_f64() * 1e9 * threads as f64 / (leaves * blocks) as f64,
                gbs(cols * lde * n * 4, d)
            );
        }
        blake_reference(threads);
    }
}

/// Blake2s compression throughput of this machine (reduced rounds, as the
/// default tree): one chain per thread, and 4 interleaved chains per thread.
fn blake_reference(threads: usize) {
    const N: usize = 1 << 20;
    let block = [0x1234_5678u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
    let t = Instant::now();
    par_for(threads, threads, |_| {
        let mut h = Blake2sState::new();
        for _ in 0..N {
            h.absorb::<true>(&block);
        }
        black_box(&h);
    });
    let d1 = t.elapsed();
    let t = Instant::now();
    par_for(threads, threads, |_| {
        let mut h = [Blake2sState::new(); 4];
        for _ in 0..N / 4 {
            for w in 0..4 {
                h[w].absorb::<true>(&block);
            }
        }
        black_box(&h);
    });
    let d4 = t.elapsed();
    let t = Instant::now();
    par_for(threads, threads, |_| unsafe {
        use blake2s_u32::vectorized_impls::neon_x4::Blake2sNeonX4;
        let words = [0x1234_5678u32; 64];
        let m = Blake2sNeonX4::load_block(words.as_ptr());
        let mut h = Blake2sNeonX4::new();
        for _ in 0..N / 4 {
            h.absorb::<true>(&m);
        }
        black_box(&h);
    });
    let dx4 = t.elapsed();
    println!(
        "[blake] {threads} thr, {N} compressions each: 1 chain {:.1} ns/compression, 4 interleaved chains {:.1} ns/compression, NEON x4 lanes {:.1} ns/compression (per thread)",
        d1.as_secs_f64() * 1e9 / N as f64,
        d4.as_secs_f64() * 1e9 / N as f64,
        dx4.as_secs_f64() * 1e9 / N as f64
    );
}

// -------------------------------------------------------------------------
// whir: intermediate oracle LDE + fused-conversion tree
// -------------------------------------------------------------------------

fn section_whir(poly_log2: usize, lde: usize, threads: usize, reps: usize, worker: &Worker) {
    let n = 1usize << poly_log2;
    let vpl = 32usize;
    println!("\n== whir: intermediate oracle poly 2^{poly_log2} x lde {lde} (2^{} ext values), {vpl} values/leaf", poly_log2 + lde.trailing_zeros() as usize);
    let backend = DefaultBabyBearBackend::default();
    let tw = backend.make_twiddles(n * lde, worker);
    let pool = crate::allocation_pool::default_pool_for::<BB, E4>();
    let mono = random_ext_poly(n, threads, 0x7171);

    let mut built = None;
    for rep in 0..reps {
        let t = Instant::now();
        let (buffer, offsets) =
            backend.lde_ext_poly_from_monomial_form_continuous(&mono, &tw, lde, &*pool, worker);
        let d = t.elapsed();
        println!(
            "[whir] continuous ext LDE rep {rep}: {:.3?} ({:.1} GB/s of output)",
            d,
            gbs(n * lde * 16, d)
        );
        built = Some((buffer, offsets));
    }
    let (buffer, offsets) = built.unwrap();
    let total_bytes = n * lde * 16;

    // production: fused conversion-at-hash-time tree over leaf accessors
    let conv = backend.ext_coeff_conv(n, vpl);
    for rep in 0..reps {
        let t = Instant::now();
        let leaves: Vec<[_; 1]> = buffer
            .chunks(n)
            .zip(offsets.iter())
            .map(|(c, o)| [backend.coset_leaves(&conv, c, *o)])
            .collect();
        let leaves_ref: Vec<&[_]> = leaves.iter().map(|l| &l[..]).collect();
        let tree = DefaultTreeConstructor::construct_from_leaf_accessors::<E4, _>(
            &leaves_ref,
            CAP,
            true,
            false,
            worker,
        );
        let d = t.elapsed();
        black_box(&tree);
        println!(
            "[whir] fused tree (convert while hashing) rep {rep}: {:.3?} ({:.1} GB/s of codeword)",
            d,
            gbs(total_bytes, d)
        );
    }

    // plain tree over the evaluation-form cosets (no conversion): gather + hash only
    {
        let src: Vec<Vec<&[E4]>> = buffer.chunks(n).map(|c| vec![c]).collect();
        let src_ref: Vec<&[&[E4]]> = src.iter().map(|c| &c[..]).collect();
        let t = Instant::now();
        let tree = DefaultTreeConstructor::construct_from_cosets::<E4, _>(
            &src_ref, vpl, CAP, true, true, false, worker,
        );
        let d = t.elapsed();
        black_box(&tree);
        let leaves = n * lde / vpl;
        let blocks = (vpl * 4).div_ceil(BLAKE2S_BLOCK_SIZE_U32_WORDS);
        println!(
            "[whir] plain tree (no conversion): {:.3?} ({:.1} GB/s; {} leaves x {} blocks = {:.1} ns/compression/thread)",
            d,
            gbs(total_bytes, d),
            leaves,
            blocks,
            d.as_secs_f64() * 1e9 * threads as f64 / (leaves * blocks) as f64
        );
    }

    // conversion alone: in-place leaves->coefficients on a copy of the codeword
    {
        use worker::rayon::prelude::*;
        let mut copy = buffer.to_vec();
        let t = Instant::now();
        worker.pool.install(|| {
            copy.par_chunks_mut(n)
                .zip(offsets.par_iter())
                .for_each(|(c, o)| conv.apply_serial(c, *o));
        });
        let d = t.elapsed();
        black_box(&copy);
        println!(
            "[whir] conversion alone (in place, per-coset serial, {} cosets on the pool): {:.3?} ({:.1} GB/s)",
            lde,
            d,
            gbs(total_bytes, d)
        );
        // then the plain tree over converted data == the non-fused path total
    }

    let t = Instant::now();
    drop(buffer);
    println!("[whir] drop of the codeword: {:.3?}", t.elapsed());
}

// -------------------------------------------------------------------------
// fwd: forward-layer relation archetypes
// -------------------------------------------------------------------------

fn section_fwd(log2: usize, threads: usize, reps: usize) {
    let n = 1usize << log2;
    println!("\n== fwd: forward-layer relation archetypes at 2^{log2} rows, {threads} thr");

    // archetype A: AggregateLookupRationalPair  (a/b + c/d) -> (a*d + c*b, b*d)
    let a = random_ext_poly(n, threads, 0xA1);
    let b = random_ext_poly(n, threads, 0xB2);
    let c = random_ext_poly(n, threads, 0xC3);
    let d = random_ext_poly(n, threads, 0xD4);
    let bytes_a = n * 16 * 6;

    let kernel = |i: usize| -> [E4; 2] {
        let (a, b, c, d) = (a[i], b[i], c[i], d[i]);
        let mut num = a;
        num.mul_assign(&d);
        let mut cb = c;
        cb.mul_assign(&b);
        num.add_assign(&cb);
        let mut den = b;
        den.mul_assign(&d);
        [num, den]
    };

    for rep in 0..reps {
        // fresh outputs (production: pool miss -> fresh buffer)
        let t = Instant::now();
        let mut o0 = fresh_e4(n);
        let mut o1 = fresh_e4(n);
        {
            let p0 = o0.as_mut_ptr() as usize;
            let p1 = o1.as_mut_ptr() as usize;
            par_rows(n, threads, |s, e| unsafe {
                let o0 = p0 as *mut E4;
                let o1 = p1 as *mut E4;
                for i in s..e {
                    let [x, y] = kernel(i);
                    o0.add(i).write(x);
                    o1.add(i).write(y);
                }
            });
        }
        let d_fresh = t.elapsed();
        // pre-faulted outputs
        let t = Instant::now();
        {
            let p0 = o0.as_mut_ptr() as usize;
            let p1 = o1.as_mut_ptr() as usize;
            par_rows(n, threads, |s, e| unsafe {
                let o0 = p0 as *mut E4;
                let o1 = p1 as *mut E4;
                for i in s..e {
                    let [x, y] = kernel(i);
                    o0.add(i).write(x);
                    o1.add(i).write(y);
                }
            });
        }
        let d_warm = t.elapsed();
        black_box(&o0);
        black_box(&o1);
        // compute only (no output stores)
        let t = Instant::now();
        {
            let acc = AtomicUsize::new(0);
            par_rows(n, threads, |s, e| {
                let mut x = E4::ZERO;
                for i in s..e {
                    let [p, q] = kernel(i);
                    x.add_assign(&p);
                    x.add_assign(&q);
                }
                acc.fetch_add(
                    crate::utils::extension_field_into_base_coeffs::<BB, E4>(x).as_ref()[0]
                        .as_u32_reduced() as usize,
                    Ordering::Relaxed,
                );
            });
            black_box(acc.load(Ordering::Relaxed));
        }
        let d_comp = t.elapsed();
        println!(
            "[fwd] A rational pair (4 ext in, 2 ext out, 3 ext mul) rep {rep}: fresh out {:.1?}, faulted out {:.1?}, compute only {:.1?}; {:.1} GB/s moved (faulted), {:.2} ns/row/thread",
            d_fresh,
            d_warm,
            d_comp,
            gbs(bytes_a, d_warm),
            d_warm.as_secs_f64() * 1e9 * threads as f64 / n as f64
        );
        drop(o0);
        drop(o1);
    }
    drop((a, b, c, d));

    // archetype B: base columns -> one ext column, out = gamma + sum c_i * col_i (K base cols)
    const K: usize = 12;
    let cols = random_base_polys(K, n, threads, 0xBEEF);
    let mut st = 0x99u64;
    let ch: [E4; K] = core::array::from_fn(|_| {
        E4::from_array_of_base(core::array::from_fn(|_| {
            BB::new((splitmix(&mut st) % P) as u32)
        }))
    });
    let gamma = E4::from_array_of_base(core::array::from_fn(|_| {
        BB::new((splitmix(&mut st) % P) as u32)
    }));
    let bytes_b = n * (K * 4 + 16);
    let kernel_b = |i: usize| -> E4 {
        let mut r = gamma;
        for k in 0..K {
            let mut t = ch[k];
            t.mul_assign_by_base(&cols[k][i]);
            r.add_assign(&t);
        }
        r
    };
    for rep in 0..reps {
        let t = Instant::now();
        let mut o = fresh_e4(n);
        {
            let p = o.as_mut_ptr() as usize;
            par_rows(n, threads, |s, e| unsafe {
                let o = p as *mut E4;
                for i in s..e {
                    o.add(i).write(kernel_b(i));
                }
            });
        }
        let d_fresh = t.elapsed();
        let t = Instant::now();
        {
            let p = o.as_mut_ptr() as usize;
            par_rows(n, threads, |s, e| unsafe {
                let o = p as *mut E4;
                for i in s..e {
                    o.add(i).write(kernel_b(i));
                }
            });
        }
        let d_warm = t.elapsed();
        black_box(&o);
        let t = Instant::now();
        {
            let acc = AtomicUsize::new(0);
            par_rows(n, threads, |s, e| {
                let mut x = E4::ZERO;
                for i in s..e {
                    x.add_assign(&kernel_b(i));
                }
                acc.fetch_add(
                    crate::utils::extension_field_into_base_coeffs::<BB, E4>(x).as_ref()[0]
                        .as_u32_reduced() as usize,
                    Ordering::Relaxed,
                );
            });
            black_box(acc.load(Ordering::Relaxed));
        }
        let d_comp = t.elapsed();
        println!(
            "[fwd] B {K} base cols -> 1 ext (ext*base MLAs) rep {rep}: fresh out {:.1?}, faulted out {:.1?}, compute only {:.1?}; {:.1} GB/s moved (faulted), {:.2} ns/row/thread",
            d_fresh,
            d_warm,
            d_comp,
            gbs(bytes_b, d_warm),
            d_warm.as_secs_f64() * 1e9 * threads as f64 / n as f64
        );
        drop(o);
    }

    // archetype C: pure streaming ext copy (the bandwidth floor of a 1-in-1-out ext relation)
    let src = random_ext_poly(n, threads, 0xCC);
    let t = Instant::now();
    let mut dst = fresh_e4(n);
    {
        let p = dst.as_mut_ptr() as usize;
        let s = &src;
        par_rows(n, threads, |a, b| unsafe {
            let o = p as *mut E4;
            core::ptr::copy_nonoverlapping(s.as_ptr().add(a), o.add(a), b - a);
        });
    }
    let d_fresh = t.elapsed();
    let t = Instant::now();
    {
        let p = dst.as_mut_ptr() as usize;
        let s = &src;
        par_rows(n, threads, |a, b| unsafe {
            let o = p as *mut E4;
            core::ptr::copy_nonoverlapping(s.as_ptr().add(a), o.add(a), b - a);
        });
    }
    let d_warm = t.elapsed();
    black_box(&dst);
    println!(
        "[fwd] C ext copy (1 in, 1 out): fresh out {:.1?}, faulted out {:.1?} = {:.1} GB/s moved",
        d_fresh,
        d_warm,
        gbs(n * 32, d_warm)
    );
}

#[test]
#[ignore]
fn stage_probe() {
    let log2 = env_usize("STAGE_LOG2", 23);
    let threads = env_usize("STAGE_THREADS", 8);
    let cols = env_usize("STAGE_COLS", 61);
    let reps = env_usize("STAGE_REPS", 2).max(1);
    let sections =
        std::env::var("STAGE_SECTIONS").unwrap_or_else(|_| "mem,lde,tree,whir,fwd".into());
    let has = |s: &str| sections.split(',').any(|x| x.trim() == s);
    let worker = Worker::new_with_num_threads(threads);
    println!("stage probe: 2^{log2}, {threads} threads, {cols} cols, sections {sections}");

    if has("mem") {
        section_mem(1 << log2, cols, threads);
    }
    if has("lde") || has("tree") {
        section_lde_tree(log2, cols, threads, reps, has("lde"), has("tree"), &worker);
    }
    if has("whir") {
        // oracle 0 of the 2^23 unified run: poly 2^22 x 16; oracle 1: 2^17 x 512
        section_whir(log2 - 1, 16, threads, reps, &worker);
        section_whir(log2 - 6, 512, threads, reps, &worker);
    }
    if has("fwd") {
        section_fwd(log2, threads, reps);
    }
}
