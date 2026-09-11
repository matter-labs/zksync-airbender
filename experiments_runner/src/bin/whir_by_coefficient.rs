//! WHIR intermediate-oracle experiment, round 2: the Ext4 WHIR polynomial
//! stored as FOUR base-field columns (by-coefficient), LDE'd with the base
//! commitment's kernels and buffers from the AllocationPool, against the
//! current Ext4 monomial-form LDE; the per-round non-LDE work (sumcheck
//! three-point evaluations, evaluation/eq/monomial-form folds, eq-poly
//! update, OOD evaluation, PoW) measured on the same shapes; and the
//! "LDE straight from hypercube evaluations" alternative (no monomial form
//! kept). Runs as `outer` pinned `inner`-thread workers at once (default
//! 12 x 16, CCX pinning), every worker on its own random data and its own
//! retaining pool; all workers start a variant together (barrier).
//!
//! Shapes are `log_n:lde` of the intermediate oracles of the add/sub 2^24
//! proof: 23:16, 18:512, 13:16384 (every codeword is 2^27 elements).
//! `--only <substring>` restricts the variants.
#![feature(allocator_api)]

#[cfg(not(all(target_arch = "x86_64", target_feature = "avx2")))]
fn main() {
    eprintln!("x86-64 + avx2 only");
}

#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
fn main() {
    use field::baby_bear::base::BabyBearField as F;
    use field::baby_bear::ext4::BabyBearExt4 as E;
    use field::{Field, PrimeField};
    use prover::allocation_pool::x86_64_baby_bear::PADDED_GEOMETRY;
    use prover::allocation_pool::{
        AllocationPool, Buffer, ColumnLayout, DefaultBabyBearAllocationPool,
    };
    use prover::gkr::prover::backend::ExtCoeffConversion;
    use prover::gkr::prover::{Backend, DefaultBabyBearBackend};
    use prover::gkr::whir::{
        evaluate_monomial_form, evaluate_multivariate, fold_eq_poly, fold_evaluation_form,
        fold_monomial_form, special_three_point_eval,
    };
    use prover::merkle_trees::{ColumnMajorMerkleTreeConstructor, DefaultTreeConstructor};
    type TR = prover::transcript::Blake2sTranscript;
    use std::sync::{Arc, Barrier};
    use std::time::Instant;
    use worker::Worker;

    let args: Vec<String> = std::env::args().collect();
    let mut shapes: Vec<(u32, usize)> = vec![(23, 16), (18, 512), (13, 16384)];
    let mut outer = 12usize;
    let mut inner = 16usize;
    let mut reps = 2usize;
    let mut pin = true;
    let mut only: Option<String> = None;
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--shapes" => {
                shapes = args[i + 1]
                    .split(',')
                    .map(|s| {
                        let (a, b) = s.split_once(':').unwrap();
                        (a.parse().unwrap(), b.parse().unwrap())
                    })
                    .collect()
            }
            "--outer" => outer = args[i + 1].parse().unwrap(),
            "--inner" => inner = args[i + 1].parse().unwrap(),
            "--reps" => reps = args[i + 1].parse().unwrap(),
            "--only" => only = Some(args[i + 1].clone()),
            "--no-pin" => {
                pin = false;
                i -= 1;
            }
            other => panic!("unknown arg {other}"),
        }
        i += 2;
    }
    const POOL_STACK: usize = 256 << 20;
    println!(
        "[whir2] outer={outer} x inner={inner} threads, pin={pin}, reps={reps}, shapes={shapes:?}"
    );

    // CCX-aligned CPU blocks, as in the outer proof benchmark
    let cpu_blocks: Vec<Vec<usize>> = if pin {
        let complexes = Worker::cpu_complexes();
        let flat: Vec<usize> = if complexes.is_empty() {
            (0..std::thread::available_parallelism()
                .map(|n| n.get())
                .unwrap_or(1))
                .collect()
        } else {
            complexes.iter().flatten().copied().collect()
        };
        assert!(
            outer * inner <= flat.len(),
            "need {} CPUs, host lists {}",
            outer * inner,
            flat.len()
        );
        (0..outer)
            .map(|i| flat[i * inner..(i + 1) * inner].to_vec())
            .collect()
    } else {
        Vec::new()
    };

    let backend = DefaultBabyBearBackend::default();
    let strided = backend.uses_strided();
    println!(
        "[whir2] backend: {} base LDE",
        if strided { "AVX-512 strided" } else { "AVX2" }
    );

    /// The strided AVX-512 base LDE of the x86 backend, on `lde_factor` cosets
    /// of 2^24 (the 2^23 polynomial zero-padded to 2^24 coefficients: the same
    /// 2^27-point codeword as 16 cosets of 2^23, grouped as 8 cosets of 2^24),
    /// into pooled block-padded buffers. Returns the outputs (the caller gives
    /// them back after timing).
    fn strided_lde_cols(
        cols: &[Vec<F>],
        tw: &<DefaultBabyBearBackend as Backend<F, E>>::TwiddleSet,
        lde_factor: usize,
        pool: &dyn AllocationPool<F, E>,
        worker: &Worker,
    ) -> Vec<Buffer<F>> {
        use fft::baby_bear_avx512::{
            out_len, strided_gather_pass_into, strided_global_phase,
            transform_partial_chunked_into, StridedCfg,
        };
        const LOG_N: u32 = 24;
        const CHUNK_STRIDE: usize = (1 << (LOG_N - 4)) + 1088;
        let n = 1usize << LOG_N;
        let geo = PADDED_GEOMETRY;
        let cfg = StridedCfg {
            stream: true,
            r256: true,
            out_block_stride: geo.stride(),
            group: 1,
            prefetch: false,
            blk_log2: geo.block_log2,
        };
        assert_eq!(
            out_len(LOG_N, cfg.blk_log2, cfg.out_block_stride),
            geo.padded_len(n)
        );
        let root = fft::domain_generator_for_size::<F>((n * lde_factor) as u64);
        let offsets: Vec<F> = fft::materialize_powers_serial_starting_with_one::<
            F,
            std::alloc::Global,
        >(root, lde_factor);
        let tw_f = &tw.plain.forward_twiddles[..];
        let tw_raw: &[u32] =
            unsafe { core::slice::from_raw_parts(tw_f.as_ptr() as *const u32, tw_f.len()) };
        let ext = &tw.forward_ext;
        let mut part = pool.alloc_base(n, ColumnLayout::PaddedBlocks(geo));
        assert_eq!(part.as_ptr() as usize % 64, 0);
        let part_len = 16 * CHUNK_STRIDE;
        let part_ptr = part.as_mut_ptr() as *mut u32;
        let mut outs = Vec::with_capacity(cols.len() * lde_factor);
        for col in cols.iter() {
            assert_eq!(col.len(), n);
            let col_raw: &[u32] =
                unsafe { core::slice::from_raw_parts(col.as_ptr() as *const u32, n) };
            unsafe {
                let part_mut = core::slice::from_raw_parts_mut(part_ptr, part_len);
                transform_partial_chunked_into(
                    col_raw,
                    part_mut,
                    LOG_N,
                    LOG_N - 4,
                    CHUNK_STRIDE,
                    true,
                    worker,
                );
            }
            let part_ref: &[u32] = unsafe { core::slice::from_raw_parts(part_ptr, part_len) };
            for &offset in offsets.iter() {
                let mut out = pool.alloc_base(n, ColumnLayout::PaddedBlocks(geo));
                assert_eq!(out.as_ptr() as usize % 64, 0);
                let out_u32: &mut [u32] = unsafe {
                    core::slice::from_raw_parts_mut(out.as_mut_ptr() as *mut u32, out.len())
                };
                unsafe {
                    strided_gather_pass_into(
                        part_ref,
                        CHUNK_STRIDE,
                        LOG_N,
                        offset,
                        tw_raw,
                        &ext.ao,
                        &ext.bo,
                        out_u32,
                        worker,
                        cfg,
                    );
                    strided_global_phase(out_u32, LOG_N, tw_raw, &ext.ao, &ext.bo, worker, cfg);
                }
                for b in 0..(n >> geo.block_log2) {
                    let g = b * geo.stride() + geo.block();
                    out_u32[g..g + geo.pad].fill(0);
                }
                outs.push(out);
            }
        }
        pool.give_base(part);
        outs
    }

    fn release_parts(
        parts: Vec<
            Vec<
                prover::gkr::prover::stages::commitment_utils::ColumnMajorCosetBoundTracePart<F, F>,
            >,
        >,
        pool: &dyn AllocationPool<F, E>,
    ) {
        for coset in parts {
            for p in coset {
                if let Ok(a) = Arc::try_unwrap(p.column) {
                    a.release_base(pool);
                }
            }
        }
    }

    fn rand_e(k: usize, w: usize, salt: u32) -> E {
        let s = (k as u32).wrapping_mul(2654435761) ^ (w as u32).wrapping_mul(0x9E3779B9) ^ salt;
        E {
            c0: field::baby_bear::ext2::BabyBearExt2 {
                c0: F::from_u32_with_reduction(s),
                c1: F::from_u32_with_reduction(s.wrapping_mul(3) ^ 0x1234567),
            },
            c1: field::baby_bear::ext2::BabyBearExt2 {
                c0: F::from_u32_with_reduction(s.wrapping_mul(5) ^ 0x7654321),
                c1: F::from_u32_with_reduction(s.wrapping_mul(7) ^ 0xabcdef),
            },
        }
    }

    struct Inputs {
        poly: Vec<E>,        // monomial form, Ext4
        cols: Vec<Vec<F>>,   // its 4 coefficient columns
        padded: Vec<Vec<F>>, // the columns zero-padded to 2^24 (log_n == 23 only)
        evals: Vec<Vec<F>>,  // hypercube evals as 4 base columns (random)
        dup: Vec<Vec<F>>,    // evals duplicated to 2^24 (log_n == 23 only)
        ev_ext: Vec<E>,      // evaluation form, Ext4 (sumcheck input)
        eq: Vec<E>,          // eq poly
        ood_samples: Vec<(E, E)>,
        in_domain: Vec<(F, E)>,
        cw_ext: Vec<E>, // a codeword-sized Ext4 buffer (tree variants; values irrelevant)
        cw_cols: Vec<Vec<F>>, // the same as 4 base columns
        offsets: Vec<F>, // coset offsets of the codeword
    }

    for &(log_n, lde) in &shapes {
        let n = 1usize << log_n;
        let domain = n * lde;
        let steps = if log_n == 23 {
            5
        } else {
            5.min(log_n as usize)
        };
        println!(
            "[whir2] ===== poly 2^{log_n} Ext4, lde {lde} (codeword 2^{}), {:.2} GB per worker per LDE =====",
            domain.trailing_zeros(),
            (domain * 16) as f64 / 1e9
        );
        let setup_worker = Worker::new_with_num_threads(outer * inner);
        let twiddles = Arc::new(<DefaultBabyBearBackend as Backend<F, E>>::make_twiddles(
            &backend,
            domain.max(1 << 25),
            &setup_worker,
        ));
        let queries = match log_n {
            23 => 87,
            18 => 23,
            13 => 10,
            _ => 8,
        };
        let mut inputs: Vec<Inputs> = (0..outer)
            .map(|w| {
                let poly: Vec<E> = (0..n).map(|k| rand_e(k, w, 0)).collect();
                let cols: Vec<Vec<F>> = vec![
                    poly.iter().map(|e| e.c0.c0).collect(),
                    poly.iter().map(|e| e.c0.c1).collect(),
                    poly.iter().map(|e| e.c1.c0).collect(),
                    poly.iter().map(|e| e.c1.c1).collect(),
                ];
                let evals: Vec<Vec<F>> = (0..4)
                    .map(|c| {
                        (0..n)
                            .map(|k| {
                                F::from_u32_with_reduction(
                                    (k as u32 ^ (c * 0x5bd1e995)).wrapping_mul(2246822519)
                                        ^ w as u32,
                                )
                            })
                            .collect()
                    })
                    .collect();
                let (padded, dup) = if log_n == 23 {
                    (
                        cols.iter()
                            .map(|c| {
                                let mut v = c.clone();
                                v.resize(1 << 24, F::ZERO);
                                v
                            })
                            .collect(),
                        evals
                            .iter()
                            .map(|c| {
                                let mut v = c.clone();
                                v.extend_from_slice(c);
                                v
                            })
                            .collect(),
                    )
                } else {
                    (Vec::new(), Vec::new())
                };
                let ev_ext: Vec<E> = (0..n).map(|k| rand_e(k, w, 0x1111)).collect();
                let eq: Vec<E> = (0..n).map(|k| rand_e(k, w, 0x2222)).collect();
                let ood_samples = vec![(rand_e(1, w, 0x3333), rand_e(2, w, 0x4444))];
                let in_domain: Vec<(F, E)> = (0..queries)
                    .map(|q| {
                        (
                            F::from_u32_with_reduction(q as u32 * 7919 + 13),
                            rand_e(q, w, 0x5555),
                        )
                    })
                    .collect();
                let cw_ext: Vec<E> = (0..domain).map(|k| rand_e(k, w, 0x8888)).collect();
                let cw_cols: Vec<Vec<F>> = (0..4)
                    .map(|c| {
                        (0..domain)
                            .map(|k| {
                                F::from_u32_with_reduction(
                                    (k as u32).wrapping_mul(0x9E3779B1)
                                        ^ (c * 0x85EBCA6B)
                                        ^ w as u32,
                                )
                            })
                            .collect()
                    })
                    .collect();
                let root = fft::domain_generator_for_size::<F>(domain as u64);
                let offsets: Vec<F> = fft::materialize_powers_serial_starting_with_one::<
                    F,
                    std::alloc::Global,
                >(root, lde);
                Inputs {
                    poly,
                    cols,
                    padded,
                    evals,
                    dup,
                    ev_ext,
                    eq,
                    ood_samples,
                    in_domain,
                    cw_ext,
                    cw_cols,
                    offsets,
                }
            })
            .collect();
        drop(setup_worker);
        let pools: Vec<DefaultBabyBearAllocationPool> = (0..outer)
            .map(|_| DefaultBabyBearAllocationPool::new())
            .collect();

        let mut variants: Vec<&str> = vec![
            "lde: ext4 continuous (current)",
            "lde: 4 base cols, backend base LDE (planner)",
            "lde: 4 base cols from hypercube evals (backend)",
            "conv: hypercube->coeffs x4 cols",
            "sumcheck: round loop (3pt eval + eval fold + eq fold), 5 steps",
            "sumcheck: three-point evals only, 5 steps",
            "fold: evaluation form, 5 steps",
            "fold: eq poly, 5 steps",
            "fold: monomial form, 5 steps",
            "eq: update_eq_poly (1 ood + queries)",
            "eq: split_eq_tensors, all samples sequential (as today)",
            "eq: split_eq_tensors, all samples in one parallel loop",
            "ood: evaluate_monomial_form at folded size",
            "ood: evaluate_multivariate at folded size",
            "tree: ext4 leaf coeff-conversion (all cosets)",
            "tree: hashing only, ext4 codeword",
            "tree: hashing only, 4 base cols",
        ];
        if log_n >= 20 {
            variants.insert(2, "lde: 4 base cols, blocked all-thr avx2");
        }
        if log_n == 23 && strided {
            variants.insert(3, "lde: 4 base cols zero-padded 2^24, strided x8 (pooled)");
            variants.insert(
                4,
                "lde: 4 base cols hypercube dup'd 2^24, strided (backend)",
            );
        }
        if log_n == 23 {
            variants.push("pow: 28 bits");
            variants.push("pow: 24 bits");
        }
        for variant in variants {
            if let Some(f) = &only {
                if !variant.contains(f.as_str()) {
                    continue;
                }
            }
            let barrier = Arc::new(Barrier::new(outer));
            let times: Vec<Vec<f64>> = std::thread::scope(|s| {
                let handles: Vec<_> = inputs
                    .iter_mut()
                    .zip(pools.iter())
                    .enumerate()
                    .map(|(w, (inp, pool))| {
                        let (barrier, twiddles, cpu_blocks, backend) =
                            (barrier.clone(), twiddles.clone(), &cpu_blocks, &backend);
                        std::thread::Builder::new()
                            .name(format!("whir2-{w}"))
                            .stack_size(1 << 30)
                            .spawn_scoped(s, move || {
                                let worker = if pin {
                                    Worker::new_with_num_threads_on_cpus_and_stack(inner, &cpu_blocks[w], POOL_STACK)
                                } else {
                                    Worker::new_with_num_threads_and_stack(inner, POOL_STACK)
                                };
                                let pool: &dyn AllocationPool<F, E> = pool;
                                worker.pool.install(|| {
                                    let mut ts = Vec::new();
                                    for _ in 0..reps + 1 {
                                        // mutable copies for the folding variants, made outside the timing
                                        let needs_copies = variant.starts_with("sumcheck") || variant.starts_with("fold") || variant.starts_with("eq:");
                                        let (mut ev, mut eq, mut mono) = if needs_copies {
                                            (inp.ev_ext.clone(), inp.eq.clone(), inp.poly.clone())
                                        } else {
                                            (Vec::new(), Vec::new(), Vec::new())
                                        };
                                        let mut mono_buf: Vec<E> = Vec::with_capacity(mono.len() / 2);
                                        let challenges: Vec<E> = (0..steps).map(|k| rand_e(k, w, 0x6666)).collect();
                                        let cols_ref: Vec<&[F]> = inp.evals.iter().map(|c| &c[..]).collect();
                                        let dup_ref: Vec<&[F]> = inp.dup.iter().map(|c| &c[..]).collect();
                                        let seed = TR::commit_initial(&[w as u32, 7, 11, 13]);
                                        barrier.wait();
                                        let t0 = Instant::now();
                                        match variant {
                                            "lde: ext4 continuous (current)" => {
                                                let out = backend.lde_ext_poly_from_monomial_form_continuous(&inp.poly, &twiddles, lde, pool, &worker);
                                                std::hint::black_box(&out);
                                                drop(out);
                                            }
                                            "lde: 4 base cols, backend base LDE (planner)" => {
                                                for c in inp.cols.iter() {
                                                    let out = backend.lde_base_poly_from_monomial_form(c, &twiddles, lde, pool, &worker);
                                                    std::hint::black_box(&out);
                                                    drop(out);
                                                }
                                            }
                                            "lde: 4 base cols, blocked all-thr avx2" => {
                                                let root = fft::domain_generator_for_size::<F>(domain as u64);
                                                let offsets: Vec<F> = fft::materialize_powers_serial_starting_with_one::<F, std::alloc::Global>(root, lde);
                                                let mut outs: Vec<Vec<F>> = Vec::with_capacity(4 * lde);
                                                for c in inp.cols.iter() {
                                                    for &off in offsets.iter() {
                                                        outs.push(fft::baby_bear_avx2::lde_coset_avx2_parallel(c, off, &twiddles.plain.forward_twiddles, &twiddles.forward_ext, &worker));
                                                    }
                                                }
                                                std::hint::black_box(&outs);
                                                drop(outs);
                                            }
                                            "lde: 4 base cols zero-padded 2^24, strided x8 (pooled)" => {
                                                let outs = strided_lde_cols(&inp.padded, &twiddles, lde / 2, pool, &worker);
                                                std::hint::black_box(&outs);
                                                let t = t0.elapsed().as_secs_f64();
                                                for o in outs { pool.give_base(o); }
                                                ts.push(t);
                                                continue;
                                            }
                                            "lde: 4 base cols hypercube dup'd 2^24, strided (backend)" => {
                                                let parts = backend.lde_multiple_polys_from_hypercubes(&dup_ref, &twiddles, lde / 2, pool, &worker);
                                                std::hint::black_box(&parts);
                                                let t = t0.elapsed().as_secs_f64();
                                                release_parts(parts, pool);
                                                ts.push(t);
                                                continue;
                                            }
                                            "lde: 4 base cols from hypercube evals (backend)" => {
                                                let parts = backend.lde_multiple_polys_from_hypercubes(&cols_ref, &twiddles, lde, pool, &worker);
                                                std::hint::black_box(&parts);
                                                let t = t0.elapsed().as_secs_f64();
                                                release_parts(parts, pool);
                                                ts.push(t);
                                                continue;
                                            }
                                            "conv: hypercube->coeffs x4 cols" => {
                                                for c in inp.evals.iter() {
                                                    let out = prover::gkr::whir::hypercube_to_monomial::multivariate_hypercube_evals_into_coeffs_avx2_bb_parallel(c, log_n, &worker);
                                                    std::hint::black_box(&out);
                                                    drop(out);
                                                }
                                            }
                                            "sumcheck: round loop (3pt eval + eval fold + eq fold), 5 steps" => {
                                                let mut ev_s: &mut [E] = &mut ev[..];
                                                let mut eq_s: &mut [E] = &mut eq[..];
                                                for ch in challenges.iter() {
                                                    let r = special_three_point_eval::<F, E>(ev_s, eq_s, &worker);
                                                    std::hint::black_box(r);
                                                    ev_s = fold_evaluation_form::<F, E>(ev_s, ch, &worker);
                                                    eq_s = fold_eq_poly::<F, E>(eq_s, ch, &worker);
                                                }
                                            }
                                            "sumcheck: three-point evals only, 5 steps" => {
                                                let mut len = n;
                                                for _ in 0..steps {
                                                    let r = special_three_point_eval::<F, E>(&inp.ev_ext[..len], &inp.eq[..len], &worker);
                                                    std::hint::black_box(r);
                                                    len /= 2;
                                                }
                                            }
                                            "fold: evaluation form, 5 steps" => {
                                                let mut ev_s: &mut [E] = &mut ev[..];
                                                for ch in challenges.iter() {
                                                    ev_s = fold_evaluation_form::<F, E>(ev_s, ch, &worker);
                                                }
                                                std::hint::black_box(&ev_s);
                                            }
                                            "fold: eq poly, 5 steps" => {
                                                let mut eq_s: &mut [E] = &mut eq[..];
                                                for ch in challenges.iter() {
                                                    eq_s = fold_eq_poly::<F, E>(eq_s, ch, &worker);
                                                }
                                                std::hint::black_box(&eq_s);
                                            }
                                            "fold: monomial form, 5 steps" => {
                                                for ch in challenges.iter() {
                                                    fold_monomial_form(&mut mono, &mut mono_buf, ch, &worker);
                                                }
                                                std::hint::black_box(&mono);
                                            }
                                            "eq: update_eq_poly (1 ood + queries)" => {
                                                backend.update_eq_poly(&mut eq[..], &inp.ood_samples, &inp.in_domain, &worker);
                                                std::hint::black_box(&eq);
                                            }
                                            "eq: split_eq_tensors, all samples sequential (as today)" => {
                                                use prover::gkr::sumcheck::eq_poly::split_eq_tensors;
                                                let log_c = core::cmp::min(10, log_n as usize - 1).max(1);
                                                let mut acc = 0usize;
                                                for (pt, _) in inp.ood_samples.iter() {
                                                    let (hi, lo) = split_eq_tensors::<E>(*pt, log_n as usize, log_c, &worker);
                                                    acc += hi.len() + lo.len();
                                                }
                                                for (pt, _) in inp.in_domain.iter() {
                                                    let (hi, lo) = split_eq_tensors::<F>(*pt, log_n as usize, log_c, &worker);
                                                    acc += hi.len() + lo.len();
                                                }
                                                std::hint::black_box(acc);
                                            }
                                            "eq: split_eq_tensors, all samples in one parallel loop" => {
                                                use prover::gkr::sumcheck::eq_poly::split_eq_tensors;
                                                use worker::rayon::prelude::*;
                                                let log_c = core::cmp::min(10, log_n as usize - 1).max(1);
                                                let solo = Worker::new_with_num_threads(1);
                                                let tensors: Vec<usize> = inp
                                                    .in_domain
                                                    .par_iter()
                                                    .map(|(pt, _)| {
                                                        let (hi, lo) = split_eq_tensors::<F>(*pt, log_n as usize, log_c, &solo);
                                                        hi.len() + lo.len()
                                                    })
                                                    .collect();
                                                let (hi, lo) = split_eq_tensors::<E>(inp.ood_samples[0].0, log_n as usize, log_c, &worker);
                                                std::hint::black_box((tensors, hi.len(), lo.len()));
                                            }
                                            "ood: evaluate_monomial_form at folded size" => {
                                                let m = n >> steps;
                                                let v = evaluate_monomial_form(&inp.poly[..m], &inp.ood_samples[0].0, &worker);
                                                std::hint::black_box(v);
                                            }
                                            "ood: evaluate_multivariate at folded size" => {
                                                let m = n >> steps;
                                                let point: Vec<E> = (0..(log_n as usize - steps)).map(|k| rand_e(k, w, 0x7777)).collect();
                                                let v = evaluate_multivariate(&inp.ev_ext[..m], &point, &worker);
                                                std::hint::black_box(v);
                                            }
                                            "tree: ext4 leaf coeff-conversion (all cosets)" => {
                                                let conv = backend.ext_coeff_conv(n, 32);
                                                let cw = &mut inp.cw_ext[..];
                                                if lde >= worker.get_num_cores() {
                                                    use worker::rayon::prelude::*;
                                                    cw.par_chunks_mut(n)
                                                        .zip(inp.offsets.par_iter())
                                                        .for_each(|(column, offset)| conv.apply_serial(column, *offset));
                                                } else {
                                                    for (column, offset) in cw.chunks_mut(n).zip(inp.offsets.iter()) {
                                                        conv.apply(column, *offset, &worker);
                                                    }
                                                }
                                                std::hint::black_box(&cw);
                                            }
                                            "tree: hashing only, ext4 codeword" => {
                                                let source: Vec<Vec<&[E]>> = inp.cw_ext.chunks(n).map(|c| vec![c]).collect();
                                                let source_ref: Vec<&[&[E]]> = source.iter().map(|el| &el[..]).collect();
                                                let tree = DefaultTreeConstructor::construct_from_cosets::<E, _>(&source_ref[..], 32, 32, true, true, false, &worker);
                                                std::hint::black_box(&tree);
                                                drop(tree);
                                            }
                                            "tree: hashing only, 4 base cols" => {
                                                let source: Vec<Vec<&[F]>> = (0..lde)
                                                    .map(|c| inp.cw_cols.iter().map(|col| &col[c * n..(c + 1) * n]).collect())
                                                    .collect();
                                                let source_ref: Vec<&[&[F]]> = source.iter().map(|el| &el[..]).collect();
                                                let tree = DefaultTreeConstructor::construct_from_cosets::<F, _>(&source_ref[..], 32, 32, true, true, false, &worker);
                                                std::hint::black_box(&tree);
                                                drop(tree);
                                            }
                                            "pow: 28 bits" | "pow: 24 bits" => {
                                                let bits = if variant.ends_with("28 bits") { 28 } else { 24 };
                                                let r = <TR as prover::transcript::Transcript<F, E>>::search_pow(&seed, bits, &worker);
                                                std::hint::black_box(r);
                                            }
                                            other => panic!("unknown variant {other}"),
                                        }
                                        ts.push(t0.elapsed().as_secs_f64());
                                    }
                                    ts
                                })
                            })
                            .unwrap()
                    })
                    .collect();
                handles.into_iter().map(|h| h.join().unwrap()).collect()
            });
            // per rep (skipping the warm-up), the batch time is the slowest worker
            let mut batch: Vec<f64> = Vec::new();
            let mut per_worker: Vec<f64> = Vec::new();
            for r in 1..reps + 1 {
                let rep_times: Vec<f64> = times.iter().map(|t| t[r]).collect();
                batch.push(rep_times.iter().cloned().fold(0.0, f64::max));
                per_worker.extend(rep_times);
            }
            batch.sort_by(|a, b| a.partial_cmp(b).unwrap());
            let mean = per_worker.iter().sum::<f64>() / per_worker.len() as f64;
            let min = per_worker.iter().cloned().fold(f64::MAX, f64::min);
            println!(
                "[whir2] 2^{log_n} x lde {lde} | {variant:<58} | batch (slowest worker) best {:8.1} ms median {:8.1} ms | per-worker min {:8.1} mean {:8.1} ms",
                batch[0] * 1e3,
                batch[batch.len() / 2] * 1e3,
                min * 1e3,
                mean * 1e3
            );
        }
        for p in pools.iter() {
            let s = p.stats();
            let _ = s;
        }
        println!(
            "[whir2] pool retained per worker: {:.1} MB",
            pools[0].stats().retained_bytes as f64 / 1e6
        );
    }
    println!("[whir2] done");
}
