//! Base-commit pipeline comparison on the AVX-512 experiment. Variants:
//! (a) the current AVX2 pipeline (parallel transform + per-coset blocked LDE);
//! (b) AVX-512 transform + AVX-512 blocked LDE with the separate prep sweep;
//! (c) AVX-512 transform + the FUSED gather kernel (16-block groups, block
//!     phase in cache, 3 DRAM sweeps per coset);
//! (d) (b) and (c) again on page-aligned buffers, (c) also with non-temporal
//!     (`_mm512_stream_si512`) copy-out stores;
//! (e) the STRIDED pipeline: partial transform (low 20 variables, per 2^20
//!     chunk), then per coset the strided pass (transform completion + coset
//!     scaling + first four DIF stages with chain-generated twiddles + register
//!     transpose, 16 sequential read streams, full-line non-temporal writes),
//!     block-local stages and the radix-16 global sweeps; and its gather
//!     variant (strided pass fused with the block-local stages).
//! 48 columns x 2 cosets of 2^24 hypercube evals per worker; single worker and
//! pinned batch modes. All outputs are verified equal to the AVX2 pipeline.
#![feature(allocator_api)]

#[cfg(not(all(target_arch = "x86_64", target_feature = "avx2")))]
fn main() {
    eprintln!("x86-64 + avx2 only");
}

#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
fn main() {
    use fft::baby_bear_avx2::{lde_coset_avx2_parallel, Avx2TwiddleExt};
    use fft::column_major::baby_bear_avx512::{
        lde_coset_avx512_fused, lde_coset_avx512_fused_into, lde_coset_avx512_into,
        lde_coset_avx512_parallel, lde_coset_avx512_r256_into, lde_coset_strided_into, out_len,
        strided_gather_pass_into, strided_global_phase, transform_avx512, transform_avx512_into,
        transform_partial_chunked_into, AlignedU32, StridedCfg, OUT_BLOCK_STRIDE_PADDED,
    };
    use field::baby_bear::base::BabyBearField as F;
    use field::PrimeField;
    use prover::gkr::whir::hypercube_to_monomial::multivariate_hypercube_evals_into_coeffs_avx2_bb_parallel as transform_avx2;
    use std::alloc::Global;
    use std::sync::{Arc, Barrier};
    use std::time::Instant;
    use worker::Worker;

    const LOG_N: u32 = 24;
    const N: usize = 1 << LOG_N;
    /// Chunk stride of the partially transformed monomials: 2^20 plus 4352 B
    /// so the 16 read streams of the strided pass hit distinct L1/L2 sets.
    const CHUNK_STRIDE: usize = (1 << (LOG_N - 4)) + 1088;

    #[derive(Clone, Copy, PartialEq)]
    enum V {
        Avx2,
        Sep,
        Fused,
        SepAligned,
        SepAlignedR256,
        FusedAligned { stream: bool },
        Strided { chunk_local: bool, cfg: StridedCfg },
        Gather { cfg: StridedCfg },
    }
    const fn cfg(
        stream: bool,
        r256: bool,
        padded: bool,
        group: usize,
        prefetch: bool,
    ) -> StridedCfg {
        StridedCfg {
            stream,
            r256,
            out_block_stride: if padded {
                OUT_BLOCK_STRIDE_PADDED
            } else {
                1 << 16
            },
            group,
            prefetch,
            blk_log2: 16,
        }
    }
    const fn cfg14(padded: bool, prefetch: bool) -> StridedCfg {
        StridedCfg {
            stream: true,
            r256: true,
            out_block_stride: (1 << 14) + if padded { 64 } else { 0 },
            group: 1,
            prefetch,
            blk_log2: 14,
        }
    }
    let variants: Vec<(&str, V)> = vec![
        ("AVX2 current", V::Avx2),
        ("AVX-512 transform + separate prep", V::Sep),
        ("AVX-512 transform + fused prep/blocks", V::Fused),
        ("aligned: AVX-512 transform + separate prep", V::SepAligned),
        (
            "aligned: fused, plain copy-out",
            V::FusedAligned { stream: false },
        ),
        (
            "aligned: fused, NT copy-out",
            V::FusedAligned { stream: true },
        ),
        (
            "strided: 2-sweep partial transform, NT",
            V::Strided {
                chunk_local: false,
                cfg: cfg(true, false, false, 1, false),
            },
        ),
        (
            "strided: chunk-local partial transform, NT",
            V::Strided {
                chunk_local: true,
                cfg: cfg(true, false, false, 1, false),
            },
        ),
        (
            "strided: chunk-local partial transform, plain",
            V::Strided {
                chunk_local: true,
                cfg: cfg(false, false, false, 1, false),
            },
        ),
        (
            "strided gather: chunk-local, NT",
            V::Gather {
                cfg: cfg(true, false, false, 1, false),
            },
        ),
        ("r256: aligned separate prep, NT", V::SepAlignedR256),
        (
            "r256: strided chunk-local, NT",
            V::Strided {
                chunk_local: true,
                cfg: cfg(true, true, false, 1, false),
            },
        ),
        (
            "r256: strided gather chunk-local, NT",
            V::Gather {
                cfg: cfg(true, true, false, 1, false),
            },
        ),
        (
            "r256pad: strided gather, G=1, no prefetch",
            V::Gather {
                cfg: cfg(true, true, true, 1, false),
            },
        ),
        (
            "r256pad: strided gather, G=1, prefetch",
            V::Gather {
                cfg: cfg(true, true, true, 1, true),
            },
        ),
        (
            "r256pad: strided gather, G=4, no prefetch",
            V::Gather {
                cfg: cfg(true, true, true, 4, false),
            },
        ),
        (
            "r256pad: strided gather, G=4, prefetch",
            V::Gather {
                cfg: cfg(true, true, true, 4, true),
            },
        ),
        (
            "r256pad: strided chunk-local, G=4, prefetch",
            V::Strided {
                chunk_local: true,
                cfg: cfg(true, true, true, 4, true),
            },
        ),
        (
            "r1024: gather blk 2^14, padded, NT, no prefetch",
            V::Gather {
                cfg: cfg14(true, false),
            },
        ),
        (
            "r1024: gather blk 2^14, padded, NT, prefetch",
            V::Gather {
                cfg: cfg14(true, true),
            },
        ),
        (
            "r1024: gather blk 2^14, contiguous, NT, no prefetch",
            V::Gather {
                cfg: cfg14(false, false),
            },
        ),
        (
            "r1024: gather blk 2^14, contiguous, NT, prefetch",
            V::Gather {
                cfg: cfg14(false, true),
            },
        ),
    ];

    let args: Vec<String> = std::env::args().collect();
    let (mut outer, mut inner, mut cols, mut reps, mut pin) =
        (12usize, 16usize, 48usize, 3usize, true);
    let mut only: Vec<String> = Vec::new();
    let mut pooled = false;
    let mut modes: Vec<String> = vec!["solo".into(), "batch".into()];
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--outer" => outer = args[i + 1].parse().unwrap(),
            "--inner" => inner = args[i + 1].parse().unwrap(),
            "--cols" => cols = args[i + 1].parse().unwrap(),
            "--reps" => reps = args[i + 1].parse().unwrap(),
            // variant names contain commas: `;`-separated substrings
            "--only" => only = args[i + 1].split(';').map(|s| s.to_string()).collect(),
            "--modes" => modes = args[i + 1].split(',').map(|s| s.to_string()).collect(),
            "--no-pin" => {
                pin = false;
                i -= 1;
            }
            "--pool" => {
                pooled = true;
                i -= 1;
            }
            other => panic!("unknown arg {other}"),
        }
        i += 2;
    }
    let selected: Vec<(&str, V)> = variants
        .iter()
        .cloned()
        .filter(|(name, _)| only.is_empty() || only.iter().any(|o| name.contains(o.as_str())))
        .collect();
    assert!(
        is_x86_feature_detected!("avx512f"),
        "no avx512f on this host"
    );
    const POOL_STACK: usize = 256 << 20;
    let lde = 2usize;
    println!(
        "[fused] outer={outer} x inner={inner}, cols={cols}, lde={lde}, reps={reps}, pin={pin}, pool={pooled}, variants={:?}",
        selected.iter().map(|(n, _)| *n).collect::<Vec<_>>()
    );
    let cpu_blocks: Vec<Vec<usize>> = if pin {
        let flat: Vec<usize> = Worker::cpu_complexes().iter().flatten().copied().collect();
        assert!(outer * inner <= flat.len());
        (0..outer)
            .map(|w| flat[w * inner..(w + 1) * inner].to_vec())
            .collect()
    } else {
        Vec::new()
    };
    let setup_worker = Worker::new_with_num_threads(outer * inner);
    let tw: Vec<F, Global> = fft::precompute_all_twiddles_for_fft_serial::<F, Global, false>(N);
    let ext = Avx2TwiddleExt::build_parallel(&tw, N, &setup_worker);
    let root = fft::domain_generator_for_size::<F>((N * lde) as u64);
    let offsets: Vec<F> = fft::materialize_powers_serial_starting_with_one::<F, Global>(root, lde);
    drop(setup_worker);
    let (tw, ext, offsets) = (Arc::new(tw), Arc::new(ext), Arc::new(offsets));
    let inputs: Vec<Vec<Vec<F>>> = (0..outer)
        .map(|w| {
            (0..cols)
                .map(|c| {
                    (0..N)
                        .map(|k| {
                            F::from_u32_with_reduction(
                                (k as u32).wrapping_mul(2654435761)
                                    ^ ((w * cols + c) as u32).wrapping_mul(0x9E3779B9),
                            )
                        })
                        .collect()
                })
                .collect()
        })
        .collect();

    /// Buffer source: fresh allocations (the real pipeline's per-proof
    /// behaviour, page faults included) or a per-worker pool that recycles the
    /// previous rep's buffers (steady state of a pooling prover).
    struct Pool {
        pooled: bool,
        als: std::collections::HashMap<usize, Vec<AlignedU32>>,
    }
    impl Pool {
        fn take(&mut self, len: usize) -> AlignedU32 {
            self.als
                .get_mut(&len)
                .and_then(|v| v.pop())
                .unwrap_or_else(|| AlignedU32::uninit(len))
        }
        fn give(&mut self, a: AlignedU32) {
            if self.pooled {
                self.als.entry(a.len()).or_default().push(a);
            }
        }
    }

    // One column of a variant: transform + `lde` cosets. Outputs are kept
    // alive (Vec or aligned) so allocation costs match the real pipeline.
    fn run_column(
        v: V,
        col: &[F],
        offsets: &[F],
        tw: &[F],
        ext: &Avx2TwiddleExt,
        worker: &Worker,
        outs_vec: &mut Vec<Vec<F>>,
        outs_al: &mut Vec<AlignedU32>,
        phases: &mut [f64; 3],
        pool: &mut Pool,
    ) {
        let n = col.len();
        let log_n = n.trailing_zeros();
        let col_raw: &[u32] = unsafe { core::slice::from_raw_parts(col.as_ptr() as *const u32, n) };
        let tw_raw: &[u32] =
            unsafe { core::slice::from_raw_parts(tw.as_ptr() as *const u32, tw.len()) };
        match v {
            V::Avx2 => {
                let mono = transform_avx2(col, log_n, worker);
                for &off in offsets {
                    outs_vec.push(lde_coset_avx2_parallel(&mono, off, tw, ext, worker));
                }
            }
            V::Sep | V::Fused => {
                let mono: Vec<F> = unsafe {
                    core::mem::transmute::<Vec<u32>, Vec<F>>(transform_avx512(
                        col_raw, log_n, worker,
                    ))
                };
                for &off in offsets {
                    outs_vec.push(if v == V::Sep {
                        unsafe { lde_coset_avx512_parallel(&mono, off, tw, ext, worker) }
                    } else {
                        unsafe { lde_coset_avx512_fused(&mono, off, tw, ext, worker) }
                    });
                }
            }
            V::SepAligned | V::SepAlignedR256 | V::FusedAligned { .. } => {
                let mut mono = pool.take(n);
                unsafe { transform_avx512_into(col_raw, &mut mono, log_n, worker) };
                for &off in offsets {
                    let mut out = pool.take(n);
                    match v {
                        V::SepAligned => unsafe {
                            lde_coset_avx512_into(&mono, off, tw_raw, ext, &mut out, worker)
                        },
                        V::SepAlignedR256 => unsafe {
                            lde_coset_avx512_r256_into(
                                &mono, off, tw_raw, ext, &mut out, worker, true,
                            )
                        },
                        V::FusedAligned { stream } => unsafe {
                            lde_coset_avx512_fused_into(
                                &mono, off, tw_raw, ext, &mut out, worker, stream,
                            )
                        },
                        _ => unreachable!(),
                    }
                    outs_al.push(out);
                }
                pool.give(mono);
            }
            V::Strided { .. } | V::Gather { .. } => {
                let (chunk_local, cfg) = match v {
                    V::Strided { chunk_local, cfg } => (chunk_local, cfg),
                    V::Gather { cfg } => (true, cfg),
                    _ => unreachable!(),
                };
                let mut part = pool.take(16 * CHUNK_STRIDE);
                let t0 = Instant::now();
                unsafe {
                    transform_partial_chunked_into(
                        col_raw,
                        &mut part,
                        log_n,
                        log_n - 4,
                        CHUNK_STRIDE,
                        chunk_local,
                        worker,
                    )
                };
                phases[0] += t0.elapsed().as_secs_f64();
                for &off in offsets {
                    let mut out = pool.take(out_len(log_n, cfg.blk_log2, cfg.out_block_stride));
                    if matches!(v, V::Gather { .. }) {
                        let t1 = Instant::now();
                        unsafe {
                            strided_gather_pass_into(
                                &part,
                                CHUNK_STRIDE,
                                log_n,
                                off,
                                tw_raw,
                                &ext.ao,
                                &ext.bo,
                                &mut out,
                                worker,
                                cfg,
                            )
                        };
                        phases[1] += t1.elapsed().as_secs_f64();
                        let t2 = Instant::now();
                        unsafe {
                            strided_global_phase(
                                &mut out, log_n, tw_raw, &ext.ao, &ext.bo, worker, cfg,
                            )
                        };
                        phases[2] += t2.elapsed().as_secs_f64();
                    } else {
                        unsafe {
                            lde_coset_strided_into(
                                &part,
                                CHUNK_STRIDE,
                                log_n,
                                off,
                                tw_raw,
                                &ext.ao,
                                &ext.bo,
                                &mut out,
                                worker,
                                cfg,
                            )
                        }
                    }
                    outs_al.push(out);
                }
                pool.give(part);
            }
        }
    }

    {
        let w = Worker::new_with_num_threads(inner);
        let col = &inputs[0][0];
        let mut reference: Vec<Vec<F>> = Vec::new();
        let mut unused = Vec::new();
        let mut ph = [0.0f64; 3];
        let mut pool = Pool {
            pooled: false,
            als: Default::default(),
        };
        run_column(
            V::Avx2,
            col,
            &offsets,
            &tw,
            &ext,
            &w,
            &mut reference,
            &mut unused,
            &mut ph,
            &mut pool,
        );
        for (name, v) in selected.iter() {
            if *v == V::Avx2 {
                continue;
            }
            let (mut ov, mut oa) = (Vec::new(), Vec::new());
            run_column(
                *v, col, &offsets, &tw, &ext, &w, &mut ov, &mut oa, &mut ph, &mut pool,
            );
            for (ci, r) in reference.iter().enumerate() {
                let r_raw: &[u32] =
                    unsafe { core::slice::from_raw_parts(r.as_ptr() as *const u32, N) };
                let got: &[u32] = if ov.is_empty() {
                    &oa[ci][..]
                } else {
                    unsafe { core::slice::from_raw_parts(ov[ci].as_ptr() as *const u32, N) }
                };
                // padded outputs: block `b` (of 2^blk_log2) at `b * stride`
                let blk_log2 = match v {
                    V::Strided { cfg, .. } | V::Gather { cfg } => cfg.blk_log2,
                    _ => 16,
                };
                let nb = N >> blk_log2;
                let stride = got.len() / nb;
                let mut first = None;
                let mut count = 0usize;
                for b in 0..nb {
                    let (g, r) = (
                        &got[b * stride..b * stride + (1 << blk_log2)],
                        &r_raw[b << blk_log2..(b + 1) << blk_log2],
                    );
                    for (i, (x, y)) in g.iter().zip(r).enumerate() {
                        if x != y {
                            count += 1;
                            first.get_or_insert((b << 16) + i);
                        }
                    }
                }
                if let Some(first) = first {
                    panic!(
                        "variant `{name}` diverged at coset {ci}: first mismatch at {first} (block {}, line {}), {count} mismatches",
                        first >> blk_log2,
                        (first >> 4) & ((1 << (blk_log2 - 4)) - 1)
                    );
                }
            }
        }
        println!(
            "[fused] correctness: {} variants == AVX2 pipeline on {} cosets",
            selected.len(),
            offsets.len()
        );
    }

    let solo_label = format!("{inner}x1");
    let batch_label = format!("{inner}x{outer}");
    for (name, v) in selected.iter() {
        for mode_name in modes.iter() {
            let (mode, active) = match mode_name.as_str() {
                "solo" => (solo_label.as_str(), 1),
                "batch" => (batch_label.as_str(), outer),
                other => panic!("unknown mode {other}"),
            };
            let barrier = Arc::new(Barrier::new(active));
            let results: Vec<(f64, [f64; 3])> = std::thread::scope(|s| {
                let handles: Vec<_> = (0..active)
                    .map(|w| {
                        let (barrier, tw, ext, offsets, cpu_blocks, inputs) = (
                            barrier.clone(),
                            tw.clone(),
                            ext.clone(),
                            offsets.clone(),
                            &cpu_blocks,
                            &inputs,
                        );
                        let v = *v;
                        std::thread::Builder::new()
                            .stack_size(1 << 30)
                            .spawn_scoped(s, move || {
                                let worker = if pin {
                                    Worker::new_with_num_threads_on_cpus_and_stack(
                                        inner,
                                        &cpu_blocks[w],
                                        POOL_STACK,
                                    )
                                } else {
                                    Worker::new_with_num_threads_and_stack(inner, POOL_STACK)
                                };
                                worker.pool.install(|| {
                                    let mut best = f64::MAX;
                                    let mut best_ph = [0.0f64; 3];
                                    let mut pool = Pool {
                                        pooled,
                                        als: Default::default(),
                                    };
                                    for _ in 0..reps {
                                        barrier.wait();
                                        let t0 = Instant::now();
                                        let mut ph = [0.0f64; 3];
                                        let mut outs_vec: Vec<Vec<F>> =
                                            Vec::with_capacity(cols * lde);
                                        let mut outs_al: Vec<AlignedU32> =
                                            Vec::with_capacity(cols * lde);
                                        for col in inputs[w].iter() {
                                            run_column(
                                                v,
                                                col,
                                                &offsets,
                                                &tw,
                                                &ext,
                                                &worker,
                                                &mut outs_vec,
                                                &mut outs_al,
                                                &mut ph,
                                                &mut pool,
                                            );
                                        }
                                        let el = t0.elapsed().as_secs_f64();
                                        if el < best {
                                            best = el;
                                            best_ph = ph;
                                        }
                                        std::hint::black_box(&outs_vec);
                                        std::hint::black_box(&outs_al);
                                        drop(outs_vec);
                                        for a in outs_al {
                                            pool.give(a);
                                        }
                                    }
                                    (best, best_ph)
                                })
                            })
                            .unwrap()
                    })
                    .collect();
                handles.into_iter().map(|h| h.join().unwrap()).collect()
            });
            let times: Vec<f64> = results.iter().map(|r| r.0).collect();
            let slowest = times.iter().cloned().fold(0.0, f64::max);
            let mean = times.iter().sum::<f64>() / times.len() as f64;
            let tag = if pooled { " [pooled]" } else { "" };
            println!("[fused] {name:<46} {mode:<6} ({active:2} workers){tag}: slowest {slowest:.3} s, mean {mean:.3} s | {:.2} ms per column (transform + 2 cosets) per worker", 1e3 * mean / cols as f64);
            if matches!(v, V::Gather { .. }) {
                let ph: Vec<f64> = (0..3)
                    .map(|i| results.iter().map(|r| r.1[i]).sum::<f64>() / results.len() as f64)
                    .collect();
                println!(
                    "[phases] {name:<46} {mode:<6}: per column transform {:.2} ms, gather pass {:.2} ms (x2 cosets), global pass {:.2} ms (x2 cosets), other {:.2} ms",
                    1e3 * ph[0] / cols as f64,
                    1e3 * ph[1] / cols as f64,
                    1e3 * ph[2] / cols as f64,
                    1e3 * (mean - ph[0] - ph[1] - ph[2]) / cols as f64
                );
            }
        }
    }
    println!("[fused] done");
}
