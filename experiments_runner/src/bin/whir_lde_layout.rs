//! WHIR intermediate-oracle storage experiment: ONE Ext4 monomial-form LDE
//! (continuous storage, as WHIR does today) versus the SAME polynomial LDE'd as
//! its FOUR base-field coefficient columns (by-coefficient storage: the packed
//! per-coset column-major path, or four single base LDEs), with identical
//! size and LDE factor, run as `outer` pinned `inner`-thread workers at once
//! (default 12 x 16 across both sockets, CCX pinning from the L3 topology).
//! Every worker LDEs its own random polynomial; all workers start a variant
//! together (barrier) so the batch is measured under full contention.
#![feature(allocator_api)]

use prover::allocation_pool::GenericAllocationPool;
#[cfg(not(all(target_arch = "x86_64", target_feature = "avx2")))]
fn main() {
    eprintln!("x86-64 + avx2 only");
}

#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
fn main() {
    use field::baby_bear::base::BabyBearField as F;
    use field::baby_bear::ext4::BabyBearExt4 as E;
    use field::PrimeField;
    use prover::gkr::prover::{Backend, DefaultBabyBearBackend};
    use std::sync::{Arc, Barrier};
    use std::time::Instant;
    use worker::Worker;

    let args: Vec<String> = std::env::args().collect();
    let mut shapes: Vec<(u32, usize)> = vec![(22, 128), (23, 16)];
    let mut outer = 12usize;
    let mut inner = 16usize;
    let mut reps = 2usize;
    let mut pin = true;
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
        "[layout] outer={outer} x inner={inner} threads, pin={pin}, reps={reps}, shapes={shapes:?}"
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
    for &(log_n, lde) in &shapes {
        let n = 1usize << log_n;
        println!(
            "[layout] ===== poly 2^{log_n} Ext4, lde {lde}: output {:.2} GB per worker per variant =====",
            (n * lde * 16) as f64 / 1e9
        );
        let setup_worker = Worker::new_with_num_threads(outer * inner);
        let twiddles = Arc::new(<DefaultBabyBearBackend as Backend<F, E>>::make_twiddles(
            &backend,
            n,
            &setup_worker,
        ));
        drop(setup_worker);

        // per-worker inputs: one random Ext4 polynomial + its 4 coefficient columns
        let inputs: Vec<(Vec<E>, Vec<Vec<F>>)> = (0..outer)
            .map(|w| {
                let poly: Vec<E> = (0..n)
                    .map(|k| {
                        let s = (k as u32).wrapping_mul(2654435761) ^ (w as u32 * 0x9E3779B9);
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
                    })
                    .collect();
                let cols: Vec<Vec<F>> = vec![
                    poly.iter().map(|e| e.c0.c0).collect(),
                    poly.iter().map(|e| e.c0.c1).collect(),
                    poly.iter().map(|e| e.c1.c0).collect(),
                    poly.iter().map(|e| e.c1.c1).collect(),
                ];
                (poly, cols)
            })
            .collect();

        // coset offsets exactly as the backend enumerates them
        let root = fft::domain_generator_for_size::<F>((n * lde) as u64);
        let offsets: Vec<F> =
            fft::materialize_powers_serial_starting_with_one::<F, std::alloc::Global>(root, lde);
        let offsets = &offsets;
        for variant in [
            "ext4 continuous",
            "base packed (4 cols)",
            "base single x4",
            "base blocked x4 (all thr)",
        ] {
            let barrier = Arc::new(Barrier::new(outer));
            let t_all = Instant::now();
            let times: Vec<Vec<f64>> = std::thread::scope(|s| {
                let handles: Vec<_> = inputs
                    .iter()
                    .enumerate()
                    .map(|(w, (poly, cols))| {
                        let (barrier, twiddles, cpu_blocks, backend) =
                            (barrier.clone(), twiddles.clone(), &cpu_blocks, &backend);
                        std::thread::Builder::new()
                            .name(format!("lde-{w}"))
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
                                    let mut ts = Vec::new();
                                    for _ in 0..reps + 1 {
                                        // inputs the packed path consumes by value: prepare outside the timing
                                        let cols_owned: Vec<Vec<F>> =
                                            if variant == "base packed (4 cols)" {
                                                cols.clone()
                                            } else {
                                                Vec::new()
                                            };
                                        barrier.wait();
                                        let t0 = Instant::now();
                                        match variant {
                                            "ext4 continuous" => {
                                                let out = backend
                                                    .lde_ext_poly_from_monomial_form_continuous(
                                                        poly, &twiddles, lde, &GenericAllocationPool::proxy(), &worker,
                                                    );
                                                std::hint::black_box(&out);
                                                drop(out);
                                            }
                                            "base packed (4 cols)" => {
                                                let out = backend.lde_packed_monomials_into_cosets(
                                                    cols_owned, &twiddles, lde, &GenericAllocationPool::proxy(), &worker,
                                                );
                                                std::hint::black_box(&out);
                                                drop(out);
                                            }
                                            "base single x4" => {
                                                for c in cols.iter() {
                                                    let out = backend
                                                        .lde_base_poly_from_monomial_form(
                                                            c, &twiddles, lde, &GenericAllocationPool::proxy(), &worker,
                                                        );
                                                    std::hint::black_box(&out);
                                                    drop(out);
                                                }
                                            }
                                            _ => {
                                                // the base commit's path: every column-coset on all
                                                // threads through the blocked kernel
                                                let mut outs: Vec<Vec<F>> = Vec::with_capacity(4 * lde);
                                                for c in cols.iter() {
                                                    for &off in offsets.iter() {
                                                        outs.push(fft::baby_bear_avx2::lde_coset_avx2_parallel(
                                                            c,
                                                            off,
                                                            &twiddles.plain.forward_twiddles,
                                                            &twiddles.forward_ext,
                                                            &worker,
                                                        ));
                                                    }
                                                }
                                                std::hint::black_box(&outs);
                                                drop(outs);
                                            }
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
            let _ = t_all;
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
                "[layout] 2^{log_n} x lde {lde} | {variant:<22} | batch (slowest worker) best {:.3} s median {:.3} s | per-worker min {:.3} mean {:.3} s | {:.1} GB/s aggregate output write",
                batch[0],
                batch[batch.len() / 2],
                min,
                mean,
                (outer * n * lde * 16) as f64 / batch[0] / 1e9
            );
        }
    }
    println!("[layout] done");
}
