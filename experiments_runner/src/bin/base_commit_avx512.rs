//! AVX2 vs experimental AVX-512 blocked DIT LDE kernel on the base-commit
//! shape (48 columns x 2 cosets of 2^24 monomial-form base polys per
//! worker), in 16x1 (one 16-thread worker) and 16x12 (twelve CCX-pinned
//! workers, barrier-synchronized) modes. The AVX-512 kernel is verified
//! against the AVX2 one on both cosets before timing.
#![feature(allocator_api)]

#[cfg(not(all(target_arch = "x86_64", target_feature = "avx2")))]
fn main() {
    eprintln!("x86-64 + avx2 only");
}

#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
fn main() {
    use fft::baby_bear_avx2::{lde_coset_avx2_parallel, Avx2TwiddleExt};
    use fft::column_major::baby_bear_avx512::lde_coset_avx512_parallel;
    use field::baby_bear::base::BabyBearField as F;
    use field::PrimeField;
    use std::alloc::Global;
    use std::sync::{Arc, Barrier};
    use std::time::Instant;
    use worker::Worker;

    const LOG_N: u32 = 24;
    const N: usize = 1 << LOG_N;
    let args: Vec<String> = std::env::args().collect();
    let (mut outer, mut inner, mut cols, mut reps, mut pin) =
        (12usize, 16usize, 48usize, 3usize, true);
    let mut misalign = false;
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--outer" => outer = args[i + 1].parse().unwrap(),
            "--inner" => inner = args[i + 1].parse().unwrap(),
            "--cols" => cols = args[i + 1].parse().unwrap(),
            "--reps" => reps = args[i + 1].parse().unwrap(),
            "--no-pin" => {
                pin = false;
                i -= 1;
            }
            "--misalign" => {
                misalign = true;
                i -= 1;
            }
            other => panic!("unknown arg {other}"),
        }
        i += 2;
    }
    let have512 = is_x86_feature_detected!("avx512f");
    println!("[avx512] avx512f detected = {have512}; outer={outer} x inner={inner}, cols={cols}, lde=2, reps={reps}, pin={pin}");
    assert!(have512, "no avx512f on this host");
    const POOL_STACK: usize = 256 << 20;
    let lde = 2usize;
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

    {
        let w = Worker::new_with_num_threads(inner);
        let col = &inputs[0][0];
        for (ci, &off) in offsets.iter().enumerate() {
            let reference = lde_coset_avx2_parallel(col, off, &tw, &ext, &w);
            let got = unsafe { lde_coset_avx512_parallel(col, off, &tw, &ext, &w) };
            assert_eq!(got, reference, "AVX-512 kernel diverged at coset {ci}");
        }
        println!(
            "[avx512] correctness: AVX-512 kernel == AVX2 kernel on {} cosets",
            offsets.len()
        );

        if misalign {
            // NTT phases (prep excluded) of both kernels on a buffer whose base
            // sits k*4 bytes into a cache line: for AVX-512 every 64 B vector
            // straddles two lines unless k*4 % 64 == 0
            use fft::baby_bear_avx2::avx2 as k2;
            use fft::column_major::baby_bear_avx512 as k5;
            let tw_raw: &[u32] =
                unsafe { core::slice::from_raw_parts(tw.as_ptr() as *const u32, N / 2) };
            let col_raw: &[u32] =
                unsafe { core::slice::from_raw_parts(col.as_ptr() as *const u32, N) };
            let mut prepared = vec![0u32; N];
            fft::baby_bear_avx2::lde_prepare_bitrev_scaled_into(
                col_raw,
                &mut prepared,
                offsets[0],
                &w,
            );
            for k in [0usize, 4, 8, 12, 16] {
                let mut big = vec![0u32; N + 64];
                let base = (big.as_ptr() as usize + 4 * k) % 64;
                let mut t2 = Vec::new();
                let mut t5 = Vec::new();
                for _ in 0..3 {
                    big[k..k + N].copy_from_slice(&prepared);
                    let t0 = Instant::now();
                    unsafe {
                        k2::ntt_bitrev_to_natural_blocked_parallel(
                            &mut big[k..k + N],
                            LOG_N,
                            tw_raw,
                            &ext.ao,
                            &ext.bo,
                            &w,
                        )
                    };
                    t2.push(t0.elapsed().as_secs_f64() * 1e3);
                    big[k..k + N].copy_from_slice(&prepared);
                    let t0 = Instant::now();
                    unsafe {
                        k5::ntt_bitrev_to_natural_blocked_parallel(
                            &mut big[k..k + N],
                            LOG_N,
                            tw_raw,
                            &ext.ao,
                            &ext.bo,
                            &w,
                        )
                    };
                    t5.push(t0.elapsed().as_secs_f64() * 1e3);
                }
                let best = |v: &Vec<f64>| v.iter().cloned().fold(f64::MAX, f64::min);
                println!(
                    "[avx512] misalign: buffer base % 64 = {base:2} B: AVX2 NTT {:6.2} ms, AVX-512 NTT {:6.2} ms ({} threads)",
                    best(&t2),
                    best(&t5),
                    inner
                );
            }
        }
    }

    for variant in ["AVX2 blocked kernel", "AVX-512 blocked kernel"] {
        let solo_label = format!("{inner}x1");
        let batch_label = format!("{inner}x{outer}");
        for mode in [solo_label.as_str(), batch_label.as_str()] {
            let active = if mode == solo_label { 1 } else { outer };
            let barrier = Arc::new(Barrier::new(active));
            let times: Vec<f64> = std::thread::scope(|s| {
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
                                    for _ in 0..reps {
                                        barrier.wait();
                                        let t0 = Instant::now();
                                        let mut outs: Vec<Vec<F>> = Vec::with_capacity(cols * lde);
                                        for col in inputs[w].iter() {
                                            for &off in offsets.iter() {
                                                outs.push(if variant.starts_with("AVX2") {
                                                    lde_coset_avx2_parallel(
                                                        col, off, &tw, &ext, &worker,
                                                    )
                                                } else {
                                                    unsafe {
                                                        lde_coset_avx512_parallel(
                                                            col, off, &tw, &ext, &worker,
                                                        )
                                                    }
                                                });
                                            }
                                        }
                                        best = best.min(t0.elapsed().as_secs_f64());
                                        std::hint::black_box(&outs);
                                        drop(outs);
                                    }
                                    best
                                })
                            })
                            .unwrap()
                    })
                    .collect();
                handles.into_iter().map(|h| h.join().unwrap()).collect()
            });
            let slowest = times.iter().cloned().fold(0.0, f64::max);
            let mean = times.iter().sum::<f64>() / times.len() as f64;
            println!("[avx512] {variant:<24} {mode:<5} ({active:2} workers): slowest {slowest:.3} s, mean {mean:.3} s | {:.2} ms per column-coset per worker", 1e3 * mean / (cols * lde) as f64);
        }
    }
    println!("[avx512] done");
}
