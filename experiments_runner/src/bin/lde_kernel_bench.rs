//! Per-phase micro-benchmark of the x86-64 AVX2 BabyBear LDE kernels at a
//! given polynomial size and worker width: the prepare sweep (fused vs the
//! two-sweep reference), the block-local NTT phase, the global phase
//! (radix-16 vs radix-4 passes), the whole coset LDE, and the
//! hypercube-to-monomial transform (serial per column vs blocked parallel,
//! in the two base-commit schedulings). Every variant is cross-checked
//! against its reference. Runs on x86-64 + AVX2 only.
#![feature(allocator_api)]

#[cfg(not(all(target_arch = "x86_64", target_feature = "avx2")))]
fn main() {
    eprintln!("x86-64 + avx2 only");
}

#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
fn main() {
    use fft::baby_bear_avx2::{self as k, avx2};
    use field::baby_bear::base::BabyBearField as F;
    use field::PrimeField;
    use prover::gkr::whir::hypercube_to_monomial::{
        multivariate_hypercube_evals_into_coeffs_avx2_bb as transform_serial,
        multivariate_hypercube_evals_into_coeffs_avx2_bb_parallel as transform_parallel,
    };
    use std::alloc::Global;
    use std::time::Instant;
    use worker::rayon::prelude::*;
    use worker::Worker;

    let args: Vec<String> = std::env::args().collect();
    let mut threads = 96usize;
    let mut log_n = 24u32;
    let mut cols = 26usize;
    let mut reps = 5usize;
    let mut pin_base: Option<usize> = None;
    let mut probe_phase_a = false;
    let mut misalign = false;
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--threads" => threads = args[i + 1].parse().unwrap(),
            "--log-n" => log_n = args[i + 1].parse().unwrap(),
            "--cols" => cols = args[i + 1].parse().unwrap(),
            "--reps" => reps = args[i + 1].parse().unwrap(),
            "--pin-base" => pin_base = Some(args[i + 1].parse().unwrap()),
            "--probe-phase-a" => {
                probe_phase_a = true;
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
    let worker = match pin_base {
        Some(base) => {
            let cpus: Vec<usize> = (base..base + threads).collect();
            Worker::new_with_num_threads_on_cpus(threads, &cpus)
        }
        None => Worker::new_with_num_threads(threads),
    };
    println!("[kbench] pinned={}", pin_base.is_some());
    let n = 1usize << log_n;
    println!("[kbench] threads={threads} log_n={log_n} cols={cols} reps={reps}");

    let input: Vec<F> = (0..n)
        .map(|el| {
            F::from_u32_with_reduction((el as u32).wrapping_mul(2654435761) ^ (el as u32 >> 7))
        })
        .collect();
    let tw: Vec<F, Global> = fft::precompute_all_twiddles_for_fft_serial::<F, Global, false>(n);
    let ext = k::Avx2TwiddleExt::build_parallel(&tw, n, &worker);
    let offset = fft::domain_generator_for_size::<F>((n * 2) as u64);
    let input_raw: &[u32] = unsafe { core::slice::from_raw_parts(input.as_ptr() as *const u32, n) };
    let tw_raw: &[u32] = unsafe { core::slice::from_raw_parts(tw.as_ptr() as *const u32, n / 2) };

    /// warm-up run, then `reps` timed runs on pre-made copies; prints min / median ms
    fn bench_on_copies(label: &str, copies: &mut [Vec<u32>], mut f: impl FnMut(&mut Vec<u32>)) {
        let reps = copies.len() - 1;
        f(&mut copies[0]);
        let mut times = Vec::with_capacity(reps);
        for c in copies[1..].iter_mut() {
            let t0 = Instant::now();
            f(c);
            times.push(t0.elapsed().as_secs_f64() * 1e3);
        }
        times.sort_by(|a, b| a.partial_cmp(b).unwrap());
        println!(
            "[kbench] {label:<44} min {:8.2} ms   median {:8.2} ms",
            times[0],
            times[reps / 2]
        );
    }
    let copies_of =
        |v: &[u32], count: usize| -> Vec<Vec<u32>> { (0..count).map(|_| v.to_vec()).collect() };

    // ---- prepare sweep: fused vs two sweeps
    let mut dst_two = vec![0u32; n];
    let mut dst_fused = vec![0u32; n];
    {
        let mut scratch = copies_of(&[0u32; 0], 0);
        scratch.push(vec![0u32; n]);
        let mut c: Vec<Vec<u32>> = (0..reps + 1).map(|_| vec![0u32; n]).collect();
        bench_on_copies(
            "prep: scaled copy + in-place bitrev (2 sweeps)",
            &mut c,
            |d| k::lde_prepare_bitrev_scaled_two_sweeps_into(input_raw, d, offset, &worker),
        );
        dst_two.copy_from_slice(&c[0]);
        let mut c: Vec<Vec<u32>> = (0..reps + 1).map(|_| vec![0u32; n]).collect();
        bench_on_copies("prep: fused scale+bitrev+copy (1 sweep)", &mut c, |d| {
            k::lde_prepare_bitrev_scaled_into(input_raw, d, offset, &worker)
        });
        dst_fused.copy_from_slice(&c[0]);
        assert_eq!(dst_two, dst_fused, "fused prep diverged");
        drop(scratch);
    }

    // ---- phase A on the prepared data
    let mut c = copies_of(&dst_fused, reps + 1);
    bench_on_copies(
        "NTT phase A: 2^16 block-local (1 sweep)",
        &mut c,
        |a| unsafe { avx2::ntt_phase_a_blocks(a, tw_raw, &ext.ao, &ext.bo, &worker) },
    );
    let after_a = c[0].clone();
    drop(c);

    let after_b_check: Vec<u32> = {
        let mut a = after_a.clone();
        unsafe { avx2::ntt_phase_b_global(&mut a, log_n, tw_raw, &ext.ao, &ext.bo, &worker) };
        a
    };
    if misalign {
        // buffers offset by k elements from a page-aligned allocation: every
        // kernel below runs on `&mut big[k..k+n]`, so its base address is
        // 4k bytes into a cache line (k = 0 aligned; k = 8 -> 32 B, no line
        // straddling; k = 1, 2, 4 -> half the 32 B vectors straddle a line)
        println!(
            "[align] input buffer ptr % 64 = {}, prepared buffer ptr % 64 = {}, tw % 64 = {}",
            input_raw.as_ptr() as usize % 64,
            dst_fused.as_ptr() as usize % 64,
            tw_raw.as_ptr() as usize % 64
        );
        // what the allocator actually returns for buffers of various sizes
        for log in [10u32, 14, 16, 18, 20, 22, 24, 26] {
            let v: Vec<u32> = Vec::with_capacity(1usize << log);
            let z: Vec<u32> = vec![0u32; 1usize << log];
            println!(
                "[align] Vec<u32> 2^{log} ({:>7} KB): with_capacity ptr % 4096 = {:4} (% 64 = {:2}) | zeroed ptr % 4096 = {:4} (% 64 = {:2})",
                (4usize << log) / 1024,
                v.as_ptr() as usize % 4096,
                v.as_ptr() as usize % 64,
                z.as_ptr() as usize % 4096,
                z.as_ptr() as usize % 64
            );
            std::hint::black_box((&v, &z));
        }
        for k in [0usize, 1, 2, 4, 8, 16] {
            let mut src_big = vec![0u32; n + 64];
            src_big[k..k + n].copy_from_slice(input_raw);
            let mut times_prep = Vec::new();
            let mut times_a = Vec::new();
            let mut times_b = Vec::new();
            for r in 0..reps + 1 {
                let mut big = vec![0u32; n + 64];
                let t0 = Instant::now();
                k::lde_prepare_bitrev_scaled_into(
                    &src_big[k..k + n],
                    &mut big[k..k + n],
                    offset,
                    &worker,
                );
                let tp = t0.elapsed();
                let t0 = Instant::now();
                unsafe {
                    avx2::ntt_phase_a_blocks(&mut big[k..k + n], tw_raw, &ext.ao, &ext.bo, &worker)
                };
                let ta = t0.elapsed();
                let t0 = Instant::now();
                unsafe {
                    avx2::ntt_phase_b_global(
                        &mut big[k..k + n],
                        log_n,
                        tw_raw,
                        &ext.ao,
                        &ext.bo,
                        &worker,
                    )
                };
                let tb = t0.elapsed();
                if r > 0 {
                    times_prep.push(tp.as_secs_f64() * 1e3);
                    times_a.push(ta.as_secs_f64() * 1e3);
                    times_b.push(tb.as_secs_f64() * 1e3);
                }
                if k == 0 && r == 0 {
                    assert_eq!(&big[..n], &after_b_check[..], "misalign k=0 diverged");
                }
                std::hint::black_box(&big);
            }
            let med = |v: &mut Vec<f64>| {
                v.sort_by(|a, b| a.partial_cmp(b).unwrap());
                v[v.len() / 2]
            };
            println!(
                "[align] offset {k:2} elems ({:2} B, base % 64 = {:2}): prep {:7.2} ms  phase A {:7.2} ms  phase B {:7.2} ms",
                4 * k,
                (4 * k) % 64,
                med(&mut times_prep),
                med(&mut times_a),
                med(&mut times_b)
            );
        }
    }

    if probe_phase_a {
        // per-task instrumentation of phase A: start offset (µs from scope
        // start), duration (µs), cpu id — to separate slow work from late
        // starts / migrations
        let blk = 1usize << avx2::BLOCK_LOG2;
        let num_blocks = n / blk;
        for probe_rep in 0..3 {
            let mut a = dst_fused.clone();
            let base_addr = a.as_mut_ptr() as usize;
            let t_addr = tw_raw.as_ptr() as usize;
            let ao_addr = ext.ao.as_ptr() as usize;
            let bo_addr = ext.bo.as_ptr() as usize;
            let records: std::sync::Mutex<Vec<(usize, f64, f64, i32, usize)>> =
                std::sync::Mutex::new(Vec::new());
            let scope_t0 = Instant::now();
            worker.scope(num_blocks, |scope, geometry| {
                for thread_idx in 0..geometry.len() {
                    let start = geometry.get_chunk_start_pos(thread_idx);
                    let size = geometry.get_chunk_size(thread_idx);
                    let records = &records;
                    Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                        let t_start = scope_t0.elapsed().as_secs_f64() * 1e6;
                        let cpu = libc::sched_getcpu();
                        let t1 = Instant::now();
                        for b in start..start + size {
                            avx2::ntt_block_local(
                                (base_addr as *mut u32).add(b * blk),
                                b,
                                t_addr as *const u32,
                                ao_addr as *const u32,
                                bo_addr as *const u32,
                            );
                        }
                        let dur = t1.elapsed().as_secs_f64() * 1e6;
                        let cpu_end = libc::sched_getcpu();
                        records.lock().unwrap().push((
                            thread_idx,
                            t_start,
                            dur,
                            cpu,
                            (cpu_end == cpu) as usize,
                        ));
                    });
                }
            });
            let total = scope_t0.elapsed().as_secs_f64() * 1e6;
            let mut r = records.into_inner().unwrap();
            r.sort_by(|x, y| x.0.cmp(&y.0));
            let n_tasks = r.len();
            let max_start = r.iter().map(|x| x.1).fold(0.0, f64::max);
            let max_dur = r.iter().map(|x| x.2).fold(0.0, f64::max);
            let mean_dur = r.iter().map(|x| x.2).sum::<f64>() / n_tasks as f64;
            let min_dur = r.iter().map(|x| x.2).fold(f64::MAX, f64::min);
            let mut cpus: Vec<i32> = r.iter().map(|x| x.3).collect();
            cpus.sort();
            let distinct = {
                let mut d = cpus.clone();
                d.dedup();
                d.len()
            };
            let migrated = r.iter().filter(|x| x.4 == 0).count();
            println!(
                "[probe] rep {probe_rep}: scope {total:.0} µs, tasks {n_tasks}, start offset max {max_start:.0} µs, task dur min/mean/max {min_dur:.0}/{mean_dur:.0}/{max_dur:.0} µs, distinct cpus {distinct}, migrated {migrated}"
            );
            if probe_rep == 2 {
                let mut slow: Vec<_> = r.iter().collect();
                slow.sort_by(|x, y| y.2.partial_cmp(&x.2).unwrap());
                let top: Vec<String> = slow
                    .iter()
                    .take(6)
                    .map(|x| format!("(task {} cpu {} start {:.0} dur {:.0})", x.0, x.3, x.1, x.2))
                    .collect();
                println!("[probe]   slowest tasks: {}", top.join(" "));
                let fast: Vec<String> = slow
                    .iter()
                    .rev()
                    .take(4)
                    .map(|x| format!("(task {} cpu {} start {:.0} dur {:.0})", x.0, x.3, x.1, x.2))
                    .collect();
                println!("[probe]   fastest tasks: {}", fast.join(" "));
            }
            std::hint::black_box(a);
        }
    }

    // ---- phase B: radix-16 (line-complete) vs radix-4 passes
    let mut c = copies_of(&after_a, reps + 1);
    bench_on_copies("NTT phase B: radix-16 passes", &mut c, |a| unsafe {
        avx2::ntt_phase_b_global(a, log_n, tw_raw, &ext.ao, &ext.bo, &worker)
    });
    let after_b16 = c[0].clone();
    drop(c);
    let phase_b_r4 = |a: &mut Vec<u32>| unsafe {
        let base_addr = a.as_mut_ptr() as usize;
        let t_addr = tw_raw.as_ptr() as usize;
        let ao_addr = ext.ao.as_ptr() as usize;
        let bo_addr = ext.bo.as_ptr() as usize;
        let mut ppg = 1usize << avx2::BLOCK_LOG2;
        let mut levels_left = log_n - avx2::BLOCK_LOG2;
        while levels_left >= 2 {
            let cur = ppg;
            worker.scope(n / 32, |scope, geometry| {
                for thread_idx in 0..geometry.len() {
                    let start = geometry.get_chunk_start_pos(thread_idx);
                    let size = geometry.get_chunk_size(thread_idx);
                    Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                        avx2::radix4_items(
                            base_addr as *mut u32,
                            cur,
                            t_addr as *const u32,
                            ao_addr as *const u32,
                            bo_addr as *const u32,
                            0,
                            start..start + size,
                        );
                    });
                }
            });
            ppg *= 4;
            levels_left -= 2;
        }
        if levels_left == 1 {
            let cur = ppg;
            worker.scope(n / 16, |scope, geometry| {
                for thread_idx in 0..geometry.len() {
                    let start = geometry.get_chunk_start_pos(thread_idx);
                    let size = geometry.get_chunk_size(thread_idx);
                    Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                        avx2::radix2_items(
                            base_addr as *mut u32,
                            cur,
                            t_addr as *const u32,
                            0,
                            start..start + size,
                        );
                    });
                }
            });
        }
    };
    let mut c = copies_of(&after_a, reps + 1);
    bench_on_copies(
        "NTT phase B: radix-4 passes (reference)",
        &mut c,
        phase_b_r4,
    );
    assert_eq!(after_b16, c[0], "radix-16 phase B diverged from radix-4");
    drop(c);

    // ---- whole coset LDE + reference check
    {
        let mut times = Vec::new();
        let mut out = Vec::new();
        for _ in 0..reps + 1 {
            let t0 = Instant::now();
            out = k::lde_coset_avx2_parallel(&input, offset, &tw, &ext, &worker);
            times.push(t0.elapsed().as_secs_f64() * 1e3);
        }
        times.remove(0);
        times.sort_by(|a, b| a.partial_cmp(b).unwrap());
        println!(
            "[kbench] {:<44} min {:8.2} ms   median {:8.2} ms",
            "coset LDE: full blocked parallel kernel",
            times[0],
            times[reps / 2]
        );
        let out_raw: &[u32] = unsafe { core::slice::from_raw_parts(out.as_ptr() as *const u32, n) };
        assert_eq!(
            out_raw,
            &after_b16[..],
            "full kernel diverged from the phase chain"
        );
        if log_n <= 22 {
            let expected = fft::lde_coset_natural_seq_fused(&input, offset, &tw);
            assert_eq!(
                out, expected,
                "full kernel diverged from the scalar reference"
            );
            println!("[kbench] scalar reference check: OK");
        }
    }

    // ---- transform: one column, serial (single thread) vs blocked parallel
    {
        let mut c: Vec<Vec<F>> = (0..reps + 1).map(|_| input.clone()).collect();
        let mut times = Vec::new();
        for v in c.iter_mut() {
            let t0 = Instant::now();
            transform_serial(v, log_n);
            times.push(t0.elapsed().as_secs_f64() * 1e3);
        }
        times.remove(0);
        times.sort_by(|a, b| a.partial_cmp(b).unwrap());
        println!(
            "[kbench] {:<44} min {:8.2} ms   median {:8.2} ms",
            "transform: serial radix-8 (ONE thread)",
            times[0],
            times[reps / 2]
        );
        let expected = c[0].clone();
        let mut times = Vec::new();
        let mut got = Vec::new();
        for _ in 0..reps + 1 {
            let t0 = Instant::now();
            got = transform_parallel(&input, log_n, &worker);
            times.push(t0.elapsed().as_secs_f64() * 1e3);
        }
        times.remove(0);
        times.sort_by(|a, b| a.partial_cmp(b).unwrap());
        println!(
            "[kbench] {:<44} min {:8.2} ms   median {:8.2} ms",
            "transform: blocked parallel (all threads)",
            times[0],
            times[reps / 2]
        );
        assert_eq!(got, expected, "parallel transform diverged");
    }

    // ---- transform, base-commit shapes: `cols` columns
    {
        let columns: Vec<Vec<F>> = (0..cols).map(|_| input.clone()).collect();
        let mut times = Vec::new();
        for _ in 0..reps + 1 {
            let t0 = Instant::now();
            let out: Vec<Vec<F>> = worker.pool.install(|| {
                columns
                    .par_iter()
                    .map(|col| {
                        let mut v = col.to_vec();
                        transform_serial(&mut v, log_n);
                        v
                    })
                    .collect()
            });
            times.push(t0.elapsed().as_secs_f64() * 1e3);
            std::hint::black_box(out);
        }
        times.remove(0);
        times.sort_by(|a, b| a.partial_cmp(b).unwrap());
        println!(
            "[kbench] {:<44} min {:8.2} ms   median {:8.2} ms",
            format!("transform x{cols}: par-over-columns serial"),
            times[0],
            times[reps / 2]
        );
        let mut times = Vec::new();
        for _ in 0..reps + 1 {
            let t0 = Instant::now();
            let out: Vec<Vec<F>> = columns
                .iter()
                .map(|col| transform_parallel(col, log_n, &worker))
                .collect();
            times.push(t0.elapsed().as_secs_f64() * 1e3);
            std::hint::black_box(out);
        }
        times.remove(0);
        times.sort_by(|a, b| a.partial_cmp(b).unwrap());
        println!(
            "[kbench] {:<44} min {:8.2} ms   median {:8.2} ms",
            format!("transform x{cols}: sequential, blocked parallel"),
            times[0],
            times[reps / 2]
        );
    }
    println!("[kbench] done");
}
