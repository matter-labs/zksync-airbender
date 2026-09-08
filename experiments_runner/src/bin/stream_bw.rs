//! Streaming-bandwidth ceiling for the prover's worker shape: `outer`
//! concurrent workers of `inner` pinned threads each stream their own
//! buffers — read-only (AVX2 loads, summed), read+write copy (regular
//! stores), and read+write copy with non-temporal stores — and report GB/s
//! per worker (data moved: reads + writes) and aggregate.
#[cfg(not(all(target_arch = "x86_64", target_feature = "avx2")))]
fn main() {
    eprintln!("x86-64 + avx2 only");
}

#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
fn main() {
    use core::arch::x86_64::*;
    use std::sync::{Arc, Barrier};
    use std::time::Instant;
    use worker::Worker;

    let args: Vec<String> = std::env::args().collect();
    let (mut outer, mut inner, mut mb_per_thread, mut reps, mut pin) = (12usize, 16usize, 256usize, 3usize, true);
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--outer" => outer = args[i + 1].parse().unwrap(),
            "--inner" => inner = args[i + 1].parse().unwrap(),
            "--mb" => mb_per_thread = args[i + 1].parse().unwrap(),
            "--reps" => reps = args[i + 1].parse().unwrap(),
            "--no-pin" => {
                pin = false;
                i -= 1;
            }
            other => panic!("unknown arg {other}"),
        }
        i += 2;
    }
    let cpu_blocks: Vec<Vec<usize>> = if pin {
        let flat: Vec<usize> = Worker::cpu_complexes().iter().flatten().copied().collect();
        assert!(outer * inner <= flat.len());
        (0..outer).map(|w| flat[w * inner..(w + 1) * inner].to_vec()).collect()
    } else {
        Vec::new()
    };
    let n = mb_per_thread << 18; // u32 per thread
    println!("[stream] outer={outer} x inner={inner}, {mb_per_thread} MB per thread per buffer, reps={reps}, pin={pin}");

    #[target_feature(enable = "avx2")]
    unsafe fn read_sum(p: *const u32, n: usize) -> u32 {
        let mut acc = _mm256_setzero_si256();
        let mut i = 0;
        while i < n {
            acc = _mm256_add_epi32(acc, _mm256_loadu_si256(p.add(i) as *const __m256i));
            i += 8;
        }
        let mut out = [0u32; 8];
        _mm256_storeu_si256(out.as_mut_ptr() as *mut __m256i, acc);
        out.iter().sum()
    }
    #[target_feature(enable = "avx2")]
    unsafe fn copy_plain(s: *const u32, d: *mut u32, n: usize) {
        let mut i = 0;
        while i < n {
            _mm256_storeu_si256(d.add(i) as *mut __m256i, _mm256_loadu_si256(s.add(i) as *const __m256i));
            i += 8;
        }
    }
    #[target_feature(enable = "avx2")]
    unsafe fn copy_nt(s: *const u32, d: *mut u32, n: usize) {
        let mut i = 0;
        while i < n {
            _mm256_stream_si256(d.add(i) as *mut __m256i, _mm256_loadu_si256(s.add(i) as *const __m256i));
            i += 8;
        }
        _mm_sfence();
    }

    for kind in ["read-only", "copy (regular stores)", "copy (non-temporal stores)"] {
        let barrier = Arc::new(Barrier::new(outer));
        let rates: Vec<f64> = std::thread::scope(|s| {
            let handles: Vec<_> = (0..outer)
                .map(|w| {
                    let (barrier, cpu_blocks) = (barrier.clone(), &cpu_blocks);
                    s.spawn(move || {
                        let worker = if pin {
                            Worker::new_with_num_threads_on_cpus_and_stack(inner, &cpu_blocks[w], 64 << 20)
                        } else {
                            Worker::new_with_num_threads_and_stack(inner, 64 << 20)
                        };
                        // per-thread source and destination buffers, 32 B aligned dst
                        let layout = std::alloc::Layout::from_size_align(n * 4, 2 << 20).unwrap();
                        let srcs: Vec<usize> = (0..inner).map(|_| unsafe { std::alloc::alloc(layout) } as usize).collect();
                        let dsts: Vec<usize> = (0..inner).map(|_| unsafe { std::alloc::alloc(layout) } as usize).collect();
                        // touch
                        worker.scope(inner, |scope, _| {
                            for t in 0..inner {
                                let (s_, d_) = (srcs[t], dsts[t]);
                                Worker::smart_spawn(scope, t == inner - 1, move |_| unsafe {
                                    for j in (0..n).step_by(1024) {
                                        *(s_ as *mut u32).add(j) = j as u32;
                                        *(d_ as *mut u32).add(j) = 0;
                                    }
                                });
                            }
                        });
                        let mut best = f64::MAX;
                        let mut sink = 0u32;
                        for _ in 0..reps {
                            barrier.wait();
                            let t0 = Instant::now();
                            worker.scope(inner, |scope, _| {
                                for t in 0..inner {
                                    let (s_, d_) = (srcs[t], dsts[t]);
                                    Worker::smart_spawn(scope, t == inner - 1, move |_| unsafe {
                                        match kind {
                                            "read-only" => {
                                                std::hint::black_box(read_sum(s_ as *const u32, n));
                                            }
                                            "copy (regular stores)" => copy_plain(s_ as *const u32, d_ as *mut u32, n),
                                            _ => copy_nt(s_ as *const u32, d_ as *mut u32, n),
                                        }
                                    });
                                }
                            });
                            best = best.min(t0.elapsed().as_secs_f64());
                            sink = sink.wrapping_add(1);
                        }
                        std::hint::black_box(sink);
                        let bytes = (inner * n * 4) as f64 * if kind == "read-only" { 1.0 } else { 2.0 };
                        bytes / best / 1e9
                    })
                })
                .collect();
            handles.into_iter().map(|h| h.join().unwrap()).collect()
        });
        let min = rates.iter().cloned().fold(f64::MAX, f64::min);
        let mean = rates.iter().sum::<f64>() / rates.len() as f64;
        println!(
            "[stream] {kind:<28} {inner}x{outer}: per worker min {min:6.1} mean {mean:6.1} GB/s, aggregate {:7.1} GB/s",
            rates.iter().sum::<f64>()
        );
    }
    println!("[stream] done");
}
