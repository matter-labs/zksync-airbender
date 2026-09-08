//! Reproduces the same-size initial-pass slowdown seen with the pooled window
//! buffers: `polys` buffers of `2^log_n` 16-byte elements are written with
//! non-temporal stores by `threads` threads, then read in lockstep (32-row
//! blocks, every buffer per block, the shape of the X86 same-size initial
//! pass). Allocation modes:
//!   exact       Box of exactly n elements (glibc mmap, data at page+16)
//!   big         Box of n + slack elements, data at the box start
//!   win2m       same box, data at the first 2 MB boundary inside it
//!   win2m_stag  win2m + (j % 64) * 4160 stagger
//!   win4k       same box, data at the first page boundary inside it
//!   big_madv    big + madvise(MADV_HUGEPAGE)
//!   mmap        anonymous mmap of exactly n*16 bytes (kernel 2 MB-aligns it)
//!   mmap_plus   mmap of n*16 + 4 KB, data at +16 (what glibc does for exact)
//!   mmap_big    mmap of n*16 + slack, data at the mapping start
//!   mmap_big2m  mmap of n*16 + slack, data at the first 2 MB boundary
//! usage: pool_layout_probe <mode> [threads=16] [polys=20] [log_n=24] [passes=5] [lockstep|polymajor]
#[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
fn main() {
    eprintln!("linux x86_64 only");
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn main() {
    use std::arch::x86_64::*;
    use std::mem::MaybeUninit;
    use std::sync::Barrier;
    use std::time::Instant;

    let args: Vec<String> = std::env::args().collect();
    let mode = args.get(1).cloned().unwrap_or_else(|| "exact".to_string());
    let threads: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(16);
    let polys: usize = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(20);
    let log_n: u32 = args.get(4).and_then(|s| s.parse().ok()).unwrap_or(24);
    let passes: usize = args.get(5).and_then(|s| s.parse().ok()).unwrap_or(5);
    let order = args
        .get(6)
        .cloned()
        .unwrap_or_else(|| "lockstep".to_string());
    let n = 1usize << log_n;
    let bytes = n * 16;
    const HUGE: usize = 2 << 20;
    // window granule + alignment granule + stagger slack, as in AllocationPool
    const SLACK: usize = 4 * (1 << 20) + 266_240;
    fn round_up(x: usize, a: usize) -> usize {
        x.div_ceil(a) * a
    }

    #[derive(Clone, Copy)]
    struct Buf {
        ptr: usize,
        base: usize,
        map_len: usize,
        kind: u8,
    }

    let alloc = |j: usize| -> Buf {
        match mode.as_str() {
            "exact" => {
                let b = Box::<[MaybeUninit<u128>]>::new_uninit_slice(n);
                let base = Box::into_raw(b) as *mut u8 as usize;
                Buf {
                    ptr: base,
                    base,
                    map_len: n,
                    kind: 0,
                }
            }
            "big" | "win2m" | "win2m_stag" | "win4k" | "big_madv" => {
                let n_alloc = n + SLACK / 16;
                let b = Box::<[MaybeUninit<u128>]>::new_uninit_slice(n_alloc);
                let base = Box::into_raw(b) as *mut u8 as usize;
                let ptr = match mode.as_str() {
                    "big" | "big_madv" => base,
                    "win2m" => round_up(base, HUGE),
                    "win2m_stag" => round_up(base, HUGE) + (j % 64) * 4160,
                    "win4k" => round_up(base, 4096),
                    _ => unreachable!(),
                };
                if mode == "big_madv" {
                    let start = round_up(base, 4096);
                    let end = (base + n_alloc * 16) / 4096 * 4096;
                    unsafe {
                        libc::madvise(start as *mut libc::c_void, end - start, libc::MADV_HUGEPAGE);
                    }
                }
                Buf {
                    ptr,
                    base,
                    map_len: n_alloc,
                    kind: 0,
                }
            }
            "mmap" | "mmap_plus" | "mmap_big" | "mmap_big2m" => {
                let len = match mode.as_str() {
                    "mmap" => bytes,
                    "mmap_plus" => bytes + 4096,
                    _ => bytes + SLACK,
                };
                let base = unsafe {
                    libc::mmap(
                        core::ptr::null_mut(),
                        len,
                        libc::PROT_READ | libc::PROT_WRITE,
                        libc::MAP_PRIVATE | libc::MAP_ANONYMOUS,
                        -1,
                        0,
                    )
                };
                assert!(base != libc::MAP_FAILED);
                let base = base as usize;
                let ptr = match mode.as_str() {
                    "mmap" | "mmap_big" => base,
                    "mmap_plus" => base + 16,
                    "mmap_big2m" => round_up(base, HUGE),
                    _ => unreachable!(),
                };
                Buf {
                    ptr,
                    base,
                    map_len: len,
                    kind: 1,
                }
            }
            m if m.starts_with("boxplus:") => {
                // Box of n*16 + extra bytes, data at the first 64-byte boundary
                let extra: usize = m["boxplus:".len()..].parse().unwrap();
                let n_alloc = n + extra.div_ceil(16);
                let b = Box::<[MaybeUninit<u128>]>::new_uninit_slice(n_alloc);
                let base = Box::into_raw(b) as *mut u8 as usize;
                let ptr = round_up(base, 64) + (j % 64) * 64 * ((extra >= 8192) as usize);
                Buf {
                    ptr,
                    base,
                    map_len: n_alloc,
                    kind: 0,
                }
            }
            other => panic!("unknown mode {other}"),
        }
    };

    let bufs: Vec<Buf> = (0..polys).map(alloc).collect();
    for (j, b) in bufs.iter().enumerate().take(4) {
        println!(
            "poly {j}: ptr {:#x} (mod 2MB {:#x}, mod 4K {:#x}), map base {:#x} len {:.2} MB",
            b.ptr,
            b.ptr % HUGE,
            b.ptr % 4096,
            b.base,
            (b.map_len * if b.kind == 0 { 16 } else { 1 }) as f64 / (1u64 << 20) as f64
        );
    }
    if polys > 1 {
        println!(
            "consecutive ptr deltas (MB): {:?}",
            bufs.windows(2)
                .take(4)
                .map(|w| (w[1].ptr as i64 - w[0].ptr as i64) as f64 / (1u64 << 20) as f64)
                .collect::<Vec<_>>()
        );
    }

    let rows_per_thread = n / threads;
    let barrier = Barrier::new(threads);
    let ptrs: Vec<usize> = bufs.iter().map(|b| b.ptr).collect();
    let results: Vec<Vec<f64>> = std::thread::scope(|s| {
        let handles: Vec<_> = (0..threads)
            .map(|t| {
                let ptrs = &ptrs;
                let barrier = &barrier;
                let order = order.as_str();
                s.spawn(move || {
                    let r0 = t * rows_per_thread;
                    let r1 = r0 + rows_per_thread;
                    // write phase: NT stores, poly-major
                    unsafe {
                        for (j, &p) in ptrs.iter().enumerate() {
                            let p = p as *mut u8;
                            for r in r0..r1 {
                                _mm_stream_si128(
                                    p.add(r * 16) as *mut __m128i,
                                    _mm_set_epi64x(r as i64, j as i64),
                                );
                            }
                        }
                        _mm_sfence();
                    }
                    let mut times = Vec::with_capacity(passes);
                    let mut sink = 0u64;
                    for _ in 0..passes {
                        barrier.wait();
                        let start = Instant::now();
                        unsafe {
                            let mut acc = _mm256_setzero_si256();
                            if order == "lockstep" {
                                let mut blk = r0;
                                while blk < r1 {
                                    for &p in ptrs.iter() {
                                        let p = p as *const u8;
                                        let mut r = 0;
                                        while r < 32 {
                                            acc = _mm256_xor_si256(
                                                acc,
                                                _mm256_loadu_si256(
                                                    p.add((blk + r) * 16) as *const __m256i
                                                ),
                                            );
                                            r += 2;
                                        }
                                    }
                                    blk += 32;
                                }
                            } else {
                                for &p in ptrs.iter() {
                                    let p = p as *const u8;
                                    let mut r = r0;
                                    while r < r1 {
                                        acc = _mm256_xor_si256(
                                            acc,
                                            _mm256_loadu_si256(p.add(r * 16) as *const __m256i),
                                        );
                                        r += 2;
                                    }
                                }
                            }
                            let mut out = [0u64; 4];
                            _mm256_storeu_si256(out.as_mut_ptr() as *mut __m256i, acc);
                            sink ^= out[0] ^ out[1] ^ out[2] ^ out[3];
                        }
                        times.push(start.elapsed().as_secs_f64() * 1e3);
                    }
                    if sink == 0x1234_5678_9abc_def0 {
                        println!("(sink) {sink}");
                    }
                    times
                })
            })
            .collect();
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let total_bytes = (polys * bytes) as f64;
    let mut per_pass: Vec<f64> = (0..passes)
        .map(|k| results.iter().map(|r| r[k]).fold(0.0, f64::max))
        .collect();
    let line: Vec<String> = per_pass.iter().map(|t| format!("{t:.1}")).collect();
    per_pass.sort_by(|a, b| a.partial_cmp(b).unwrap());
    println!(
        "mode {mode} order {order}: passes [{}] ms; min {:.1} ms = {:.1} GB/s; median {:.1} ms",
        line.join(", "),
        per_pass[0],
        total_bytes / per_pass[0] / 1e6,
        per_pass[passes / 2]
    );
    for b in bufs {
        unsafe {
            if b.kind == 0 {
                drop(Box::from_raw(core::ptr::slice_from_raw_parts_mut(
                    b.base as *mut MaybeUninit<u128>,
                    b.map_len,
                )));
            } else {
                libc::munmap(b.base as *mut libc::c_void, b.map_len);
            }
        }
    }
}
