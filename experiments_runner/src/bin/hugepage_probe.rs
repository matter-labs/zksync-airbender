//! Do large allocations get transparent huge pages? Allocates buffers the
//! way the kernels do (`Vec::with_capacity`, `std::alloc` page-aligned,
//! 2 MB-aligned, 2 MB-aligned + `madvise(MADV_HUGEPAGE)`), touches them
//! (single thread, then 16 threads on slices), and reads the kernel's own
//! accounting of the mapping from `/proc/self/smaps` (`AnonHugePages`).
#[cfg(not(target_os = "linux"))]
fn main() {
    eprintln!("linux only");
}

#[cfg(target_os = "linux")]
fn main() {
    use std::alloc::{alloc, dealloc, Layout};
    use std::time::Instant;

    fn smaps_entry(addr: usize) -> Option<(usize, usize, usize, usize)> {
        // (vma size kB, rss kB, anon huge kB, vma start)
        let text = std::fs::read_to_string("/proc/self/smaps").ok()?;
        let mut start = 0usize;
        let (mut size, mut rss, mut huge) = (0usize, 0usize, 0usize);
        let mut hit = false;
        for line in text.lines() {
            let first = line.split_whitespace().next().unwrap_or("");
            let header = first
                .split_once('-')
                .and_then(|(lo, hi)| Some((usize::from_str_radix(lo, 16).ok()?, usize::from_str_radix(hi, 16).ok()?)));
            if let Some((lo, hi)) = header {
                if hit {
                    break;
                }
                hit = lo <= addr && addr < hi;
                start = lo;
                continue;
            }
            if hit {
                let mut it = line.split_whitespace();
                let key = it.next().unwrap_or("");
                let val: usize = it.next().and_then(|v| v.parse().ok()).unwrap_or(0);
                match key {
                    "Size:" => size = val,
                    "Rss:" => rss = val,
                    "AnonHugePages:" => huge = val,
                    _ => {}
                }
            }
        }
        if hit {
            Some((size, rss, huge, start))
        } else {
            None
        }
    }

    fn touch(p: *mut u32, len: usize, threads: usize) -> f64 {
        let t0 = Instant::now();
        let addr = p as usize;
        std::thread::scope(|s| {
            let per = len / threads;
            for t in 0..threads {
                s.spawn(move || {
                    let q = (addr as *mut u32).wrapping_add(t * per);
                    let mut i = 0;
                    while i < per {
                        unsafe { q.add(i).write_volatile(i as u32) };
                        i += 1024; // one write per 4 KB page
                    }
                });
            }
        });
        t0.elapsed().as_secs_f64() * 1e3
    }

    let mbs = [1usize, 4, 64, 256];
    for &mb in &mbs {
        let len = mb << 18; // u32 elements
        for kind in ["Vec::with_capacity", "alloc align 4K", "alloc align 2M", "alloc align 2M + madvise"] {
            for threads in [1usize, 16] {
                let (ptr, layout, vec): (*mut u32, Option<Layout>, Option<Vec<u32>>) = match kind {
                    "Vec::with_capacity" => {
                        let mut v: Vec<u32> = Vec::with_capacity(len);
                        let p = v.as_mut_ptr();
                        (p, None, Some(v))
                    }
                    "alloc align 4K" => {
                        let l = Layout::from_size_align(len * 4, 4096).unwrap();
                        (unsafe { alloc(l) } as *mut u32, Some(l), None)
                    }
                    _ => {
                        let l = Layout::from_size_align(len * 4, 2 << 20).unwrap();
                        let p = unsafe { alloc(l) } as *mut u32;
                        if kind.ends_with("madvise") {
                            let r = unsafe { libc::madvise(p as *mut libc::c_void, len * 4, libc::MADV_HUGEPAGE) };
                            assert_eq!(r, 0, "madvise failed");
                        }
                        (p, Some(l), None)
                    }
                };
                let touch_ms = touch(ptr, len, threads);
                let (size, rss, huge, start) = smaps_entry(ptr as usize).unwrap_or((0, 0, 0, 0));
                let t0 = Instant::now();
                match (layout, vec) {
                    (Some(l), _) => unsafe { dealloc(ptr as *mut u8, l) },
                    (None, Some(v)) => drop(v),
                    _ => unreachable!(),
                }
                let free_ms = t0.elapsed().as_secs_f64() * 1e3;
                println!(
                    "[thp] {mb:>4} MB {kind:<26} touch by {threads:>2} thr: {touch_ms:7.2} ms | ptr%2M={:>8} vma {size:>7} kB rss {rss:>7} kB AnonHugePages {huge:>7} kB ({:.0}% of rss) vma-start%2M={} | free {free_ms:6.2} ms",
                    (ptr as usize) % (2 << 20),
                    if rss > 0 { 100.0 * huge as f64 / rss as f64 } else { 0.0 },
                    start % (2 << 20),
                );
            }
        }
    }
    // Contention: `workers` outer threads each loop over `iters` x (alloc 64 MB,
    // touch by 16 threads, free), all at once — the per-column pattern of the
    // batch (12 workers x 16 threads in one process).
    for workers in [1usize, 12] {
        let iters = 8usize;
        let len = 64usize << 18;
        let res: Vec<(f64, f64, f64)> = std::thread::scope(|s| {
            let hs: Vec<_> = (0..workers)
                .map(|_| {
                    s.spawn(move || {
                        let (mut ta, mut tt, mut tf) = (0.0, 0.0, 0.0);
                        for _ in 0..iters {
                            let l = Layout::from_size_align(len * 4, 4096).unwrap();
                            let t0 = Instant::now();
                            let p = unsafe { alloc(l) } as *mut u32;
                            ta += t0.elapsed().as_secs_f64() * 1e3;
                            tt += touch(p, len, 16);
                            let t0 = Instant::now();
                            unsafe { dealloc(p as *mut u8, l) };
                            tf += t0.elapsed().as_secs_f64() * 1e3;
                        }
                        (ta / iters as f64, tt / iters as f64, tf / iters as f64)
                    })
                })
                .collect();
            hs.into_iter().map(|h| h.join().unwrap()).collect()
        });
        let mean = |f: fn(&(f64, f64, f64)) -> f64| res.iter().map(f).sum::<f64>() / res.len() as f64;
        println!(
            "[thp] contention: {workers:>2} concurrent workers, 64 MB alloc+touch(16 thr)+free per iteration: alloc {:.2} ms, touch {:.2} ms, free {:.2} ms (per worker, mean over {iters} iters)",
            mean(|r| r.0),
            mean(|r| r.1),
            mean(|r| r.2)
        );
    }
    println!("[thp] done");
}
