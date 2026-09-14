//! Base-oracle commitment LDE simulation, 12 x 16-thread pinned provers:
//! the prover's current path (every 2^24 column-coset on all threads through
//! the blocked AVX2 kernel: prep sweep + block phase + two radix-16 global
//! sweeps, ~4 DRAM sweeps per coset plus streamed twiddle slices) against a
//! FOUR-STEP formulation (2^24 = 4096 x 4096) in which every thread stays in
//! its own L2: step 1 gathers 16-column tiles (256 KB) — scaled by the coset
//! powers on load — transposes them in registers, runs sixteen 4096-point
//! NTTs and the inter-step twiddles in cache, and writes the tile back
//! transposed; step 2 runs 4096-point NTTs on 16-row groups and writes the
//! rows transposed into natural order. Two DRAM sweeps per coset (read input,
//! write/read the intermediate once, write the output), 16 KB twiddle tables.
//! Values are checked against the blocked kernel before timing.
#![feature(allocator_api)]

#[cfg(not(all(target_arch = "x86_64", target_feature = "avx2")))]
fn main() {
    eprintln!("x86-64 + avx2 only");
}

#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
mod imp {
    use core::arch::x86_64::*;
    use fft::baby_bear_avx2::{avx2, Avx2TwiddleExt};
    use field::baby_bear::base::BabyBearField as F;
    use field::{Field, PrimeField};
    use std::alloc::Global;
    use worker::Worker;

    pub const LOG_N: u32 = 24;
    pub const N1: usize = 4096;
    pub const N2: usize = 4096;
    pub const N: usize = N1 * N2;
    const TILE: usize = 16;

    /// Everything the four-step kernel needs for one (size, coset offset).
    pub struct FourStepTables {
        pub tw12: Vec<u32>,
        pub ao12: Vec<u32>,
        pub bo12: Vec<u32>,
        /// `offset^{i1}` for `i1 < N1`
        pub lo: Vec<u32>,
        /// `offset^{N1 * i2}` for `i2 < N2`
        pub hi: Vec<u32>,
        /// per column `i1`: `[w^0..w^7]` and `w^8` with `w = omega_N^{i1}`
        pub col_tw: Vec<([u32; 8], u32)>,
    }

    impl FourStepTables {
        pub fn new(offset: F) -> Self {
            let tw12_f: Vec<F, Global> =
                fft::precompute_all_twiddles_for_fft_serial::<F, Global, false>(N1);
            let ext12 = Avx2TwiddleExt::build(&tw12_f, N1);
            let tw12: Vec<u32> = tw12_f.iter().map(|x| x.raw_u32_value()).collect();
            let omega_n = fft::domain_generator_for_size::<F>(N as u64);
            let mut lo = Vec::with_capacity(N1);
            let mut hi = Vec::with_capacity(N2);
            let mut col_tw = Vec::with_capacity(N1);
            let mut p = F::ONE;
            for _ in 0..N1 {
                lo.push(p.raw_u32_value());
                p.mul_assign(&offset);
            }
            // p == offset^{N1} now
            let offset_n1 = p;
            let mut q = F::ONE;
            for _ in 0..N2 {
                hi.push(q.raw_u32_value());
                q.mul_assign(&offset_n1);
            }
            let mut w = F::ONE;
            for _ in 0..N1 {
                let mut pw = [0u32; 8];
                let mut x = F::ONE;
                for k in 0..8 {
                    pw[k] = x.raw_u32_value();
                    x.mul_assign(&w);
                }
                col_tw.push((pw, x.raw_u32_value()));
                w.mul_assign(&omega_n);
            }
            Self {
                tw12,
                ao12: ext12.ao,
                bo12: ext12.bo,
                lo,
                hi,
                col_tw,
            }
        }
    }

    /// 64-byte-aligned scratch of `len` u32s.
    struct Aligned {
        v: Vec<u32>,
        off: usize,
        len: usize,
    }
    impl Aligned {
        fn new(len: usize) -> Self {
            let v = vec![0u32; len + 16];
            let off = (64 - (v.as_ptr() as usize % 64)) % 64 / 4;
            Self { v, off, len }
        }
        fn ptr(&mut self) -> *mut u32 {
            unsafe { self.v.as_mut_ptr().add(self.off) }
        }
        fn slice(&mut self) -> &mut [u32] {
            let (off, len) = (self.off, self.len);
            &mut self.v[off..off + len]
        }
    }

    #[inline(always)]
    unsafe fn ld(p: *const u32) -> __m256i {
        _mm256_loadu_si256(p as *const __m256i)
    }
    #[inline(always)]
    unsafe fn st(p: *mut u32, v: __m256i) {
        _mm256_storeu_si256(p as *mut __m256i, v)
    }

    /// Step 1 for the tile of columns `16t..16t+16`: gather + scale +
    /// transpose into column buffers, per-column NTT + inter-step twiddle,
    /// transposed write into the intermediate `c` (row-major `C[j2][i1]`).
    unsafe fn step1_tile(
        input: *const u32,
        c: *mut u32,
        t: usize,
        tb: &FourStepTables,
        colbuf: &mut Aligned,
    ) {
        let cb = colbuf.ptr();
        let lo0 = ld(tb.lo.as_ptr().add(TILE * t));
        let lo1 = ld(tb.lo.as_ptr().add(TILE * t + 8));
        for i2 in (0..N2).step_by(8) {
            let mut r0 = [_mm256_setzero_si256(); 8];
            let mut r1 = [_mm256_setzero_si256(); 8];
            for r in 0..8 {
                let row = i2 + r;
                let h = _mm256_set1_epi32(tb.hi[row] as i32);
                let base = input.add(row * N1 + TILE * t);
                r0[r] = avx2::mont_mul(avx2::mont_mul(ld(base), lo0), h);
                r1[r] = avx2::mont_mul(avx2::mont_mul(ld(base.add(8)), lo1), h);
            }
            avx2::transpose_8x8(&mut r0);
            avx2::transpose_8x8(&mut r1);
            for k in 0..8 {
                st(cb.add(k * N2 + i2), r0[k]);
                st(cb.add((8 + k) * N2 + i2), r1[k]);
            }
        }
        for k in 0..TILE {
            let col = core::slice::from_raw_parts_mut(cb.add(k * N2), N2);
            fft::bitreverse_enumeration_inplace(col);
            avx2::ntt_bitrev_to_natural(col, 12, &tb.tw12, &tb.ao12, &tb.bo12);
            let (pw, step) = tb.col_tw[TILE * t + k];
            let mut v = ld(pw.as_ptr());
            let step = _mm256_set1_epi32(step as i32);
            let p = cb.add(k * N2);
            for j2 in (0..N2).step_by(8) {
                st(p.add(j2), avx2::mont_mul(ld(p.add(j2)), v));
                v = avx2::mont_mul(v, step);
            }
        }
        for j2 in (0..N2).step_by(8) {
            let mut r0: [__m256i; 8] = core::array::from_fn(|k| ld(cb.add(k * N2 + j2)));
            let mut r1: [__m256i; 8] = core::array::from_fn(|k| ld(cb.add((8 + k) * N2 + j2)));
            avx2::transpose_8x8(&mut r0);
            avx2::transpose_8x8(&mut r1);
            for r in 0..8 {
                let dst = c.add((j2 + r) * N1 + TILE * t);
                st(dst, r0[r]);
                st(dst.add(8), r1[r]);
            }
        }
    }

    /// Step 2 for rows `16g..16g+16` of the intermediate: per-row NTT in a
    /// cache buffer, then the transposed natural-order write
    /// `out[j2 + N2*j1]`.
    unsafe fn step2_group(
        c: *const u32,
        out: *mut u32,
        g: usize,
        tb: &FourStepTables,
        rowbuf: &mut Aligned,
    ) {
        let rb = rowbuf.ptr();
        for r in 0..TILE {
            let j2 = TILE * g + r;
            core::ptr::copy_nonoverlapping(c.add(j2 * N1), rb.add(r * N1), N1);
            let row = core::slice::from_raw_parts_mut(rb.add(r * N1), N1);
            fft::bitreverse_enumeration_inplace(row);
            avx2::ntt_bitrev_to_natural(row, 12, &tb.tw12, &tb.ao12, &tb.bo12);
        }
        for j1 in (0..N1).step_by(8) {
            let mut r0: [__m256i; 8] = core::array::from_fn(|r| ld(rb.add(r * N1 + j1)));
            let mut r1: [__m256i; 8] = core::array::from_fn(|r| ld(rb.add((8 + r) * N1 + j1)));
            avx2::transpose_8x8(&mut r0);
            avx2::transpose_8x8(&mut r1);
            for k in 0..8 {
                let dst = out.add((j1 + k) * N2 + TILE * g);
                st(dst, r0[k]);
                st(dst.add(8), r1[k]);
            }
        }
    }

    /// The four-step coset LDE of one 2^24 column on the worker: tiles and
    /// row groups are balanced over the threads; each task owns a 256 KB
    /// cache buffer.
    pub fn four_step_lde(input: &[u32], tb: &FourStepTables, worker: &Worker) -> Vec<u32> {
        assert_eq!(input.len(), N);
        let mut c: Vec<u32> = Vec::with_capacity(N);
        let mut out: Vec<u32> = Vec::with_capacity(N);
        #[allow(clippy::uninit_vec)]
        unsafe {
            c.set_len(N);
            out.set_len(N);
        }
        let (in_addr, c_addr, out_addr) = (
            input.as_ptr() as usize,
            c.as_mut_ptr() as usize,
            out.as_mut_ptr() as usize,
        );
        let tiles = N1 / TILE;
        worker.scope(tiles, |scope, geometry| {
            for idx in 0..geometry.len() {
                let start = geometry.get_chunk_start_pos(idx);
                let size = geometry.get_chunk_size(idx);
                scope.spawn(move |_| {
                    let mut colbuf = Aligned::new(TILE * N2);
                    for t in start..start + size {
                        unsafe {
                            step1_tile(
                                in_addr as *const u32,
                                c_addr as *mut u32,
                                t,
                                tb,
                                &mut colbuf,
                            )
                        };
                    }
                });
            }
        });
        let groups = N2 / TILE;
        worker.scope(groups, |scope, geometry| {
            for idx in 0..geometry.len() {
                let start = geometry.get_chunk_start_pos(idx);
                let size = geometry.get_chunk_size(idx);
                scope.spawn(move |_| {
                    let mut rowbuf = Aligned::new(TILE * N1);
                    for g in start..start + size {
                        unsafe {
                            step2_group(
                                c_addr as *const u32,
                                out_addr as *mut u32,
                                g,
                                tb,
                                &mut rowbuf,
                            )
                        };
                    }
                });
            }
        });
        drop(c);
        out
    }

    pub fn run() {
        use std::sync::{Arc, Barrier};
        use std::time::Instant;
        let args: Vec<String> = std::env::args().collect();
        let (mut outer, mut inner, mut cols, mut lde, mut reps, mut pin) =
            (12usize, 16usize, 48usize, 2usize, 1usize, true);
        let mut i = 1;
        while i < args.len() {
            match args[i].as_str() {
                "--outer" => outer = args[i + 1].parse().unwrap(),
                "--inner" => inner = args[i + 1].parse().unwrap(),
                "--cols" => cols = args[i + 1].parse().unwrap(),
                "--lde" => lde = args[i + 1].parse().unwrap(),
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
        println!("[sixstep] outer={outer} x inner={inner}, cols={cols}, lde={lde}, reps={reps}, pin={pin}: {} column-cosets of 2^{LOG_N} per worker", cols * lde);
        let cpu_blocks: Vec<Vec<usize>> = if pin {
            let complexes = Worker::cpu_complexes();
            let flat: Vec<usize> = complexes.iter().flatten().copied().collect();
            assert!(outer * inner <= flat.len());
            (0..outer)
                .map(|w| flat[w * inner..(w + 1) * inner].to_vec())
                .collect()
        } else {
            Vec::new()
        };

        // shared read-only tables
        let setup_worker = Worker::new_with_num_threads(outer * inner);
        let tw_full: Vec<F, Global> =
            fft::precompute_all_twiddles_for_fft_serial::<F, Global, false>(N);
        let ext_full = Avx2TwiddleExt::build_parallel(&tw_full, N, &setup_worker);
        let root = fft::domain_generator_for_size::<F>((N * lde) as u64);
        let offsets: Vec<F> =
            fft::materialize_powers_serial_starting_with_one::<F, Global>(root, lde);
        let tables: Vec<FourStepTables> = offsets.iter().map(|&o| FourStepTables::new(o)).collect();
        drop(setup_worker);
        let tw_full = Arc::new(tw_full);
        let ext_full = Arc::new(ext_full);
        let tables = Arc::new(tables);
        let offsets = Arc::new(offsets);

        // per-worker inputs: `cols` random monomial-form columns
        let inputs: Vec<Vec<Vec<F>>> = (0..outer)
            .map(|w| {
                (0..cols)
                    .map(|cidx| {
                        (0..N)
                            .map(|k| {
                                F::from_u32_with_reduction(
                                    (k as u32).wrapping_mul(2654435761)
                                        ^ ((w * cols + cidx) as u32).wrapping_mul(0x9E3779B9),
                                )
                            })
                            .collect()
                    })
                    .collect()
            })
            .collect();

        // correctness: four-step == blocked kernel on one column, every coset
        {
            let w = Worker::new_with_num_threads(inner);
            let col = &inputs[0][0];
            let col_raw: &[u32] =
                unsafe { core::slice::from_raw_parts(col.as_ptr() as *const u32, N) };
            for (ci, &off) in offsets.iter().enumerate() {
                let reference =
                    fft::baby_bear_avx2::lde_coset_avx2_parallel(col, off, &tw_full, &ext_full, &w);
                let ref_raw: &[u32] =
                    unsafe { core::slice::from_raw_parts(reference.as_ptr() as *const u32, N) };
                let got = four_step_lde(col_raw, &tables[ci], &w);
                assert_eq!(&got[..], ref_raw, "four-step LDE diverged at coset {ci}");
            }
            println!(
                "[sixstep] correctness: four-step == blocked kernel on {} cosets",
                offsets.len()
            );
        }

        for variant in ["blocked (current)", "four-step (L2-resident)"] {
            for mode in ["solo", "batch"] {
                let active = if mode == "solo" { 1 } else { outer };
                let barrier = Arc::new(Barrier::new(active));
                let times: Vec<f64> = std::thread::scope(|s| {
                    let handles: Vec<_> = (0..active)
                        .map(|w| {
                            let (barrier, tw_full, ext_full, tables, offsets, cpu_blocks, inputs) =
                                (barrier.clone(), tw_full.clone(), ext_full.clone(), tables.clone(), offsets.clone(), &cpu_blocks, &inputs);
                            std::thread::Builder::new()
                                .stack_size(1 << 30)
                                .spawn_scoped(s, move || {
                                    let worker = if pin {
                                        Worker::new_with_num_threads_on_cpus_and_stack(inner, &cpu_blocks[w], POOL_STACK)
                                    } else {
                                        Worker::new_with_num_threads_and_stack(inner, POOL_STACK)
                                    };
                                    worker.pool.install(|| {
                                        let mut best = f64::MAX;
                                        for _ in 0..reps {
                                            barrier.wait();
                                            let t0 = Instant::now();
                                            let mut outs: Vec<Vec<u32>> = Vec::with_capacity(cols * offsets.len());
                                            for col in inputs[w].iter() {
                                                let col_raw: &[u32] = unsafe { core::slice::from_raw_parts(col.as_ptr() as *const u32, N) };
                                                for (ci, &off) in offsets.iter().enumerate() {
                                                    if variant.starts_with("blocked") {
                                                        let v = fft::baby_bear_avx2::lde_coset_avx2_parallel(col, off, &tw_full, &ext_full, &worker);
                                                        outs.push(unsafe { core::mem::transmute::<Vec<F>, Vec<u32>>(v) });
                                                    } else {
                                                        outs.push(four_step_lde(col_raw, &tables[ci], &worker));
                                                    }
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
                let bytes = (active * cols * lde * N * 4) as f64;
                println!(
                    "[sixstep] {variant:<26} {mode:<5} ({active:2} workers): slowest {slowest:.3} s, mean {mean:.3} s | {:.1} ms per column-coset per worker | {:.1} GB/s aggregate output",
                    1e3 * mean / (cols * lde) as f64,
                    bytes / slowest / 1e9
                );
            }
        }
        println!("[sixstep] done");
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
fn main() {
    imp::run();
}
