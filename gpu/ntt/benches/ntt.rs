#![feature(custom_test_frameworks)]
#![test_runner(criterion::runner)]

use criterion::{criterion_group, criterion_main, Bencher, Criterion};
use era_criterion_cuda::CudaMeasurement;
use era_cudart::stream::CudaStream;
use gpu_ntt::bench::{is_valid, DitBenchHarness, LaunchCfg, TOTAL_LOG};

// Wrapper matrices (must match the bench-gated EXTERN symbol set in
// `gpu/ntt/native/bench/dit_bench_kernels.cu` + the production two-pass stream
// symbols). Two-pass covers log_n in [8, 13]; single-pass covers log_n in [2, 8].
const TWO_PASS_CONFIGS: &[(usize, usize)] = &[
    (9, 3),
    (10, 3),
    (11, 3),
    (12, 3),
    (13, 3),
    (8, 2),
    (9, 2),
    (10, 2),
    (11, 2),
    (12, 2),
];
const SINGLE_CONFIGS: &[(usize, usize)] = &[
    (3, 3),
    (4, 3),
    (5, 3),
    (6, 3),
    (7, 3),
    (8, 3),
    (2, 2),
    (3, 2),
    (4, 2),
    (5, 2),
    (6, 2),
    (7, 2),
];

const KS: &[u32] = &[1, 2, 4, 8, 16];

/// Two-pass STREAM: sweep `grid = 1 << log_grid` for `log_grid` in
/// `0..=(27 - log_n)` (a pow2 divisor of `num_cosets`). One harness per
/// `(log_n, log_vpt)`, reused across the grid sweep.
fn two_pass_stream(c: &mut Criterion<CudaMeasurement>) {
    let stream = CudaStream::default();
    let mut group = c.benchmark_group("dit/two_pass_stream");
    for &(log_n, log_vpt) in TWO_PASS_CONFIGS {
        let mut harness = DitBenchHarness::new(log_n, log_vpt, &stream).unwrap();
        let num_cosets = 1u32 << (TOTAL_LOG - log_n);
        for log_grid in 0..=(TOTAL_LOG - log_n) {
            let grid = 1u32 << log_grid;
            let cfg = LaunchCfg::TwoPassStream { grid };
            if !is_valid(log_n, log_vpt, cfg) {
                continue;
            }
            eprintln!("{}", harness.describe(&cfg));
            group.bench_function(
                format!("log_n_{log_n:02}_vpt{log_vpt}/grid_{grid:06}"),
                |b: &mut Bencher<CudaMeasurement>| {
                    b.iter(|| harness.run(cfg, &stream).unwrap());
                },
            );
        }
        // Exact one-wave grid (occupancy API) + 2x/4x oversubscription — the
        // principled launch the production launcher uses. Not a pow2, so NOT
        // covered by the sweep above.
        let ow = harness.one_wave_grid_two_pass().unwrap();
        for (mult, tag) in [(1u32, "ow01"), (2, "ow02"), (4, "ow04"), (8, "ow08"), (16, "ow16")] {
            let grid = ow.saturating_mul(mult).min(num_cosets).max(1);
            let cfg = LaunchCfg::TwoPassStream { grid };
            eprintln!("{} [{tag}=one_wave*{mult}]", harness.describe(&cfg));
            group.bench_function(
                format!("log_n_{log_n:02}_vpt{log_vpt}/{tag}_grid_{grid:06}"),
                |b: &mut Bencher<CudaMeasurement>| {
                    b.iter(|| harness.run(cfg, &stream).unwrap());
                },
            );
        }
    }
    group.finish();
}

/// Two-pass FIXED-K: sweep `k` in {1,2,4,8,16}. One harness per
/// `(log_n, log_vpt)`, reused across the k sweep.
fn two_pass_fixed(c: &mut Criterion<CudaMeasurement>) {
    let stream = CudaStream::default();
    let mut group = c.benchmark_group("dit/two_pass_fixed");
    for &(log_n, log_vpt) in TWO_PASS_CONFIGS {
        let mut harness = DitBenchHarness::new(log_n, log_vpt, &stream).unwrap();
        for &k in KS {
            let cfg = LaunchCfg::TwoPassFixed { k };
            if !is_valid(log_n, log_vpt, cfg) {
                continue;
            }
            eprintln!("{}", harness.describe(&cfg));
            group.bench_function(
                format!("log_n_{log_n:02}_vpt{log_vpt}/k_{k:02}"),
                |b: &mut Bencher<CudaMeasurement>| {
                    b.iter(|| harness.run(cfg, &stream).unwrap());
                },
            );
        }
    }
    group.finish();
}

/// Single-pass FIXED-K: sweep `k` in {1,2,4,8,16}, skipping combos whose
/// `slots_per_block * k` does not divide `num_cosets`.
fn single_fixed(c: &mut Criterion<CudaMeasurement>) {
    let stream = CudaStream::default();
    let mut group = c.benchmark_group("dit/single_fixed");
    for &(log_n, log_vpt) in SINGLE_CONFIGS {
        let mut harness = DitBenchHarness::new(log_n, log_vpt, &stream).unwrap();
        for &k in KS {
            let cfg = LaunchCfg::SinglePassFixed { k };
            if !is_valid(log_n, log_vpt, cfg) {
                continue;
            }
            eprintln!("{}", harness.describe(&cfg));
            group.bench_function(
                format!("log_n_{log_n:02}_vpt{log_vpt}/k_{k:02}"),
                |b: &mut Bencher<CudaMeasurement>| {
                    b.iter(|| harness.run(cfg, &stream).unwrap());
                },
            );
        }
    }
    group.finish();
}

/// Single-pass STREAM: sweep `grid = 1 << log_grid` for `log_grid` in
/// `0..=(27 - log_n)`, skipping combos where `grid * slots_per_block` does not
/// divide `num_cosets`.
fn single_stream(c: &mut Criterion<CudaMeasurement>) {
    let stream = CudaStream::default();
    let mut group = c.benchmark_group("dit/single_stream");
    for &(log_n, log_vpt) in SINGLE_CONFIGS {
        let mut harness = DitBenchHarness::new(log_n, log_vpt, &stream).unwrap();
        let num_cosets = 1u32 << (TOTAL_LOG - log_n);
        for log_grid in 0..=(TOTAL_LOG - log_n) {
            let grid = 1u32 << log_grid;
            let cfg = LaunchCfg::SinglePassStream { grid };
            if !is_valid(log_n, log_vpt, cfg) {
                continue;
            }
            eprintln!("{}", harness.describe(&cfg));
            group.bench_function(
                format!("log_n_{log_n:02}_vpt{log_vpt}/grid_{grid:06}"),
                |b: &mut Bencher<CudaMeasurement>| {
                    b.iter(|| harness.run(cfg, &stream).unwrap());
                },
            );
        }
        let ow = harness.one_wave_grid_single().unwrap();
        for (mult, tag) in [(1u32, "ow01"), (2, "ow02"), (4, "ow04"), (8, "ow08"), (16, "ow16")] {
            let grid = ow.saturating_mul(mult).min(num_cosets).max(1);
            let cfg = LaunchCfg::SinglePassStream { grid };
            eprintln!("{} [{tag}=one_wave*{mult}]", harness.describe(&cfg));
            group.bench_function(
                format!("log_n_{log_n:02}_vpt{log_vpt}/{tag}_grid_{grid:06}"),
                |b: &mut Bencher<CudaMeasurement>| {
                    b.iter(|| harness.run(cfg, &stream).unwrap());
                },
            );
        }
    }
    group.finish();
}

criterion_group!(
    name = ntt;
    config = Criterion::default().with_measurement(CudaMeasurement);
    targets = two_pass_stream, two_pass_fixed, single_fixed, single_stream,
);
criterion_main!(ntt);
