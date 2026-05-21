#![feature(custom_test_frameworks)]
#![test_runner(criterion::runner)]

use criterion::{criterion_group, criterion_main, Bencher, Criterion};
use era_criterion_cuda::CudaMeasurement;
use era_cudart::stream::CudaStream;
use gpu_prover::bench::ntt::NttBenchHarness;

// log_n values to sweep. Covers the strategy's full supported range so both
// the compact-1-pass and 2-pass-compact-initial paths get measured, plus the
// 21-24 multi-pass kernels for completeness.
const LOG_NS: &[usize] = &[4, 6, 8, 10, 12, 13, 14, 15, 16, 18, 20, 21, 22, 24];
const LOG_LDE_FACTOR: usize = 2;
const COSET_INDEX: usize = 1;

fn new_path(c: &mut Criterion<CudaMeasurement>) {
    let stream = CudaStream::default();
    let mut group = c.benchmark_group("ntt_new");
    for &log_n in LOG_NS {
        let mut harness = NttBenchHarness::new(log_n, LOG_LDE_FACTOR, COSET_INDEX).unwrap();
        group.bench_function(format!("log_n_{log_n:02}"), |b: &mut Bencher<CudaMeasurement>| {
            b.iter(|| {
                harness.run_new_path(&stream).unwrap();
            })
        });
    }
    group.finish();
}

fn old_path(c: &mut Criterion<CudaMeasurement>) {
    let stream = CudaStream::default();
    let mut group = c.benchmark_group("ntt_old_single_stage");
    for &log_n in LOG_NS {
        let mut harness = NttBenchHarness::new(log_n, LOG_LDE_FACTOR, COSET_INDEX).unwrap();
        group.bench_function(format!("log_n_{log_n:02}"), |b: &mut Bencher<CudaMeasurement>| {
            b.iter(|| {
                harness.run_old_path(&stream).unwrap();
            })
        });
    }
    group.finish();
}

criterion_group!(
    name = ntt;
    config = Criterion::default().with_measurement(CudaMeasurement);
    targets = new_path, old_path,
);
criterion_main!(ntt);
