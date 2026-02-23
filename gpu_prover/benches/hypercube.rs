#![feature(custom_test_frameworks)]
#![test_runner(criterion::runner)]

use std::time::Duration;

use criterion::{criterion_group, criterion_main, Bencher, BenchmarkId, Criterion, Throughput};
use era_criterion_cuda::CudaMeasurement;
use era_cudart::memory::{memory_copy_async, DeviceAllocation};
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;
use field::Field;
use gpu_prover::field::BF;
use gpu_prover::{
    hypercube_evals_into_coeffs_bitrev_bf, hypercube_evals_into_coeffs_bitrev_bf_in_place,
};

const LOG_ROWS: u32 = 24;
const COLS: usize = 10;

struct HypercubeBitrevBenchCase {
    rows: usize,
    d_src: DeviceAllocation<BF>,
    d_dst: DeviceAllocation<BF>,
}

impl HypercubeBitrevBenchCase {
    fn new(stream: &CudaStream) -> CudaResult<Self> {
        let rows = 1usize << LOG_ROWS;

        let mut d_src = DeviceAllocation::alloc(rows * COLS)?;
        let d_dst = DeviceAllocation::alloc(rows * COLS)?;

        // Fill once to avoid benchmarking uninitialized memory reads.
        let h_src = vec![BF::ZERO; rows * COLS];
        memory_copy_async(&mut d_src, &h_src, stream)?;
        stream.synchronize()?;

        Ok(Self { rows, d_src, d_dst })
    }

    fn run_out_of_place(&mut self, stream: &CudaStream) -> CudaResult<()> {
        for (src, dst) in self.d_src.chunks(self.rows).zip(self.d_dst.chunks_mut(self.rows)) {
            hypercube_evals_into_coeffs_bitrev_bf(src, dst, stream)?;
        }
        Ok(())
    }

    fn run_in_place(&mut self, stream: &CudaStream) -> CudaResult<()> {
        for src in self.d_src.chunks_mut(self.rows) {
            hypercube_evals_into_coeffs_bitrev_bf_in_place(src, stream)?;
        }
        Ok(())
    }

    fn bytes_per_transform(&self) -> u64 {
        // Approximate traffic: read + write per launch, with exactly 3 launches.
        ((self.rows * COLS) as u64) * (std::mem::size_of::<BF>() as u64) * 2 * 3
    }
}

fn benchmark_out_of_place(c: &mut Criterion<CudaMeasurement>) {
    let stream = CudaStream::default();
    let mut group = c.benchmark_group("hypercube_bitrev_bf_out_of_place");
    group.sample_size(10);
    group.warm_up_time(Duration::from_secs(1));
    group.measurement_time(Duration::from_secs(4));

    let mut bench_case = HypercubeBitrevBenchCase::new(&stream).unwrap();
    group.throughput(Throughput::Bytes(bench_case.bytes_per_transform()));
    group.bench_with_input(
        BenchmarkId::new("transform", format!("log_rows={LOG_ROWS}")),
        &LOG_ROWS,
        |b: &mut Bencher<CudaMeasurement>, _| {
            b.iter(|| {
                bench_case.run_out_of_place(&stream).unwrap();
                stream.synchronize().unwrap();
            })
        },
    );

    group.finish();
}

fn benchmark_in_place(c: &mut Criterion<CudaMeasurement>) {
    let stream = CudaStream::default();
    let mut group = c.benchmark_group("hypercube_bitrev_bf_in_place");
    group.sample_size(10);
    group.warm_up_time(Duration::from_secs(1));
    group.measurement_time(Duration::from_secs(4));

    let mut bench_case = HypercubeBitrevBenchCase::new(&stream).unwrap();
    group.throughput(Throughput::Bytes(bench_case.bytes_per_transform()));
    group.bench_with_input(
        BenchmarkId::new("transform", format!("log_rows={LOG_ROWS}")),
        &LOG_ROWS,
        |b: &mut Bencher<CudaMeasurement>, _| {
            b.iter(|| {
                bench_case.run_in_place(&stream).unwrap();
                stream.synchronize().unwrap();
            })
        },
    );

    group.finish();
}

criterion_group!(
    name = bench;
    config = Criterion::default().with_measurement::<CudaMeasurement>(CudaMeasurement {});
    targets = benchmark_out_of_place, benchmark_in_place
);
criterion_main!(bench);
