// #![feature(allocator_api)]
// #![feature(custom_test_frameworks)]
// #![test_runner(criterion::runner)]
//
// use zksync_airbender::compiler::AirCompiler;
// use cs::config::Config;
// use cs::cs_reference::BasicAssembly;
// use zksync_airbender::devices::executor::run;
// use std::alloc::Global;
//
// use fft::Twiddles;
// use criterion::{criterion_group, criterion_main, Bencher, BenchmarkId, Criterion};
// use era_criterion_cuda::CudaMeasurement;
// use era_cudart::memory::DeviceAllocation;
// use era_cudart::stream::CudaStream;
//
// use gpu_prover::context::Context;
// use gpu_prover::field::Ext2Field;
// use gpu_prover::quotient::{compute_quotient, quotient_precompute, Precompute};
// use gpu_prover::utils::memcpy_to_symbol;
//
// type E2 = Ext2Field;
//
// fn quotient(c: &mut Criterion<CudaMeasurement>) {
//     const MIN_LOG_N: usize = 15;
//     const MAX_LOG_N: usize = 22;
//     const COLUMNS_COUNT: usize = 112;
//     const VALUES_COUNT: usize = COLUMNS_COUNT << MAX_LOG_N;
//     let d_values = DeviceAllocation::alloc(VALUES_COUNT).unwrap();
//     let mut d_results = DeviceAllocation::alloc(1 << MAX_LOG_N).unwrap();
//     let _context = Context::create(12).unwrap();
//     let stream = CudaStream::default();
//     let mut bench_fn = |b: &mut Bencher<CudaMeasurement>, log_n: &usize| {
//         let values_count = COLUMNS_COUNT << log_n;
//         let values = &d_values[0..values_count];
//         let results_count = 1 << log_n;
//         let results = &mut d_results[0..results_count];
//         let quotient_degree = (1 << (log_n + 1)) - 1;
//         let cs_config = Config::new_default();
//         let cs_output = run::<_, BasicAssembly<_>>(cs_config, true);
//         let zksync_airbender = AirCompiler::<_>::init();
//         let air_cs = zksync_airbender.synthesize(&cs_output, &cs_config);
//         let twiddles =
//             Twiddles::<E2, Global>::precompute_all_twiddles_for_fft_serial(1 << log_n, 2);
//         let precompute = Precompute::new(&air_cs, &twiddles, quotient_degree);
//         unsafe {
//             memcpy_to_symbol(&quotient_precompute, &precompute).unwrap();
//         }
//         b.iter(|| {
//             compute_quotient(values, 0, results, &stream).unwrap();
//             stream.synchronize().unwrap();
//         })
//     };
//     let mut group = c.benchmark_group("quotient");
//     for log_n in MIN_LOG_N..=MAX_LOG_N {
//         group.bench_with_input(BenchmarkId::from_parameter(log_n), &log_n, &mut bench_fn);
//     }
//     group.finish();
// }
//
// criterion_group!(
//     name = bench_quotient;
//     config = Criterion::default().with_measurement::<CudaMeasurement>(CudaMeasurement{});
//     targets = quotient
// );
// criterion_main!(bench_quotient);
