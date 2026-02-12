// #![feature(custom_test_frameworks)]
// #![test_runner(criterion::runner)]
//
// use std::cell::RefCell;
// use std::mem::size_of;
//
// use criterion::{criterion_group, criterion_main, Bencher, Criterion, Throughput};
// use era_criterion_cuda::CudaMeasurement;
// use era_cudart::memory::DeviceAllocation;
// use era_cudart::result::CudaResult;
// use era_cudart::slice::DeviceSlice;
// use era_cudart::stream::CudaStream;
//
// use gpu_prover::field::BaseField;
// use gpu_prover::monolith::*;
//
// type BF = BaseField;
// type LeavesFn = fn(&DeviceSlice<BF>, &mut DeviceSlice<Digest>, u32, &CudaStream) -> CudaResult<()>;
//
// type NodesFn = fn(&DeviceSlice<Digest>, &mut DeviceSlice<Digest>, &CudaStream) -> CudaResult<()>;
//
// fn leaves(c: &mut Criterion<CudaMeasurement>) {
//     const MIN_LOG_N: usize = 8;
//     const MAX_LOG_N: usize = 24;
//     const COLUMNS_COUNT: usize = 112;
//     const LOG_ROWS_PER_HASH: usize = 0;
//     const VALUES_COUNT: usize = COLUMNS_COUNT << (MAX_LOG_N + LOG_ROWS_PER_HASH);
//     let d_values = DeviceAllocation::alloc(VALUES_COUNT).unwrap();
//     let mut d_results = DeviceAllocation::alloc(1 << MAX_LOG_N).unwrap();
//     let stream = CudaStream::default();
//     let bench_fn = |b: &mut Bencher<CudaMeasurement>, parameter: &(usize, LeavesFn)| {
//         let (log_n, leaves_fn) = *parameter;
//         let values_count = COLUMNS_COUNT << (log_n + LOG_ROWS_PER_HASH);
//         let values = &d_values[0..values_count];
//         let results_count = 1 << log_n;
//         let results = &mut d_results[0..results_count];
//         b.iter(|| leaves_fn(values, results, LOG_ROWS_PER_HASH as u32, &stream).unwrap())
//     };
//     let bench_fn_ref = RefCell::new(bench_fn);
//     let mut group = c.benchmark_group("leaves");
//     for log_n in MIN_LOG_N..=MAX_LOG_N {
//         let hashes_count = ((COLUMNS_COUNT - RATE) << (log_n + LOG_ROWS_PER_HASH)) / RATE;
//         let bytes_count = (COLUMNS_COUNT * size_of::<BF>()) << (log_n + LOG_ROWS_PER_HASH);
//         group.throughput(Throughput::Elements(hashes_count as u64));
//         group.throughput(Throughput::Bytes(bytes_count as u64));
//         group.bench_with_input(
//             format!("{}/st", log_n),
//             &(log_n, launch_leaves_st_kernel as LeavesFn),
//             |b, p| bench_fn_ref.borrow_mut()(b, p),
//         );
//         group.bench_with_input(
//             format!("{}/mt", log_n),
//             &(log_n, launch_leaves_mt_kernel as LeavesFn),
//             |b, p| bench_fn_ref.borrow_mut()(b, p),
//         );
//         group.bench_with_input(
//             format!("{}", log_n),
//             &(log_n, launch_leaves_kernel as LeavesFn),
//             |b, p| bench_fn_ref.borrow_mut()(b, p),
//         );
//     }
//     group.finish();
// }
//
// fn nodes(c: &mut Criterion<CudaMeasurement>) {
//     const MIN_LOG_N: usize = 8;
//     const MAX_LOG_N: usize = 24;
//     let d_values = DeviceAllocation::alloc(1 << (MAX_LOG_N + 1)).unwrap();
//     let mut d_results = DeviceAllocation::alloc(1 << MAX_LOG_N).unwrap();
//     let stream = CudaStream::default();
//     let bench_fn = |b: &mut Bencher<CudaMeasurement>, parameter: &(usize, NodesFn)| {
//         let (log_n, nodes_fn) = *parameter;
//         let values_count = 1 << (log_n + 1);
//         let values = &d_values[0..values_count];
//         let results_count = 1 << log_n;
//         let results = &mut d_results[0..results_count];
//         b.iter(|| nodes_fn(values, results, &stream).unwrap())
//     };
//     let bench_fn_ref = RefCell::new(bench_fn);
//     let mut group = c.benchmark_group("nodes");
//     for log_n in MIN_LOG_N..=MAX_LOG_N {
//         let hashes_count = 1 << log_n;
//         let bytes_count = hashes_count * size_of::<Digest>() * 2;
//         group.throughput(Throughput::Bytes(bytes_count as u64));
//         group.throughput(Throughput::Elements(hashes_count as u64));
//         group.bench_with_input(
//             format!("{}/st", log_n),
//             &(log_n, launch_nodes_st_kernel as NodesFn),
//             |b, p| bench_fn_ref.borrow_mut()(b, p),
//         );
//         group.bench_with_input(
//             format!("{}/mt", log_n),
//             &(log_n, launch_nodes_mt_kernel as NodesFn),
//             |b, p| bench_fn_ref.borrow_mut()(b, p),
//         );
//         group.bench_with_input(
//             format!("{}", log_n),
//             &(log_n, launch_nodes_kernel as NodesFn),
//             |b, p| bench_fn_ref.borrow_mut()(b, p),
//         );
//     }
//     group.finish();
// }
//
// fn tree(c: &mut Criterion<CudaMeasurement>) {
//     const MIN_LOG_N: usize = 8;
//     const MAX_LOG_N: usize = 24;
//     const COLUMNS_COUNT: usize = 112;
//     const LOG_ROWS_PER_HASH: usize = 0;
//     const VALUES_COUNT: usize = COLUMNS_COUNT << (MAX_LOG_N + LOG_ROWS_PER_HASH);
//     let d_values = DeviceAllocation::alloc(VALUES_COUNT).unwrap();
//     let mut d_results = DeviceAllocation::alloc(1 << (MAX_LOG_N + 1)).unwrap();
//     let stream = CudaStream::default();
//     let mut group = c.benchmark_group("tree");
//     for log_n in MIN_LOG_N..=MAX_LOG_N {
//         let hashes_count = (COLUMNS_COUNT << (log_n + LOG_ROWS_PER_HASH)) / RATE;
//         group.throughput(Throughput::Elements(hashes_count as u64));
//         group.bench_with_input(
//             format!("{}", log_n),
//             &log_n,
//             |b: &mut Bencher<CudaMeasurement>, log_n: &usize| {
//                 let values_count = COLUMNS_COUNT << (log_n + LOG_ROWS_PER_HASH);
//                 let values = &d_values[0..values_count];
//                 let results_count = 1 << (log_n + 1);
//                 let results = &mut d_results[0..results_count];
//                 let layers_count: u32 = (log_n + 1) as u32;
//                 b.iter(|| {
//                     build_merkle_tree(
//                         values,
//                         results,
//                         LOG_ROWS_PER_HASH as u32,
//                         &stream,
//                         layers_count,
//                     )
//                     .unwrap();
//                 })
//             },
//         );
//     }
//     group.finish();
// }
//
// criterion_group!(
//     name = bench_monolith;
//     config = Criterion::default().with_measurement::<CudaMeasurement>(CudaMeasurement{});
//     targets = leaves, nodes, tree
// );
// criterion_main!(bench_monolith);
