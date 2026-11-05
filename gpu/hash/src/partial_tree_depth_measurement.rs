use era_cudart::event::{elapsed_time, CudaEvent};
use era_cudart::memory::{memory_copy_async, DeviceAllocation};
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use gpu_core::primitives::field::{BF, PR};
use gpu_core::primitives::utils::LOG_WARP_SIZE;

use crate::blake2s::{
    build_partial_merkle_tree_multi_coset_physical,
    gather_merkle_paths_partial_for_queries_single_coset_physical,
    MAX_PARTIAL_TREE_REDUCTION_LAYERS, STATE_SIZE,
};
use crate::keccak256::{
    build_partial_coset_tree, build_partial_coset_tree_with_scratch,
    gather_merkle_paths_partial_for_queries_single_coset, partial_coset_tree_scratch_len,
};

const WARMUP_SWEEPS: usize = 2;
const MEASURED_SWEEPS: usize = 6;

struct Shape {
    name: &'static str,
    log_domain: u32,
    log_lde: u32,
    log_rows_per_leaf: u32,
    log_cap: u32,
    columns: usize,
    queries: usize,
}

const BLAKE2S_SHAPES: [Shape; 2] = [
    Shape {
        name: "feeder_merged",
        log_domain: 23,
        log_lde: 4,
        log_rows_per_leaf: 1,
        log_cap: 4,
        columns: 104,
        queries: 21,
    },
    Shape {
        name: "feeder_setup",
        log_domain: 23,
        log_lde: 4,
        log_rows_per_leaf: 1,
        log_cap: 4,
        columns: 10,
        queries: 21,
    },
];

const KECCAK_SHAPES: [Shape; 2] = [
    Shape {
        name: "wrap_packed_merged",
        log_domain: 26,
        log_lde: 5,
        log_rows_per_leaf: 2,
        log_cap: 3,
        columns: 7,
        queries: 17,
    },
    Shape {
        name: "wrap_packed_setup",
        log_domain: 26,
        log_lde: 5,
        log_rows_per_leaf: 2,
        log_cap: 3,
        columns: 1,
        queries: 17,
    },
];

fn queries(shape: &Shape, seed: u64) -> Vec<u32> {
    let log_total = shape.log_domain - shape.log_rows_per_leaf + shape.log_lde;
    let mut state = seed;
    (0..shape.queries)
        .map(|_| {
            state = state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            ((state >> 32) as u32) & ((1u32 << log_total) - 1)
        })
        .collect()
}

fn fill_random(dst: &mut DeviceSlice<u32>, seed: u64, stream: &CudaStream) {
    const CHUNK: usize = 1 << 26;
    let mut state = seed;
    let mut host = vec![0u32; CHUNK.min(dst.len())];
    for start in (0..dst.len()).step_by(CHUNK) {
        let len = CHUNK.min(dst.len() - start);
        for word in &mut host[..len] {
            state = state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            *word = (state >> 33) as u32;
        }
        memory_copy_async(&mut dst[start..start + len], &host[..len], stream).unwrap();
        stream.synchronize().unwrap();
    }
}

fn named_queries(shape: &Shape) -> Vec<u32> {
    let leaves = 1u32 << (shape.log_domain - shape.log_rows_per_leaf);
    let subtree = 1u32 << MAX_PARTIAL_TREE_REDUCTION_LAYERS;
    let internals = [
        0,
        1,
        subtree - 1,
        subtree,
        leaves - subtree - 1,
        leaves - subtree,
        leaves - 2,
        leaves - 1,
    ];
    (0..1u32 << shape.log_lde)
        .flat_map(|coset| internals.map(|leaf| (leaf << shape.log_lde) | coset))
        .collect()
}

fn download<T: Copy + Default>(device: &DeviceSlice<T>, stream: &CudaStream) -> Vec<T> {
    let mut host = vec![T::default(); device.len()];
    memory_copy_async(&mut host, device, stream).unwrap();
    stream.synchronize().unwrap();
    host
}

fn sweep_order(sweep: usize) -> Vec<u32> {
    let ascending: Vec<u32> = (LOG_WARP_SIZE..=MAX_PARTIAL_TREE_REDUCTION_LAYERS).collect();
    if sweep.is_multiple_of(2) {
        ascending
    } else {
        ascending.into_iter().rev().collect()
    }
}

fn timed(stream: &CudaStream, mut work: impl FnMut()) -> f32 {
    let start = CudaEvent::create().unwrap();
    let end = CudaEvent::create().unwrap();
    start.record(stream).unwrap();
    work();
    end.record(stream).unwrap();
    end.synchronize().unwrap();
    elapsed_time(&start, &end).unwrap()
}

fn report(
    shape: &Shape,
    reduction_layers: u32,
    retained_bytes: usize,
    scratch_bytes: usize,
    build: &[f32],
    gather: &[f32],
) {
    let median = |samples: &[f32]| {
        let mut sorted = samples.to_vec();
        sorted.sort_by(f32::total_cmp);
        (sorted[sorted.len() / 2 - 1] + sorted[sorted.len() / 2]) / 2.0
    };
    println!(
        "PTREE {{\"shape\":\"{}\",\"L\":{},\"retained_bytes\":{},\"scratch_bytes\":{},\"build_ms\":{:?},\"gather_ms\":{:?},\"build_median_ms\":{},\"gather_median_ms\":{}}}",
        shape.name,
        reduction_layers,
        retained_bytes,
        scratch_bytes,
        build,
        gather,
        median(build),
        median(gather),
    );
}

fn measure_blake2s(shape: &Shape, stream: &CudaStream) {
    let cosets = 1usize << shape.log_lde;
    let coset_values_len = shape.columns << shape.log_domain;
    let mut values = DeviceAllocation::<BF>::alloc(coset_values_len).unwrap();
    fill_random(unsafe { values.transmute_mut() }, 0x243f_6a88, stream);
    let log_leaves = shape.log_domain - shape.log_rows_per_leaf;
    let log_coset_cap = shape.log_cap - shape.log_lde;
    let layers_count = log_leaves - log_coset_cap;
    let query_host = queries(shape, 0x9e37_79b9);
    let mut query_device = DeviceAllocation::<u32>::alloc(query_host.len()).unwrap();
    memory_copy_async(&mut query_device, &query_host, stream).unwrap();
    let mut paths =
        DeviceAllocation::<u32>::alloc(query_host.len() * layers_count as usize * STATE_SIZE)
            .unwrap();
    let mut scratch = DeviceAllocation::alloc(1usize << (log_leaves - LOG_WARP_SIZE)).unwrap();
    let depths: Vec<u32> = (LOG_WARP_SIZE..=MAX_PARTIAL_TREE_REDUCTION_LAYERS).collect();
    let mut trees: Vec<DeviceAllocation<[u32; STATE_SIZE]>> = depths
        .iter()
        .map(|&l| DeviceAllocation::alloc(cosets << (log_leaves + 1 - l)).unwrap())
        .collect();
    let mut build = vec![Vec::new(); depths.len()];
    let mut gather = vec![Vec::new(); depths.len()];
    for sweep in 0..WARMUP_SWEEPS + MEASURED_SWEEPS {
        for reduction_layers in sweep_order(sweep) {
            let index = (reduction_layers - LOG_WARP_SIZE) as usize;
            let stride = 1usize << (log_leaves + 1 - reduction_layers);
            let tree = &mut trees[index];
            let build_ms = timed(stream, || {
                for coset in 0..cosets {
                    build_partial_merkle_tree_multi_coset_physical(
                        &values,
                        &mut tree[coset * stride..(coset + 1) * stride],
                        shape.log_rows_per_leaf,
                        log_leaves + 1 - reduction_layers - log_coset_cap,
                        1,
                        reduction_layers,
                        (reduction_layers != LOG_WARP_SIZE).then_some(&mut scratch[..]),
                        stream,
                    )
                    .unwrap();
                }
            });
            let gather_ms = timed(stream, || {
                for coset in 0..cosets {
                    gather_merkle_paths_partial_for_queries_single_coset_physical(
                        &values,
                        &tree[coset * stride..(coset + 1) * stride],
                        coset as u32,
                        shape.log_lde,
                        shape.log_domain,
                        shape.log_rows_per_leaf,
                        layers_count,
                        reduction_layers,
                        &query_device,
                        &mut paths,
                        stream,
                    )
                    .unwrap();
                }
            });
            if sweep >= WARMUP_SWEEPS {
                build[index].push(build_ms);
                gather[index].push(gather_ms);
            }
        }
    }
    let checks = named_queries(shape);
    let mut check_device = DeviceAllocation::<u32>::alloc(checks.len()).unwrap();
    memory_copy_async(&mut check_device, &checks, stream).unwrap();
    let mut check_paths =
        DeviceAllocation::<u32>::alloc(checks.len() * layers_count as usize * STATE_SIZE).unwrap();
    let cap_size = 1usize << log_coset_cap;
    let mut reference = None;
    let poison = vec![0xdead_beefu32; check_paths.len()];
    for (index, &reduction_layers) in depths.iter().enumerate() {
        let stride = 1usize << (log_leaves + 1 - reduction_layers);
        memory_copy_async(&mut check_paths, &poison, stream).unwrap();
        for coset in 0..cosets {
            gather_merkle_paths_partial_for_queries_single_coset_physical(
                &values,
                &trees[index][coset * stride..(coset + 1) * stride],
                coset as u32,
                shape.log_lde,
                shape.log_domain,
                shape.log_rows_per_leaf,
                layers_count,
                reduction_layers,
                &check_device,
                &mut check_paths,
                stream,
            )
            .unwrap();
        }
        let tree_host = download(&trees[index], stream);
        let caps: Vec<_> = (0..cosets)
            .flat_map(|coset| {
                tree_host[(coset + 1) * stride - 2 * cap_size..(coset + 1) * stride - cap_size]
                    .to_vec()
            })
            .collect();
        let paths_host = download(&check_paths, stream);
        assert!(
            paths_host
                .chunks(STATE_SIZE)
                .all(|digest| digest.iter().any(|&word| word != 0xdead_beef)),
            "{}: L={reduction_layers} left a path digest unwritten",
            shape.name
        );
        let outputs = (caps, paths_host);
        match &reference {
            None => reference = Some(outputs),
            Some(expected) => assert!(
                &outputs == expected,
                "{}: L={reduction_layers} caps/paths differ from L=5",
                shape.name
            ),
        }
        println!(
            "PTREE_CHECK {{\"shape\":\"{}\",\"L\":{},\"queries\":{},\"equal_to_L5\":true}}",
            shape.name,
            reduction_layers,
            checks.len()
        );
    }
    for (index, &reduction_layers) in depths.iter().enumerate() {
        let retained = (cosets << (log_leaves + 1 - reduction_layers)) * 32;
        let scratch_bytes = if reduction_layers == LOG_WARP_SIZE {
            0
        } else {
            (1usize << (log_leaves - LOG_WARP_SIZE)) * 32
        };
        report(
            shape,
            reduction_layers,
            retained,
            scratch_bytes,
            &build[index],
            &gather[index],
        );
    }
}

fn measure_keccak(shape: &Shape, stream: &CudaStream) {
    let cosets = 1usize << shape.log_lde;
    let coset_values_len = shape.columns << shape.log_domain;
    let mut values = DeviceAllocation::<PR>::alloc(coset_values_len).unwrap();
    fill_random(unsafe { values.transmute_mut() }, 0x1319_8a2e, stream);
    let log_leaves = shape.log_domain - shape.log_rows_per_leaf;
    let query_host = queries(shape, 0x7f4a_7c15);
    let mut query_device = DeviceAllocation::<u32>::alloc(query_host.len()).unwrap();
    memory_copy_async(&mut query_device, &query_host, stream).unwrap();
    let depth = (log_leaves + shape.log_lde - shape.log_cap) as usize;
    let mut paths = DeviceAllocation::<[u32; 8]>::alloc(query_host.len() * depth).unwrap();
    let depths: Vec<u32> = (LOG_WARP_SIZE..=MAX_PARTIAL_TREE_REDUCTION_LAYERS).collect();
    let retained_len = |l: u32| 2 * ((1usize << log_leaves) >> l) - 1;
    let mut trees: Vec<DeviceAllocation<[u32; 8]>> = depths
        .iter()
        .map(|&l| DeviceAllocation::alloc(cosets * retained_len(l)).unwrap())
        .collect();
    let scratch_len = partial_coset_tree_scratch_len(
        shape.log_domain,
        shape.log_rows_per_leaf,
        MAX_PARTIAL_TREE_REDUCTION_LAYERS,
    );
    let mut scratch = DeviceAllocation::<[u32; 8]>::alloc(scratch_len).unwrap();
    let mut build = vec![Vec::new(); depths.len()];
    let mut gather = vec![Vec::new(); depths.len()];
    for sweep in 0..WARMUP_SWEEPS + MEASURED_SWEEPS {
        for reduction_layers in sweep_order(sweep) {
            let index = (reduction_layers - LOG_WARP_SIZE) as usize;
            let per_coset = retained_len(reduction_layers);
            let needs_scratch = partial_coset_tree_scratch_len(
                shape.log_domain,
                shape.log_rows_per_leaf,
                reduction_layers,
            );
            let tree = &mut trees[index];
            let build_ms = timed(stream, || {
                for coset in 0..cosets {
                    let retained = &mut tree[coset * per_coset..(coset + 1) * per_coset];
                    if needs_scratch == 0 {
                        build_partial_coset_tree(
                            &values,
                            shape.log_domain,
                            shape.log_rows_per_leaf,
                            shape.columns as u32,
                            reduction_layers,
                            retained,
                            stream,
                        )
                        .unwrap();
                    } else {
                        build_partial_coset_tree_with_scratch(
                            &values,
                            shape.log_domain,
                            shape.log_rows_per_leaf,
                            shape.columns as u32,
                            reduction_layers,
                            retained,
                            &mut scratch[..needs_scratch],
                            stream,
                        )
                        .unwrap();
                    }
                }
            });
            let gather_ms = timed(stream, || {
                for coset in 0..cosets {
                    gather_merkle_paths_partial_for_queries_single_coset(
                        &values,
                        coset as u32,
                        shape.log_lde,
                        shape.log_domain,
                        shape.log_rows_per_leaf,
                        shape.log_cap,
                        reduction_layers,
                        &tree[coset * per_coset..(coset + 1) * per_coset],
                        &query_device,
                        &mut paths,
                        stream,
                    )
                    .unwrap();
                }
            });
            if sweep >= WARMUP_SWEEPS {
                build[index].push(build_ms);
                gather[index].push(gather_ms);
            }
        }
    }
    let checks = named_queries(shape);
    let mut check_device = DeviceAllocation::<u32>::alloc(checks.len()).unwrap();
    memory_copy_async(&mut check_device, &checks, stream).unwrap();
    let mut check_paths = DeviceAllocation::<[u32; 8]>::alloc(checks.len() * depth).unwrap();
    let mut reference = None;
    let poison = vec![[0xdead_beefu32; 8]; check_paths.len()];
    for (index, &reduction_layers) in depths.iter().enumerate() {
        let per_coset = retained_len(reduction_layers);
        memory_copy_async(&mut check_paths, &poison, stream).unwrap();
        for coset in 0..cosets {
            gather_merkle_paths_partial_for_queries_single_coset(
                &values,
                coset as u32,
                shape.log_lde,
                shape.log_domain,
                shape.log_rows_per_leaf,
                shape.log_cap,
                reduction_layers,
                &trees[index][coset * per_coset..(coset + 1) * per_coset],
                &check_device,
                &mut check_paths,
                stream,
            )
            .unwrap();
        }
        let tree_host = download(&trees[index], stream);
        let roots: Vec<_> = (0..cosets)
            .map(|coset| tree_host[(coset + 1) * per_coset - 1])
            .collect();
        let coset_paths: Vec<_> = download(&check_paths, stream)
            .chunks(depth)
            .flat_map(|path| path[..log_leaves as usize].to_vec())
            .collect();
        assert!(
            coset_paths
                .iter()
                .all(|digest| *digest != [0xdead_beefu32; 8]),
            "{}: L={reduction_layers} left a path digest unwritten",
            shape.name
        );
        let outputs = (roots, coset_paths);
        match &reference {
            None => reference = Some(outputs),
            Some(expected) => assert!(
                &outputs == expected,
                "{}: L={reduction_layers} roots/paths differ from L=5",
                shape.name
            ),
        }
        println!(
            "PTREE_CHECK {{\"shape\":\"{}\",\"L\":{},\"queries\":{},\"equal_to_L5\":true}}",
            shape.name,
            reduction_layers,
            checks.len()
        );
    }
    for (index, &reduction_layers) in depths.iter().enumerate() {
        let retained = cosets * retained_len(reduction_layers) * 32;
        let scratch_bytes = partial_coset_tree_scratch_len(
            shape.log_domain,
            shape.log_rows_per_leaf,
            reduction_layers,
        ) * 32;
        report(
            shape,
            reduction_layers,
            retained,
            scratch_bytes,
            &build[index],
            &gather[index],
        );
    }
}

#[test]
#[ignore]
fn partial_tree_depth_measurement() {
    let stream = CudaStream::default();
    for shape in &BLAKE2S_SHAPES {
        measure_blake2s(shape, &stream);
    }
    for shape in &KECCAK_SHAPES {
        measure_keccak(shape, &stream);
    }
}

#[test]
#[ignore]
fn partial_tree_depth_measurement_keccak() {
    let stream = CudaStream::default();
    for shape in &KECCAK_SHAPES {
        measure_keccak(shape, &stream);
    }
}
