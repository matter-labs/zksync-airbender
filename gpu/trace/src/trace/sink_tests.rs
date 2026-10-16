use era_cudart::memory::{memory_copy, memory_copy_async, DeviceAllocation};
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use gpu_core::primitives::device_structures::{DeviceMatrix, DeviceMatrixMut};
use gpu_core::primitives::field::PR;
use gpu_hash::keccak256::{
    build_partial_coset_tree, build_partial_coset_tree_with_scratch, build_retained_layers,
    partial_coset_tree_scratch_len, reduce_digests, Digest,
};
use gpu_ntt::proth120::{
    convert_coset_leaves, dispatch, launch_suffix_micro, lde_coset, lde_coset_slot, CosetSource,
    DeviceContext, ScaleArgs, SuffixShape,
};

use super::packed::retained_len;
use super::sink::{launch_sink, sink_launch, sink_tree_depth, SinkLaunch, SinkMode};
use crate::upstream::{domain_generator_for_size, Field};

fn random_values(count: usize, seed: u64) -> Vec<PR> {
    let mut state = seed;
    (0..count)
        .map(|_| {
            let mut next = || {
                state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
                let mut z = state;
                z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
                z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
                z ^ (z >> 31)
            };
            PR::new(((u128::from(next()) << 64) | u128::from(next())) % PR::ORDER)
        })
        .collect()
}

fn upload<T: Copy>(values: &[T]) -> DeviceAllocation<T> {
    let mut device = DeviceAllocation::<T>::alloc(values.len()).unwrap();
    memory_copy(&mut device, values).unwrap();
    device
}

fn download<T: Copy + Default>(values: &DeviceSlice<T>, stream: &CudaStream) -> Vec<T> {
    let mut host = vec![T::default(); values.len()];
    memory_copy_async(&mut host, values, stream).unwrap();
    stream.synchronize().unwrap();
    host
}

fn device_l2() -> usize {
    gpu_core::primitives::context::DeviceProperties::new()
        .unwrap()
        .l2_cache_size_bytes
}

fn shape(log_n: u32, columns: u32, log_v: u32, skip_bottom: u32, r: u32) -> SuffixShape {
    SuffixShape {
        log_n,
        r,
        log_v,
        skip_bottom,
        columns,
    }
}

#[test]
fn cpu_sink_launch_geometry() {
    let s = shape(25, 7, 2, 10, 8);
    assert_eq!(
        sink_launch(
            31,
            &s,
            &SinkMode::Commit,
            2 * (7 << 18),
            126,
            2,
            1,
            1 << 15,
            1 << 15
        ),
        SinkLaunch {
            grid: (512, 1, 1),
            tree_depth: 8,
            tile_coset_stride: 2 * (7 << 18),
        }
    );
    let s = shape(19, 1, 4, 5, 8);
    let mode = SinkMode::CoefficientTree {
        log_domain: 22,
        k0: 5,
    };
    let per_coset = retained_len(15, 5);
    assert_eq!(
        sink_launch(
            31,
            &s,
            &mode,
            3 * 64 * (1 << 13),
            0,
            64,
            3,
            3 * per_coset,
            per_coset
        ),
        SinkLaunch {
            grid: (128, 1, 3),
            tree_depth: 5,
            tile_coset_stride: 64 << 13,
        }
    );
}

#[test]
fn cpu_sink_launch_rejects_invalid_launches() {
    let s = shape(19, 1, 4, 5, 8);
    let tile_len = 1 << 13;
    let per_coset = retained_len(15, 5);
    let ct = |log_domain, k0| SinkMode::CoefficientTree { log_domain, k0 };
    for (log_max_domain, s, mode, tiles_len, tile_count, cosets, out_len, message) in [
        (31, s, ct(22, 5), 2 * tile_len, 1, 2, 2 * per_coset, None),
        (
            18,
            s,
            ct(22, 5),
            2 * tile_len,
            1,
            2,
            2 * per_coset,
            Some("log_max_domain 18"),
        ),
        (
            31,
            s,
            ct(22, 6),
            2 * tile_len,
            1,
            3,
            3 * per_coset,
            Some("cosets out of range"),
        ),
        (
            31,
            s,
            ct(18, 0),
            2 * tile_len,
            1,
            2,
            2 * per_coset,
            Some("log_domain 18"),
        ),
        (
            31,
            s,
            SinkMode::Commit,
            tile_len,
            1,
            1,
            per_coset,
            Some("no kernel"),
        ),
        (
            31,
            s,
            ct(22, 5),
            2 * tile_len + 1,
            1,
            2,
            2 * per_coset,
            Some("tiles length"),
        ),
        (
            31,
            s,
            ct(22, 5),
            65 * tile_len,
            65,
            1,
            per_coset,
            Some("tiles out of range"),
        ),
        (
            31,
            s,
            ct(22, 5),
            2 * tile_len,
            1,
            2,
            per_coset + (1 << 10) - 1,
            Some("out shorter"),
        ),
        (
            31,
            shape(19, 1, 4, 6, 8),
            ct(22, 5),
            tile_len,
            1,
            1,
            per_coset,
            Some("no kernel"),
        ),
        (
            31,
            shape(15, 1, 4, 5, 6),
            ct(22, 5),
            tile_len,
            1,
            1,
            per_coset,
            Some("fewer than 256 leaves"),
        ),
    ] {
        let result = std::panic::catch_unwind(|| {
            sink_launch(
                log_max_domain,
                &s,
                &mode,
                tiles_len,
                0,
                tile_count,
                cosets,
                out_len,
                per_coset,
            )
        });
        match message {
            None => assert!(result.is_ok()),
            Some(message) => {
                let payload = result.expect_err(message);
                let text = payload
                    .downcast_ref::<String>()
                    .map(String::as_str)
                    .or_else(|| payload.downcast_ref::<&str>().copied())
                    .unwrap();
                assert!(text.contains(message), "{text}");
            }
        }
    }
}

// Commit sink over the production batch loop (prefix, then suffix micro + sink per batch of
// tiles, depth-8 sub-roots closed by reduce_digests) against the natural-order reference tree.
#[test]
#[cfg(not(no_cuda))]
fn sink_commit_matches_reference() {
    let ctx = DeviceContext::create(31).unwrap();
    let stream = CudaStream::create().unwrap();
    let k = 5u32;
    let nu = domain_generator_for_size::<PR>(1u64 << 31);
    for (log_n, columns, log_v, skip_bottom) in [
        (16, 7, 2, 10),
        (16, 13, 1, 10),
        (17, 1, 2, 10),
        (17, 2, 1, 9),
        (18, 7, 2, 8),
        (25, 7, 2, 10),
        (24, 13, 1, 10),
    ] {
        let rows = 1usize << log_n;
        let h = log_n - log_v;
        let monomials = upload(&random_values(rows * columns as usize, u64::from(log_n)));
        let plan = dispatch(log_n, columns as usize, log_v, skip_bottom, device_l2()).unwrap();
        let s = SuffixShape::new(&plan, log_n, log_v, skip_bottom, columns);
        let mut prefix = DeviceAllocation::<PR>::alloc(rows * columns as usize).unwrap();
        lde_coset_slot(
            &ctx,
            &monomials,
            &mut prefix,
            columns as usize,
            plan.prefix.as_ref().unwrap(),
            ScaleArgs {
                coset: CosetSource::Constant(k),
                log_domain: 31,
            },
            &stream,
        )
        .unwrap();
        let batch = plan.tiles_per_batch;
        let mut tiles = DeviceAllocation::<PR>::alloc(batch * s.tile_len()).unwrap();
        let tree_depth = sink_tree_depth(skip_bottom);
        let mut nodes = DeviceAllocation::<Digest>::alloc(1 << (h - tree_depth)).unwrap();
        let per_coset = retained_len(h, skip_bottom);
        let mut retained = DeviceAllocation::<Digest>::alloc(per_coset).unwrap();
        for first in (0..s.tiles_per_coset()).step_by(batch) {
            let count = batch.min(s.tiles_per_coset() - first);
            let tiles = &mut tiles[..count * s.tile_len()];
            launch_suffix_micro(
                &ctx,
                &prefix,
                rows * columns as usize,
                tiles,
                &s,
                first as u32,
                count as u32,
                1,
                &stream,
            )
            .unwrap();
            launch_sink(
                &ctx,
                tiles,
                &s,
                first as u32,
                count as u32,
                1,
                SinkMode::Commit,
                &mut nodes,
                1 << (h - tree_depth),
                &stream,
            )
            .unwrap();
        }
        let bottom = 1usize << (h - skip_bottom);
        if skip_bottom > tree_depth {
            reduce_digests(
                &nodes,
                skip_bottom - tree_depth,
                &mut retained[..bottom],
                &stream,
            )
            .unwrap();
        } else {
            memory_copy_async(&mut retained[..bottom], &nodes, &stream).unwrap();
        }
        build_retained_layers(h, skip_bottom, 1, per_coset, &mut retained, &stream).unwrap();
        let candidate = download(&retained, &stream);

        let mut natural = DeviceAllocation::<PR>::alloc(rows * columns as usize).unwrap();
        lde_coset(
            &ctx,
            &DeviceMatrix::new(&monomials, rows),
            &mut DeviceMatrixMut::new(&mut natural, rows),
            &upload(&[nu.pow(k)]),
            &stream,
        )
        .unwrap();
        let mut reference = DeviceAllocation::<Digest>::alloc(per_coset).unwrap();
        let mut scratch = DeviceAllocation::<Digest>::alloc(
            partial_coset_tree_scratch_len(log_n, log_v, skip_bottom).max(1),
        )
        .unwrap();
        build_partial_coset_tree_with_scratch(
            &natural,
            log_n,
            log_v,
            columns,
            skip_bottom,
            &mut reference,
            &mut scratch,
            &stream,
        )
        .unwrap();
        let reference = download(&reference, &stream);
        let mismatches = (0..per_coset)
            .filter(|&i| candidate[i] != reference[i])
            .count();
        assert_eq!(
            mismatches, 0,
            "({log_n},{columns},{log_v},{skip_bottom}): {mismatches} of {per_coset} retained digests differ"
        );
        println!(
            "sink_commit_matches_reference: ({log_n},{columns},{log_v},{skip_bottom}) r {} tiles {} x batch {batch}: {per_coset} retained digests, 0 mismatches",
            s.r,
            s.tiles_per_coset()
        );
    }
}

// CoefficientTree sink over batched cosets (one micro + one sink launch per batch of cosets)
// against lde_coset + convert_coset_leaves + the partial tree, per coset.
#[test]
#[cfg(not(no_cuda))]
fn sink_coefficient_tree_matches_reference() {
    let ctx = DeviceContext::create(31).unwrap();
    let stream = CudaStream::create().unwrap();
    for (log_n, log_v, log_lde, k0, cosets) in [
        (13, 4, 2, 1, 3),
        (15, 4, 6, 60, 4),
        (19, 4, 4, 13, 3),
        (19, 3, 4, 0, 2),
        (23, 4, 3, 7, 1),
    ] {
        let skip_bottom = 5;
        let log_domain = log_n + log_lde;
        let rows = 1usize << log_n;
        let h = log_n - log_v;
        let monomials = upload(&random_values(
            rows,
            u64::from(log_n) << 8 | u64::from(log_v),
        ));
        let plan = dispatch(log_n, 1, log_v, skip_bottom, device_l2()).unwrap();
        let s = SuffixShape::new(&plan, log_n, log_v, skip_bottom, 1);
        let mut prefix = DeviceAllocation::<PR>::alloc(rows * cosets as usize).unwrap();
        lde_coset_slot(
            &ctx,
            &monomials,
            &mut prefix,
            cosets as usize,
            plan.prefix.as_ref().unwrap(),
            ScaleArgs {
                coset: CosetSource::Batched { k0 },
                log_domain,
            },
            &stream,
        )
        .unwrap();
        let tiles_per_coset = s.tiles_per_coset() as u32;
        let mut tiles = DeviceAllocation::<PR>::alloc(
            cosets as usize * s.tile_len() * tiles_per_coset as usize,
        )
        .unwrap();
        launch_suffix_micro(
            &ctx,
            &prefix,
            rows,
            &mut tiles,
            &s,
            0,
            tiles_per_coset,
            cosets,
            &stream,
        )
        .unwrap();
        let per_coset = retained_len(h, skip_bottom);
        let mut retained = DeviceAllocation::<Digest>::alloc(cosets as usize * per_coset).unwrap();
        launch_sink(
            &ctx,
            &tiles,
            &s,
            0,
            tiles_per_coset,
            cosets,
            SinkMode::CoefficientTree { log_domain, k0 },
            &mut retained,
            per_coset,
            &stream,
        )
        .unwrap();
        build_retained_layers(h, skip_bottom, cosets, per_coset, &mut retained, &stream).unwrap();
        let candidate = download(&retained, &stream);

        let nu = domain_generator_for_size::<PR>(1u64 << log_domain);
        let mut natural = DeviceAllocation::<PR>::alloc(rows).unwrap();
        let mut reference = DeviceAllocation::<Digest>::alloc(per_coset).unwrap();
        for coset in 0..cosets as usize {
            let offset = upload(&[nu.pow(k0 + coset as u32)]);
            lde_coset(
                &ctx,
                &DeviceMatrix::new(&monomials, rows),
                &mut DeviceMatrixMut::new(&mut natural, rows),
                &offset,
                &stream,
            )
            .unwrap();
            convert_coset_leaves(&ctx, &mut natural, log_v, &offset, &stream).unwrap();
            build_partial_coset_tree(
                &natural,
                log_n,
                log_v,
                1,
                skip_bottom,
                &mut reference,
                &stream,
            )
            .unwrap();
            let reference = download(&reference, &stream);
            let candidate = &candidate[coset * per_coset..(coset + 1) * per_coset];
            let mismatches = (0..per_coset)
                .filter(|&i| candidate[i] != reference[i])
                .count();
            assert_eq!(
                mismatches, 0,
                "({log_n},{log_v},D {log_domain}) coset {}: {mismatches} of {per_coset} retained digests differ",
                k0 as usize + coset
            );
        }
        println!(
            "sink_coefficient_tree_matches_reference: ({log_n},1,{log_v},{skip_bottom}) D {log_domain} cosets {k0}..{} r {} tiles {tiles_per_coset}: {per_coset} retained digests per coset, 0 mismatches",
            k0 + cosets,
            s.r
        );
    }
}

// ncu/timing probe of the Commit sink at the base shape (2^25 x 7 columns, v = 2, sb = 10): NVTX
// `ab@sink.probe` = four production batches (micro + sink, two tiles = 512 sink blocks each),
// `ab@sink.wide` = one sink launch over 16 micro-filled tiles (4,096 blocks).
#[test]
#[ignore]
#[cfg(not(no_cuda))]
fn sink_profile_probe() {
    use era_cudart::memory::memory_set_async;
    use gpu_core::primitives::nvtx::scoped_range;
    let ctx = DeviceContext::create(31).unwrap();
    let stream = CudaStream::create().unwrap();
    let (log_n, columns, log_v, skip_bottom) = (25u32, 7u32, 2u32, 10u32);
    let h = log_n - log_v;
    let plan = dispatch(log_n, columns as usize, log_v, skip_bottom, device_l2()).unwrap();
    let s = SuffixShape::new(&plan, log_n, log_v, skip_bottom, columns);
    let column_len = (columns as usize) << log_n;
    let mut prefix = DeviceAllocation::<PR>::alloc(column_len).unwrap();
    unsafe {
        memory_set_async(prefix.transmute_mut(), 0, &stream).unwrap();
    }
    let batch = plan.tiles_per_batch as u32;
    let wide = 16u32;
    let mut tiles = DeviceAllocation::<PR>::alloc(batch as usize * s.tile_len()).unwrap();
    let mut wide_tiles = DeviceAllocation::<PR>::alloc(wide as usize * s.tile_len()).unwrap();
    let mut nodes = DeviceAllocation::<Digest>::alloc(1 << (h - 8)).unwrap();
    let start = era_cudart::event::CudaEvent::create().unwrap();
    let end = era_cudart::event::CudaEvent::create().unwrap();
    let leaf_permutations = ((2 * columns) << log_v) / 17 + 1;
    let mut sink = |label: &str, tiles: &DeviceSlice<PR>, first: u32, count: u32| {
        start.record(&stream).unwrap();
        launch_sink(
            &ctx,
            tiles,
            &s,
            first,
            count,
            1,
            SinkMode::Commit,
            &mut nodes,
            1 << (h - 8),
            &stream,
        )
        .unwrap();
        end.record(&stream).unwrap();
        end.synchronize().unwrap();
        let ms = era_cudart::event::elapsed_time(&start, &end).unwrap();
        let leaves = u64::from(count) << (skip_bottom + s.r - log_v);
        let permutations = leaves * u64::from(leaf_permutations) + (leaves >> 8) * 255;
        println!(
            "sink_profile_probe: {label} tiles {first}..{} {ms:.3} ms, {:.2} G keccak-f/s",
            first + count,
            permutations as f64 / f64::from(ms) / 1e6
        );
    };
    for (label, batches) in [("sink.warmup", 0..1u32), ("sink.probe", 1..5)] {
        let _range = scoped_range(Some("ab"), label);
        for index in batches {
            launch_suffix_micro(
                &ctx,
                &prefix,
                column_len,
                &mut tiles,
                &s,
                index * batch,
                batch,
                1,
                &stream,
            )
            .unwrap();
            sink(label, &tiles, index * batch, batch);
        }
    }
    launch_suffix_micro(
        &ctx,
        &prefix,
        column_len,
        &mut wide_tiles,
        &s,
        0,
        wide,
        1,
        &stream,
    )
    .unwrap();
    let _range = scoped_range(Some("ab"), "sink.wide");
    sink("sink.wide", &wide_tiles, 0, wide);
}
