use era_cudart::memory::{memory_copy, memory_copy_async, DeviceAllocation};
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use gpu_core::primitives::device_structures::{DeviceMatrix, DeviceMatrixMut};
use gpu_core::primitives::field::PR;
use gpu_hash::keccak256::{
    build_partial_coset_tree, build_partial_coset_tree_with_scratch, build_retained_layers,
    partial_coset_tree_scratch_len, reduce_digest_layers, Digest,
};
use gpu_ntt::proth120::{
    convert_coset_leaves, dispatch, launch_suffix_micro, lde_coset, lde_coset_slot, CosetSource,
    DeviceContext, ScaleArgs, SuffixShape,
};

use super::packed::retained_len;
use super::sink::{
    coefficient_batches, commit_coset, commit_coset_scratch_lens, launch_sink,
    launch_sink_reference, sink_launch, SinkLaunch, SinkMode,
};
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
            1 << 20,
            1 << 20
        ),
        SinkLaunch {
            grid: (512, 1, 1),
            tree_depth: 3,
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

// commit_coset (prefix, then suffix micro + Commit sink per batch of tiles, the node layers above
// the depth-3 sink nodes) against the natural-order reference tree.
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
        (16, 12, 1, 10),
        (16, 6, 2, 10),
        (17, 1, 2, 10),
        (17, 2, 1, 9),
        (18, 7, 2, 8),
        (18, 2, 1, 5),
        (17, 1, 2, 4),
        (25, 1, 2, 5),
        (25, 7, 2, 10),
        (24, 13, 1, 10),
        (24, 12, 1, 10),
        (25, 6, 2, 10),
    ] {
        let rows = 1usize << log_n;
        let h = log_n - log_v;
        let monomials = upload(&random_values(rows * columns as usize, u64::from(log_n)));
        let plan = dispatch(log_n, columns as usize, log_v, skip_bottom, device_l2()).unwrap();
        let s = SuffixShape::new(&plan, log_n, log_v, skip_bottom, columns);
        let mut prefix = DeviceAllocation::<PR>::alloc(rows * columns as usize).unwrap();
        let (tiles_len, nodes_len, node_scratch_len) = commit_coset_scratch_lens(&plan, &s);
        let mut tiles = DeviceAllocation::<PR>::alloc(tiles_len).unwrap();
        let mut nodes = DeviceAllocation::<Digest>::alloc(nodes_len).unwrap();
        let mut node_scratch = DeviceAllocation::<Digest>::alloc(node_scratch_len).unwrap();
        let per_coset = retained_len(h, skip_bottom);
        let mut retained = DeviceAllocation::<Digest>::alloc(per_coset).unwrap();
        commit_coset(
            &ctx,
            &monomials,
            &plan,
            &s,
            k,
            31,
            &mut prefix,
            &mut tiles,
            &mut nodes,
            &mut node_scratch,
            &mut retained,
            &stream,
        )
        .unwrap();
        let batch = plan.tiles_per_batch;
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

// coefficient_batches covers every (coset, tile) of a call once, each batch within one batch.
#[test]
fn coefficient_batches_cover_each_tile_once() {
    for (cosets, tiles, batch_cosets, batch_tiles) in [
        (4, 1024, 1, 464),
        (8, 1024, 1, 464),
        (1, 1024, 1, 464),
        (3, 1024, 1, 512),
        (5, 7, 1, 3),
        (7, 100, 1, 33),
        (128, 64, 7, 64),
        (2048, 4, 116, 4),
        (1, 64, 1, 64),
    ] {
        let batches = coefficient_batches(cosets, tiles, batch_cosets, batch_tiles);
        let mut seen = vec![0u32; cosets * tiles];
        for &(first_coset, coset_count, first_tile, tile_count) in &batches {
            assert!(coset_count >= 1 && tile_count >= 1);
            assert!(coset_count * tile_count <= batch_cosets * batch_tiles);
            for coset in first_coset..first_coset + coset_count {
                for tile in first_tile..first_tile + tile_count {
                    seen[coset * tiles + tile] += 1;
                }
            }
        }
        assert!(
            seen.iter().all(|&count| count == 1),
            "({cosets}, {tiles}, {batch_cosets}, {batch_tiles})"
        );
    }
    assert_eq!(coefficient_batches(4, 1024, 1, 464)[8..], [(0, 4, 928, 96)]);
}

// The Commit sinks (several keccak-f rounds per loop iteration) against the round-loop reference
// kernels on the same tiles: last tiles of two cosets.
#[test]
#[cfg(not(no_cuda))]
fn sink_commit_matches_round_loop() {
    let ctx = DeviceContext::create(31).unwrap();
    let stream = CudaStream::create().unwrap();
    for (log_n, columns, log_v, skip_bottom) in [
        (16, 7, 2, 10),
        (16, 13, 1, 10),
        (16, 12, 1, 10),
        (16, 6, 2, 10),
        (17, 1, 2, 10),
        (17, 2, 1, 9),
        (25, 7, 2, 10),
        (24, 13, 1, 10),
    ] {
        let plan = dispatch(log_n, columns as usize, log_v, skip_bottom, device_l2()).unwrap();
        let s = SuffixShape::new(&plan, log_n, log_v, skip_bottom, columns);
        let cosets = 2u32;
        let tile_count = plan.tiles_per_batch.min(s.tiles_per_coset()) as u32;
        let first_tile = s.tiles_per_coset() as u32 - tile_count;
        let tiles = upload(&random_values(
            cosets as usize * tile_count as usize * s.tile_len(),
            u64::from(log_n) << 8 | u64::from(columns),
        ));
        let items = 1usize << (log_n - log_v - 3);
        let mut candidate = upload(&vec![Digest::default(); cosets as usize * items]);
        let mut reference = upload(&vec![Digest::default(); cosets as usize * items]);
        for (out, launch) in [
            (
                &mut candidate,
                launch_sink as fn(_, _, _, _, _, _, _, _, _, _) -> _,
            ),
            (&mut reference, launch_sink_reference),
        ] {
            launch(
                &ctx,
                &tiles,
                &s,
                first_tile,
                tile_count,
                cosets,
                SinkMode::Commit,
                out,
                items,
                &stream,
            )
            .unwrap();
        }
        let candidate = download(&candidate, &stream);
        let reference = download(&reference, &stream);
        let written = reference
            .iter()
            .filter(|&&node| node != Digest::default())
            .count();
        assert_eq!(
            written,
            (cosets as usize * tile_count as usize) << (skip_bottom + s.r - log_v - 3),
            "({log_n},{columns},{log_v},{skip_bottom}): written nodes"
        );
        assert!(
            candidate == reference,
            "({log_n},{columns},{log_v},{skip_bottom}): Commit sink and round-loop reference differ"
        );
        println!(
            "sink_commit_matches_round_loop: ({log_n},{columns},{log_v},{skip_bottom}) tiles {first_tile}..{} of 2 cosets: {written} nodes equal",
            first_tile + tile_count
        );
    }
}

// CoefficientTree sink over batched cosets (one micro + one sink launch per batch of cosets)
// against lde_coset + convert_coset_leaves + the partial tree, per coset; the residue-tree sink
// nodes equal the converting kernel's.
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
            None,
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
        let mut converted = DeviceAllocation::<Digest>::alloc(cosets as usize * per_coset).unwrap();
        launch_sink_reference(
            &ctx,
            &tiles,
            &s,
            0,
            tiles_per_coset,
            cosets,
            SinkMode::CoefficientTree { log_domain, k0 },
            &mut converted,
            per_coset,
            &stream,
        )
        .unwrap();
        let sink_nodes = 1usize << (h - skip_bottom);
        let residue_nodes = download(&retained, &stream);
        let converted_nodes = download(&converted, &stream);
        for coset in 0..cosets as usize {
            let range = coset * per_coset..coset * per_coset + sink_nodes;
            assert_eq!(
                residue_nodes[range.clone()],
                converted_nodes[range],
                "({log_n},{log_v},D {log_domain}) coset {}: residue-tree and converting sinks differ",
                k0 as usize + coset
            );
        }
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
    let mut nodes = DeviceAllocation::<Digest>::alloc(1 << (h - 3)).unwrap();
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
            1 << (h - 3),
            &stream,
        )
        .unwrap();
        end.record(&stream).unwrap();
        end.synchronize().unwrap();
        let ms = era_cudart::event::elapsed_time(&start, &end).unwrap();
        let leaves = u64::from(count) << (skip_bottom + s.r - log_v);
        let permutations = leaves * u64::from(leaf_permutations) + (leaves >> 8) * 224;
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
                None,
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
        None,
        &stream,
    )
    .unwrap();
    let _range = scoped_range(Some("ab"), "sink.wide");
    sink("sink.wide", &wide_tiles, 0, wide);
}

// Timing probe of the suffix batch loop of one coset for the Commit shapes base (2^25 x 7, v = 2),
// (d) base (2^24 x 13, v = 1) and the two setup shapes (2^25 x 1, v = 2; 2^24 x 2, v = 1), all at
// skip_bottom 10: batches of suffix micro + Commit sink over a resident prefix plus the node
// layers up to skip_bottom, one warmup coset, then five measured cosets (CUDA-event span per coset).
#[test]
#[ignore]
#[cfg(not(no_cuda))]
fn sink_coset_probe() {
    use era_cudart::memory::memory_set_async;
    let ctx = DeviceContext::create(31).unwrap();
    let stream = CudaStream::create().unwrap();
    for (log_n, columns, log_v, skip_bottom) in [
        (25u32, 7u32, 2u32, 10u32),
        (24, 13, 1, 10),
        (25, 1, 2, 10),
        (24, 2, 1, 10),
        (24, 12, 1, 10),
        (25, 6, 2, 10),
    ] {
        let h = log_n - log_v;
        let plan = dispatch(log_n, columns as usize, log_v, skip_bottom, device_l2()).unwrap();
        let s = SuffixShape::new(&plan, log_n, log_v, skip_bottom, columns);
        let column_len = (columns as usize) << log_n;
        let mut prefix = DeviceAllocation::<PR>::alloc(column_len).unwrap();
        unsafe {
            memory_set_async(prefix.transmute_mut(), 0, &stream).unwrap();
        }
        let batch = plan.tiles_per_batch;
        let mut tiles = DeviceAllocation::<PR>::alloc(batch * s.tile_len()).unwrap();
        let mut nodes = DeviceAllocation::<Digest>::alloc(1 << (h - 3)).unwrap();
        let mut node_scratch = DeviceAllocation::<Digest>::alloc(1 << (h - 4)).unwrap();
        let mut bottom = DeviceAllocation::<Digest>::alloc(1 << (h - skip_bottom)).unwrap();
        let start = era_cudart::event::CudaEvent::create().unwrap();
        let end = era_cudart::event::CudaEvent::create().unwrap();
        for coset in 0..6 {
            start.record(&stream).unwrap();
            for first in (0..s.tiles_per_coset()).step_by(batch) {
                launch_suffix_micro(
                    &ctx,
                    &prefix,
                    column_len,
                    &mut tiles,
                    &s,
                    first as u32,
                    batch as u32,
                    1,
                    None,
                    &stream,
                )
                .unwrap();
                launch_sink(
                    &ctx,
                    &tiles,
                    &s,
                    first as u32,
                    batch as u32,
                    1,
                    SinkMode::Commit,
                    &mut nodes,
                    1 << (h - 3),
                    &stream,
                )
                .unwrap();
            }
            reduce_digest_layers(
                &mut nodes,
                skip_bottom - 3,
                &mut node_scratch,
                &mut bottom,
                &stream,
            )
            .unwrap();
            end.record(&stream).unwrap();
            end.synchronize().unwrap();
            let ms = era_cudart::event::elapsed_time(&start, &end).unwrap();
            println!(
                "sink_coset_probe: ({log_n},{columns},{log_v},{skip_bottom}) {} coset {coset}: {ms:.3} ms ({} batches of micro + sink, then the layers up to skip_bottom)",
                if coset == 0 { "warmup" } else { "measured" },
                s.tiles_per_coset() / batch
            );
        }
    }
}

// Openings through the touched-coset plan (one gated `open_coset_slot` per query slot) against
// today's per-coset gathers on the natural-order cosets, for distinct retained trees per coset and
// the query sets of spec 3.1: all in one coset, duplicates, one per coset, the last valid index,
// Q = 1, touched order [last, 1, 0].
#[test]
#[cfg(not(no_cuda))]
fn sink_open_queries_matches_gathers() {
    use super::sink::{open_coset_slot, open_coset_slot_scratch_lens, OpenQueries, OpenSlot};
    use gpu_hash::keccak256::{
        gather_leaves_for_queries_single_coset,
        gather_merkle_paths_partial_for_queries_single_coset, launch_coset_query_plan,
    };
    let ctx = DeviceContext::create(31).unwrap();
    let stream = CudaStream::create().unwrap();
    let mut state = 0x0f0e_0d0c_u64;
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state as u32
    };
    for (log_n, columns, log_v, skip_bottom, log_lde, cap_log) in [
        (16u32, 7u32, 2u32, 10u32, 3u32, 2u32),
        (17, 13, 1, 10, 2, 1),
        (17, 12, 1, 10, 2, 1),
        (16, 6, 2, 10, 3, 2),
        (18, 1, 2, 8, 3, 3),
        (18, 2, 1, 9, 1, 0),
    ] {
        let rows = 1usize << log_n;
        let h = log_n - log_v;
        let log_domain = log_n + log_lde;
        let cosets = 1usize << log_lde;
        let leaf_len = (columns as usize) << log_v;
        let depth = (h + log_lde - cap_log) as usize;
        let monomials = upload(&random_values(
            rows * columns as usize,
            u64::from(log_n) << 4 | u64::from(columns),
        ));
        let nu = domain_generator_for_size::<PR>(1u64 << log_domain);
        let per_coset = retained_len(h, skip_bottom);
        let mut naturals = Vec::new();
        let mut retained_all = DeviceAllocation::<Digest>::alloc(cosets * per_coset).unwrap();
        let mut scratch = DeviceAllocation::<Digest>::alloc(
            partial_coset_tree_scratch_len(log_n, log_v, skip_bottom).max(1),
        )
        .unwrap();
        for k in 0..cosets {
            let mut natural = DeviceAllocation::<PR>::alloc(rows * columns as usize).unwrap();
            lde_coset(
                &ctx,
                &DeviceMatrix::new(&monomials, rows),
                &mut DeviceMatrixMut::new(&mut natural, rows),
                &upload(&[nu.pow(k as u32)]),
                &stream,
            )
            .unwrap();
            build_partial_coset_tree_with_scratch(
                &natural,
                log_n,
                log_v,
                columns,
                skip_bottom,
                &mut retained_all[k * per_coset..(k + 1) * per_coset],
                &mut scratch,
                &stream,
            )
            .unwrap();
            naturals.push(natural);
        }
        let plan = dispatch(log_n, columns as usize, log_v, skip_bottom, device_l2()).unwrap();
        let s = SuffixShape::new(&plan, log_n, log_v, skip_bottom, columns);
        let (tiles_len, nodes_len) = open_coset_slot_scratch_lens(&plan, &s);
        let mut prefix = DeviceAllocation::<PR>::alloc(rows * columns as usize).unwrap();
        let mut tiles = DeviceAllocation::<PR>::alloc(tiles_len).unwrap();
        let mut nodes = DeviceAllocation::<Digest>::alloc(nodes_len).unwrap();
        let query = |leaf: u32, coset: u32| (leaf << log_lde) | coset;
        let last_leaf = (1u32 << h) - 1;
        let last_coset = cosets as u32 - 1;
        let query_sets: Vec<(&str, Vec<u32>)> = vec![
            (
                "one coset",
                (0..14)
                    .map(|i| query((i * 977) & last_leaf, last_coset))
                    .collect(),
            ),
            (
                "duplicates",
                vec![
                    query(5, 1 % cosets as u32),
                    query(5, 1 % cosets as u32),
                    query(1029, 0),
                    query(5, 1 % cosets as u32),
                ],
            ),
            (
                "one per coset",
                (0..cosets as u32)
                    .map(|c| query(next() & last_leaf, c))
                    .collect(),
            ),
            (
                "last valid index",
                vec![
                    query(last_leaf, last_coset),
                    query(0, 0),
                    query(last_leaf, last_coset),
                ],
            ),
            (
                "single",
                vec![query(next() & last_leaf, next() & last_coset)],
            ),
            (
                "touched order [last, 1, 0]",
                vec![
                    query(3, last_coset),
                    query(1 << 10 | 7, 1 % cosets as u32),
                    query(511, 0),
                    query(12, last_coset),
                ],
            ),
            (
                "14 random",
                (0..14)
                    .map(|_| query(next() & last_leaf, next() & last_coset))
                    .collect(),
            ),
        ];
        for (name, queries) in query_sets {
            let count = queries.len();
            let device_queries = upload(&queries);
            let sentinel = [0xdead_beefu32; 8];
            let mut reference_leaves = DeviceAllocation::<PR>::alloc(count * leaf_len).unwrap();
            let mut reference_paths = upload(&vec![sentinel; count * depth]);
            for (k, natural) in naturals.iter().enumerate() {
                gather_leaves_for_queries_single_coset(
                    natural,
                    k as u32,
                    log_lde,
                    log_n,
                    log_v,
                    &device_queries,
                    &mut reference_leaves,
                    &stream,
                )
                .unwrap();
                gather_merkle_paths_partial_for_queries_single_coset(
                    natural,
                    k as u32,
                    log_lde,
                    log_n,
                    log_v,
                    cap_log,
                    skip_bottom,
                    &retained_all[k * per_coset..(k + 1) * per_coset],
                    &device_queries,
                    &mut reference_paths,
                    &stream,
                )
                .unwrap();
            }
            let mut touched = DeviceAllocation::<u32>::alloc(count).unwrap();
            let mut active = DeviceAllocation::<u32>::alloc(count).unwrap();
            let mut touched_count = DeviceAllocation::<u32>::alloc(1).unwrap();
            launch_coset_query_plan(
                &device_queries,
                log_lde,
                &mut touched,
                &mut active,
                &mut touched_count,
                &stream,
            )
            .unwrap();
            let mut leaves = DeviceAllocation::<PR>::alloc(count * leaf_len).unwrap();
            let mut paths = upload(&vec![sentinel; count * depth]);
            let mut open = OpenQueries {
                queries: &device_queries,
                log_lde,
                cap_log,
                leaves: &mut leaves,
                paths: &mut paths,
            };
            for slot in 0..count {
                open_coset_slot(
                    &ctx,
                    &monomials,
                    &plan,
                    &s,
                    OpenSlot {
                        coset: &touched[slot..slot + 1],
                        active: &active[slot..slot + 1],
                    },
                    log_domain,
                    &retained_all,
                    per_coset,
                    &mut open,
                    &mut prefix,
                    &mut tiles,
                    &mut nodes,
                    &stream,
                )
                .unwrap();
            }
            let candidate_leaves = download(&leaves, &stream);
            let candidate_paths = download(&paths, &stream);
            let expected_leaves = download(&reference_leaves, &stream);
            let expected_paths = download(&reference_paths, &stream);
            for q in 0..count {
                assert!(
                    candidate_leaves[q * leaf_len..(q + 1) * leaf_len]
                        == expected_leaves[q * leaf_len..(q + 1) * leaf_len],
                    "({log_n},{columns},{log_v},{skip_bottom}) {name}: leaf of query {q}"
                );
                for layer in 0..depth {
                    assert_eq!(
                        candidate_paths[q * depth + layer],
                        expected_paths[q * depth + layer],
                        "({log_n},{columns},{log_v},{skip_bottom}) {name}: query {q} path layer {layer}"
                    );
                }
            }
            let touched_count = download(&touched_count, &stream)[0];
            println!(
                "sink_open_queries_matches_gathers: ({log_n},{columns},{log_v},{skip_bottom}) log_lde {log_lde} {name}: Q {count}, {touched_count} active slots, leaves + {depth}-layer paths byte-equal"
            );
        }
    }
}

// ncu probe of the hot sink launches: NVTX `ab@sink.commit` = one batch (suffix micro + Commit sink)
// of each Commit shape (base, (d) base, the two setup shapes) after a warmup batch; `ab@sink.open`
// = the touched-coset plan and one openings slot of the base shape whose 14 queries all lie in the
// first batch of tiles (its first open-sink launch is the hit batch), then the open paths.
#[test]
#[ignore]
#[cfg(not(no_cuda))]
fn sink_gate_profile_probe() {
    use super::sink::{open_coset_slot, open_coset_slot_scratch_lens, OpenQueries, OpenSlot};
    use era_cudart::memory::memory_set_async;
    use gpu_core::primitives::nvtx::scoped_range;
    use gpu_hash::keccak256::launch_coset_query_plan;
    let ctx = DeviceContext::create(31).unwrap();
    let stream = CudaStream::create().unwrap();
    for (log_n, columns, log_v, skip_bottom) in [
        (25u32, 7u32, 2u32, 10u32),
        (24, 13, 1, 10),
        (25, 1, 2, 10),
        (24, 2, 1, 10),
        (24, 12, 1, 10),
        (25, 6, 2, 10),
    ] {
        let h = log_n - log_v;
        let plan = dispatch(log_n, columns as usize, log_v, skip_bottom, device_l2()).unwrap();
        let s = SuffixShape::new(&plan, log_n, log_v, skip_bottom, columns);
        let column_len = (columns as usize) << log_n;
        let mut prefix = DeviceAllocation::<PR>::alloc(column_len).unwrap();
        unsafe {
            memory_set_async(prefix.transmute_mut(), 0, &stream).unwrap();
        }
        let batch = plan.tiles_per_batch as u32;
        let mut tiles = DeviceAllocation::<PR>::alloc(batch as usize * s.tile_len()).unwrap();
        let mut nodes = DeviceAllocation::<Digest>::alloc(1 << (h - 3)).unwrap();
        for (label, first) in [("sink.warmup", 0u32), ("sink.commit", batch)] {
            let _range = scoped_range(Some("ab"), label);
            launch_suffix_micro(
                &ctx, &prefix, column_len, &mut tiles, &s, first, batch, 1, None, &stream,
            )
            .unwrap();
            launch_sink(
                &ctx,
                &tiles,
                &s,
                first,
                batch,
                1,
                SinkMode::Commit,
                &mut nodes,
                1 << (h - 3),
                &stream,
            )
            .unwrap();
        }
        stream.synchronize().unwrap();
    }
    // Base (7 columns) and setup (1 column) openings at the L1 wrap shapes, and the 96-column base
    // packed at 3 (12 columns, v 1) and at 4 (6 columns).
    for (columns, log_n, log_v, open_label) in [
        (7u32, 25u32, 2u32, "sink.open"),
        (1, 25, 2, "sink.setup_open"),
        (12, 24, 1, "sink.open_12"),
        (6, 25, 2, "sink.open_6"),
    ] {
        let (skip_bottom, log_lde, cap_log) = (10u32, 6u32, 5u32);
        let h = log_n - log_v;
        let rows = 1usize << log_n;
        let plan = dispatch(log_n, columns as usize, log_v, skip_bottom, device_l2()).unwrap();
        let s = SuffixShape::new(&plan, log_n, log_v, skip_bottom, columns);
        let monomials = upload(&random_values(rows * columns as usize, 25));
        let per_coset = retained_len(h, skip_bottom);
        let retained_all = upload(&vec![[7u32; 8]; per_coset << log_lde]);
        let a = s.log_a();
        let queries: Vec<u32> = (0..14u32)
            .map(|i| ((((i * 37) & 2047) + ((i % 64) << a)) << log_lde) | 3)
            .collect();
        let device_queries = upload(&queries);
        let mut touched = DeviceAllocation::<u32>::alloc(queries.len()).unwrap();
        let mut active = DeviceAllocation::<u32>::alloc(queries.len()).unwrap();
        let mut touched_count = DeviceAllocation::<u32>::alloc(1).unwrap();
        let (tiles_len, nodes_len) = open_coset_slot_scratch_lens(&plan, &s);
        let mut prefix = DeviceAllocation::<PR>::alloc(rows * columns as usize).unwrap();
        let mut tiles = DeviceAllocation::<PR>::alloc(tiles_len).unwrap();
        let mut nodes = DeviceAllocation::<Digest>::alloc(nodes_len).unwrap();
        let mut leaves =
            DeviceAllocation::<PR>::alloc(queries.len() * ((columns as usize) << log_v)).unwrap();
        let depth = (h + log_lde - cap_log) as usize;
        let mut paths = DeviceAllocation::<Digest>::alloc(queries.len() * depth).unwrap();
        for label in ["sink.warmup", open_label] {
            let _range = scoped_range(Some("ab"), label);
            launch_coset_query_plan(
                &device_queries,
                log_lde,
                &mut touched,
                &mut active,
                &mut touched_count,
                &stream,
            )
            .unwrap();
            let mut open = OpenQueries {
                queries: &device_queries,
                log_lde,
                cap_log,
                leaves: &mut leaves,
                paths: &mut paths,
            };
            open_coset_slot(
                &ctx,
                &monomials,
                &plan,
                &s,
                OpenSlot {
                    coset: &touched[..1],
                    active: &active[..1],
                },
                log_n + log_lde,
                &retained_all,
                per_coset,
                &mut open,
                &mut prefix,
                &mut tiles,
                &mut nodes,
                &stream,
            )
            .unwrap();
            stream.synchronize().unwrap();
        }
    }
    println!("sink_gate_profile_probe: done");
}

// Codex T4.6 repro: an openings slot with cap_log above log_lde (n = 18, v = 2, h = 16, log_lde 3,
// cap_log 19, Q = 1, paths.len 0) is rejected before any launch, leaving its outputs untouched.
#[test]
#[cfg(not(no_cuda))]
fn sink_open_slot_rejects_invalid_cap_before_launch() {
    use super::sink::{open_coset_slot, open_coset_slot_scratch_lens, OpenQueries, OpenSlot};
    let ctx = DeviceContext::create(31).unwrap();
    let stream = CudaStream::create().unwrap();
    let (log_n, columns, log_v, skip_bottom, log_lde, cap_log) =
        (18u32, 7u32, 2u32, 8u32, 3u32, 19u32);
    let h = log_n - log_v;
    let rows = 1usize << log_n;
    let plan = dispatch(log_n, columns as usize, log_v, skip_bottom, device_l2()).unwrap();
    let s = SuffixShape::new(&plan, log_n, log_v, skip_bottom, columns);
    let (tiles_len, nodes_len) = open_coset_slot_scratch_lens(&plan, &s);
    let monomials = upload(&random_values(rows * columns as usize, 18));
    let per_coset = retained_len(h, skip_bottom);
    let retained_all = upload(&vec![[1u32; 8]; per_coset << log_lde]);
    let queries = upload(&[(5u32 << log_lde) | 1]);
    let coset = upload(&[1u32]);
    let active = upload(&[1u32]);
    let sentinel = [0x5a5a_5a5au32; 8];
    let mut nodes = upload(&vec![sentinel; nodes_len]);
    let mut leaves = upload(&vec![PR::new(9); (columns as usize) << log_v]);
    let mut paths = upload::<Digest>(&[]);
    let mut prefix = DeviceAllocation::<PR>::alloc(rows * columns as usize).unwrap();
    let mut tiles = DeviceAllocation::<PR>::alloc(tiles_len).unwrap();
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut open = OpenQueries {
            queries: &queries,
            log_lde,
            cap_log,
            leaves: &mut leaves,
            paths: &mut paths,
        };
        open_coset_slot(
            &ctx,
            &monomials,
            &plan,
            &s,
            OpenSlot {
                coset: &coset,
                active: &active,
            },
            log_n + log_lde,
            &retained_all,
            per_coset,
            &mut open,
            &mut prefix,
            &mut tiles,
            &mut nodes,
            &stream,
        )
    }));
    let payload = result.expect_err("invalid cap_log accepted");
    let text = payload
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| payload.downcast_ref::<&str>().copied())
        .unwrap();
    assert!(text.contains("cap_log <= log_lde"), "{text}");
    stream.synchronize().unwrap();
    assert!(download(&nodes, &stream)
        .iter()
        .all(|node| *node == sentinel));
    assert!(download(&leaves, &stream)
        .iter()
        .all(|value| value.0 == PR::new(9).0));
}
