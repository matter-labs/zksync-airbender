use era_cudart::memory::{memory_copy, memory_copy_async, DeviceAllocation};
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use gpu_core::primitives::device_structures::{DeviceMatrix, DeviceMatrixMut};
use gpu_core::primitives::field::PR;
use gpu_hash::keccak256::{
    build_partial_coset_tree, build_partial_coset_tree_with_scratch, build_retained_layers,
    partial_coset_tree_scratch_len, Digest,
};
use gpu_ntt::proth120::{
    convert_coset_leaves, dispatch, launch_suffix_micro, lde_coset, lde_coset_slot, CosetSource,
    DeviceContext, ScaleArgs, SuffixShape,
};

use super::packed::retained_len;
use super::sink::{
    coefficient_batches, commit_coset, commit_coset_scratch_lens, launch_sink, sink_launch,
    SinkLaunch, SinkMode,
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
        (16, 12, 1, 10),
        (17, 2, 1, 9),
        (18, 2, 1, 5),
        (24, 12, 1, 10),
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

// Compare the batched residue sink with the independent LDE and partial-tree construction.
#[test]
#[cfg(not(no_cuda))]
fn sink_coefficient_tree_matches_reference() {
    let ctx = DeviceContext::create(31).unwrap();
    let stream = CudaStream::create().unwrap();
    for (log_n, log_v, log_lde, k0, cosets) in [
        (13, 4, 2, 1, 3),
        (15, 4, 6, 60, 4),
        (19, 4, 4, 13, 3),
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
    for (log_n, columns, log_v, skip_bottom, log_lde, cap_log) in
        [(17, 12, 1, 10, 2, 1), (18, 2, 1, 9, 1, 0)]
    {
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

// Reject an openings cap outside the coset tree before launching or touching outputs.
#[test]
#[cfg(not(no_cuda))]
fn sink_open_slot_rejects_invalid_cap_before_launch() {
    use super::sink::{open_coset_slot, open_coset_slot_scratch_lens, OpenQueries, OpenSlot};
    let ctx = DeviceContext::create(31).unwrap();
    let stream = CudaStream::create().unwrap();
    let (log_n, columns, log_v, skip_bottom, log_lde, cap_log) =
        (18u32, 12u32, 1u32, 8u32, 3u32, 19u32);
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
