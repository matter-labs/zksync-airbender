use std::panic::{catch_unwind, AssertUnwindSafe};

use era_cudart::memory::{memory_copy_async, DeviceAllocation};
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;

use super::super::hash::{leaf_shape, leaf_sponge_probe, leaf_tile};
use super::super::merkle::{partial_tree_shape, partial_tree_tile, top_tree_log_lde};
use super::super::{
    assert_no_overlap, build_partial_coset_tree, build_partial_coset_tree_with_scratch,
    build_partial_coset_trees_multi_coset, build_partial_coset_trees_multi_coset_with_scratch,
    build_top_tree, gather_tree_cap, hash_leaves, hash_leaves_multi_coset,
    partial_coset_tree_scratch_len, retained_layer_offset, top_nodes_layer_offset, Digest,
};
use super::{
    bitreverse_index, column_slices, cpu_layer, cpu_tree, download, random_columns, test_worker,
    upload, TestRng, SENTINEL,
};
use crate::upstream::{
    ColumnMajorMerkleTreeConstructor, Keccak256MerkleTreeWithCap, PathQueryable, PlainCosetLeaves,
    Proth120,
};

#[test]
fn keccak256_partial_scratch_validation() {
    let stream = CudaStream::default();
    let values = upload(&vec![Proth120::new(1); 1 << 12], &stream);
    let mut retained = sentinel_buffer(128, &stream);
    let mut scratch = sentinel_buffer(64, &stream);
    for skip_bottom in 6..=10 {
        let retained_len = 2 * (1 << (11 - skip_bottom)) - 1;
        if skip_bottom > 8 {
            assert_named_panic(
                "keccak256::build_partial_coset_tree: skip_bottom <= 8",
                || {
                    build_partial_coset_tree(
                        &values,
                        12,
                        1,
                        1,
                        skip_bottom,
                        &mut retained[..retained_len],
                        &stream,
                    )
                    .unwrap();
                },
            );
            assert_named_panic(
                "keccak256::build_partial_coset_trees_multi_coset: skip_bottom <= 8",
                || {
                    build_partial_coset_trees_multi_coset(
                        &values,
                        12,
                        1,
                        1,
                        skip_bottom,
                        1,
                        values.len(),
                        retained_len,
                        &mut retained[..retained_len],
                        &stream,
                    )
                    .unwrap();
                },
            );
        }
        assert_named_panic(
            "keccak256::build_partial_coset_tree_with_scratch: scratch.len() >= leaves >> 5",
            || {
                build_partial_coset_tree_with_scratch(
                    &values,
                    12,
                    1,
                    1,
                    skip_bottom,
                    &mut retained[..retained_len],
                    &mut scratch[..63],
                    &stream,
                )
                .unwrap();
            },
        );
        assert_named_panic("keccak256::build_partial_coset_trees_multi_coset_with_scratch: scratch.len() >= leaves >> 5", || {
            build_partial_coset_trees_multi_coset_with_scratch(&values, 12, 1, 1, skip_bottom, 1, values.len(), retained_len,
                &mut retained[..retained_len], &mut scratch[..63], &stream).unwrap();
        });
        let overlap_values =
            unsafe { DeviceSlice::from_raw_parts_mut(values.as_ptr() as *mut Digest, 8) };
        assert_named_panic(
            "keccak256::build_partial_coset_tree_with_scratch: buffers must not overlap",
            || {
                build_partial_coset_tree_with_scratch(
                    &values,
                    12,
                    1,
                    1,
                    skip_bottom,
                    &mut retained[..retained_len],
                    overlap_values,
                    &stream,
                )
                .unwrap();
            },
        );
        let overlap_retained =
            unsafe { DeviceSlice::from_raw_parts_mut(retained.as_mut_ptr().add(1), 8) };
        assert_named_panic("keccak256::build_partial_coset_trees_multi_coset_with_scratch: buffers must not overlap", || {
            build_partial_coset_trees_multi_coset_with_scratch(&values, 12, 1, 1, skip_bottom, 1, values.len(), retained_len,
                &mut retained[..retained_len], overlap_retained, &stream).unwrap();
        });
    }
    assert_named_panic(
        "keccak256::build_partial_coset_tree_with_scratch: skip_bottom <= 10",
        || {
            build_partial_coset_tree_with_scratch(
                &values,
                12,
                1,
                1,
                11,
                &mut retained[..1],
                &mut scratch,
                &stream,
            )
            .unwrap();
        },
    );
    stream.synchronize().unwrap();
}

fn cpu_leaves_from_columns(cols: &[&[Proth120]], log_v: u32) -> Vec<Digest> {
    let worker = test_worker();
    let leaves = cols[0].len() >> log_v;
    let tree = <Keccak256MerkleTreeWithCap as ColumnMajorMerkleTreeConstructor<Proth120>>::construct_from_cosets::<
        Proth120,
        &[Proth120],
    >(&[cols], 1 << log_v, leaves, true, false, false, &worker);
    assert!(tree.node_hashes_enumerated_from_leafs.is_empty());
    tree.leaf_hashes.to_vec()
}

fn cpu_leaves(values: &[Proth120], columns: usize, log_v: u32) -> Vec<Digest> {
    cpu_leaves_from_columns(&column_slices(values, columns), log_v)
}

fn cpu_leaves_from_accessors(cols: &[&[Proth120]], log_v: u32) -> Vec<Digest> {
    let worker = test_worker();
    let accessors: Vec<PlainCosetLeaves<Proth120>> = cols
        .iter()
        .map(|column| PlainCosetLeaves::new(column, 1 << log_v))
        .collect();
    let leaves = cols[0].len() >> log_v;
    let tree = <Keccak256MerkleTreeWithCap as ColumnMajorMerkleTreeConstructor<Proth120>>::construct_from_leaf_accessors::<
        Proth120,
        PlainCosetLeaves<Proth120>,
    >(&[&accessors[..]], leaves, false, false, &worker);
    assert!(tree.node_hashes_enumerated_from_leafs.is_empty());
    tree.leaf_hashes.to_vec()
}

fn sentinel_buffer(len: usize, stream: &CudaStream) -> DeviceAllocation<Digest> {
    upload(&vec![SENTINEL; len], stream)
}

fn gpu_partial_tree(
    values: &[Proth120],
    log_domain: u32,
    log_v: u32,
    columns: usize,
    skip_bottom: u32,
    stream: &CudaStream,
) -> Vec<Digest> {
    let retained_len = 2 * ((1usize << (log_domain - log_v)) >> skip_bottom) - 1;
    let d_values = upload(values, stream);
    let mut d_retained = sentinel_buffer(retained_len + 2, stream);
    if skip_bottom <= 8 {
        build_partial_coset_tree(
            &d_values,
            log_domain,
            log_v,
            columns as u32,
            skip_bottom,
            &mut d_retained[..retained_len],
            stream,
        )
        .unwrap();
    }
    if skip_bottom > 5 {
        let direct = (skip_bottom <= 8).then(|| download(&d_retained, SENTINEL, stream));
        let poison = vec![SENTINEL; retained_len];
        memory_copy_async(&mut d_retained[..retained_len], &poison, stream).unwrap();
        let scratch_len = partial_coset_tree_scratch_len(log_domain, log_v, skip_bottom);
        let mut scratch = sentinel_buffer(scratch_len + 2, stream);
        build_partial_coset_tree_with_scratch(
            &d_values,
            log_domain,
            log_v,
            columns as u32,
            skip_bottom,
            &mut d_retained[..retained_len],
            &mut scratch[1..scratch_len + 1],
            stream,
        )
        .unwrap();
        if let Some(direct) = direct {
            assert_eq!(download(&d_retained, SENTINEL, stream), direct);
        }
        let scratch = download(&scratch, SENTINEL, stream);
        assert_eq!([scratch[0], scratch[scratch_len + 1]], [SENTINEL; 2]);
    }
    let retained = download(&d_retained, SENTINEL, stream);
    assert_eq!(&retained[retained_len..], &[SENTINEL; 2]);
    retained[..retained_len].to_vec()
}

#[test]
fn keccak256_leaf_parity() {
    let stream = CudaStream::default();
    let mut rng = TestRng::new(0x6c65_6166);
    for log_domain in [8u32, 12] {
        for log_v in [0u32, 1, 2, 4] {
            for columns in [1usize, 7, 17] {
                let label = format!("log_domain={log_domain} log_v={log_v} columns={columns}");
                let domain = 1usize << log_domain;
                let leaves = domain >> log_v;
                let values = random_columns(&mut rng, columns, domain);
                let d_values = upload(&values, &stream);
                let mut d_out = sentinel_buffer(leaves + 3, &stream);
                hash_leaves(
                    &d_values,
                    log_domain,
                    log_v,
                    columns as u32,
                    &mut d_out[..leaves],
                    &stream,
                )
                .unwrap();
                let gpu = download(&d_out, SENTINEL, &stream);
                assert_eq!(&gpu[leaves..], &[SENTINEL; 3], "{label}");
                let expected = cpu_leaves(&values, columns, log_v);
                assert_eq!(&gpu[..leaves], &expected[..], "{label}");
                let cols = column_slices(&values, columns);
                let from_accessors = cpu_leaves_from_accessors(&cols, log_v);
                assert_eq!(&gpu[..leaves], &from_accessors[..], "{label}");
                if columns > 1 {
                    let mut swapped = cols.clone();
                    swapped.swap(0, 1);
                    let control = cpu_leaves_from_columns(&swapped, log_v);
                    assert!(
                        gpu[..leaves].iter().zip(&control).all(|(a, b)| a != b),
                        "{label}: swapped columns must change every leaf"
                    );
                }
            }
        }
    }
}

#[test]
fn keccak256_leaf_sponge_matches_hash_leaf() {
    let stream = CudaStream::default();
    let mut rng = TestRng::new(0x7370_6f6e);
    for (columns, log_v) in [
        (1usize, 1u32),
        (1, 2),
        (1, 3),
        (1, 4),
        (2, 1),
        (7, 2),
        (13, 1),
    ] {
        let log_domain = 10 + log_v;
        let domain = 1usize << log_domain;
        let leaves = domain >> log_v;
        let values = random_columns(&mut rng, columns, domain);
        let d_values = upload(&values, &stream);
        let mut d_out = sentinel_buffer(leaves, &stream);
        leaf_sponge_probe(
            &d_values,
            log_domain,
            log_v,
            columns as u32,
            &mut d_out,
            &stream,
        )
        .unwrap();
        let expected = cpu_leaves(&values, columns, log_v);
        assert_eq!(
            download(&d_out, SENTINEL, &stream),
            expected,
            "columns={columns} log_v={log_v}"
        );
    }
}

#[test]
fn keccak256_partial_tree_parity() {
    let stream = CudaStream::default();
    let mut rng = TestRng::new(0x7472_6565);
    for log_domain in [0u32, 4, 8, 10, 12] {
        for log_v in [0u32, 2, 4] {
            if log_v > log_domain {
                continue;
            }
            let log_leaves = log_domain - log_v;
            let columns = if log_domain % 4 == 0 { 3 } else { 1 };
            let values = random_columns(&mut rng, columns, 1 << log_domain);
            let tree = cpu_tree(&[values.clone()], columns, log_v, 1);
            for skip_bottom in 0..=log_leaves.min(10) {
                let label = format!("log_domain={log_domain} log_v={log_v} columns={columns} skip_bottom={skip_bottom}");
                let retained =
                    gpu_partial_tree(&values, log_domain, log_v, columns, skip_bottom, &stream);
                for layer in skip_bottom..=log_leaves {
                    let offset = retained_layer_offset(log_leaves, skip_bottom, layer);
                    let len = (1usize << log_leaves) >> layer;
                    assert_eq!(
                        &retained[offset..offset + len],
                        cpu_layer(&tree, layer),
                        "{label} layer={layer}"
                    );
                }
                assert_eq!(
                    retained[retained.len() - 1],
                    tree.get_cap().cap[0],
                    "{label} root"
                );
            }
        }
    }
}

#[test]
fn keccak256_top_tree_cap_parity() {
    let stream = CudaStream::default();
    let mut rng = TestRng::new(0x746f_7074);
    let (log_domain, log_v, columns, skip_bottom) = (6u32, 2u32, 2usize, 3u32);
    let log_leaves = log_domain - log_v;
    let retained_len = 2 * ((1usize << log_leaves) >> skip_bottom) - 1;
    for log_lde in [2u32, 5] {
        let cosets_count = 1usize << log_lde;
        let cosets: Vec<Vec<Proth120>> = (0..cosets_count)
            .map(|_| random_columns(&mut rng, columns, 1 << log_domain))
            .collect();
        let mut d_roots = sentinel_buffer(cosets_count, &stream);
        for (coset, values) in cosets.iter().enumerate() {
            let d_values = upload(values, &stream);
            let mut d_retained = sentinel_buffer(retained_len, &stream);
            build_partial_coset_tree(
                &d_values,
                log_domain,
                log_v,
                columns as u32,
                skip_bottom,
                &mut d_retained,
                &stream,
            )
            .unwrap();
            let physical = bitreverse_index(coset, log_lde);
            memory_copy_async(
                &mut d_roots[physical..physical + 1],
                &d_retained[retained_len - 1..],
                &stream,
            )
            .unwrap();
            stream.synchronize().unwrap();
        }
        let roots = download(&d_roots, SENTINEL, &stream);
        for cap_log in 0..=log_lde {
            let label = format!("log_lde={log_lde} cap_log={cap_log}");
            let cap_size = 1usize << cap_log;
            let tree = cpu_tree(&cosets, columns, log_v, cap_size);
            assert_eq!(&roots[..], cpu_layer(&tree, log_leaves), "{label} roots");
            let nodes_len = cosets_count - cap_size;
            let mut d_nodes = sentinel_buffer(nodes_len + 2, &stream);
            build_top_tree(&d_roots, cap_log, &mut d_nodes[..nodes_len], &stream).unwrap();
            let mut d_cap = sentinel_buffer(cap_size + 2, &stream);
            gather_tree_cap(
                &d_roots,
                &d_nodes[..nodes_len],
                cap_log,
                &mut d_cap[..cap_size],
                &stream,
            )
            .unwrap();
            let nodes = download(&d_nodes, SENTINEL, &stream);
            let cap = download(&d_cap, SENTINEL, &stream);
            assert_eq!(&nodes[nodes_len..], &[SENTINEL; 2], "{label}");
            assert_eq!(&cap[cap_size..], &[SENTINEL; 2], "{label}");
            for layer in 1..=log_lde - cap_log {
                let offset = top_nodes_layer_offset(log_lde, layer);
                let len = cosets_count >> layer;
                assert_eq!(
                    &nodes[offset..offset + len],
                    cpu_layer(&tree, log_leaves + layer),
                    "{label} top layer={layer}"
                );
            }
            assert_eq!(&cap[..cap_size], &tree.get_cap().cap[..], "{label} cap");
        }
    }
}

#[test]
fn keccak256_multi_coset_tile_parity() {
    let stream = CudaStream::default();
    let mut rng = TestRng::new(0x7469_6c65);
    for (log_domain, log_v, columns, skip_bottom) in [
        (8u32, 2u32, 3usize, 5u32),
        (8, 4, 1, 4),
        (4, 4, 2, 0),
        (10, 2, 3, 6),
        (10, 2, 3, 7),
        (10, 2, 3, 8),
        (12, 2, 3, 9),
        (12, 2, 3, 10),
        (12, 0, 1, 10),
    ] {
        let log_leaves = log_domain - log_v;
        let leaves = 1usize << log_leaves;
        let coset_values = columns << log_domain;
        let retained_len = 2 * (leaves >> skip_bottom) - 1;
        for cosets_count in [2usize, 4] {
            let label = format!("log_domain={log_domain} log_v={log_v} columns={columns} skip_bottom={skip_bottom} cosets={cosets_count}");
            let (values_stride, out_stride, retained_stride) =
                (coset_values + 5, leaves + 3, retained_len + 2);
            let values_len = (cosets_count - 1) * values_stride + coset_values;
            let value_sentinel = Proth120::new(0x5eed);
            let mut tile_values = vec![value_sentinel; values_len];
            for coset in 0..cosets_count {
                tile_values[coset * values_stride..coset * values_stride + coset_values]
                    .copy_from_slice(&random_columns(&mut rng, columns, 1 << log_domain));
            }
            let d_values = upload(&tile_values, &stream);
            let out_len = (cosets_count - 1) * out_stride + leaves + 2;
            let retained_tile_len = (cosets_count - 1) * retained_stride + retained_len + 2;
            let mut d_out = sentinel_buffer(out_len, &stream);
            let mut d_retained = sentinel_buffer(retained_tile_len, &stream);
            hash_leaves_multi_coset(
                &d_values,
                log_domain,
                log_v,
                columns as u32,
                cosets_count as u32,
                values_stride,
                out_stride,
                &mut d_out[..out_len - 2],
                &stream,
            )
            .unwrap();
            if skip_bottom <= 5 {
                build_partial_coset_trees_multi_coset(
                    &d_values,
                    log_domain,
                    log_v,
                    columns as u32,
                    skip_bottom,
                    cosets_count as u32,
                    values_stride,
                    retained_stride,
                    &mut d_retained[..retained_tile_len - 2],
                    &stream,
                )
                .unwrap();
            } else {
                let scratch_len = partial_coset_tree_scratch_len(log_domain, log_v, skip_bottom);
                let mut scratch = sentinel_buffer(scratch_len + 2, &stream);
                build_partial_coset_trees_multi_coset_with_scratch(
                    &d_values,
                    log_domain,
                    log_v,
                    columns as u32,
                    skip_bottom,
                    cosets_count as u32,
                    values_stride,
                    retained_stride,
                    &mut d_retained[..retained_tile_len - 2],
                    &mut scratch[1..scratch_len + 1],
                    &stream,
                )
                .unwrap();
                let scratch = download(&scratch, SENTINEL, &stream);
                assert_eq!([scratch[0], scratch[scratch_len + 1]], [SENTINEL; 2]);
            }
            let out = download(&d_out, SENTINEL, &stream);
            let retained = download(&d_retained, SENTINEL, &stream);
            let values_after = download(&d_values, Proth120::new(0), &stream);
            assert_eq!(values_after, tile_values, "{label} values");
            for coset in 1..cosets_count {
                assert!(
                    values_after[(coset - 1) * values_stride + coset_values..coset * values_stride]
                        .iter()
                        .all(|v| *v == value_sentinel),
                    "{label} coset={coset} values gap"
                );
            }
            for coset in 0..cosets_count {
                let values =
                    &tile_values[coset * values_stride..coset * values_stride + coset_values];
                let expected_leaves = cpu_leaves(values, columns, log_v);
                let out_window = &out[coset * out_stride..coset * out_stride + leaves];
                assert_eq!(
                    out_window,
                    &expected_leaves[..],
                    "{label} coset={coset} leaves"
                );
                let single =
                    gpu_partial_tree(values, log_domain, log_v, columns, skip_bottom, &stream);
                let retained_window =
                    &retained[coset * retained_stride..coset * retained_stride + retained_len];
                assert_eq!(
                    retained_window,
                    &single[..],
                    "{label} coset={coset} retained"
                );
                let tree = cpu_tree(&[values.to_vec()], columns, log_v, 1);
                assert_eq!(
                    retained_window[retained_len - 1],
                    tree.get_cap().cap[0],
                    "{label} coset={coset} root"
                );
                let out_gap_end = if coset + 1 == cosets_count {
                    out_len
                } else {
                    (coset + 1) * out_stride
                };
                assert!(
                    out[coset * out_stride + leaves..out_gap_end]
                        .iter()
                        .all(|d| *d == SENTINEL),
                    "{label} coset={coset} out gap"
                );
                let retained_gap_end = if coset + 1 == cosets_count {
                    retained_tile_len
                } else {
                    (coset + 1) * retained_stride
                };
                assert!(
                    retained[coset * retained_stride + retained_len..retained_gap_end]
                        .iter()
                        .all(|d| *d == SENTINEL),
                    "{label} coset={coset} retained gap"
                );
            }
        }
    }
}

fn panic_message(f: impl FnOnce()) -> String {
    let payload = catch_unwind(AssertUnwindSafe(f)).expect_err("expected a named panic");
    payload
        .downcast_ref::<String>()
        .cloned()
        .or_else(|| payload.downcast_ref::<&str>().map(|s| s.to_string()))
        .unwrap()
}

fn assert_named_panic(expected: &str, f: impl FnOnce()) {
    let message = panic_message(f);
    assert!(
        message.contains(expected),
        "expected `{expected}`, got `{message}`"
    );
}

#[test]
fn cpu_keccak256_shape_validation() {
    const NAME: &str = "keccak256::shape";
    let name = "shape";
    assert_named_panic(&format!("{NAME}: log_domain <= 31"), || {
        leaf_shape(name, 32, 0, 1);
    });
    assert_named_panic(
        &format!("{NAME}: log_values_per_leaf <= log_domain"),
        || {
            leaf_shape(name, 8, 9, 1);
        },
    );
    assert_named_panic(&format!("{NAME}: columns >= 1"), || {
        leaf_shape(name, 8, 2, 0);
    });
    assert_named_panic(&format!("{NAME}: count overflow"), || {
        leaf_shape(name, 31, 31, u32::MAX);
    });
    assert_named_panic(&format!("{NAME}: u32 count overflow"), || {
        leaf_shape(name, 28, 0, 1 << 28);
    });
    let shape = leaf_shape(name, 8, 2, 3);
    assert_eq!(
        (shape.log_leaves, shape.leaves, shape.coset_values),
        (6, 64, 768)
    );
    assert_named_panic(&format!("{NAME}: cosets_in_tile >= 1"), || {
        leaf_tile(name, &shape, 768, 0, 768);
    });
    assert_named_panic(&format!("{NAME}: stride >= extent"), || {
        leaf_tile(name, &shape, 1536, 2, 767);
    });
    assert_named_panic(&format!("{NAME}: values.len() >="), || {
        leaf_tile(name, &shape, 1535, 2, 768);
    });
    assert_named_panic(&format!("{NAME}: count overflow"), || {
        leaf_tile(name, &shape, usize::MAX, u32::MAX, usize::MAX / 2);
    });
    let wide = leaf_shape(name, 31, 0, 1);
    assert_named_panic(&format!("{NAME}: grid <= 2^31 - 1"), || {
        leaf_tile(name, &wide, usize::MAX, u32::MAX, 1 << 31);
    });
    assert_eq!(leaf_tile(name, &shape, 1541, 2, 773).threads, 128);
    assert_named_panic(
        &format!("{NAME}: skip_bottom <= log_domain - log_values_per_leaf"),
        || {
            partial_tree_shape(name, 5, 2, 1, 4);
        },
    );
    assert_named_panic(&format!("{NAME}: skip_bottom <= 10"), || {
        partial_tree_shape(name, 13, 2, 1, 11);
    });
    for skip_bottom in 0..=10 {
        assert_eq!(
            partial_coset_tree_scratch_len(14, 2, skip_bottom),
            if skip_bottom <= 5 { 0 } else { 128 },
        );
    }
    assert_named_panic(
        &format!("{NAME}: skip_bottom <= log_domain - log_values_per_leaf"),
        || {
            partial_tree_shape(name, 8, 4, 1, 6);
        },
    );
    let tree = partial_tree_shape(name, 8, 2, 3, 5);
    assert_eq!(tree.retained_per_coset, 3);
    assert_named_panic(&format!("{NAME}: retained.len() >="), || {
        partial_tree_tile(name, &tree, 1536, 2, 768, 4, 6);
    });
    assert_named_panic(&format!("{NAME}: stride >= extent"), || {
        partial_tree_tile(name, &tree, 1536, 2, 768, 2, 6);
    });
    partial_tree_tile(name, &tree, 1536, 2, 768, 4, 7);
    assert_named_panic(&format!("{NAME}: roots.len() is a power of two"), || {
        top_tree_log_lde(name, 6, 0, 5);
    });
    assert_named_panic(&format!("{NAME}: cap_log <= log_lde"), || {
        top_tree_log_lde(name, 8, 4, 0);
    });
    assert_named_panic(
        &format!("{NAME}: nodes.len() == roots.len() - 2^cap_log"),
        || {
            top_tree_log_lde(name, 8, 1, 7);
        },
    );
    assert_eq!(top_tree_log_lde(name, 32, 3, 24), 5);
    assert_eq!(top_tree_log_lde(name, 32, 5, 0), 5);
    assert_named_panic(
        "keccak256::retained_layer_offset: skip_bottom <= layer <= log_leaves",
        || {
            retained_layer_offset(4, 3, 2);
        },
    );
    assert_named_panic(
        "keccak256::retained_layer_offset: skip_bottom <= layer <= log_leaves",
        || {
            retained_layer_offset(4, 3, 5);
        },
    );
    assert_named_panic(
        "keccak256::top_nodes_layer_offset: 1 <= layer <= log_lde",
        || {
            top_nodes_layer_offset(5, 0);
        },
    );
    assert_named_panic(
        "keccak256::top_nodes_layer_offset: 1 <= layer <= log_lde",
        || {
            top_nodes_layer_offset(5, 6);
        },
    );
    assert_eq!(retained_layer_offset(24, 5, 5), 0);
    assert_eq!(retained_layer_offset(24, 5, 6), 1 << 19);
    assert_eq!(retained_layer_offset(24, 5, 24), (1 << 20) - 2);
    assert_eq!(top_nodes_layer_offset(5, 1), 0);
    assert_eq!(top_nodes_layer_offset(5, 2), 16);
    assert_eq!(top_nodes_layer_offset(5, 5), 30);
    let base = partial_tree_shape(name, 26, 2, 7, 5);
    assert_eq!(base.leaves.leaves, 1 << 24);
    assert_eq!(base.leaves.coset_values, 7 << 26);
    assert_eq!(base.retained_per_coset, (1 << 20) - 1);
    let base_tile = partial_tree_tile(
        name,
        &base,
        7 << 26,
        1,
        7 << 26,
        (1 << 20) - 1,
        (1 << 20) - 1,
    );
    assert_eq!(base_tile.leaves.threads, 1 << 24);
    for (log_poly, skip_bottom, retained_per_coset) in [
        (24u32, 5u32, (1usize << 16) - 1),
        (20, 5, (1 << 12) - 1),
        (16, 5, 255),
        (12, 5, 15),
        (8, 4, 1),
    ] {
        let oracle = partial_tree_shape(name, log_poly, 4, 1, skip_bottom);
        assert_eq!(oracle.retained_per_coset, retained_per_coset);
        let cosets_per_pass = 1u32 << (26 - log_poly);
        let tile = partial_tree_tile(
            name,
            &oracle,
            (cosets_per_pass as usize) << log_poly,
            cosets_per_pass,
            1 << log_poly,
            retained_per_coset,
            cosets_per_pass as usize * retained_per_coset,
        );
        assert_eq!(tile.leaves.threads, 1 << 22);
    }
    let bytes = unsafe { DeviceSlice::<u8>::from_raw_parts(0x1000 as *const u8, 64) };
    let overlapping = unsafe { DeviceSlice::<Digest>::from_raw_parts(0x1020 as *const Digest, 2) };
    let adjacent = unsafe { DeviceSlice::<Digest>::from_raw_parts(0x1040 as *const Digest, 2) };
    assert_named_panic(&format!("{NAME}: buffers must not overlap"), || {
        assert_no_overlap(name, bytes, overlapping);
    });
    assert_no_overlap(name, bytes, adjacent);
}
