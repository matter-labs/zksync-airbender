use era_cudart::memory::{memory_copy_async, DeviceAllocation};
use era_cudart::stream::CudaStream;

use super::super::{
    build_partial_coset_trees_multi_coset, build_top_tree, gather_tree_cap, hash_leaves,
    hash_leaves_multi_coset, retained_layer_offset, top_nodes_layer_offset, Digest,
};
use super::{
    bitreverse_index, column_slices, cpu_layer, cpu_tree, download, random_columns, test_worker,
    upload, TestRng, SENTINEL,
};
use crate::upstream::{
    ColumnMajorMerkleTreeConstructor, Keccak256MerkleTreeWithCap, PathQueryable, PlainCosetLeaves,
    Proth120,
};

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

#[test]
fn keccak256_leaf_parity() {
    let stream = CudaStream::default();
    let mut rng = TestRng::new(0x6c65_6166);
    // Diagnostic base12/setup2 and WHIR v4 leaf widths.
    for (log_domain, log_v, columns) in [(18u32, 1u32, 12usize), (18, 1, 2), (11, 4, 1)] {
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

#[test]
fn keccak256_top_tree_cap_parity() {
    let stream = CudaStream::default();
    let mut rng = TestRng::new(0x746f_7074);
    let (log_domain, log_v, columns, skip_bottom) = (11u32, 4u32, 1usize, 5u32);
    let log_leaves = log_domain - log_v;
    let retained_len = 2 * ((1usize << log_leaves) >> skip_bottom) - 1;
    for log_lde in [7u32] {
        let cosets_count = 1usize << log_lde;
        let cosets: Vec<Vec<Proth120>> = (0..cosets_count)
            .map(|_| random_columns(&mut rng, columns, 1 << log_domain))
            .collect();
        let mut d_roots = sentinel_buffer(cosets_count, &stream);
        for (coset, values) in cosets.iter().enumerate() {
            let d_values = upload(values, &stream);
            let mut d_retained = sentinel_buffer(retained_len, &stream);
            build_partial_coset_trees_multi_coset(
                &d_values,
                log_domain,
                log_v,
                columns as u32,
                skip_bottom,
                1,
                values.len(),
                retained_len,
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
        for cap_log in [3u32] {
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
    for (log_domain, log_v, columns, skip_bottom) in [(11u32, 4u32, 1usize, 5u32)] {
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
                let retained_window =
                    &retained[coset * retained_stride..coset * retained_stride + retained_len];
                let tree = cpu_tree(&[values.to_vec()], columns, log_v, 1);
                for layer in skip_bottom..=log_domain - log_v {
                    let offset = retained_layer_offset(log_domain - log_v, skip_bottom, layer);
                    let expected = cpu_layer(&tree, layer);
                    assert_eq!(
                        &retained_window[offset..offset + expected.len()],
                        expected,
                        "{label} coset={coset} layer={layer}"
                    );
                }
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
