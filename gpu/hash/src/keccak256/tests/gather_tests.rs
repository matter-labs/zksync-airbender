use std::panic::{catch_unwind, AssertUnwindSafe};

use era_cudart::memory::memory_copy_async;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use sha3::{Digest as _, Keccak256};
use worker::Worker;

use super::super::{
    append_top_paths, build_partial_coset_tree, build_top_tree,
    gather_leaves_for_queries_single_coset, gather_merkle_paths_partial_for_queries_single_coset,
    gather_tree_cap, Digest,
};
use super::{
    bitreverse_index, cpu_tree, download, random_columns, test_worker, upload, TestRng, SENTINEL,
};
use crate::upstream::{
    keccak_leaf_encoding_words, CosetByCosetBaseCommitment, CosetByCosetExtCommitment,
    Keccak256MerkleTreeWithCap, PathQueryable, Proth120, Twiddles,
};

struct Openings {
    values: Vec<Proth120>,
    paths: Vec<Vec<Digest>>,
    indexes: Vec<u32>,
    cap: Vec<Digest>,
}

fn boundary_queries(leaves: usize, cosets: usize, skip_bottom: u32) -> Vec<u32> {
    let log_lde = cosets.trailing_zeros();
    let block = 1usize << skip_bottom;
    let indexes = [
        0,
        leaves - 1,
        leaves / 2,
        leaves / 2 - 1,
        leaves / 2 + 1,
        block - 1,
        block.min(leaves - 1),
        (block + 1).min(leaves - 1),
        0,
    ];
    let mut queries: Vec<u32> = (0..cosets)
        .flat_map(|coset| indexes.map(|leaf| ((leaf << log_lde) + coset) as u32))
        .collect();
    queries.reverse();
    queries.rotate_left(3);
    queries
}

fn gather_openings(
    cosets: &[Vec<Proth120>],
    log_domain: u32,
    log_v: u32,
    cap_log: u32,
    skip_bottom: u32,
    queries: &[u32],
    check_resident_sentinels: bool,
) -> Openings {
    let stream = CudaStream::default();
    let domain = 1usize << log_domain;
    let values_per_leaf = 1usize << log_v;
    let columns = cosets[0].len() / domain;
    let log_leaves = log_domain - log_v;
    let leaves = 1usize << log_leaves;
    let log_lde = cosets.len().trailing_zeros();
    let depth = (log_leaves + log_lde - cap_log) as usize;
    let value_count = queries.len() * values_per_leaf * columns;
    let path_count = queries.len() * depth;
    let retained_count = 2 * (leaves >> skip_bottom) - 1;
    let value_sentinel = Proth120::new(0x5eed);
    let d_queries = upload(queries, &stream);
    let mut d_values_out = upload(&vec![value_sentinel; value_count + 2], &stream);
    let mut d_paths = upload(&vec![SENTINEL; path_count + 2], &stream);
    let mut d_indexes = upload(&vec![0xaaaa_aaaa; queries.len() + 2], &stream);
    let mut d_roots = upload(&vec![SENTINEL; cosets.len() + 2], &stream);
    let mut processed = vec![false; cosets.len()];
    for resident in (0..cosets.len()).rev() {
        let d_values = upload(&cosets[resident], &stream);
        let mut d_retained = upload(&vec![SENTINEL; retained_count + 2], &stream);
        build_partial_coset_tree(
            &d_values,
            log_domain,
            log_v,
            columns as u32,
            skip_bottom,
            &mut d_retained[1..retained_count + 1],
            &stream,
        )
        .unwrap();
        gather_leaves_for_queries_single_coset(
            &d_values,
            resident as u32,
            log_lde,
            log_domain,
            log_v,
            &d_queries,
            &mut d_values_out[1..value_count + 1],
            &stream,
        )
        .unwrap();
        gather_merkle_paths_partial_for_queries_single_coset(
            &d_values,
            resident as u32,
            log_lde,
            log_domain,
            log_v,
            cap_log,
            skip_bottom,
            &d_retained[1..retained_count + 1],
            &d_queries,
            &mut d_paths[1..path_count + 1],
            &stream,
        )
        .unwrap();
        let physical = bitreverse_index(resident, log_lde);
        memory_copy_async(
            &mut d_roots[physical + 1..physical + 2],
            &d_retained[retained_count..retained_count + 1],
            &stream,
        )
        .unwrap();
        let retained = download(&d_retained, SENTINEL, &stream);
        assert_eq!(retained[0], SENTINEL);
        assert_eq!(retained[retained_count + 1], SENTINEL);
        processed[resident] = true;
        if check_resident_sentinels {
            let values = download(&d_values_out, value_sentinel, &stream);
            let paths = download(&d_paths, SENTINEL, &stream);
            for (i, &query) in queries.iter().enumerate() {
                let coset = query as usize & (cosets.len() - 1);
                let value_start = 1 + i * values_per_leaf * columns;
                let path_start = 1 + i * depth;
                if !processed[coset] {
                    assert!(
                        values[value_start..value_start + values_per_leaf * columns]
                            .iter()
                            .all(|value| *value == value_sentinel),
                        "resident={resident} query={query} unmatched values"
                    );
                    assert!(
                        paths[path_start..path_start + depth]
                            .iter()
                            .all(|digest| *digest == SENTINEL),
                        "resident={resident} query={query} unmatched path"
                    );
                }
                assert!(
                    paths[path_start + log_leaves as usize..path_start + depth]
                        .iter()
                        .all(|digest| *digest == SENTINEL),
                    "resident={resident} query={query} top path"
                );
            }
        }
    }
    let cap_count = 1usize << cap_log;
    let nodes_count = cosets.len() - cap_count;
    let mut d_nodes = upload(&vec![SENTINEL; nodes_count + 2], &stream);
    let mut d_cap = upload(&vec![SENTINEL; cap_count + 2], &stream);
    build_top_tree(
        &d_roots[1..cosets.len() + 1],
        cap_log,
        &mut d_nodes[1..nodes_count + 1],
        &stream,
    )
    .unwrap();
    gather_tree_cap(
        &d_roots[1..cosets.len() + 1],
        &d_nodes[1..nodes_count + 1],
        cap_log,
        &mut d_cap[1..cap_count + 1],
        &stream,
    )
    .unwrap();
    append_top_paths(
        &d_roots[1..cosets.len() + 1],
        &d_nodes[1..nodes_count + 1],
        log_lde,
        cap_log,
        log_leaves,
        &d_queries,
        &mut d_paths[1..path_count + 1],
        &mut d_indexes[1..queries.len() + 1],
        &stream,
    )
    .unwrap();
    let values = download(&d_values_out, value_sentinel, &stream);
    let paths = download(&d_paths, SENTINEL, &stream);
    let indexes = download(&d_indexes, 0, &stream);
    let roots = download(&d_roots, SENTINEL, &stream);
    let nodes = download(&d_nodes, SENTINEL, &stream);
    let cap = download(&d_cap, SENTINEL, &stream);
    assert_eq!([values[0], values[value_count + 1]], [value_sentinel; 2]);
    assert_eq!([paths[0], paths[path_count + 1]], [SENTINEL; 2]);
    assert_eq!([indexes[0], indexes[queries.len() + 1]], [0xaaaa_aaaa; 2]);
    assert_eq!([roots[0], roots[cosets.len() + 1]], [SENTINEL; 2]);
    assert_eq!([nodes[0], nodes[nodes_count + 1]], [SENTINEL; 2]);
    assert_eq!([cap[0], cap[cap_count + 1]], [SENTINEL; 2]);
    Openings {
        values: values[1..value_count + 1].to_vec(),
        paths: if depth == 0 {
            vec![vec![]; queries.len()]
        } else {
            paths[1..path_count + 1]
                .chunks_exact(depth)
                .map(|path| path.to_vec())
                .collect()
        },
        indexes: indexes[1..queries.len() + 1].to_vec(),
        cap: cap[1..cap_count + 1].to_vec(),
    }
}

fn expected_values(coset: &[Proth120], leaf: usize, columns: usize, log_v: u32) -> Vec<Proth120> {
    let domain = coset.len() / columns;
    let leaves = domain >> log_v;
    (0..1usize << log_v)
        .flat_map(|slot| {
            (0..columns).map(move |column| {
                coset[column * domain + leaf + bitreverse_index(slot, log_v) * leaves]
            })
        })
        .collect()
}

fn hash_words(words: impl IntoIterator<Item = u32>) -> Digest {
    let bytes: Vec<u8> = words.into_iter().flat_map(u32::to_be_bytes).collect();
    let bytes = Keccak256::digest(bytes);
    std::array::from_fn(|word| {
        u32::from_be_bytes(bytes[4 * word..4 * word + 4].try_into().unwrap())
    })
}

fn included(
    values: &[Proth120],
    columns: usize,
    log_v: u32,
    path: &[Digest],
    index: usize,
    cap: &[Digest],
) -> bool {
    let values: Vec<Proth120> = (0..columns)
        .flat_map(|column| (0..1usize << log_v).map(move |slot| values[slot * columns + column]))
        .collect();
    let mut digest = hash_words(keccak_leaf_encoding_words(&values));
    for (level, sibling) in path.iter().enumerate() {
        digest = if (index >> level) & 1 == 0 {
            hash_words(digest.into_iter().chain(*sibling))
        } else {
            hash_words(sibling.iter().copied().chain(digest))
        };
    }
    digest == cap[index >> path.len()]
}

#[test]
fn keccak256_query_gather_parity() {
    let mut rng = TestRng::new(0x6761_7468_6572);
    let log_domain = 10;
    for (log_lde, cap_log) in [(2, 0), (2, 2), (5, 0), (5, 3)] {
        for log_v in [2, 4] {
            for columns in [1, 7] {
                let cosets: Vec<_> = (0..1usize << log_lde)
                    .map(|_| random_columns(&mut rng, columns, 1 << log_domain))
                    .collect();
                let tree = cpu_tree(&cosets, columns, log_v, 1 << cap_log);
                let leaves = 1usize << (log_domain - log_v);
                for skip_bottom in [0, 1, 5] {
                    let queries = boundary_queries(leaves, cosets.len(), skip_bottom);
                    let gpu = gather_openings(
                        &cosets,
                        log_domain,
                        log_v,
                        cap_log,
                        skip_bottom,
                        &queries,
                        true,
                    );
                    let label = format!("log_lde={log_lde} cap_log={cap_log} log_v={log_v} columns={columns} skip={skip_bottom}");
                    assert_eq!(gpu.cap, tree.get_cap().cap, "{label}");
                    for (i, &query) in queries.iter().enumerate() {
                        let coset = query as usize & (cosets.len() - 1);
                        let leaf = query as usize >> log_lde;
                        let index = bitreverse_index(coset, log_lde) * leaves + leaf;
                        let (_, path) = tree.get_proof(index);
                        let values =
                            &gpu.values[i * (columns << log_v)..(i + 1) * (columns << log_v)];
                        assert_eq!(
                            values,
                            expected_values(&cosets[coset], leaf, columns, log_v),
                            "{label} q={query}"
                        );
                        assert_eq!(gpu.indexes[i] as usize, index, "{label} q={query}");
                        assert_eq!(gpu.paths[i], path, "{label} q={query}");
                        assert!(
                            included(values, columns, log_v, &gpu.paths[i], index, &gpu.cap),
                            "{label} q={query}"
                        );
                    }
                    let mut corrupt_values = gpu.values[..columns << log_v].to_vec();
                    corrupt_values[0] = Proth120::new(if corrupt_values[0] == Proth120::new(0) {
                        1
                    } else {
                        0
                    });
                    assert!(
                        !included(
                            &corrupt_values,
                            columns,
                            log_v,
                            &gpu.paths[0],
                            gpu.indexes[0] as usize,
                            &gpu.cap
                        ),
                        "{label} corrupt value"
                    );
                    let mut corrupt_path = gpu.paths[0].clone();
                    corrupt_path[0][0] ^= 1;
                    assert!(
                        !included(
                            &gpu.values[..columns << log_v],
                            columns,
                            log_v,
                            &corrupt_path,
                            gpu.indexes[0] as usize,
                            &gpu.cap
                        ),
                        "{label} corrupt sibling"
                    );
                }
            }
        }
    }
}

fn scatter_openings(
    values: impl IntoIterator<Item = (usize, Vec<Proth120>)>,
    log_domain: u32,
    log_v: u32,
    cosets_count: usize,
    columns: usize,
) -> Vec<Vec<Proth120>> {
    let domain = 1usize << log_domain;
    let leaves = domain >> log_v;
    let log_lde = cosets_count.trailing_zeros();
    let mut cosets = vec![vec![Proth120::new(0); columns * domain]; cosets_count];
    let mut seen = vec![false; cosets_count * domain * columns];
    for (query, values) in values {
        let coset = query & (cosets_count - 1);
        let leaf = query >> log_lde;
        assert_eq!(values.len(), columns << log_v);
        for slot in 0..1usize << log_v {
            for column in 0..columns {
                let position = column * domain + leaf + bitreverse_index(slot, log_v) * leaves;
                assert!(!seen[coset * columns * domain + position]);
                seen[coset * columns * domain + position] = true;
                cosets[coset][position] = values[slot * columns + column];
            }
        }
    }
    assert!(seen.into_iter().all(|value| value));
    cosets
}

#[test]
fn keccak256_openings_cpu_parity() {
    let (log_domain, log_v, log_lde, cap_log, columns) = (8, 2, 2, 1, 3);
    let worker = test_worker();
    let twiddles = Twiddles::new(1 << log_domain, &worker);
    let mut rng = TestRng::new(0x6261_7365);
    let input = random_columns(&mut rng, columns, 1 << log_domain);
    let columns_input: Vec<_> = input.chunks_exact(1 << log_domain).collect();
    let commitment = CosetByCosetBaseCommitment::<Proth120, Keccak256MerkleTreeWithCap>::commit(
        &columns_input,
        &twiddles,
        1 << log_lde,
        log_v as usize,
        1 << cap_log,
        log_domain as usize,
        &worker,
    );
    let all_queries: Vec<usize> = (0..1usize << (log_domain - log_v + log_lde)).collect();
    let all = commitment.query_many(&all_queries, &twiddles, &worker);
    let cosets = scatter_openings(
        all_queries
            .iter()
            .copied()
            .zip(all.into_iter().map(|query| query.leaf_values_concatenated)),
        log_domain,
        log_v,
        1 << log_lde,
        columns,
    );
    let queries = boundary_queries(1 << (log_domain - log_v), 1 << log_lde, 3);
    let expected = commitment.query_many(
        &queries.iter().map(|&q| q as usize).collect::<Vec<_>>(),
        &twiddles,
        &worker,
    );
    let gpu = gather_openings(&cosets, log_domain, log_v, cap_log, 3, &queries, true);
    assert_eq!(gpu.cap, commitment.get_cap().cap);
    for (i, expected) in expected.iter().enumerate() {
        assert_eq!(gpu.indexes[i] as usize, expected.index);
        assert_eq!(gpu.paths[i], expected.path);
        assert_eq!(
            &gpu.values[i * (columns << log_v)..(i + 1) * (columns << log_v)],
            &expected.leaf_values_concatenated
        );
    }
}

#[test]
fn keccak256_grouped_ext_openings_cpu_parity() {
    let (log_domain, log_v, log_lde, cap_log) = (8, 4, 4, 1);
    let worker = test_worker();
    let serial_worker = Worker::new_with_num_threads(1);
    let twiddles = Twiddles::new(1 << log_domain, &worker);
    let mut rng = TestRng::new(0x6578_7465_6e64);
    let coefficients = random_columns(&mut rng, 1, 1 << log_domain);
    let commitment =
        CosetByCosetExtCommitment::<Proth120, Proth120, Keccak256MerkleTreeWithCap>::commit(
            &coefficients,
            &twiddles,
            1 << log_lde,
            1 << log_v,
            1 << cap_log,
            &worker,
        );
    let serial =
        CosetByCosetExtCommitment::<Proth120, Proth120, Keccak256MerkleTreeWithCap>::commit(
            &coefficients,
            &twiddles,
            1 << log_lde,
            1 << log_v,
            1 << cap_log,
            &serial_worker,
        );
    assert!(commitment.group_log2 > 0);
    assert_eq!(serial.group_log2, 0);
    assert_eq!(commitment.get_cap().cap, serial.get_cap().cap);
    let all_queries: Vec<usize> = (0..1usize << (log_domain - log_v + log_lde)).collect();
    let all = commitment.query_many(&all_queries, &twiddles, &worker);
    let cosets = scatter_openings(
        all_queries
            .iter()
            .copied()
            .zip(all.into_iter().map(|(_, values, _)| values)),
        log_domain,
        log_v,
        1 << log_lde,
        1,
    );
    let queries = boundary_queries(1 << (log_domain - log_v), 1 << log_lde, 1);
    let query_indexes = queries.iter().map(|&q| q as usize).collect::<Vec<_>>();
    let expected = commitment.query_many(&query_indexes, &twiddles, &worker);
    let serial_expected = serial.query_many(&query_indexes, &twiddles, &serial_worker);
    let gpu = gather_openings(&cosets, log_domain, log_v, cap_log, 1, &queries, true);
    assert_eq!(gpu.cap, commitment.get_cap().cap);
    for (i, ((coset, values, query), (serial_coset, serial_values, serial_query))) in
        expected.iter().zip(&serial_expected).enumerate()
    {
        assert_eq!(coset, serial_coset);
        assert_eq!(values, serial_values);
        assert_eq!(query.index, serial_query.index);
        assert_eq!(
            query.leaf_values_concatenated,
            serial_query.leaf_values_concatenated
        );
        assert_eq!(query.path, serial_query.path);
        assert_eq!(gpu.indexes[i] as usize, query.index);
        assert_eq!(gpu.paths[i], query.path);
        assert_eq!(&gpu.values[i << log_v..(i + 1) << log_v], values);
    }
}

fn named_panic(name: &str, condition: &str, f: impl FnOnce()) {
    let payload = catch_unwind(AssertUnwindSafe(f)).expect_err("expected a named panic");
    let message = payload
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| payload.downcast_ref::<&str>().copied())
        .unwrap();
    let expected = format!("keccak256::{name}:");
    assert!(
        message.contains(&expected) && message.contains(condition),
        "expected {expected} {condition}, got {message}"
    );
}

#[test]
fn keccak256_gather_invalid_shape_rejected() {
    let stream = CudaStream::default();
    let d_values = upload(&vec![Proth120::new(0); 256], &stream);
    let d_queries = upload(&[0u32, 1], &stream);
    let d_retained = upload(&vec![SENTINEL; 63], &stream);
    let d_roots = upload(&[SENTINEL; 4], &stream);
    let d_nodes = upload(&[SENTINEL; 2], &stream);
    let mut d_out = upload(&[Proth120::new(0x5eed); 8], &stream);
    let mut d_paths = upload(&[SENTINEL; 14], &stream);
    let mut d_indexes = upload(&[0xaaaa_aaaau32; 2], &stream);
    let leaves_name = "gather_leaves_for_queries_single_coset";
    for (resident, log_lde, log_domain, log_v, condition) in [
        (0, 2, 32, 2, "log_domain <= 31"),
        (0, 2, 8, 9, "log_values_per_leaf <= log_domain"),
        (0, 32, 8, 2, "log_domain <= 31"),
        (0, 26, 8, 2, "log_coset_leaves + log_lde <= 31"),
        (4, 2, 8, 2, "resident_coset < C"),
    ] {
        named_panic(leaves_name, condition, || {
            gather_leaves_for_queries_single_coset(
                &d_values, resident, log_lde, log_domain, log_v, &d_queries, &mut d_out, &stream,
            )
            .unwrap();
        });
    }
    named_panic(leaves_name, "values.len() % N == 0", || {
        gather_leaves_for_queries_single_coset(
            &d_values[..255],
            0,
            2,
            8,
            2,
            &d_queries,
            &mut d_out,
            &stream,
        )
        .unwrap();
    });
    named_panic(leaves_name, "columns >= 1", || {
        gather_leaves_for_queries_single_coset(
            &d_values[..0],
            0,
            2,
            8,
            2,
            &d_queries,
            &mut d_out,
            &stream,
        )
        .unwrap();
    });
    named_panic(leaves_name, "out.len() == Q * V * columns", || {
        gather_leaves_for_queries_single_coset(
            &d_values,
            0,
            2,
            8,
            2,
            &d_queries,
            &mut d_out[..7],
            &stream,
        )
        .unwrap();
    });
    let huge_queries = unsafe { DeviceSlice::from_raw_parts(d_queries.as_ptr(), usize::MAX) };
    named_panic(leaves_name, "count overflow", || {
        gather_leaves_for_queries_single_coset(
            &d_values,
            0,
            2,
            8,
            2,
            huge_queries,
            &mut d_out,
            &stream,
        )
        .unwrap();
    });
    let overlap_values =
        unsafe { DeviceSlice::from_raw_parts_mut(d_values.as_ptr() as *mut Proth120, 8) };
    named_panic(leaves_name, "buffers must not overlap", || {
        gather_leaves_for_queries_single_coset(
            &d_values,
            0,
            2,
            8,
            2,
            &d_queries,
            overlap_values,
            &stream,
        )
        .unwrap();
    });
    let paths_name = "gather_merkle_paths_partial_for_queries_single_coset";
    for (log_v, cap_log, skip, condition) in [
        (2, 3, 1, "cap_log <= log_lde"),
        (4, 1, 5, "skip_bottom <= log_domain - log_values_per_leaf"),
        (2, 1, 6, "skip_bottom <= 5"),
    ] {
        named_panic(paths_name, condition, || {
            gather_merkle_paths_partial_for_queries_single_coset(
                &d_values,
                0,
                2,
                8,
                log_v,
                cap_log,
                skip,
                &d_retained,
                &d_queries,
                &mut d_paths,
                &stream,
            )
            .unwrap();
        });
    }
    named_panic(paths_name, "retained.len() ==", || {
        gather_merkle_paths_partial_for_queries_single_coset(
            &d_values,
            0,
            2,
            8,
            2,
            1,
            1,
            &d_retained[..62],
            &d_queries,
            &mut d_paths,
            &stream,
        )
        .unwrap();
    });
    named_panic(paths_name, "paths.len() == Q * D", || {
        gather_merkle_paths_partial_for_queries_single_coset(
            &d_values,
            0,
            2,
            8,
            2,
            1,
            1,
            &d_retained,
            &d_queries,
            &mut d_paths[..13],
            &stream,
        )
        .unwrap();
    });
    let overlap_paths =
        unsafe { DeviceSlice::from_raw_parts_mut(d_retained.as_ptr() as *mut Digest, 14) };
    named_panic(paths_name, "buffers must not overlap", || {
        gather_merkle_paths_partial_for_queries_single_coset(
            &d_values,
            0,
            2,
            8,
            2,
            1,
            1,
            &d_retained,
            &d_queries,
            overlap_paths,
            &stream,
        )
        .unwrap();
    });
    let append_name = "append_top_paths";
    for (log_lde, cap_log, log_leaves, condition) in [
        (2, 3, 6, "cap_log <= log_lde"),
        (2, 1, 30, "log_coset_leaves + log_lde <= 31"),
        (2, 1, 32, "log_domain <= 31"),
    ] {
        named_panic(append_name, condition, || {
            append_top_paths(
                &d_roots,
                &d_nodes,
                log_lde,
                cap_log,
                log_leaves,
                &d_queries,
                &mut d_paths,
                &mut d_indexes,
                &stream,
            )
            .unwrap();
        });
    }
    named_panic(append_name, "roots.len() == C", || {
        append_top_paths(
            &d_roots[..3],
            &d_nodes,
            2,
            1,
            6,
            &d_queries,
            &mut d_paths,
            &mut d_indexes,
            &stream,
        )
        .unwrap();
    });
    named_panic(append_name, "nodes.len() ==", || {
        append_top_paths(
            &d_roots,
            &d_nodes[..1],
            2,
            1,
            6,
            &d_queries,
            &mut d_paths,
            &mut d_indexes,
            &stream,
        )
        .unwrap();
    });
    named_panic(append_name, "paths.len() == Q * D", || {
        append_top_paths(
            &d_roots,
            &d_nodes,
            2,
            1,
            6,
            &d_queries,
            &mut d_paths[..13],
            &mut d_indexes,
            &stream,
        )
        .unwrap();
    });
    named_panic(append_name, "tree_indexes.len() == Q", || {
        append_top_paths(
            &d_roots,
            &d_nodes,
            2,
            1,
            6,
            &d_queries,
            &mut d_paths,
            &mut d_indexes[..1],
            &stream,
        )
        .unwrap();
    });
    let overlap_indexes =
        unsafe { DeviceSlice::from_raw_parts_mut(d_paths.as_mut_ptr() as *mut u32, 2) };
    named_panic(append_name, "buffers must not overlap", || {
        append_top_paths(
            &d_roots,
            &d_nodes,
            2,
            1,
            6,
            &d_queries,
            &mut d_paths,
            overlap_indexes,
            &stream,
        )
        .unwrap();
    });
    let empty_queries = &d_queries[..0];
    gather_leaves_for_queries_single_coset(
        &d_values,
        0,
        2,
        8,
        2,
        empty_queries,
        &mut d_out[..0],
        &stream,
    )
    .unwrap();
    gather_merkle_paths_partial_for_queries_single_coset(
        &d_values,
        0,
        2,
        8,
        2,
        1,
        1,
        &d_retained,
        empty_queries,
        &mut d_paths[..0],
        &stream,
    )
    .unwrap();
    append_top_paths(
        &d_roots,
        &d_nodes,
        2,
        1,
        6,
        empty_queries,
        &mut d_paths[..0],
        &mut d_indexes[..0],
        &stream,
    )
    .unwrap();
    named_panic(paths_name, "skip_bottom <= 5", || {
        gather_merkle_paths_partial_for_queries_single_coset(
            &d_values,
            0,
            2,
            8,
            2,
            1,
            6,
            &d_retained,
            empty_queries,
            &mut d_paths[..0],
            &stream,
        )
        .unwrap();
    });
    named_panic(append_name, "nodes.len() ==", || {
        append_top_paths(
            &d_roots,
            &d_nodes[..1],
            2,
            1,
            6,
            empty_queries,
            &mut d_paths[..0],
            &mut d_indexes[..0],
            &stream,
        )
        .unwrap();
    });
    assert_eq!(
        download(&d_out, Proth120::new(0), &stream),
        [Proth120::new(0x5eed); 8]
    );
    assert_eq!(download(&d_paths, SENTINEL, &stream), [SENTINEL; 14]);
    assert_eq!(download(&d_indexes, 0, &stream), [0xaaaa_aaaa; 2]);
}
