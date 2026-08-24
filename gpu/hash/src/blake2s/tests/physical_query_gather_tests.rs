use era_cudart::memory::{memory_copy_async, DeviceAllocation};
use era_cudart::stream::CudaStream;

use super::super::{
    build_partial_merkle_tree_multi_coset, build_partial_merkle_tree_multi_coset_physical,
    gather_leaf_rows, gather_leaf_rows_physical, gather_leaves_for_queries,
    gather_leaves_for_queries_physical, gather_merkle_paths_from_rows,
    gather_merkle_paths_from_rows_physical, gather_merkle_paths_partial_for_queries,
    gather_merkle_paths_partial_for_queries_physical, Digest, OracleGatherDesc,
    OraclePartialPathDesc,
};
use super::bitreverse_index;
use super::physical_leaf_tests::{bitreverse_rows, host_logical_leaf, random_values, upload};
use super::physical_partial_tree_tests::host_layer_above;
use gpu_core::primitives::device_structures::{DeviceMatrix, DeviceMatrixMut};
use gpu_core::primitives::field::BF;
use gpu_core::primitives::utils::LOG_WARP_SIZE;

/// `(log_domain_size, log_rows_per_leaf, log_lde_factor)` for the multi-coset
/// multi-oracle leaf gather: `V = 2` is the production base-oracle leaf width,
/// `V = 1` and `V = 32` pin the degenerate and wide ends.
const LEAF_SHAPES: [(u32, u32, u32); 4] = [(11, 1, 0), (11, 1, 1), (12, 0, 2), (14, 5, 1)];

/// `(log_rows_per_coset, log_rows_per_hash, cosets_count)`, reused from the
/// partial-tree builder tests: every entry keeps `log_leaves_per_coset >= 9`.
const PARTIAL_SHAPES: [(u32, u32, usize); 2] = [(11, 1, 2), (14, 5, 2)];

/// `(log_rows_count, log_rows_per_leaf)` for the single-coset holder readers.
const SINGLE_COSET_SHAPES: [(u32, u32); 3] = [(11, 1), (12, 0), (14, 5)];

const ORACLE_COLS: [&[usize]; 1] = [&[1, 2, 3]];
const COLS_COUNTS: [usize; 2] = [1, 3];
const LOG_CAPS: [u32; 2] = [0, 2];

/// Boundary queries over the flat domain `q = (internal << log_lde_factor) | coset`:
/// per coset, leaves 0/1, 31/32 (a 32-leaf warp-reduction group boundary), the
/// midpoint pair, and L-33/L-32/L-2/L-1. Element 0 is the global minimum, the
/// last the global maximum, and one query is repeated.
fn boundary_queries(log_lde_factor: u32, log_leaves_count: u32) -> Vec<u32> {
    assert!(log_leaves_count >= 6);
    let leaves = 1u32 << log_leaves_count;
    let cosets = 1u32 << log_lde_factor;
    let mut internals = vec![
        0,
        1,
        31,
        32,
        (leaves >> 1) - 1,
        leaves >> 1,
        leaves - 33,
        leaves - 32,
        leaves - 2,
        leaves - 1,
    ];
    internals.sort_unstable();
    internals.dedup();
    let mut queries = Vec::new();
    for coset in 0..cosets {
        for &internal in &internals {
            queries.push((internal << log_lde_factor) | coset);
        }
    }
    assert_eq!(queries[0], 0);
    queries.push(queries[3]);
    queries.push(((leaves - 1) << log_lde_factor) | (cosets - 1));
    queries
}

fn upload_u32(values: &[u32], stream: &CudaStream) -> DeviceAllocation<u32> {
    let mut device = DeviceAllocation::alloc(values.len()).unwrap();
    memory_copy_async(&mut device, values, stream).unwrap();
    device
}

fn download<T: Copy + Default>(device: &DeviceAllocation<T>, stream: &CudaStream) -> Vec<T> {
    let mut host = vec![T::default(); device.len()];
    memory_copy_async(&mut host, device, stream).unwrap();
    host
}

fn assert_elementwise_eq<T: Copy + PartialEq + std::fmt::Debug>(
    actual: &[T],
    expected: &[T],
    label: &str,
) {
    assert_eq!(actual.len(), expected.len(), "{label}: length");
    for (i, (&a, &e)) in actual.iter().zip(expected.iter()).enumerate() {
        assert_eq!(a, e, "{label}: element {i}");
    }
}

/// Logical leaf digests of one coset, then every node layer above them, so
/// `tower[layer][i]` is the tree node at height `layer`, index `i`.
fn host_tower(
    natural: &[BF],
    coset_base: usize,
    rows_count: usize,
    cols_count: usize,
    leaves_count: usize,
    log_rows_per_hash: u32,
    log_leaves_count: u32,
) -> Vec<Vec<Digest>> {
    let leaves = (0..leaves_count)
        .map(|leaf| {
            host_logical_leaf(
                natural,
                coset_base,
                rows_count,
                cols_count,
                leaves_count,
                log_rows_per_hash,
                leaf,
            )
        })
        .collect::<Vec<_>>();
    let mut tower = vec![leaves];
    for layer in 0..log_leaves_count as usize {
        tower.push(host_layer_above(&tower[layer]));
    }
    tower
}

fn check_leaf_gather(
    stream: &CudaStream,
    log_domain_size: u32,
    log_rows_per_leaf: u32,
    log_lde_factor: u32,
    cols_per_oracle: &[usize],
) {
    let num_oracles = cols_per_oracle.len();
    let log_leaves_count = log_domain_size - log_rows_per_leaf;
    let rows_count = 1usize << log_domain_size;
    let leaves_count = 1usize << log_leaves_count;
    let cosets_count = 1usize << log_lde_factor;
    let values_per_leaf = 1usize << log_rows_per_leaf;
    let lde_mask = cosets_count as u32 - 1;
    let queries = boundary_queries(log_lde_factor, log_leaves_count);
    let indexes_count = queries.len();
    let label = format!(
        "n={log_domain_size} b={log_rows_per_leaf} lde={log_lde_factor} cols={cols_per_oracle:?}"
    );
    let queries_device = upload_u32(&queries, stream);

    let mut natural_hosts = Vec::new();
    let mut natural_devices = Vec::new();
    let mut physical_devices = Vec::new();
    let mut old_slabs = Vec::new();
    let mut new_slabs = Vec::new();
    let mut control_slabs = Vec::new();
    for &cols in cols_per_oracle {
        let natural = random_values(cols * rows_count * cosets_count);
        let physical = bitreverse_rows(&natural, cosets_count, cols, log_domain_size);
        natural_devices.push(upload(&natural, stream));
        physical_devices.push(upload(&physical, stream));
        natural_hosts.push(natural);
        let slab_len = indexes_count * values_per_leaf * cols;
        old_slabs.push(DeviceAllocation::<BF>::alloc(slab_len).unwrap());
        new_slabs.push(DeviceAllocation::<BF>::alloc(slab_len).unwrap());
        control_slabs.push(DeviceAllocation::<BF>::alloc(slab_len).unwrap());
    }

    let mut old_descs = [OracleGatherDesc::default(); 3];
    let mut new_descs = [OracleGatherDesc::default(); 3];
    let mut control_descs = [OracleGatherDesc::default(); 3];
    for i in 0..num_oracles {
        let columns_count = cols_per_oracle[i] as u32;
        old_descs[i] = OracleGatherDesc {
            cosets_ptr: natural_devices[i].as_ptr() as u64,
            columns_count,
            _pad: 0,
            slab_dst_ptr: old_slabs[i].as_mut_ptr() as u64,
        };
        new_descs[i] = OracleGatherDesc {
            cosets_ptr: physical_devices[i].as_ptr() as u64,
            columns_count,
            _pad: 0,
            slab_dst_ptr: new_slabs[i].as_mut_ptr() as u64,
        };
        // Negative control: donor natural-order addressing over the bitreversed codeword.
        control_descs[i] = OracleGatherDesc {
            cosets_ptr: physical_devices[i].as_ptr() as u64,
            columns_count,
            _pad: 0,
            slab_dst_ptr: control_slabs[i].as_mut_ptr() as u64,
        };
    }

    gather_leaves_for_queries(
        &old_descs,
        num_oracles as u32,
        log_lde_factor,
        log_domain_size,
        log_rows_per_leaf,
        &queries_device,
        stream,
    )
    .unwrap();
    gather_leaves_for_queries_physical(
        &new_descs,
        num_oracles as u32,
        log_lde_factor,
        log_domain_size,
        log_rows_per_leaf,
        &queries_device,
        stream,
    )
    .unwrap();
    gather_leaves_for_queries(
        &control_descs,
        num_oracles as u32,
        log_lde_factor,
        log_domain_size,
        log_rows_per_leaf,
        &queries_device,
        stream,
    )
    .unwrap();

    let old_hosts = old_slabs
        .iter()
        .map(|slab| download(slab, stream))
        .collect::<Vec<_>>();
    let new_hosts = new_slabs
        .iter()
        .map(|slab| download(slab, stream))
        .collect::<Vec<_>>();
    let control_hosts = control_slabs
        .iter()
        .map(|slab| download(slab, stream))
        .collect::<Vec<_>>();
    stream.synchronize().unwrap();

    for (oracle, &cols) in cols_per_oracle.iter().enumerate() {
        assert_elementwise_eq(
            &new_hosts[oracle],
            &old_hosts[oracle],
            &format!("{label}: oracle {oracle} slab"),
        );
        assert!(
            new_hosts[oracle] != control_hosts[oracle],
            "{label}: oracle {oracle} untranslated control matched",
        );
        let natural = &natural_hosts[oracle];
        for (idx, &q) in queries.iter().enumerate() {
            let coset = (q & lde_mask) as usize;
            let internal = (q >> log_lde_factor) as usize;
            for slot in 0..values_per_leaf {
                let row = internal + bitreverse_index(slot, log_rows_per_leaf) * leaves_count;
                for col in 0..cols {
                    let expected = natural[coset * cols * rows_count + col * rows_count + row];
                    let actual =
                        new_hosts[oracle][idx * values_per_leaf * cols + slot * cols + col];
                    assert_eq!(
                        actual, expected,
                        "{label}: oracle {oracle} query {idx} (q={q}) slot {slot} col {col}",
                    );
                }
            }
        }
    }
}

fn check_partial_path_gather(
    stream: &CudaStream,
    log_rows_per_coset: u32,
    log_rows_per_hash: u32,
    cosets_count: usize,
    cols_per_oracle: &[usize],
    log_cap: u32,
) {
    let num_oracles = cols_per_oracle.len();
    let log_lde_factor = cosets_count.trailing_zeros();
    let log_leaves_count = log_rows_per_coset - log_rows_per_hash;
    let rows_count = 1usize << log_rows_per_coset;
    let leaves_count = 1usize << log_leaves_count;
    let lde_mask = cosets_count as u32 - 1;
    let tree_stride = (leaves_count << 1) >> LOG_WARP_SIZE;
    let builder_layers_count = log_leaves_count + 1 - LOG_WARP_SIZE;
    let layers_count = log_leaves_count - log_cap;
    assert!(layers_count >= LOG_WARP_SIZE);
    let queries = boundary_queries(log_lde_factor, log_leaves_count);
    let indexes_count = queries.len();
    let paths_len = indexes_count * layers_count as usize;
    let label = format!(
        "n={log_rows_per_coset} b={log_rows_per_hash} cosets={cosets_count} \
         cols={cols_per_oracle:?} cap=2^{log_cap}"
    );
    let queries_device = upload_u32(&queries, stream);

    let mut natural_hosts = Vec::new();
    let mut natural_devices = Vec::new();
    let mut physical_devices = Vec::new();
    let mut old_trees = Vec::new();
    let mut new_trees = Vec::new();
    let mut old_slabs = Vec::new();
    let mut new_slabs = Vec::new();
    let mut control_slabs = Vec::new();
    for &cols in cols_per_oracle {
        let natural = random_values(cols * rows_count * cosets_count);
        let physical = bitreverse_rows(&natural, cosets_count, cols, log_rows_per_coset);
        let natural_device = upload(&natural, stream);
        let physical_device = upload(&physical, stream);
        let mut old_tree = DeviceAllocation::<Digest>::alloc(tree_stride * cosets_count).unwrap();
        let mut new_tree = DeviceAllocation::<Digest>::alloc(tree_stride * cosets_count).unwrap();
        // The partial backing's last slot per coset is deliberately unwritten
        // (the tower stops at the cap); give both slabs identical contents so
        // the whole-slab comparison below is deterministic.
        let backing_fill = vec![Digest::default(); tree_stride * cosets_count];
        memory_copy_async(&mut old_tree, &backing_fill, stream).unwrap();
        memory_copy_async(&mut new_tree, &backing_fill, stream).unwrap();
        build_partial_merkle_tree_multi_coset(
            &natural_device[..natural.len()],
            &mut old_tree,
            log_rows_per_hash,
            builder_layers_count,
            cosets_count,
            stream,
        )
        .unwrap();
        let mut staging = DeviceAllocation::<Digest>::alloc(leaves_count * cosets_count).unwrap();
        build_partial_merkle_tree_multi_coset_physical(
            &physical_device[..physical.len()],
            &mut staging,
            &mut new_tree,
            log_rows_per_hash,
            builder_layers_count,
            cosets_count,
            stream,
        )
        .unwrap();
        natural_devices.push(natural_device);
        physical_devices.push(physical_device);
        natural_hosts.push(natural);
        old_trees.push(old_tree);
        new_trees.push(new_tree);
        old_slabs.push(DeviceAllocation::<Digest>::alloc(paths_len).unwrap());
        new_slabs.push(DeviceAllocation::<Digest>::alloc(paths_len).unwrap());
        control_slabs.push(DeviceAllocation::<Digest>::alloc(paths_len).unwrap());
    }

    let mut old_descs = [OraclePartialPathDesc::default(); 3];
    let mut new_descs = [OraclePartialPathDesc::default(); 3];
    let mut control_descs = [OraclePartialPathDesc::default(); 3];
    for i in 0..num_oracles {
        let columns_count = cols_per_oracle[i] as u32;
        old_descs[i] = OraclePartialPathDesc {
            cosets_ptr: natural_devices[i].as_ptr() as u64,
            partial_tree_ptr: old_trees[i].as_ptr() as u64,
            columns_count,
            _pad: 0,
            slab_dst_ptr: old_slabs[i].as_mut_ptr() as u64,
        };
        new_descs[i] = OraclePartialPathDesc {
            cosets_ptr: physical_devices[i].as_ptr() as u64,
            partial_tree_ptr: new_trees[i].as_ptr() as u64,
            columns_count,
            _pad: 0,
            slab_dst_ptr: new_slabs[i].as_mut_ptr() as u64,
        };
        // Negative control: donor natural-order leaf addressing over the bitreversed codeword.
        control_descs[i] = OraclePartialPathDesc {
            cosets_ptr: physical_devices[i].as_ptr() as u64,
            partial_tree_ptr: new_trees[i].as_ptr() as u64,
            columns_count,
            _pad: 0,
            slab_dst_ptr: control_slabs[i].as_mut_ptr() as u64,
        };
    }

    gather_merkle_paths_partial_for_queries(
        &old_descs,
        num_oracles as u32,
        log_lde_factor,
        log_rows_per_hash,
        log_leaves_count,
        layers_count,
        &queries_device,
        stream,
    )
    .unwrap();
    gather_merkle_paths_partial_for_queries_physical(
        &new_descs,
        num_oracles as u32,
        log_lde_factor,
        log_rows_per_hash,
        log_leaves_count,
        layers_count,
        &queries_device,
        stream,
    )
    .unwrap();
    gather_merkle_paths_partial_for_queries(
        &control_descs,
        num_oracles as u32,
        log_lde_factor,
        log_rows_per_hash,
        log_leaves_count,
        layers_count,
        &queries_device,
        stream,
    )
    .unwrap();

    let old_tree_hosts = old_trees
        .iter()
        .map(|tree| download(tree, stream))
        .collect::<Vec<_>>();
    let new_tree_hosts = new_trees
        .iter()
        .map(|tree| download(tree, stream))
        .collect::<Vec<_>>();
    let old_hosts = old_slabs
        .iter()
        .map(|slab| download(slab, stream))
        .collect::<Vec<_>>();
    let new_hosts = new_slabs
        .iter()
        .map(|slab| download(slab, stream))
        .collect::<Vec<_>>();
    let control_hosts = control_slabs
        .iter()
        .map(|slab| download(slab, stream))
        .collect::<Vec<_>>();
    stream.synchronize().unwrap();

    for (oracle, &cols) in cols_per_oracle.iter().enumerate() {
        assert_elementwise_eq(
            &new_tree_hosts[oracle],
            &old_tree_hosts[oracle],
            &format!("{label}: oracle {oracle} partial tree"),
        );
        assert_elementwise_eq(
            &new_hosts[oracle],
            &old_hosts[oracle],
            &format!("{label}: oracle {oracle} path slab"),
        );
        assert!(
            new_hosts[oracle] != control_hosts[oracle],
            "{label}: oracle {oracle} untranslated control matched",
        );
        let towers = (0..cosets_count)
            .map(|coset| {
                host_tower(
                    &natural_hosts[oracle],
                    coset * cols * rows_count,
                    rows_count,
                    cols,
                    leaves_count,
                    log_rows_per_hash,
                    log_leaves_count,
                )
            })
            .collect::<Vec<_>>();
        for (idx, &q) in queries.iter().enumerate() {
            let coset = (q & lde_mask) as usize;
            let internal = (q >> log_lde_factor) as usize;
            for layer in 0..layers_count as usize {
                // Query-major output: consecutive layers are one digest apart.
                let expected = towers[coset][layer][(internal >> layer) ^ 1];
                assert_eq!(
                    new_hosts[oracle][idx * layers_count as usize + layer],
                    expected,
                    "{label}: oracle {oracle} query {idx} (q={q}) layer {layer}",
                );
            }
        }
    }
}

fn check_leaf_rows(
    stream: &CudaStream,
    log_rows_count: u32,
    log_rows_per_leaf: u32,
    cols_count: usize,
    bit_reverse_indexes: bool,
) {
    let log_leaves_count = log_rows_count - log_rows_per_leaf;
    let rows_count = 1usize << log_rows_count;
    let leaves_count = 1usize << log_leaves_count;
    let values_per_leaf = 1usize << log_rows_per_leaf;
    let indexes = boundary_queries(0, log_leaves_count);
    let indexes_count = indexes.len();
    let dst_rows = indexes_count << log_rows_per_leaf;
    let label = format!(
        "n={log_rows_count} b={log_rows_per_leaf} cols={cols_count} rev={bit_reverse_indexes}"
    );
    let indexes_device = upload_u32(&indexes, stream);

    let natural = random_values(cols_count * rows_count);
    let physical = bitreverse_rows(&natural, 1, cols_count, log_rows_count);
    let natural_device = upload(&natural, stream);
    let physical_device = upload(&physical, stream);
    let mut old_result = DeviceAllocation::<BF>::alloc(dst_rows * cols_count).unwrap();
    let mut new_result = DeviceAllocation::<BF>::alloc(dst_rows * cols_count).unwrap();
    let mut control_result = DeviceAllocation::<BF>::alloc(dst_rows * cols_count).unwrap();

    gather_leaf_rows(
        &indexes_device,
        bit_reverse_indexes,
        log_rows_per_leaf,
        &DeviceMatrix::new(&natural_device[..natural.len()], rows_count),
        &mut DeviceMatrixMut::new(&mut old_result, dst_rows),
        stream,
    )
    .unwrap();
    gather_leaf_rows_physical(
        &indexes_device,
        bit_reverse_indexes,
        log_rows_per_leaf,
        &DeviceMatrix::new(&physical_device[..physical.len()], rows_count),
        &mut DeviceMatrixMut::new(&mut new_result, dst_rows),
        stream,
    )
    .unwrap();
    // Negative control: donor natural-order addressing over the bitreversed codeword.
    gather_leaf_rows(
        &indexes_device,
        bit_reverse_indexes,
        log_rows_per_leaf,
        &DeviceMatrix::new(&physical_device[..physical.len()], rows_count),
        &mut DeviceMatrixMut::new(&mut control_result, dst_rows),
        stream,
    )
    .unwrap();

    let old_host = download(&old_result, stream);
    let new_host = download(&new_result, stream);
    let control_host = download(&control_result, stream);
    stream.synchronize().unwrap();

    assert_elementwise_eq(&new_host, &old_host, &format!("{label}: slab"));
    assert!(
        new_host != control_host,
        "{label}: untranslated control matched",
    );
    for (idx, &index) in indexes.iter().enumerate() {
        let leaf = if bit_reverse_indexes {
            bitreverse_index(index as usize, log_leaves_count)
        } else {
            index as usize
        };
        for slot in 0..values_per_leaf {
            let row = leaf + bitreverse_index(slot, log_rows_per_leaf) * leaves_count;
            for col in 0..cols_count {
                let expected = natural[col * rows_count + row];
                let actual = new_host[col * dst_rows + (idx << log_rows_per_leaf) + slot];
                assert_eq!(
                    actual, expected,
                    "{label}: index {idx} (leaf {leaf}) slot {slot} col {col}",
                );
            }
        }
    }
}

fn check_paths_from_rows(
    stream: &CudaStream,
    log_rows_count: u32,
    log_rows_per_hash: u32,
    cols_count: usize,
    log_cap: u32,
) {
    let log_leaves_count = log_rows_count - log_rows_per_hash;
    let rows_count = 1usize << log_rows_count;
    let leaves_count = 1usize << log_leaves_count;
    let tree_stride = (leaves_count << 1) >> LOG_WARP_SIZE;
    let builder_layers_count = log_leaves_count + 1 - LOG_WARP_SIZE;
    let layers_count = log_leaves_count - log_cap;
    assert!(layers_count >= LOG_WARP_SIZE);
    let indexes = boundary_queries(0, log_leaves_count);
    let indexes_count = indexes.len();
    let paths_len = indexes_count * layers_count as usize;
    let label =
        format!("n={log_rows_count} b={log_rows_per_hash} cols={cols_count} cap=2^{log_cap}");
    let indexes_device = upload_u32(&indexes, stream);

    let natural = random_values(cols_count * rows_count);
    let physical = bitreverse_rows(&natural, 1, cols_count, log_rows_count);
    let natural_device = upload(&natural, stream);
    let physical_device = upload(&physical, stream);
    let mut old_tree = DeviceAllocation::<Digest>::alloc(tree_stride).unwrap();
    let mut new_tree = DeviceAllocation::<Digest>::alloc(tree_stride).unwrap();
    build_partial_merkle_tree_multi_coset(
        &natural_device[..natural.len()],
        &mut old_tree,
        log_rows_per_hash,
        builder_layers_count,
        1,
        stream,
    )
    .unwrap();
    let mut staging = DeviceAllocation::<Digest>::alloc(leaves_count).unwrap();
    build_partial_merkle_tree_multi_coset_physical(
        &physical_device[..physical.len()],
        &mut staging,
        &mut new_tree,
        log_rows_per_hash,
        builder_layers_count,
        1,
        stream,
    )
    .unwrap();
    let mut old_paths = DeviceAllocation::<Digest>::alloc(paths_len).unwrap();
    let mut new_paths = DeviceAllocation::<Digest>::alloc(paths_len).unwrap();
    let mut control_paths = DeviceAllocation::<Digest>::alloc(paths_len).unwrap();

    gather_merkle_paths_from_rows(
        &indexes_device,
        false,
        &natural_device[..natural.len()],
        log_rows_per_hash,
        cols_count,
        &old_tree,
        &mut old_paths,
        layers_count,
        stream,
    )
    .unwrap();
    gather_merkle_paths_from_rows_physical(
        &indexes_device,
        false,
        &physical_device[..physical.len()],
        log_rows_per_hash,
        cols_count,
        &new_tree,
        &mut new_paths,
        layers_count,
        stream,
    )
    .unwrap();
    // Negative control: donor natural-order leaf addressing over the bitreversed codeword.
    gather_merkle_paths_from_rows(
        &indexes_device,
        false,
        &physical_device[..physical.len()],
        log_rows_per_hash,
        cols_count,
        &new_tree,
        &mut control_paths,
        layers_count,
        stream,
    )
    .unwrap();

    let old_tree_host = download(&old_tree, stream);
    let new_tree_host = download(&new_tree, stream);
    let old_host = download(&old_paths, stream);
    let new_host = download(&new_paths, stream);
    let control_host = download(&control_paths, stream);
    stream.synchronize().unwrap();

    assert_elementwise_eq(
        &new_tree_host,
        &old_tree_host,
        &format!("{label}: partial tree"),
    );
    assert_elementwise_eq(&new_host, &old_host, &format!("{label}: path slab"));
    assert!(
        new_host != control_host,
        "{label}: untranslated control matched",
    );

    let tower = host_tower(
        &natural,
        0,
        rows_count,
        cols_count,
        leaves_count,
        log_rows_per_hash,
        log_leaves_count,
    );
    for (idx, &index) in indexes.iter().enumerate() {
        let leaf = index as usize;
        for layer in 0..layers_count as usize {
            // Layer-major output: consecutive layers are indexes_count digests apart.
            let expected = tower[layer][(leaf >> layer) ^ 1];
            assert_eq!(
                new_host[layer * indexes_count + idx],
                expected,
                "{label}: index {idx} (leaf {leaf}) layer {layer}",
            );
        }
    }
}

#[test]
fn physical_leaf_gather_matches_old_kernel() {
    let stream = CudaStream::default();
    for (log_domain_size, log_rows_per_leaf, log_lde_factor) in LEAF_SHAPES {
        for cols_per_oracle in ORACLE_COLS {
            check_leaf_gather(
                &stream,
                log_domain_size,
                log_rows_per_leaf,
                log_lde_factor,
                cols_per_oracle,
            );
        }
    }
}

#[test]
fn physical_partial_path_gather_matches_old_kernel() {
    let stream = CudaStream::default();
    for (log_rows_per_coset, log_rows_per_hash, cosets_count) in PARTIAL_SHAPES {
        for cols_per_oracle in ORACLE_COLS {
            for log_cap in LOG_CAPS {
                check_partial_path_gather(
                    &stream,
                    log_rows_per_coset,
                    log_rows_per_hash,
                    cosets_count,
                    cols_per_oracle,
                    log_cap,
                );
            }
        }
    }
}

#[test]
fn physical_leaf_rows_matches_old_kernel() {
    let stream = CudaStream::default();
    for (log_rows_count, log_rows_per_leaf) in SINGLE_COSET_SHAPES {
        for cols_count in COLS_COUNTS {
            for bit_reverse_indexes in [false, true] {
                check_leaf_rows(
                    &stream,
                    log_rows_count,
                    log_rows_per_leaf,
                    cols_count,
                    bit_reverse_indexes,
                );
            }
        }
    }
}

#[test]
fn physical_paths_from_rows_matches_old_kernel() {
    let stream = CudaStream::default();
    for (log_rows_count, log_rows_per_hash) in SINGLE_COSET_SHAPES {
        for cols_count in COLS_COUNTS {
            for log_cap in LOG_CAPS {
                check_paths_from_rows(
                    &stream,
                    log_rows_count,
                    log_rows_per_hash,
                    cols_count,
                    log_cap,
                );
            }
        }
    }
}
