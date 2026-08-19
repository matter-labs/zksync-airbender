use era_cudart::memory::{memory_copy_async, DeviceAllocation};
use era_cudart::stream::CudaStream;

use super::super::{
    build_partial_merkle_tree_multi_coset, build_partial_merkle_tree_multi_coset_physical, Digest,
};
use super::physical_leaf_tests::{bitreverse_rows, host_logical_leaf, random_values, upload};
use super::{bitreverse_index, random_digest};
use crate::upstream::{Blake2sState, USE_REDUCED_BLAKE2_ROUNDS};
use gpu_core::primitives::utils::LOG_WARP_SIZE;

/// `(log_rows_per_coset, log_rows_per_hash, cosets_count)`. Every entry keeps
/// `log_leaves_per_coset >= 9`, so a 512-leaf CTA never spans two cosets — the
/// only regime the partial-tree kernels are valid in.
const SHAPES: [(u32, u32, usize); 3] = [(11, 1, 1), (11, 1, 2), (14, 5, 2)];
const COLS_COUNTS: [usize; 2] = [1, 3];
const LOG_CAPS: [u32; 2] = [0, 2];

fn host_parent(left: &Digest, right: &Digest) -> Digest {
    let mut block = [0u32; 16];
    block[..8].copy_from_slice(left);
    block[8..].copy_from_slice(right);
    let mut digest = Digest::default();
    Blake2sState::compress_two_to_one::<USE_REDUCED_BLAKE2_ROUNDS>(&block, &mut digest);
    digest
}

pub(super) fn host_layer_above(layer: &[Digest]) -> Vec<Digest> {
    layer
        .as_chunks::<2>()
        .0
        .iter()
        .map(|pair| host_parent(&pair[0], &pair[1]))
        .collect()
}

/// One coset's partial-tree backing as the GPU lays it out: the CTA reduction
/// roots (`LOG_WARP_SIZE` layers above the leaves) followed by every node layer
/// the tower writes, `layers_count` layers in total.
fn host_partial_tower(leaves: &[Digest], layers_count: u32) -> Vec<Digest> {
    let mut layer = leaves.to_vec();
    for _ in 0..LOG_WARP_SIZE {
        layer = host_layer_above(&layer);
    }
    let mut tower = layer.clone();
    for _ in 1..layers_count {
        layer = host_layer_above(&layer);
        tower.extend_from_slice(&layer);
    }
    tower
}

fn check_partial_tree(
    stream: &CudaStream,
    log_rows_per_coset: u32,
    log_rows_per_hash: u32,
    cosets_count: usize,
    cols_count: usize,
    log_cap: u32,
) {
    let log_leaves_count = log_rows_per_coset - log_rows_per_hash;
    assert!(log_leaves_count >= 9);
    let rows_count = 1usize << log_rows_per_coset;
    let leaves_count = 1usize << log_leaves_count;
    let values_stride = cols_count * rows_count;
    let tree_stride = (leaves_count << 1) >> LOG_WARP_SIZE;
    let layers_count = log_leaves_count + 1 - LOG_WARP_SIZE - log_cap;
    let cap_size = 1usize << log_cap;
    let initialized_len = tree_stride - cap_size;
    let label = format!(
        "n={log_rows_per_coset} b={log_rows_per_hash} cosets={cosets_count} \
         cols={cols_count} cap={cap_size}"
    );

    let natural = random_values(values_stride * cosets_count);
    let physical = bitreverse_rows(&natural, cosets_count, cols_count, log_rows_per_coset);
    let natural_device = upload(&natural, stream);
    let physical_device = upload(&physical, stream);

    // Sentinel fill: a digest neither path writes must stay identical in both
    // backings, so an out-of-region write shows up in the whole-backing
    // comparison below.
    let sentinel = (0..tree_stride * cosets_count)
        .map(|_| random_digest())
        .collect::<Vec<_>>();
    let mut old_device = DeviceAllocation::alloc(sentinel.len()).unwrap();
    let mut new_device = DeviceAllocation::alloc(sentinel.len()).unwrap();
    memory_copy_async(&mut old_device, &sentinel, stream).unwrap();
    memory_copy_async(&mut new_device, &sentinel, stream).unwrap();

    build_partial_merkle_tree_multi_coset(
        &natural_device[..natural.len()],
        &mut old_device,
        log_rows_per_hash,
        layers_count,
        cosets_count,
        stream,
    )
    .unwrap();
    build_partial_merkle_tree_multi_coset_physical(
        &physical_device[..physical.len()],
        &mut new_device,
        log_rows_per_hash,
        layers_count,
        cosets_count,
        stream,
    )
    .unwrap();

    let mut old_host = vec![Digest::default(); sentinel.len()];
    let mut new_host = vec![Digest::default(); sentinel.len()];
    memory_copy_async(&mut old_host, &old_device, stream).unwrap();
    memory_copy_async(&mut new_host, &new_device, stream).unwrap();
    stream.synchronize().unwrap();

    for coset in 0..cosets_count {
        let start = coset * tree_stride;
        for digest in 0..tree_stride {
            assert_eq!(
                new_host[start + digest],
                old_host[start + digest],
                "{label}: coset {coset} backing digest {digest}",
            );
        }
        assert_eq!(
            &new_host[start + initialized_len - cap_size..start + initialized_len],
            &old_host[start + initialized_len - cap_size..start + initialized_len],
            "{label}: coset {coset} cap",
        );

        let host_leaves = (0..leaves_count)
            .map(|leaf| {
                host_logical_leaf(
                    &natural,
                    coset * values_stride,
                    rows_count,
                    cols_count,
                    leaves_count,
                    log_rows_per_hash,
                    leaf,
                )
            })
            .collect::<Vec<_>>();
        let host_tower = host_partial_tower(&host_leaves, layers_count);
        assert_eq!(host_tower.len(), initialized_len);
        assert_eq!(
            &new_host[start..start + initialized_len],
            &host_tower[..],
            "{label}: coset {coset} host tower",
        );

        // Negative control: the same tower over leaves left in PHYSICAL block
        // order — what the kernel would build if the logical -> physical block
        // translation were dropped — must not match.
        let untranslated_leaves = (0..leaves_count)
            .map(|block| host_leaves[bitreverse_index(block, log_leaves_count)])
            .collect::<Vec<_>>();
        let untranslated_tower = host_partial_tower(&untranslated_leaves, layers_count);
        assert_ne!(
            &new_host[start..start + initialized_len],
            &untranslated_tower[..],
            "{label}: coset {coset} untranslated control",
        );
    }
}

#[test]
fn physical_partial_tree_matches_old_kernel() {
    let stream = CudaStream::default();
    for (log_rows_per_coset, log_rows_per_hash, cosets_count) in SHAPES {
        for cols_count in COLS_COUNTS {
            for log_cap in LOG_CAPS {
                check_partial_tree(
                    &stream,
                    log_rows_per_coset,
                    log_rows_per_hash,
                    cosets_count,
                    cols_count,
                    log_cap,
                );
            }
        }
    }
}

#[test]
#[should_panic(expected = "one coset")]
fn physical_partial_tree_rejects_cta_spanning_cosets() {
    let stream = CudaStream::default();
    let (log_rows_per_coset, log_rows_per_hash, cosets_count, cols_count) = (8u32, 0u32, 2usize, 1);
    let rows_count = 1usize << log_rows_per_coset;
    let leaves_count = rows_count >> log_rows_per_hash;
    let tree_stride = (leaves_count << 1) >> LOG_WARP_SIZE;
    let values = random_values(cols_count * rows_count * cosets_count);
    let values_device = upload(&values, &stream);
    let mut tree_device = DeviceAllocation::<Digest>::alloc(tree_stride * cosets_count).unwrap();
    build_partial_merkle_tree_multi_coset_physical(
        &values_device[..values.len()],
        &mut tree_device,
        log_rows_per_hash,
        log_rows_per_coset + 1 - LOG_WARP_SIZE,
        cosets_count,
        &stream,
    )
    .unwrap();
}
