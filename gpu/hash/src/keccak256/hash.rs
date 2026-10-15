use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use gpu_core::primitives::field::PR;

use super::{
    assert_no_overlap, checked_bytes, checked_log_size, checked_product, checked_u32, checked_u64,
    grid_dim, tile_extent, Digest, BLOCK_THREADS, SEED_BYTES,
};

cuda_kernel!(
    HashBytes,
    ab_keccak256_hash_bytes_kernel(input: *const u8, len: u64, out: *mut u8)
);

#[doc(hidden)]
pub fn hash_bytes(
    input: &DeviceSlice<u8>,
    out: &mut DeviceSlice<u8>,
    stream: &CudaStream,
) -> CudaResult<()> {
    const NAME: &str = "hash_bytes";
    assert_eq!(
        out.len(),
        SEED_BYTES,
        "keccak256::hash_bytes: out.len() == 32"
    );
    checked_bytes::<u8>(NAME, input.len());
    checked_bytes::<u8>(NAME, out.len());
    let len = checked_u64(NAME, input.len());
    assert_no_overlap(NAME, input, out);
    let args = HashBytesArguments::new(input.as_ptr(), len, out.as_mut_ptr());
    HashBytesFunction::default().launch(&CudaLaunchConfig::basic(1, 1, stream), &args)
}

pub(super) struct LeafShape {
    pub(super) log_leaves: u32,
    pub(super) leaves: usize,
    pub(super) coset_values: usize,
}

pub(super) fn leaf_shape(
    name: &str,
    log_domain: u32,
    log_values_per_leaf: u32,
    columns: u32,
) -> LeafShape {
    let domain = checked_log_size(name, log_domain);
    assert!(
        log_values_per_leaf <= log_domain,
        "keccak256::{name}: log_values_per_leaf <= log_domain"
    );
    assert!(columns >= 1, "keccak256::{name}: columns >= 1");
    let coset_values = checked_product(name, columns as usize, domain);
    let leaf_values = checked_product(name, columns as usize, 1usize << log_values_per_leaf);
    checked_u32(name, checked_bytes::<PR>(name, leaf_values));
    let log_leaves = log_domain - log_values_per_leaf;
    LeafShape {
        log_leaves,
        leaves: 1usize << log_leaves,
        coset_values,
    }
}

pub(super) struct LeafTile {
    pub(super) values_stride: u64,
    pub(super) threads: usize,
}

pub(super) fn leaf_tile(
    name: &str,
    shape: &LeafShape,
    values_len: usize,
    cosets_in_tile: u32,
    values_stride: usize,
) -> LeafTile {
    let values_extent = tile_extent(name, cosets_in_tile, values_stride, shape.coset_values);
    assert!(
        values_len >= values_extent,
        "keccak256::{name}: values.len() >= (cosets_in_tile - 1) * values_stride + columns << log_domain"
    );
    let threads = checked_product(name, cosets_in_tile as usize, shape.leaves);
    grid_dim(name, threads, BLOCK_THREADS);
    LeafTile {
        values_stride: checked_u64(name, values_stride),
        threads,
    }
}

cuda_kernel!(
    Leaves,
    ab_keccak256_leaves_kernel(
        values: *const PR,
        log_domain: u32,
        log_v: u32,
        columns: u32,
        cosets_in_tile: u32,
        values_stride: u64,
        out_stride: u64,
        out: *mut Digest,
    )
);

pub fn hash_leaves(
    values: &DeviceSlice<PR>,
    log_domain: u32,
    log_values_per_leaf: u32,
    columns: u32,
    out: &mut DeviceSlice<Digest>,
    stream: &CudaStream,
) -> CudaResult<()> {
    const NAME: &str = "hash_leaves";
    let shape = leaf_shape(NAME, log_domain, log_values_per_leaf, columns);
    assert_eq!(
        values.len(),
        shape.coset_values,
        "keccak256::hash_leaves: values.len() == columns << log_domain"
    );
    assert_eq!(
        out.len(),
        shape.leaves,
        "keccak256::hash_leaves: out.len() == 2^(log_domain - log_values_per_leaf)"
    );
    hash_leaves_multi_coset(
        values,
        log_domain,
        log_values_per_leaf,
        columns,
        1,
        values.len(),
        out.len(),
        out,
        stream,
    )
}

pub fn hash_leaves_multi_coset(
    values: &DeviceSlice<PR>,
    log_domain: u32,
    log_values_per_leaf: u32,
    columns: u32,
    cosets_in_tile: u32,
    values_stride: usize,
    out_stride: usize,
    out: &mut DeviceSlice<Digest>,
    stream: &CudaStream,
) -> CudaResult<()> {
    const NAME: &str = "hash_leaves_multi_coset";
    let shape = leaf_shape(NAME, log_domain, log_values_per_leaf, columns);
    let tile = leaf_tile(NAME, &shape, values.len(), cosets_in_tile, values_stride);
    let out_extent = tile_extent(NAME, cosets_in_tile, out_stride, shape.leaves);
    assert!(
        out.len() >= out_extent,
        "keccak256::hash_leaves_multi_coset: out.len() >= (cosets_in_tile - 1) * out_stride + leaves"
    );
    assert_no_overlap(NAME, values, out);
    let args = LeavesArguments::new(
        values.as_ptr(),
        log_domain,
        log_values_per_leaf,
        columns,
        cosets_in_tile,
        tile.values_stride,
        checked_u64(NAME, out_stride),
        out.as_mut_ptr(),
    );
    let grid = grid_dim(NAME, tile.threads, BLOCK_THREADS);
    let config = CudaLaunchConfig::basic(grid, BLOCK_THREADS, stream);
    LeavesFunction::default().launch(&config, &args)
}
