use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use gpu_core::primitives::field::BF;
use gpu_core::primitives::utils::{
    get_grid_block_dims_for_threads_count, LOG_WARP_SIZE, WARP_SIZE,
};

use super::{checked_u32, Digest, OracleGatherDesc, OraclePartialPathDesc, STATE_SIZE};

cuda_kernel!(
    GatherLeavesForQueriesSingleCosetPhysical,
    ab_gather_leaves_for_queries_single_coset_physical_kernel(
        desc: OracleGatherDesc,
        resident_coset: u32,
        log_lde_factor: u32,
        log_domain_size: u32,
        log_rows_per_leaf: u32,
        query_indexes: *const u32,
        indexes_count: u32,
    )
);

fn columns_count(
    values: &DeviceSlice<BF>,
    resident_coset: u32,
    log_lde_factor: u32,
    log_domain_size: u32,
    log_rows_per_leaf: u32,
) -> u32 {
    assert!(log_domain_size < 32 && log_lde_factor < 32);
    assert!(log_rows_per_leaf <= log_domain_size);
    assert!(log_domain_size - log_rows_per_leaf + log_lde_factor <= 32);
    assert!(resident_coset < (1u32 << log_lde_factor));
    let domain_size = 1usize << log_domain_size;
    assert_eq!(values.len() % domain_size, 0);
    // The shared gather bodies form scalar row offsets in u32.
    checked_u32(values.len());
    checked_u32(values.len() / domain_size)
}

/// Gather from a single column-major, bitreversed coset buffer. `resident_coset`
/// is the natural coset index, not the bitreversed coset label in the proof tree.
/// Other query slots in `slab_dst` are left untouched. All cosets must be opened
/// before the combined slab can be consumed.
pub fn gather_leaves_for_queries_single_coset_physical(
    values: &DeviceSlice<BF>,
    resident_coset: u32,
    log_lde_factor: u32,
    log_domain_size: u32,
    log_rows_per_leaf: u32,
    query_indexes: &DeviceSlice<u32>,
    slab_dst: &mut DeviceSlice<BF>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let cols = columns_count(
        values,
        resident_coset,
        log_lde_factor,
        log_domain_size,
        log_rows_per_leaf,
    );
    let indexes_count = checked_u32(query_indexes.len());
    checked_u32(slab_dst.len());
    let rows_per_leaf = 1u32 << log_rows_per_leaf;
    assert_eq!(
        slab_dst.len(),
        query_indexes.len() * rows_per_leaf as usize * cols as usize
    );
    if indexes_count == 0 || cols == 0 {
        return Ok(());
    }
    assert!(rows_per_leaf <= 1024 && cols <= 65535);
    let (grid, block) = if log_rows_per_leaf < LOG_WARP_SIZE {
        get_grid_block_dims_for_threads_count(
            1 << (LOG_WARP_SIZE - log_rows_per_leaf),
            indexes_count,
        )
    } else {
        (indexes_count.into(), 1.into())
    };
    let config = CudaLaunchConfig::basic((grid.x, cols, 1), (rows_per_leaf, block.x), stream);
    let desc = OracleGatherDesc {
        cosets_ptr: values.as_ptr() as u64,
        columns_count: cols,
        slab_dst_ptr: slab_dst.as_mut_ptr() as u64,
        ..Default::default()
    };
    let args = GatherLeavesForQueriesSingleCosetPhysicalArguments::new(
        desc,
        resident_coset,
        log_lde_factor,
        log_domain_size,
        log_rows_per_leaf,
        query_indexes.as_ptr(),
        indexes_count,
    );
    GatherLeavesForQueriesSingleCosetPhysicalFunction::default().launch(&config, &args)
}

cuda_kernel!(
    GatherMerklePathsPartialForQueriesSingleCosetPhysical,
    ab_gather_merkle_paths_partial_for_queries_single_coset_physical_kernel(
        desc: OraclePartialPathDesc,
        resident_coset: u32,
        log_lde_factor: u32,
        log_rows_per_leaf: u32,
        log_total_leaves_count: u32,
        stride_per_coset_in_digests: u32,
        layers_count: u32,
        query_indexes: *const u32,
        indexes_count: u32,
    )
);

/// Gather paths from one bitreversed coset and its partial tree. `partial_tree`
/// is the per-coset pyramid above the warp-hashed bottom layers; `layers_count`
/// ends at the per-coset cap. Unmatched query slots remain untouched.
pub fn gather_merkle_paths_partial_for_queries_single_coset_physical(
    values: &DeviceSlice<BF>,
    partial_tree: &DeviceSlice<Digest>,
    resident_coset: u32,
    log_lde_factor: u32,
    log_domain_size: u32,
    log_rows_per_leaf: u32,
    layers_count: u32,
    query_indexes: &DeviceSlice<u32>,
    slab_dst: &mut DeviceSlice<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let cols = columns_count(
        values,
        resident_coset,
        log_lde_factor,
        log_domain_size,
        log_rows_per_leaf,
    );
    let log_leaves = log_domain_size - log_rows_per_leaf;
    assert!(layers_count >= LOG_WARP_SIZE && layers_count <= log_leaves);
    let tree_stride = 1u32 << (log_leaves + 1 - LOG_WARP_SIZE);
    assert_eq!(partial_tree.len(), tree_stride as usize);
    let indexes_count = checked_u32(query_indexes.len());
    checked_u32(slab_dst.len());
    assert_eq!(
        slab_dst.len(),
        query_indexes.len() * layers_count as usize * STATE_SIZE
    );
    if indexes_count == 0 || cols == 0 {
        return Ok(());
    }
    assert_eq!(slab_dst.as_ptr() as usize % 32, 0);
    let desc = OraclePartialPathDesc {
        cosets_ptr: values.as_ptr() as u64,
        partial_tree_ptr: partial_tree.as_ptr() as u64,
        columns_count: cols,
        slab_dst_ptr: slab_dst.as_mut_ptr() as u64,
        ..Default::default()
    };
    let config = CudaLaunchConfig::basic((indexes_count, 1), WARP_SIZE, stream);
    let args = GatherMerklePathsPartialForQueriesSingleCosetPhysicalArguments::new(
        desc,
        resident_coset,
        log_lde_factor,
        log_rows_per_leaf,
        log_leaves,
        tree_stride,
        layers_count,
        query_indexes.as_ptr(),
        indexes_count,
    );
    GatherMerklePathsPartialForQueriesSingleCosetPhysicalFunction::default().launch(&config, &args)
}
