use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use gpu_core::primitives::field::PR;

use super::hash::{leaf_shape, LeafShape};
use super::merkle::{partial_tree_shape, top_tree_log_lde};
use super::{
    assert_no_overlap, checked_bytes, checked_log_size, checked_product, checked_u32, checked_u64,
    grid_dim, Digest, BLOCK_THREADS,
};

cuda_kernel!(
    GatherLeaves,
    ab_keccak256_gather_leaves_kernel(
        values: *const PR,
        resident_coset: u32,
        log_lde: u32,
        log_domain: u32,
        log_v: u32,
        columns: u64,
        queries: *const u32,
        count: u64,
        out: *mut PR,
    )
);

cuda_kernel!(
    GatherPartialPaths,
    ab_keccak256_gather_partial_paths_kernel(
        values: *const PR,
        resident_coset: u32,
        log_lde: u32,
        log_domain: u32,
        log_v: u32,
        columns: u64,
        cap_log: u32,
        skip_bottom: u32,
        retained: *const Digest,
        queries: *const u32,
        count: u64,
        paths: *mut Digest,
    )
);

cuda_kernel!(
    AppendTopPaths,
    ab_keccak256_append_top_paths_kernel(
        roots: *const Digest,
        top_nodes: *const Digest,
        log_lde: u32,
        cap_log: u32,
        log_coset_leaves: u32,
        queries: *const u32,
        count: u64,
        paths: *mut Digest,
        tree_indexes: *mut u32,
    )
);

fn gather_shape(
    name: &str,
    values_len: usize,
    resident_coset: u32,
    log_lde: u32,
    log_domain: u32,
    log_v: u32,
) -> (LeafShape, u32) {
    let domain = checked_log_size(name, log_domain);
    assert!(
        values_len % domain == 0,
        "keccak256::{name}: values.len() % N == 0"
    );
    let columns = checked_u32(name, values_len / domain);
    let shape = leaf_shape(name, log_domain, log_v, columns);
    let cosets = checked_log_size(name, log_lde);
    assert!(
        shape.log_leaves + log_lde <= 31,
        "keccak256::{name}: log_coset_leaves + log_lde <= 31"
    );
    assert!(
        (resident_coset as usize) < cosets,
        "keccak256::{name}: resident_coset < C"
    );
    checked_bytes::<PR>(name, values_len);
    (shape, columns)
}

fn path_depth(name: &str, log_leaves: u32, log_lde: u32, cap_log: u32) -> usize {
    checked_log_size(name, log_leaves);
    checked_log_size(name, log_lde);
    assert!(
        log_leaves + log_lde <= 31,
        "keccak256::{name}: log_coset_leaves + log_lde <= 31"
    );
    assert!(cap_log <= log_lde, "keccak256::{name}: cap_log <= log_lde");
    (log_leaves + log_lde - cap_log) as usize
}

pub fn gather_leaves_for_queries_single_coset(
    values: &DeviceSlice<PR>,
    resident_coset: u32,
    log_lde: u32,
    log_domain: u32,
    log_v: u32,
    queries: &DeviceSlice<u32>,
    out: &mut DeviceSlice<PR>,
    stream: &CudaStream,
) -> CudaResult<()> {
    const NAME: &str = "gather_leaves_for_queries_single_coset";
    let (_, columns) = gather_shape(
        NAME,
        values.len(),
        resident_coset,
        log_lde,
        log_domain,
        log_v,
    );
    let leaf_values = checked_product(NAME, 1usize << log_v, columns as usize);
    let threads = checked_product(NAME, queries.len(), leaf_values);
    assert_eq!(
        out.len(),
        threads,
        "keccak256::gather_leaves_for_queries_single_coset: out.len() == Q * V * columns"
    );
    checked_bytes::<u32>(NAME, queries.len());
    assert_no_overlap(NAME, values, out);
    assert_no_overlap(NAME, queries, out);
    let count = checked_u64(NAME, queries.len());
    let grid = grid_dim(NAME, threads, BLOCK_THREADS);
    if count == 0 {
        return Ok(());
    }
    let args = GatherLeavesArguments::new(
        values.as_ptr(),
        resident_coset,
        log_lde,
        log_domain,
        log_v,
        columns as u64,
        queries.as_ptr(),
        count,
        out.as_mut_ptr(),
    );
    GatherLeavesFunction::default()
        .launch(&CudaLaunchConfig::basic(grid, BLOCK_THREADS, stream), &args)
}

pub fn gather_merkle_paths_partial_for_queries_single_coset(
    values: &DeviceSlice<PR>,
    resident_coset: u32,
    log_lde: u32,
    log_domain: u32,
    log_v: u32,
    cap_log: u32,
    skip_bottom: u32,
    retained: &DeviceSlice<Digest>,
    queries: &DeviceSlice<u32>,
    paths: &mut DeviceSlice<Digest>,
    stream: &CudaStream,
) -> CudaResult<()> {
    const NAME: &str = "gather_merkle_paths_partial_for_queries_single_coset";
    let (leaves, columns) = gather_shape(
        NAME,
        values.len(),
        resident_coset,
        log_lde,
        log_domain,
        log_v,
    );
    let shape = partial_tree_shape(NAME, log_domain, log_v, columns, skip_bottom);
    let depth = path_depth(NAME, leaves.log_leaves, log_lde, cap_log);
    assert_eq!(retained.len(), shape.retained_per_coset, "keccak256::gather_merkle_paths_partial_for_queries_single_coset: retained.len() == 2 * (L >> skip_bottom) - 1");
    assert_eq!(
        paths.len(),
        checked_product(NAME, queries.len(), depth),
        "keccak256::gather_merkle_paths_partial_for_queries_single_coset: paths.len() == Q * D"
    );
    checked_bytes::<u32>(NAME, queries.len());
    assert_no_overlap(NAME, values, paths);
    assert_no_overlap(NAME, retained, paths);
    assert_no_overlap(NAME, queries, paths);
    let count = checked_u64(NAME, queries.len());
    let threads = if skip_bottom <= 5 {
        32
    } else {
        (1u32 << skip_bottom).min(256)
    };
    let grid = grid_dim(
        NAME,
        checked_product(NAME, queries.len(), threads as usize),
        threads,
    );
    if count == 0 {
        return Ok(());
    }
    let args = GatherPartialPathsArguments::new(
        values.as_ptr(),
        resident_coset,
        log_lde,
        log_domain,
        log_v,
        columns as u64,
        cap_log,
        skip_bottom,
        retained.as_ptr(),
        queries.as_ptr(),
        count,
        paths.as_mut_ptr(),
    );
    let mut config = CudaLaunchConfig::basic(grid, threads, stream);
    if skip_bottom > 5 {
        config.dynamic_smem_bytes = checked_bytes::<Digest>(NAME, 1usize << skip_bottom);
    }
    GatherPartialPathsFunction::default().launch(&config, &args)
}

pub fn append_top_paths(
    roots: &DeviceSlice<Digest>,
    top_nodes: &DeviceSlice<Digest>,
    log_lde: u32,
    cap_log: u32,
    log_coset_leaves: u32,
    queries: &DeviceSlice<u32>,
    paths: &mut DeviceSlice<Digest>,
    tree_indexes: &mut DeviceSlice<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    const NAME: &str = "append_top_paths";
    let cosets = checked_log_size(NAME, log_lde);
    let depth = path_depth(NAME, log_coset_leaves, log_lde, cap_log);
    assert_eq!(
        roots.len(),
        cosets,
        "keccak256::append_top_paths: roots.len() == C"
    );
    top_tree_log_lde(NAME, roots.len(), cap_log, top_nodes.len());
    assert_eq!(
        paths.len(),
        checked_product(NAME, queries.len(), depth),
        "keccak256::append_top_paths: paths.len() == Q * D"
    );
    assert_eq!(
        tree_indexes.len(),
        queries.len(),
        "keccak256::append_top_paths: tree_indexes.len() == Q"
    );
    assert_no_overlap(NAME, roots, paths);
    assert_no_overlap(NAME, top_nodes, paths);
    assert_no_overlap(NAME, queries, paths);
    assert_no_overlap(NAME, roots, tree_indexes);
    assert_no_overlap(NAME, top_nodes, tree_indexes);
    assert_no_overlap(NAME, queries, tree_indexes);
    assert_no_overlap(NAME, paths, tree_indexes);
    let count = checked_u64(NAME, queries.len());
    let grid = grid_dim(NAME, queries.len(), BLOCK_THREADS);
    if count == 0 {
        return Ok(());
    }
    let args = AppendTopPathsArguments::new(
        roots.as_ptr(),
        top_nodes.as_ptr(),
        log_lde,
        cap_log,
        log_coset_leaves,
        queries.as_ptr(),
        count,
        paths.as_mut_ptr(),
        tree_indexes.as_mut_ptr(),
    );
    AppendTopPathsFunction::default()
        .launch(&CudaLaunchConfig::basic(grid, BLOCK_THREADS, stream), &args)
}
