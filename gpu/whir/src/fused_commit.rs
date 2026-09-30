//! Fused residue-polynomial commitment and query launchers for recursive WHIR
//! oracles on the `CachePartial` route.
//!
//! `f(X) = sum_r X^r P_r(X^V)` with `P_r(Y) = sum_t a[r + V t] Y^t` and
//! `M = N / V`. The committed coefficient leaf slot `r` of row `row` in natural
//! coset `c` is `P_r(omega_{M C}^c * omega_M^row)`, so a leaf is produced
//! directly from the monomial coefficients: no evaluation-form LDE backing and
//! no evaluation-to-coefficient transform. The kernels hash the leaves and
//! reduce the `PARTIAL_TREE_REDUCTION_LAYERS` bottom layers in one launch,
//! writing only the boundary roots; queries rebuild the queried 32-leaf
//! subtree from the same coefficients and walk the cached upper tree.
//!
//! `coeffs` is the existing bit-reversed monomial copy: four BF limb columns
//! of `N`, each bit-reversed over `log_n`. Boundary roots use the existing flat
//! tree order (tree leaf `bitrev_C(c) * M + row`, root `k` over leaves
//! `32k .. 32k + 31`). Leaf bytes and Merkle paths use the layouts of the
//! evaluation-backed query kernels.

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};

use gpu_core::primitives::field::BF;
use gpu_core::primitives::utils::WARP_SIZE;
use gpu_hash::blake2s::{Digest, STATE_SIZE};
use gpu_ntt::ntt_twiddles::WhirLeafTransformParams;
use gpu_trace::trace::holder::PARTIAL_TREE_REDUCTION_LAYERS;

/// Sub-warp family: one warp per 32-leaf subtree, `M <= 16`.
const SUBWARP_WARPS_PER_BLOCK: u32 = 8;
/// The block family (one block of `M` threads per coset) transforms 16 BF
/// columns (four E4 slots) per step: one Blake2s block per leaf.
const BLOCK_TILE_COLUMNS: usize = 16;

const _: () = assert!(PARTIAL_TREE_REDUCTION_LAYERS == WARP_SIZE.trailing_zeros());

cuda_kernel_signature_arguments_and_function!(
    WhirResidueCommitSubwarp,
    coeffs: *const BF,
    boundary_roots: *mut u32,
    transform_params: WhirLeafTransformParams,
    log_n: u32,
    log_c: u32,
    log_v: u32,
    subtrees_count: u32,
);

cuda_kernel_declaration!(
    ab_whir_residue_commit_subwarp_cooperative_kernel(
        coeffs: *const BF,
        boundary_roots: *mut u32,
        transform_params: WhirLeafTransformParams,
        log_n: u32,
        log_c: u32,
        log_v: u32,
        subtrees_count: u32,
    )
);

cuda_kernel_signature_arguments_and_function!(
    WhirResidueQuerySubwarp,
    coeffs: *const BF,
    partial_tree: *const u32,
    leaves: *mut BF,
    paths: *mut u32,
    transform_params: WhirLeafTransformParams,
    log_n: u32,
    log_c: u32,
    log_v: u32,
    log_total_leaves: u32,
    layers_count: u32,
    indexes: *const u32,
    indexes_count: u32,
);

cuda_kernel_declaration!(
    ab_whir_residue_query_subwarp_kernel(
        coeffs: *const BF,
        partial_tree: *const u32,
        leaves: *mut BF,
        paths: *mut u32,
        transform_params: WhirLeafTransformParams,
        log_n: u32,
        log_c: u32,
        log_v: u32,
        log_total_leaves: u32,
        layers_count: u32,
        indexes: *const u32,
        indexes_count: u32,
    )
);

cuda_kernel_signature_arguments_and_function!(
    WhirResidueCommitBlock,
    coeffs: *const BF,
    boundary_roots: *mut u32,
    transform_params: WhirLeafTransformParams,
    log_n: u32,
    log_c: u32,
    log_v: u32,
);

cuda_kernel_declaration!(
    ab_whir_residue_commit_block_kernel(
        coeffs: *const BF,
        boundary_roots: *mut u32,
        transform_params: WhirLeafTransformParams,
        log_n: u32,
        log_c: u32,
        log_v: u32,
    )
);

cuda_kernel_declaration!(
    ab_whir_residue_commit_block_hybrid_kernel(
        coeffs: *const BF,
        boundary_roots: *mut u32,
        transform_params: WhirLeafTransformParams,
        log_n: u32,
        log_c: u32,
        log_v: u32,
    )
);

cuda_kernel_declaration!(
    ab_whir_residue_commit_block_radix4_unity_kernel(
        coeffs: *const BF,
        boundary_roots: *mut u32,
        transform_params: WhirLeafTransformParams,
        log_n: u32,
        log_c: u32,
        log_v: u32,
    )
);

cuda_kernel_signature_arguments_and_function!(
    WhirResidueQueryBlock,
    coeffs: *const BF,
    partial_tree: *const u32,
    leaves: *mut BF,
    paths: *mut u32,
    transform_params: WhirLeafTransformParams,
    log_n: u32,
    log_c: u32,
    log_v: u32,
    log_total_leaves: u32,
    layers_count: u32,
    indexes: *const u32,
    indexes_count: u32,
);

cuda_kernel_declaration!(
    ab_whir_residue_query_block_kernel(
        coeffs: *const BF,
        partial_tree: *const u32,
        leaves: *mut BF,
        paths: *mut u32,
        transform_params: WhirLeafTransformParams,
        log_n: u32,
        log_c: u32,
        log_v: u32,
        log_total_leaves: u32,
        layers_count: u32,
        indexes: *const u32,
        indexes_count: u32,
    )
);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Family {
    Subwarp,
    Block,
}

/// Shapes qualified by CPU cap/leaf/path parity and the standard Sec100
/// schedule comparison. Keep explicit: generic kernels also admit unmeasured
/// geometries with different register/shared-memory requirements.
const VALIDATED_SHAPES: [(u32, u32, Family); 10] = [
    (13, 5, Family::Block),
    (12, 5, Family::Block),
    (11, 5, Family::Block),
    (10, 5, Family::Block),
    (9, 4, Family::Block),
    (8, 4, Family::Subwarp),
    (7, 4, Family::Subwarp),
    (6, 5, Family::Subwarp),
    (5, 4, Family::Subwarp),
    (4, 3, Family::Subwarp),
];

fn family(log_n: u32, log_v: u32) -> Option<Family> {
    VALIDATED_SHAPES
        .iter()
        .find(|(n, v, _)| *n == log_n && *v == log_v)
        .map(|(_, _, family)| *family)
}

/// Whether the fused kernels cover a recursive oracle of `2^log_n` monomial
/// coefficients committed with `2^log_v` values per leaf.
pub(crate) fn supported(log_n: u32, log_v: u32) -> bool {
    family(log_n, log_v).is_some()
}

struct Shape {
    family: Family,
    log_m: u32,
    log_total_leaves: u32,
}

fn shape(
    coeffs: &DeviceSlice<BF>,
    log_n: u32,
    log_c: u32,
    log_v: u32,
    params: &WhirLeafTransformParams,
) -> Shape {
    let family = family(log_n, log_v).unwrap_or_else(|| {
        panic!("fused residue commit does not support log_n {log_n}, log_v {log_v}")
    });
    assert!(log_c >= 1, "recursive WHIR oracles require LDE factor > 1");
    let log_m = log_n - log_v;
    assert!(
        log_m + log_c <= params.omega_log_order,
        "residue domain 2^{} exceeds the two-adic order 2^{}",
        log_m + log_c,
        params.omega_log_order
    );
    assert_eq!(
        coeffs.len(),
        4usize << log_n,
        "coeffs must hold four bit-reversed limb columns of N"
    );
    let log_total_leaves = log_m + log_c;
    assert!(
        log_total_leaves >= PARTIAL_TREE_REDUCTION_LAYERS,
        "the oracle must have at least one 32-leaf subtree"
    );
    Shape {
        family,
        log_m,
        log_total_leaves,
    }
}

fn subwarp_smem_bytes(log_n: u32) -> usize {
    (4usize << log_n) * core::mem::size_of::<BF>()
}

fn block_smem_bytes(log_m: u32) -> usize {
    let m = 1usize << log_m;
    (BLOCK_TILE_COLUMNS * m + m + m / 2) * core::mem::size_of::<BF>()
}

/// Commits the oracle: boundary roots of every 32-leaf subtree, in flat tree
/// order, from the bit-reversed monomial coefficients.
pub(crate) fn commit(
    coeffs: &DeviceSlice<BF>,
    boundary_roots: &mut DeviceSlice<Digest>,
    log_n: u32,
    log_c: u32,
    log_v: u32,
    params: WhirLeafTransformParams,
    stream: &CudaStream,
) -> CudaResult<()> {
    let shape = shape(coeffs, log_n, log_c, log_v, &params);
    let subtrees_count = 1usize << (shape.log_total_leaves - PARTIAL_TREE_REDUCTION_LAYERS);
    assert_eq!(boundary_roots.len(), subtrees_count);
    assert!(subtrees_count <= u32::MAX as usize);
    match shape.family {
        Family::Subwarp => {
            let block_dim = SUBWARP_WARPS_PER_BLOCK * WARP_SIZE;
            let grid_dim = (subtrees_count as u32).div_ceil(SUBWARP_WARPS_PER_BLOCK);
            let mut config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
            config.dynamic_smem_bytes = subwarp_smem_bytes(log_n);
            config.dynamic_smem_bytes = config
                .dynamic_smem_bytes
                .max(2 * STATE_SIZE * block_dim as usize * core::mem::size_of::<u32>());
            let args = WhirResidueCommitSubwarpArguments::new(
                coeffs.as_ptr(),
                boundary_roots.as_mut_ptr() as *mut u32,
                params,
                log_n,
                log_c,
                log_v,
                subtrees_count as u32,
            );
            WhirResidueCommitSubwarpFunction(ab_whir_residue_commit_subwarp_cooperative_kernel)
                .launch(&config, &args)
        }
        Family::Block => {
            let grid_dim = 1u32 << log_c;
            let block_dim = 1u32 << shape.log_m;
            let mut config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
            config.dynamic_smem_bytes = block_smem_bytes(shape.log_m);
            let args = WhirResidueCommitBlockArguments::new(
                coeffs.as_ptr(),
                boundary_roots.as_mut_ptr() as *mut u32,
                params,
                log_n,
                log_c,
                log_v,
            );
            let kernel = match (log_n, log_v) {
                (13, 5) => ab_whir_residue_commit_block_radix4_unity_kernel,
                (12, 5) => ab_whir_residue_commit_block_hybrid_kernel,
                _ => ab_whir_residue_commit_block_kernel,
            };
            WhirResidueCommitBlockFunction(kernel).launch(&config, &args)
        }
    }
}

/// Answers queries by tree index: rebuilds each queried 32-leaf subtree from
/// the coefficients, writes the queried leaf (`V` E4 values, slot-major) and
/// its full Merkle path (`layers_count` digests, bottom five recomputed, the
/// rest read from `partial_tree`).
pub(crate) fn query(
    coeffs: &DeviceSlice<BF>,
    partial_tree: &DeviceSlice<Digest>,
    indexes: &DeviceSlice<u32>,
    leaves: &mut DeviceSlice<BF>,
    paths: &mut DeviceSlice<u32>,
    log_n: u32,
    log_c: u32,
    log_v: u32,
    log_cap: u32,
    params: WhirLeafTransformParams,
    stream: &CudaStream,
) -> CudaResult<()> {
    let shape = shape(coeffs, log_n, log_c, log_v, &params);
    let log_total_leaves = shape.log_total_leaves;
    // CachePartial route only. Equality is the boundary-equals-cap case:
    // `layers_count == PARTIAL_TREE_REDUCTION_LAYERS`, the kernel rebuilds
    // the five bottom layers and reads nothing from the upper tree, matching
    // the evaluation-backed partial path gather's `layers_count >= 5` bound.
    assert!(
        log_total_leaves >= PARTIAL_TREE_REDUCTION_LAYERS + log_cap,
        "fused queries serve the CachePartial route only (log_total_leaves {log_total_leaves}, log_cap {log_cap})"
    );
    let layers_count = log_total_leaves - log_cap;
    let queries_count = indexes.len();
    assert!(queries_count > 0);
    assert!(queries_count <= u32::MAX as usize);
    assert_eq!(leaves.len(), queries_count << (log_v + 2));
    assert_eq!(
        paths.len(),
        queries_count * layers_count as usize * STATE_SIZE
    );
    assert_eq!(
        partial_tree.len(),
        2usize << (log_total_leaves - PARTIAL_TREE_REDUCTION_LAYERS)
    );
    let partial_tree_ptr = partial_tree.as_ptr() as *const u32;
    match shape.family {
        Family::Subwarp => {
            let mut config = CudaLaunchConfig::basic(queries_count as u32, WARP_SIZE, stream);
            config.dynamic_smem_bytes = subwarp_smem_bytes(log_n);
            let args = WhirResidueQuerySubwarpArguments::new(
                coeffs.as_ptr(),
                partial_tree_ptr,
                leaves.as_mut_ptr(),
                paths.as_mut_ptr(),
                params,
                log_n,
                log_c,
                log_v,
                log_total_leaves,
                layers_count,
                indexes.as_ptr(),
                queries_count as u32,
            );
            WhirResidueQuerySubwarpFunction(ab_whir_residue_query_subwarp_kernel)
                .launch(&config, &args)
        }
        Family::Block => {
            let block_dim = 1u32 << shape.log_m;
            let mut config = CudaLaunchConfig::basic(queries_count as u32, block_dim, stream);
            config.dynamic_smem_bytes = block_smem_bytes(shape.log_m);
            let args = WhirResidueQueryBlockArguments::new(
                coeffs.as_ptr(),
                partial_tree_ptr,
                leaves.as_mut_ptr(),
                paths.as_mut_ptr(),
                params,
                log_n,
                log_c,
                log_v,
                log_total_leaves,
                layers_count,
                indexes.as_ptr(),
                queries_count as u32,
            );
            WhirResidueQueryBlockFunction(ab_whir_residue_query_block_kernel).launch(&config, &args)
        }
    }
}

#[cfg(test)]
mod cpu_tests {
    use super::*;

    #[test]
    fn production_shapes_are_supported() {
        assert!(supported(13, 5));
        assert!(supported(8, 4));
        assert!(supported(4, 3));
        assert!(!supported(18, 5));
        assert!(!supported(23, 5));
        assert!(supported(12, 5));
        assert!(supported(11, 5));
        assert!(supported(10, 5));
        assert!(supported(9, 4));
        assert!(supported(7, 4));
        assert!(supported(6, 5));
        assert!(supported(5, 4));
        assert!(!supported(5, 3));
        assert!(!supported(6, 1));
    }
}
