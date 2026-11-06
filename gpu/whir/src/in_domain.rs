use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use gpu_core::primitives::field::{BF, E4};
use gpu_core::primitives::utils::get_grid_block_dims_for_threads_count;
use gpu_hash::blake2s::STATE_SIZE;
use gpu_ntt::ntt_twiddles::WhirLeafTransformParams;

/// Must equal `WHIR_IN_DOMAIN_BLOCK_THREADS` in `in_domain.cu`: the one-CTA
/// corrections reduce exactly this many partials.
const IN_DOMAIN_BLOCK_THREADS: u32 = 256;
const IN_DOMAIN_LEAF_THREADS: u32 = 256;
const IN_DOMAIN_FOLD_THREADS: u32 = 128;

cuda_kernel_signature_arguments_and_function!(
    WhirInDomainAddTerms,
    indexes: *const u32,
    challenges: *const E4,
    query_domain_log2: u32,
    generator: BF,
    weights: *mut E4,
    points: *mut BF,
    exponents: *mut u32,
    count: u32,
);

cuda_kernel_declaration!(
    ab_whir_in_domain_add_terms_kernel(
        indexes: *const u32,
        challenges: *const E4,
        query_domain_log2: u32,
        generator: BF,
        weights: *mut E4,
        points: *mut BF,
        exponents: *mut u32,
        count: u32,
    )
);

cuda_kernel_signature_arguments_and_function!(
    WhirInDomainPrepareIndexes,
    exponents: *const u32,
    domain_log2: u32,
    log_v: u32,
    indexes: *mut u32,
    count: u32,
);

cuda_kernel_declaration!(
    ab_whir_in_domain_prepare_indexes_kernel(
        exponents: *const u32,
        domain_log2: u32,
        log_v: u32,
        indexes: *mut u32,
        count: u32,
    )
);

fn term_count(weights_len: usize, points_len: usize) -> u32 {
    assert_eq!(points_len, weights_len);
    u32::try_from(weights_len).expect("term count must fit u32")
}

fn check_leaf_geometry(leaves_len: usize, leaf_stride: u32, leaf_width: u32, count: u32) {
    assert!(leaf_width >= 2 && leaf_width.is_multiple_of(2));
    assert!(leaf_width <= leaf_stride);
    assert_eq!(leaves_len, count as usize * leaf_stride as usize);
}

/// Appends `count` terms: weight = challenge, point = generator^index, exponent =
/// `index << (32 - query_domain_log2)`. Destinations are already sliced to the new terms.
pub(crate) fn add_terms(
    indexes: &DeviceSlice<u32>,
    challenges: &DeviceSlice<E4>,
    query_domain_log2: u32,
    generator: BF,
    weights: &mut DeviceSlice<E4>,
    points: &mut DeviceSlice<BF>,
    exponents: &mut DeviceSlice<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = term_count(weights.len(), points.len());
    assert_eq!(exponents.len(), count as usize);
    assert_eq!(indexes.len(), count as usize);
    assert_eq!(challenges.len(), count as usize);
    assert!(query_domain_log2 <= 32);
    if count == 0 {
        return Ok(());
    }
    let (grid_dim, block_dim) =
        get_grid_block_dims_for_threads_count(IN_DOMAIN_BLOCK_THREADS, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = WhirInDomainAddTermsArguments::new(
        indexes.as_ptr(),
        challenges.as_ptr(),
        query_domain_log2,
        generator,
        weights.as_mut_ptr(),
        points.as_mut_ptr(),
        exponents.as_mut_ptr(),
        count,
    );
    WhirInDomainAddTermsFunction(ab_whir_in_domain_add_terms_kernel).launch(&config, &args)
}

/// Writes each term's protocol leaf index in the current oracle: the low
/// `domain_log2 - log_v` bits of `exponent >> (32 - domain_log2)`.
pub(crate) fn prepare_indexes(
    exponents: &DeviceSlice<u32>,
    domain_log2: u32,
    log_v: u32,
    indexes: &mut DeviceSlice<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(indexes.len(), exponents.len());
    assert!(domain_log2 <= 32);
    assert!(log_v <= domain_log2);
    let count = u32::try_from(exponents.len()).expect("term count must fit u32");
    if count == 0 {
        return Ok(());
    }
    let (grid_dim, block_dim) =
        get_grid_block_dims_for_threads_count(IN_DOMAIN_BLOCK_THREADS, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = WhirInDomainPrepareIndexesArguments::new(
        exponents.as_ptr(),
        domain_log2,
        log_v,
        indexes.as_mut_ptr(),
        count,
    );
    WhirInDomainPrepareIndexesFunction(ab_whir_in_domain_prepare_indexes_kernel)
        .launch(&config, &args)
}

cuda_kernel_signature_arguments_and_function!(
    WhirInDomainLeavesFromMonomials,
    coeffs: *const BF,
    transform_params: WhirLeafTransformParams,
    log_n: u32,
    log_c: u32,
    log_v: u32,
    tree_indexes: *const u32,
    leaves: *mut E4,
    count: u32,
);

cuda_kernel_declaration!(
    ab_whir_in_domain_leaves_from_monomials_kernel(
        coeffs: *const BF,
        transform_params: WhirLeafTransformParams,
        log_n: u32,
        log_c: u32,
        log_v: u32,
        tree_indexes: *const u32,
        leaves: *mut E4,
        count: u32,
    )
);

/// Writes each term's natural-order coefficient leaf `[P_0(x^V) .. P_{V-1}(x^V)]`
/// straight from a recomputed oracle's bit-reversed limb columns (`4 << log_n`
/// BF), addressed by tree index like the residue query kernels.
pub(crate) fn leaves_from_monomials(
    coeffs: &DeviceSlice<BF>,
    params: WhirLeafTransformParams,
    log_n: u32,
    log_c: u32,
    log_v: u32,
    tree_indexes: &DeviceSlice<u32>,
    leaves: &mut DeviceSlice<E4>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(
        log_v <= 8,
        "leaf width must fit the 256-thread interleave: log_r = 8 - log_v"
    );
    assert!(log_n >= log_v);
    let log_m = log_n - log_v;
    assert!(log_c >= 1);
    assert!(log_m + log_c <= params.omega_log_order);
    assert_eq!(coeffs.len(), 4usize << log_n);
    assert_eq!(leaves.len(), tree_indexes.len() << log_v);
    let count = u32::try_from(tree_indexes.len()).expect("term count must fit u32");
    if count == 0 {
        return Ok(());
    }
    let config = CudaLaunchConfig::basic(count, IN_DOMAIN_LEAF_THREADS, stream);
    let args = WhirInDomainLeavesFromMonomialsArguments::new(
        coeffs.as_ptr(),
        params,
        log_n,
        log_c,
        log_v,
        tree_indexes.as_ptr(),
        leaves.as_mut_ptr(),
        count,
    );
    WhirInDomainLeavesFromMonomialsFunction(ab_whir_in_domain_leaves_from_monomials_kernel)
        .launch(&config, &args)
}

cuda_kernel_signature_arguments_and_function!(
    WhirInDomainCorrectUpdateAndFold,
    leaves: *mut E4,
    leaf_stride: u32,
    leaf_width: u32,
    weights: *mut E4,
    points: *mut BF,
    exponents: *mut u32,
    reductions: *mut E4,
    seed_io: *mut u32,
    coeffs_out: *mut E4,
    challenge_out: *mut E4,
    count: u32,
);

cuda_kernel_declaration!(
    ab_whir_in_domain_correct_update_and_fold_kernel(
        leaves: *mut E4,
        leaf_stride: u32,
        leaf_width: u32,
        weights: *mut E4,
        points: *mut BF,
        exponents: *mut u32,
        reductions: *mut E4,
        seed_io: *mut u32,
        coeffs_out: *mut E4,
        challenge_out: *mut E4,
        count: u32,
    )
);

/// Correct the sumcheck reductions, update the transcript, and fold the
/// symbolic terms with the derived challenge in one launch.
pub(crate) fn correct_update_and_fold(
    leaves: &mut DeviceSlice<E4>,
    leaf_stride: u32,
    leaf_width: u32,
    weights: &mut DeviceSlice<E4>,
    points: &mut DeviceSlice<BF>,
    exponents: &mut DeviceSlice<u32>,
    reductions: &mut DeviceSlice<E4>,
    seed: &mut DeviceSlice<u32>,
    coefficients: &mut DeviceSlice<E4>,
    challenge: &mut DeviceSlice<E4>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = term_count(weights.len(), points.len());
    assert_eq!(exponents.len(), count as usize);
    assert!(
        count > 0,
        "fused symbolic step needs terms; empty steps use whir_fold_round_update alone"
    );
    check_leaf_geometry(leaves.len(), leaf_stride, leaf_width, count);
    assert!(reductions.len() >= 3);
    assert_eq!(seed.len(), STATE_SIZE);
    assert_eq!(coefficients.len(), 3);
    assert_eq!(challenge.len(), 1);
    let config = CudaLaunchConfig::basic(1, IN_DOMAIN_BLOCK_THREADS, stream);
    let args = WhirInDomainCorrectUpdateAndFoldArguments::new(
        leaves.as_mut_ptr(),
        leaf_stride,
        leaf_width,
        weights.as_mut_ptr(),
        points.as_mut_ptr(),
        exponents.as_mut_ptr(),
        reductions.as_mut_ptr(),
        seed.as_mut_ptr(),
        coefficients.as_mut_ptr(),
        challenge.as_mut_ptr(),
        count,
    );
    WhirInDomainCorrectUpdateAndFoldFunction(ab_whir_in_domain_correct_update_and_fold_kernel)
        .launch(&config, &args)
}

// The symbolic step split around a PoW-gated folding draw: correct the reductions and commit the
// round polynomial, then fold the terms with the challenge drawn in between.

cuda_kernel_signature_arguments_and_function!(
    WhirInDomainCorrectAndCommit,
    leaves: *const E4,
    leaf_stride: u32,
    leaf_width: u32,
    weights: *const E4,
    points: *const BF,
    reductions: *mut E4,
    seed_io: *mut u32,
    coeffs_out: *mut E4,
    count: u32,
);

cuda_kernel_declaration!(
    ab_whir_in_domain_correct_and_commit_kernel(
        leaves: *const E4,
        leaf_stride: u32,
        leaf_width: u32,
        weights: *const E4,
        points: *const BF,
        reductions: *mut E4,
        seed_io: *mut u32,
        coeffs_out: *mut E4,
        count: u32,
    )
);

cuda_kernel_signature_arguments_and_function!(
    WhirInDomainFoldTerms,
    leaves: *mut E4,
    leaf_stride: u32,
    leaf_width: u32,
    weights: *mut E4,
    points: *mut BF,
    exponents: *mut u32,
    challenge: *const E4,
    count: u32,
);

cuda_kernel_declaration!(
    ab_whir_in_domain_fold_terms_kernel(
        leaves: *mut E4,
        leaf_stride: u32,
        leaf_width: u32,
        weights: *mut E4,
        points: *mut BF,
        exponents: *mut u32,
        challenge: *const E4,
        count: u32,
    )
);

/// Adds the terms' `[h(0), h(1), 4 h(1/2)]` to `reductions`, then writes the
/// round polynomial to `coefficients` and commits it into `seed`. Draws no
/// challenge and leaves the terms unfolded.
pub(crate) fn correct_and_commit(
    leaves: &DeviceSlice<E4>,
    leaf_stride: u32,
    leaf_width: u32,
    weights: &DeviceSlice<E4>,
    points: &DeviceSlice<BF>,
    reductions: &mut DeviceSlice<E4>,
    seed: &mut DeviceSlice<u32>,
    coefficients: &mut DeviceSlice<E4>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = term_count(weights.len(), points.len());
    assert!(count > 0, "split symbolic step needs terms");
    check_leaf_geometry(leaves.len(), leaf_stride, leaf_width, count);
    assert!(reductions.len() >= 3);
    assert_eq!(seed.len(), STATE_SIZE);
    assert_eq!(coefficients.len(), 3);
    let config = CudaLaunchConfig::basic(1, IN_DOMAIN_BLOCK_THREADS, stream);
    let args = WhirInDomainCorrectAndCommitArguments::new(
        leaves.as_ptr(),
        leaf_stride,
        leaf_width,
        weights.as_ptr(),
        points.as_ptr(),
        reductions.as_mut_ptr(),
        seed.as_mut_ptr(),
        coefficients.as_mut_ptr(),
        count,
    );
    WhirInDomainCorrectAndCommitFunction(ab_whir_in_domain_correct_and_commit_kernel)
        .launch(&config, &args)
}

/// Folds every term's leaf pairs, weight, point and angle by the
/// device-resident `challenge`.
pub(crate) fn fold_terms(
    leaves: &mut DeviceSlice<E4>,
    leaf_stride: u32,
    leaf_width: u32,
    weights: &mut DeviceSlice<E4>,
    points: &mut DeviceSlice<BF>,
    exponents: &mut DeviceSlice<u32>,
    challenge: &DeviceSlice<E4>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = term_count(weights.len(), points.len());
    assert!(count > 0, "split symbolic step needs terms");
    assert_eq!(exponents.len(), count as usize);
    check_leaf_geometry(leaves.len(), leaf_stride, leaf_width, count);
    assert_eq!(challenge.len(), 1);
    let (grid_dim, block_dim) =
        get_grid_block_dims_for_threads_count(IN_DOMAIN_FOLD_THREADS, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = WhirInDomainFoldTermsArguments::new(
        leaves.as_mut_ptr(),
        leaf_stride,
        leaf_width,
        weights.as_mut_ptr(),
        points.as_mut_ptr(),
        exponents.as_mut_ptr(),
        challenge.as_ptr(),
        count,
    );
    WhirInDomainFoldTermsFunction(ab_whir_in_domain_fold_terms_kernel).launch(&config, &args)
}
