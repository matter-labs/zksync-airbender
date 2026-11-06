//! Launchers for the symbolic in-domain step split around a PoW-gated folding
//! draw (`in_domain.cu`): correct the reductions and commit the round
//! polynomial, then fold the terms with the challenge drawn in between.

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use gpu_core::primitives::field::{BF, E4};
use gpu_core::primitives::utils::get_grid_block_dims_for_threads_count;
use gpu_hash::blake2s::STATE_SIZE;

/// Must equal `WHIR_IN_DOMAIN_BLOCK_THREADS` in `in_domain.cu`: the one-CTA
/// correction reduces exactly this many partials.
const CORRECT_BLOCK_THREADS: u32 = 256;
const FOLD_BLOCK_THREADS: u32 = 128;

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

fn term_count(weights_len: usize, points_len: usize) -> u32 {
    assert_eq!(points_len, weights_len);
    let count = u32::try_from(weights_len).expect("term count must fit u32");
    assert!(count > 0, "split symbolic step needs terms");
    count
}

fn check_leaf_geometry(leaves_len: usize, leaf_stride: u32, leaf_width: u32, count: u32) {
    assert!(leaf_width >= 2 && leaf_width.is_multiple_of(2));
    assert!(leaf_width <= leaf_stride);
    assert_eq!(leaves_len, count as usize * leaf_stride as usize);
}

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
    check_leaf_geometry(leaves.len(), leaf_stride, leaf_width, count);
    assert!(reductions.len() >= 3);
    assert_eq!(seed.len(), STATE_SIZE);
    assert_eq!(coefficients.len(), 3);
    let config = CudaLaunchConfig::basic(1, CORRECT_BLOCK_THREADS, stream);
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
    assert_eq!(exponents.len(), count as usize);
    check_leaf_geometry(leaves.len(), leaf_stride, leaf_width, count);
    assert_eq!(challenge.len(), 1);
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(FOLD_BLOCK_THREADS, count);
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
