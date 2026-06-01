use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;

use crate::ops::blake2s::STATE_SIZE;
use crate::primitives::field::E4;
use crate::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};

#[cfg(test)]
mod tests;

cuda_kernel!(
    BackwardSumcheckRoundUpdate,
    ab_backward_sumcheck_round_update_kernel(
        reduction_output: *const E4,
        prev_claim_coord: *const E4,
        seed_io: *mut u32,
        claim_io: *mut E4,
        eq_prefactor_io: *mut E4,
        coeffs_out: *mut E4,
        challenge_out: *mut E4,
    )
);

/// Fused device-side per-round backward sumcheck state update.
///
/// Replaces the host callback that runs after each CUB reduction in the
/// backward sumcheck loop. Consumes device-resident state and writes back
/// updated state plus the new folding challenge — no host round-trip.
///
/// Buffer contracts:
/// - `reduction_output`: 2 E4 values `[e_partial, c_partial]` (constant and
///   quadratic coefficients from the CUB reduction over round accumulators).
/// - `prev_claim_coord`: 1 E4, the previous-round claim point coordinate.
/// - `seed`: `STATE_SIZE` u32 words, updated in place with the new Blake2s seed.
/// - `claim`: 1 E4, updated in place to `poly(challenge)`.
/// - `eq_prefactor`: 1 E4, updated in place to `eq(challenge, prev_coord)`.
/// - `coeffs_out`: 4 E4 values `[c0, c1, c2, c3]`, the round's univariate
///   coefficients, written for later bulk readback.
/// - `challenge_out`: 1 E4, the next round's folding challenge.
pub(crate) fn backward_sumcheck_round_update(
    reduction_output: &DeviceSlice<E4>,
    prev_claim_coord: &DeviceSlice<E4>,
    seed: &mut DeviceSlice<u32>,
    claim: &mut DeviceSlice<E4>,
    eq_prefactor: &mut DeviceSlice<E4>,
    coeffs_out: &mut DeviceSlice<E4>,
    challenge_out: &mut DeviceSlice<E4>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(reduction_output.len(), 2);
    assert_eq!(prev_claim_coord.len(), 1);
    assert_eq!(seed.len(), STATE_SIZE);
    assert_eq!(claim.len(), 1);
    assert_eq!(eq_prefactor.len(), 1);
    assert_eq!(coeffs_out.len(), 4);
    assert_eq!(challenge_out.len(), 1);
    let config = CudaLaunchConfig::basic(1u32, 1u32, stream);
    let args = BackwardSumcheckRoundUpdateArguments::new(
        reduction_output.as_ptr(),
        prev_claim_coord.as_ptr(),
        seed.as_mut_ptr(),
        claim.as_mut_ptr(),
        eq_prefactor.as_mut_ptr(),
        coeffs_out.as_mut_ptr(),
        challenge_out.as_mut_ptr(),
    );
    BackwardSumcheckRoundUpdateFunction::default().launch(&config, &args)
}

cuda_kernel!(
    WhirFoldRoundUpdate,
    ab_whir_fold_round_update_kernel(
        reduction_output: *const E4,
        seed_io: *mut u32,
        coeffs_out: *mut E4,
        challenge_out: *mut E4,
    )
);

/// Fused device-side per-round WHIR fold state update.
///
/// Replaces the host callback that runs after each special 3-point reduction
/// in the WHIR folding loop. Consumes device-resident state and writes back
/// the new coefficients, challenge, and updated seed — no host round-trip.
///
/// Buffer contracts:
/// - `reduction_output`: 3 E4 values `[f(0), f(1), ⟨eval_l+eval_h, eq_l+eq_h⟩]`
///   as produced by the three reductions in `schedule_special_three_point_eval_device`.
///   The kernel scales the third element by `1/4` internally to obtain `f(1/2)`.
/// - `seed`: `STATE_SIZE` u32 words, updated in place with the new Blake2s seed.
/// - `coeffs_out`: 3 E4 values `[c0, c1, c2]`, the round's sumcheck polynomial
///   coefficients, written for later bulk readback.
/// - `challenge_out`: 1 E4, the next round's folding challenge.
pub(crate) fn whir_fold_round_update(
    reduction_output: &DeviceSlice<E4>,
    seed: &mut DeviceSlice<u32>,
    coeffs_out: &mut DeviceSlice<E4>,
    challenge_out: &mut DeviceSlice<E4>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(reduction_output.len(), 3);
    assert_eq!(seed.len(), STATE_SIZE);
    assert_eq!(coeffs_out.len(), 3);
    assert_eq!(challenge_out.len(), 1);
    let config = CudaLaunchConfig::basic(1u32, 1u32, stream);
    let args = WhirFoldRoundUpdateArguments::new(
        reduction_output.as_ptr(),
        seed.as_mut_ptr(),
        coeffs_out.as_mut_ptr(),
        challenge_out.as_mut_ptr(),
    );
    WhirFoldRoundUpdateFunction::default().launch(&config, &args)
}

cuda_kernel!(
    BackwardNewClaimsTwoVar,
    ab_backward_new_claims_two_var_kernel(
        last_evals_packed: *const E4,
        challenges: *const E4,
        new_claims_out: *mut E4,
        num_addresses: u32,
    )
);

cuda_kernel!(
    BackwardNewClaimsLinear,
    ab_backward_new_claims_linear_kernel(
        last_evals_packed: *const E4,
        challenges: *const E4,
        new_claims_out: *mut E4,
        num_addresses: u32,
    )
);

/// Device-side per-address dim-reducing `new_claims` evaluator.
///
/// Replaces the host loop inside the end-of-layer final-readback callback
/// that computed `evaluate_with_two_variable_eq_ext(values, r_before_last,
/// r_last)` per address. `last_evals_packed` holds 4 E4 values per address,
/// `challenges` holds `[r_before_last, r_last]`. Produces `num_addresses`
/// E4 outputs.
pub(crate) fn backward_new_claims_two_var(
    last_evals_packed: &DeviceSlice<E4>,
    challenges: &DeviceSlice<E4>,
    new_claims_out: &mut DeviceSlice<E4>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let num_addresses = new_claims_out.len();
    assert!(num_addresses > 0);
    assert!(num_addresses <= u32::MAX as usize);
    assert_eq!(last_evals_packed.len(), num_addresses * 4);
    assert!(challenges.len() >= 2);
    let (grid_dim, block_dim) =
        get_grid_block_dims_for_threads_count(WARP_SIZE * 4, num_addresses as u32);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = BackwardNewClaimsTwoVarArguments::new(
        last_evals_packed.as_ptr(),
        challenges.as_ptr(),
        new_claims_out.as_mut_ptr(),
        num_addresses as u32,
    );
    BackwardNewClaimsTwoVarFunction::default().launch(&config, &args)
}

/// Device-side per-address main-layer `new_claims` evaluator.
///
/// Replaces the host loop inside the end-of-layer final-readback callback
/// that computed `interpolate_linear(f0, f1, last_r)` per address.
/// `last_evals_packed` holds 2 E4 values per address, `challenges` holds
/// `[last_r, ..]`. Produces `num_addresses` E4 outputs.
pub(crate) fn backward_new_claims_linear(
    last_evals_packed: &DeviceSlice<E4>,
    challenges: &DeviceSlice<E4>,
    new_claims_out: &mut DeviceSlice<E4>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let num_addresses = new_claims_out.len();
    assert!(num_addresses > 0);
    assert!(num_addresses <= u32::MAX as usize);
    assert_eq!(last_evals_packed.len(), num_addresses * 2);
    assert!(!challenges.is_empty());
    let (grid_dim, block_dim) =
        get_grid_block_dims_for_threads_count(WARP_SIZE * 4, num_addresses as u32);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = BackwardNewClaimsLinearArguments::new(
        last_evals_packed.as_ptr(),
        challenges.as_ptr(),
        new_claims_out.as_mut_ptr(),
        num_addresses as u32,
    );
    BackwardNewClaimsLinearFunction::default().launch(&config, &args)
}

/// Maximum `(batch_challenge_offset, claim_idx)` pairs the
/// `build_combined_claim` kernel-arg descriptor can hold.
/// See [`crate::prover::gkr::gkr_address_audit_helpers::GKR_COMBINED_CLAIM_MAX_PAIRS`]
/// for the rationale; the audit panics if any future circuit exceeds this.
pub(crate) const GKR_COMBINED_CLAIM_MAX_PAIRS: usize = 1024;

/// Kernel-arg descriptor for `build_combined_claim`. Inline form: passed
/// by value as `__grid_constant__` data, avoiding per-layer H2D.
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct GpuCombinedClaimDesc {
    /// Number of `(exp, idx)` pairs populated in `entries`.
    pub num_terms: u32,
    /// Reserved padding to keep `entries` aligned at offset 8.
    pub _pad: u32,
    /// Flattened `(exp_0, idx_0, exp_1, idx_1, ...)` pairs.
    pub entries: [u32; GKR_COMBINED_CLAIM_MAX_PAIRS * 2],
}

impl Default for GpuCombinedClaimDesc {
    fn default() -> Self {
        Self {
            num_terms: 0,
            _pad: 0,
            entries: [0u32; GKR_COMBINED_CLAIM_MAX_PAIRS * 2],
        }
    }
}

const _: () = {
    assert!(
        std::mem::size_of::<GpuCombinedClaimDesc>() <= 32 * 1024,
        "GpuCombinedClaimDesc must fit under the 32 KB inline kernel-arg ceiling"
    );
};

cuda_kernel!(
    BuildCombinedClaim,
    ab_build_combined_claim_kernel(
        claims: *const E4,
        batching: *const E4,
        desc: GpuCombinedClaimDesc,
        claim_out: *mut E4,
        eq_prefactor_out: *mut E4,
    )
);

/// Builds the per-layer combined claim on device. `desc_pairs` is a host slice
/// of `(exp, claim_idx)` u32 pairs (flattened: `[exp_0, idx_0, exp_1, idx_1, ...]`).
/// Panics if `desc_pairs.len() / 2 > GKR_COMBINED_CLAIM_MAX_PAIRS` — production
/// callers must respect the audit-locked ceiling.
pub(crate) fn build_combined_claim(
    claims: &DeviceSlice<E4>,
    batching: &DeviceSlice<E4>,
    desc_pairs: &[u32],
    claim_out: &mut DeviceSlice<E4>,
    eq_prefactor_out: &mut DeviceSlice<E4>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(batching.len(), 1);
    assert_eq!(claim_out.len(), 1);
    assert_eq!(eq_prefactor_out.len(), 1);
    assert_eq!(
        desc_pairs.len() % 2,
        0,
        "combined-claim descriptor must be `(exponent, claim_idx)` pairs",
    );
    let num_pairs = desc_pairs.len() / 2;
    assert!(
        num_pairs <= GKR_COMBINED_CLAIM_MAX_PAIRS,
        "combined-claim descriptor has {} pairs; exceeds GKR_COMBINED_CLAIM_MAX_PAIRS = {}. \
         Raise the constant in gkr_address_audit.rs after re-running the audit.",
        num_pairs,
        GKR_COMBINED_CLAIM_MAX_PAIRS,
    );
    let mut desc = GpuCombinedClaimDesc::default();
    desc.num_terms = num_pairs as u32;
    desc.entries[..desc_pairs.len()].copy_from_slice(desc_pairs);
    let config = CudaLaunchConfig::basic(1u32, 1u32, stream);
    let args = BuildCombinedClaimArguments::new(
        claims.as_ptr(),
        batching.as_ptr(),
        desc,
        claim_out.as_mut_ptr(),
        eq_prefactor_out.as_mut_ptr(),
    );
    BuildCombinedClaimFunction::default().launch(&config, &args)
}

cuda_kernel!(
    AssembleQueryIndexes,
    ab_assemble_query_indexes_kernel(
        raw_bits: *const u32,
        indexes_out: *mut u32,
        num_queries: u32,
        log_domain_size: u32,
    )
);

/// Assembles `num_queries` query indexes on device from a padded random u32
/// buffer as produced by `transcript_squeeze`.
///
/// Mirrors the host `draw_query_bits_after_verified_pow` + `BitSource` +
/// `assemble_query_index` chain: the first 32 bits of `raw_bits` are skipped
/// (they were the PoW header word), and each query reads `log_domain_size`
/// LE-packed bits thereafter. `raw_bits.len()` must cover `ceil((32 +
/// num_queries * log_domain_size) / 32)` u32 words (the caller typically
/// over-allocates to a multiple of `STATE_SIZE` to match the squeeze output).
pub(crate) fn assemble_query_indexes(
    raw_bits: &DeviceSlice<u32>,
    indexes_out: &mut DeviceSlice<u32>,
    log_domain_size: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let num_queries = indexes_out.len() as u32;
    assert!(num_queries > 0);
    assert!(log_domain_size > 0);
    assert!(log_domain_size <= 32);
    let total_bits = 32u64 + (num_queries as u64) * (log_domain_size as u64);
    let required_words = total_bits.div_ceil(32) as usize;
    assert!(
        raw_bits.len() >= required_words,
        "raw_bits buffer is too small for query index assembly"
    );
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, num_queries);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = AssembleQueryIndexesArguments::new(
        raw_bits.as_ptr(),
        indexes_out.as_mut_ptr(),
        num_queries,
        log_domain_size,
    );
    AssembleQueryIndexesFunction::default().launch(&config, &args)
}
