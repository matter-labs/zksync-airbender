use era_cudart::{
    cuda_kernel,
    execution::{CudaLaunchConfig, KernelFunction},
    result::CudaResult,
    slice::DeviceSlice,
    stream::CudaStream,
};
use gpu_core::primitives::{
    field::E4,
    utils::{get_grid_block_dims_for_threads_count, WARP_SIZE},
};
use gpu_hash::blake2s::STATE_SIZE;

use crate::gkr_ops::*;

#[cfg(test)]
pub(crate) mod tests;

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
pub fn whir_fold_round_update(
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
    WhirFoldRoundCommit,
    ab_whir_fold_round_commit_kernel(
        reduction_output: *const E4,
        seed_io: *mut u32,
        coeffs_out: *mut E4,
    )
);

/// [`whir_fold_round_update`] without the challenge draw: commits the round
/// polynomial and leaves the advanced seed in `seed`, for a PoW-gated folding
/// step that draws its challenge afterward.
pub fn whir_fold_round_commit(
    reduction_output: &DeviceSlice<E4>,
    seed: &mut DeviceSlice<u32>,
    coeffs_out: &mut DeviceSlice<E4>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(reduction_output.len(), 3);
    assert_eq!(seed.len(), STATE_SIZE);
    assert_eq!(coeffs_out.len(), 3);
    let config = CudaLaunchConfig::basic(1u32, 1u32, stream);
    let args = WhirFoldRoundCommitArguments::new(
        reduction_output.as_ptr(),
        seed.as_mut_ptr(),
        coeffs_out.as_mut_ptr(),
    );
    WhirFoldRoundCommitFunction::default().launch(&config, &args)
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

cuda_kernel!(
    BackwardDimReducingLsbLines,
    ab_backward_dim_reducing_lsb_lines_kernel(
        last_evals_packed: *const E4,
        challenges: *const E4,
        lsb_lines_out: *mut E4,
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

/// Device-side dim-reducing final-round LSB-line reduction.
///
/// The last sumcheck round now emits a monomial and draws `r_before_last`
/// in-loop; this reduces the `[E4; 4]` bilinear `last_evals` (packed 4 per
/// address) over the last-output coordinate at `r_before_last` into the
/// `[E4; 2]` LSB line that is sent in the proof and committed to the
/// transcript. Per address: `out[0] = lerp(v0, v2, rbl)`,
/// `out[1] = lerp(v1, v3, rbl)`, matching the host `interpolate_linear`
/// over `(evals[0], evals[2])` / `(evals[1], evals[3])`. `challenges` reads
/// only slot 0 (`r_before_last`). Produces `2 * num_addresses` outputs.
pub(crate) fn backward_dim_reducing_lsb_lines(
    last_evals_packed: &DeviceSlice<E4>,
    challenges: &DeviceSlice<E4>,
    lsb_lines_out: &mut DeviceSlice<E4>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(lsb_lines_out.len() % 2, 0);
    let num_addresses = lsb_lines_out.len() / 2;
    assert!(num_addresses > 0);
    assert!(num_addresses <= u32::MAX as usize);
    assert_eq!(last_evals_packed.len(), num_addresses * 4);
    assert!(!challenges.is_empty());
    let (grid_dim, block_dim) =
        get_grid_block_dims_for_threads_count(WARP_SIZE * 4, num_addresses as u32);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = BackwardDimReducingLsbLinesArguments::new(
        last_evals_packed.as_ptr(),
        challenges.as_ptr(),
        lsb_lines_out.as_mut_ptr(),
        num_addresses as u32,
    );
    BackwardDimReducingLsbLinesFunction::default().launch(&config, &args)
}

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
/// callers must respect the descriptor ceiling.
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
    let desc = GpuCombinedClaimDesc::from_pairs(desc_pairs);
    // Matches the native block reduction and its 256-thread launch bound.
    let config = CudaLaunchConfig::basic(1u32, 256u32, stream);
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
    MergePackedClaims,
    ab_gkr_merge_claims_e4_kernel(
        claims: *const E4,
        count: u32,
        coordinates: *const E4,
        pack_log2: u32,
        merged: *mut E4,
    )
);

/// Folds each group of `2^pack_log2` consecutive claims of a physically packed polynomial into one,
/// coordinate zero first, zero-padding the last group. `pack_log2 = 0` aliases the claims at the
/// caller and never reaches this launcher; a group fits one warp for `pack_log2 <= 5`.
pub fn merge_packed_claims(
    claims: &DeviceSlice<E4>,
    coordinates: &DeviceSlice<E4>,
    pack_log2: u32,
    merged: &mut DeviceSlice<E4>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(
        (1..=5).contains(&pack_log2),
        "E4 claim merging requires pack_log2 in 1..=5; larger groups need a cross-warp reduction"
    );
    assert_eq!(coordinates.len(), pack_log2 as usize);
    assert_eq!(merged.len(), claims.len().div_ceil(1usize << pack_log2));
    if claims.is_empty() {
        return Ok(());
    }
    let count = u32::try_from(claims.len()).expect("E4 packed claim count exceeds u32");
    let groups = u32::try_from(merged.len()).expect("E4 packed group count exceeds u32");
    let config = CudaLaunchConfig::basic(groups.div_ceil(4), 128u32, stream);
    let args = MergePackedClaimsArguments::new(
        claims.as_ptr(),
        count,
        coordinates.as_ptr(),
        pack_log2,
        merged.as_mut_ptr(),
    );
    MergePackedClaimsFunction::default().launch(&config, &args)
}
