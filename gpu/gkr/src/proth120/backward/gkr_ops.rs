use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use gpu_core::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};

use crate::gkr_ops::{GpuCombinedClaimDesc, GKR_COMBINED_CLAIM_MAX_PAIRS};
use crate::upstream::PR;

cuda_kernel!(
    PrNewClaimsTwoVar,
    ab_pr_gkr_ops_new_claims_two_var_kernel(
        last_evals_packed: *const PR,
        challenges: *const PR,
        new_claims_out: *mut PR,
        num_addresses: u32,
    )
);

cuda_kernel!(
    PrNewClaimsLinear,
    ab_pr_gkr_ops_new_claims_linear_kernel(
        last_evals_packed: *const PR,
        challenges: *const PR,
        new_claims_out: *mut PR,
        num_addresses: u32,
    )
);

cuda_kernel!(
    PrDimReducingLsbLines,
    ab_pr_gkr_ops_dim_reducing_lsb_lines_kernel(
        last_evals_packed: *const PR,
        challenges: *const PR,
        lsb_lines_out: *mut PR,
        num_addresses: u32,
    )
);

cuda_kernel!(
    PrBuildCombinedClaim,
    ab_pr_gkr_ops_build_combined_claim_kernel(
        claims: *const PR,
        batching: *const PR,
        desc: GpuCombinedClaimDesc,
        claim_out: *mut PR,
        eq_prefactor_out: *mut PR,
    )
);

const _: () = assert!(size_of::<GpuCombinedClaimDesc>() == 8 + 8 * GKR_COMBINED_CLAIM_MAX_PAIRS);

fn address_config(num_addresses: usize, stream: &CudaStream) -> (CudaLaunchConfig<'_>, u32) {
    assert!(
        num_addresses > 0,
        "Proth120 claim update needs at least one address"
    );
    let count =
        u32::try_from(num_addresses).expect("Proth120 claim update address count exceeds u32");
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    (CudaLaunchConfig::basic(grid_dim, block_dim, stream), count)
}

pub(crate) fn new_claims_two_var(
    last_evals_packed: &DeviceSlice<PR>,
    challenges: &DeviceSlice<PR>,
    new_claims_out: &mut DeviceSlice<PR>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(last_evals_packed.len(), new_claims_out.len() * 4);
    assert!(challenges.len() >= 2);
    let (config, count) = address_config(new_claims_out.len(), stream);
    PrNewClaimsTwoVarFunction::default().launch(
        &config,
        &PrNewClaimsTwoVarArguments::new(
            last_evals_packed.as_ptr(),
            challenges.as_ptr(),
            new_claims_out.as_mut_ptr(),
            count,
        ),
    )
}

pub(crate) fn new_claims_linear(
    last_evals_packed: &DeviceSlice<PR>,
    challenges: &DeviceSlice<PR>,
    new_claims_out: &mut DeviceSlice<PR>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(last_evals_packed.len(), new_claims_out.len() * 2);
    assert!(!challenges.is_empty());
    let (config, count) = address_config(new_claims_out.len(), stream);
    PrNewClaimsLinearFunction::default().launch(
        &config,
        &PrNewClaimsLinearArguments::new(
            last_evals_packed.as_ptr(),
            challenges.as_ptr(),
            new_claims_out.as_mut_ptr(),
            count,
        ),
    )
}

pub(crate) fn dim_reducing_lsb_lines(
    last_evals_packed: &DeviceSlice<PR>,
    challenges: &DeviceSlice<PR>,
    lsb_lines_out: &mut DeviceSlice<PR>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(lsb_lines_out.len() % 2, 0);
    let num_addresses = lsb_lines_out.len() / 2;
    assert_eq!(last_evals_packed.len(), num_addresses * 4);
    assert!(!challenges.is_empty());
    let (config, count) = address_config(num_addresses, stream);
    PrDimReducingLsbLinesFunction::default().launch(
        &config,
        &PrDimReducingLsbLinesArguments::new(
            last_evals_packed.as_ptr(),
            challenges.as_ptr(),
            lsb_lines_out.as_mut_ptr(),
            count,
        ),
    )
}

pub(crate) fn build_combined_claim(
    claims: &DeviceSlice<PR>,
    batching: &DeviceSlice<PR>,
    desc_pairs: &[u32],
    claim_out: &mut DeviceSlice<PR>,
    eq_prefactor_out: &mut DeviceSlice<PR>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(batching.len(), 1);
    assert_eq!(claim_out.len(), 1);
    assert_eq!(eq_prefactor_out.len(), 1);
    assert_eq!(desc_pairs.len() % 2, 0);
    let num_pairs = desc_pairs.len() / 2;
    assert!(
        num_pairs <= GKR_COMBINED_CLAIM_MAX_PAIRS,
        "Proth120 combined claim has {num_pairs} pairs; the descriptor holds {GKR_COMBINED_CLAIM_MAX_PAIRS}"
    );
    let mut desc = GpuCombinedClaimDesc {
        num_terms: num_pairs as u32,
        ..Default::default()
    };
    desc.entries[..desc_pairs.len()].copy_from_slice(desc_pairs);
    let config = CudaLaunchConfig::basic(1u32, 256u32, stream);
    PrBuildCombinedClaimFunction::default().launch(
        &config,
        &PrBuildCombinedClaimArguments::new(
            claims.as_ptr(),
            batching.as_ptr(),
            desc,
            claim_out.as_mut_ptr(),
            eq_prefactor_out.as_mut_ptr(),
        ),
    )
}
