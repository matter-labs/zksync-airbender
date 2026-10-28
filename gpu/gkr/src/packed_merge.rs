//! BabyBear extension-field claim folding at the GKR-to-WHIR boundary.

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use gpu_core::primitives::field::E4;
use gpu_prover_context::ProverContext;

cuda_kernel_signature_arguments_and_function!(E4MergeClaims, claims: *const E4, count: u32, coordinates: *const E4, pack_log2: u32, merged: *mut E4);
cuda_kernel_declaration!(ab_gkr_merge_claims_e4_kernel(claims: *const E4, count: u32, coordinates: *const E4, pack_log2: u32, merged: *mut E4));

/// Fold adjacent claims with coordinate zero first, zero-padding the last group.
/// k=0 aliases the original claims at the caller and never reaches this launcher.
pub fn launch_merge_claims_e4(
    claims: &DeviceSlice<E4>,
    coordinates: &DeviceSlice<E4>,
    pack_log2: u32,
    merged: &mut DeviceSlice<E4>,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(
        (1..=4).contains(&pack_log2),
        "unsupported E4 packing factor"
    );
    assert_eq!(coordinates.len(), pack_log2 as usize);
    assert_eq!(merged.len(), claims.len().div_ceil(1usize << pack_log2));
    if claims.is_empty() {
        return Ok(());
    }
    let count = u32::try_from(claims.len()).expect("E4 packed claim count exceeds u32");
    let groups = u32::try_from(merged.len()).expect("E4 packed group count exceeds u32");
    E4MergeClaimsFunction(ab_gkr_merge_claims_e4_kernel).launch(
        &CudaLaunchConfig::basic(groups.div_ceil(4), 128, context.get_exec_stream()),
        &E4MergeClaimsArguments::new(
            claims.as_ptr(),
            count,
            coordinates.as_ptr(),
            pack_log2,
            merged.as_mut_ptr(),
        ),
    )
}

#[cfg(test)]
pub(crate) mod tests;
