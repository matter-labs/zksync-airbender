//! One-time kernel shared-memory carveout setup and the device-symbol address
//! lookup for the flat `__constant__` coefficient buffer shared by round-0
//! and continuation phases.

use std::ffi::c_void;

use era_cudart::result::CudaResultWrap;
use era_cudart_sys::cudaGetSymbolAddress;

use super::types::FLAT_CONST_MAX;
use crate::primitives::field::E4;
use crate::primitives::utils::{
    compute_minimal_carveout, set_shared_carveout, smem_pool_bytes_per_sm,
};

/// One-time setup: configure shared memory carveout for flat kernels.
/// Kernels without shared memory get 0% (maximize L1).
/// The unified tiled kernels get a minimal carveout (just enough for their
/// static shared memory at max occupancy), leaving the rest for L1.
pub(in crate::prover) fn configure_flat_kernel_cache_preference() {
    static ONCE: std::sync::Once = std::sync::Once::new();
    ONCE.call_once(|| {
        use super::super::compact::{
            ab_gkr_main_round0_flat_compact_e4_kernel,
            ab_gkr_main_round0_flat_constant_compact_e4_kernel,
            ab_gkr_main_round1_flat_constant_compact_unified_compact_e4_kernel,
            ab_gkr_main_round2_flat_constant_compact_unified_compact_e4_kernel,
            ab_gkr_main_round3_flat_constant_explicit_unified_compact_e4_kernel,
            ab_gkr_main_round3_flat_constant_unified_compact_e4_kernel,
        };
        // Kernels with zero shared memory → 0% carveout → maximize L1.
        let no_smem_kernels: &[*const std::ffi::c_void] = &[
            ab_gkr_main_round0_flat_compact_e4_kernel as *const std::ffi::c_void,
            ab_gkr_main_round0_flat_constant_compact_e4_kernel as *const std::ffi::c_void,
        ];
        for &kernel in no_smem_kernels {
            set_shared_carveout(kernel, 0);
        }

        // Unified tiled kernels: compute the minimal carveout from the device's
        // configurable shared/L1 pool size and each kernel's actual shared memory
        // footprint at max occupancy.
        let pool_bytes = smem_pool_bytes_per_sm();
        let block_size = 128i32; // all unified tiled kernels use 128 threads
        for kernel in [
            ab_gkr_main_round1_flat_constant_compact_unified_compact_e4_kernel
                as *const std::ffi::c_void,
            ab_gkr_main_round3_flat_constant_unified_compact_e4_kernel as *const std::ffi::c_void,
            ab_gkr_main_round3_flat_constant_explicit_unified_compact_e4_kernel
                as *const std::ffi::c_void,
            ab_gkr_main_round2_flat_constant_compact_unified_compact_e4_kernel
                as *const std::ffi::c_void,
        ] {
            let pct = compute_minimal_carveout(kernel, block_size, pool_bytes);
            set_shared_carveout(kernel, pct);
        }
    });
}

// ---------------------------------------------------------------------------
// __constant__ symbol address
// ---------------------------------------------------------------------------

extern "C" {
    static ab_gkr_flat_coefficients: [E4; FLAT_CONST_MAX];
}

/// Get the device address of the `__constant__` coefficient symbol.
/// This is a trivial host-side symbol lookup (no GPU blocking).
/// The same pointer is used by both round-0 and continuation compiler
/// kernels (their writes are stream-serialized into disjoint phases).
pub(crate) fn get_constant_coefficients_device_ptr() -> *mut E4 {
    let mut ptr: *mut c_void = std::ptr::null_mut();
    // SAFETY: ab_gkr_flat_coefficients is a valid __constant__ symbol
    // defined in backward/round3_compute_coeff.cu.
    unsafe {
        cudaGetSymbolAddress(
            &mut ptr,
            &ab_gkr_flat_coefficients as *const _ as *const c_void,
        )
    }
    .wrap()
    .expect("cudaGetSymbolAddress failed for ab_gkr_flat_coefficients");
    ptr as *mut E4
}
