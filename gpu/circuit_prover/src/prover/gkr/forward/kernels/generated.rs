//! Production binding for the pre-generated fused GKR forward layer-0 kernel
//! (`add_sub_lui_auipc_mop` circuit, cached layout).
//!
//! This is the production counterpart of the validated test bindings in
//! `prover::gkr::forward::tests::generated_layer0_parity` and
//! `prover::tests::generated_forward_layer0_real_witness`: the same
//! `#[repr(C)]` proxy, the same `cuda_kernel_*` ABI, and the same
//! `__constant__` challenge-table symbols. It is wired into the forward pass by
//! the `AB_GKR_FWD_GENERATED_LAYER0` A/B switch (see
//! `super::super::generated_layer0`).

use era_cudart::execution::KernelFunction;
use era_cudart::result::CudaResult;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};

use super::gkr_forward_launch_config;
use crate::primitives::field::{BF, E4};
use crate::prover::ProverContext;

/// Per-row forward proxy. Field-for-field mirror of the native
/// `GkrFwdProxy<E>` in `gkr_forward_generation.cuh`. Column-major data buffers:
/// element `(column c, row gid)` lives at `base[c * trace_len + gid]`. The
/// forward-generation-specific challenge data rides here (was `__constant__`):
/// `perm_challenges` / `perm_additive` by value (host-known at schedule time),
/// `decoder_fill_value` by device pointer (computed in setup). The shared
/// gamma/alpha-power tables still live in `__constant__`.
#[repr(C)]
pub(crate) struct GpuGkrFwdProxy<E> {
    pub(crate) memory: *const BF,
    pub(crate) witness: *const BF,
    pub(crate) setup: *const BF,
    pub(crate) generic_lookup: *const E,
    pub(crate) generic_lookup_len: u32,
    pub(crate) cache_base: *mut BF,
    pub(crate) cache_ext: *mut E,
    pub(crate) out_base: *mut BF,
    pub(crate) out_ext: *mut E,
    pub(crate) trace_len: u32,
    /// Permutation linearization challenges by role (zero-padded to the slot
    /// count). Mirrors `GkrFwdProxy::perm_challenges`.
    pub(crate) perm_challenges: [E; PERM_CHALLENGE_SLOTS],
    /// Additive linearization seed. Mirrors `GkrFwdProxy::perm_additive`.
    pub(crate) perm_additive: E,
    /// Pointer to the device-resident decoder fill value (one `E`), read on
    /// padding rows. Mirrors `GkrFwdProxy::decoder_fill_value`.
    pub(crate) decoder_fill_value: *const E,
}

impl<E: Copy> Copy for GpuGkrFwdProxy<E> {}
impl<E: Copy> Clone for GpuGkrFwdProxy<E> {
    fn clone(&self) -> Self {
        *self
    }
}

// SAFETY: raw device pointers passed by value into a grid-constant kernel arg.
// The forward scheduler keeps the backing allocations (consolidated storage
// backings + the forward-setup fill-value allocation) alive across the
// stream-ordered launch.
unsafe impl<E> Send for GpuGkrFwdProxy<E> {}
unsafe impl<E> Sync for GpuGkrFwdProxy<E> {}

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GpuGkrFwdAddSubLayer0<T>,
    proxy: GpuGkrFwdProxy<T>,
    count: u32,
);
cuda_kernel_declaration!(pub(crate)
    ab_gkr_forward_add_sub_lui_auipc_mop_layer0_kernel(proxy: GpuGkrFwdProxy<E4>, count: u32)
);

/// Launch the pre-generated fused `add_sub_lui_auipc_mop` layer-0 forward
/// kernel (one thread per trace row). The proxy must already point at valid,
/// stream-live input/output device buffers; the `__constant__` challenge tables
/// must already be populated stream-ordered before this launch.
pub(crate) fn launch_generated_add_sub_layer0(
    proxy: GpuGkrFwdProxy<E4>,
    trace_len: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(trace_len <= u32::MAX as usize);
    let count = trace_len as u32;
    let config = gkr_forward_launch_config(count, context);
    let args = GpuGkrFwdAddSubLayer0Arguments::new(proxy, count);
    GpuGkrFwdAddSubLayer0Function(ab_gkr_forward_add_sub_lui_auipc_mop_layer0_kernel)
        .launch(&config, &args)
}

/// Number of permutation linearization challenge slots in the proxy's
/// `perm_challenges` array (= `GKR_FORWARD_CACHE_MEMORY_LINEAR_TERMS` on the
/// native side, = `MEMORY_TUPLE_LINEAR_TERMS` on the Rust side).
pub(crate) const PERM_CHALLENGE_SLOTS: usize = super::MEMORY_TUPLE_LINEAR_TERMS;
