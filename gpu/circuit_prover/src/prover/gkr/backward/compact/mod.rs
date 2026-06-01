//! Compact descriptors for the GKR backward main-layer flat path.
//!
//! Each per-launch source pointer collapses to a `u16` packed
//! `(virtual?/slot, poly_idx)` reference, with a small per-launch `tables`
//! block (`bases[8]` / `log2_stride[16]`) that the kernel uses to resolve
//! the byte address. Term tables (`c0_bf`, `c0_ext`, `c1_*`, `c1_linear`,
//! etc.) use u16 source indices.
//!
//! Round 0's source u16 has no folding cache, so bit 15 doubles as
//! `is_virtual`.

mod cont_backing;
mod cont_descs;
pub(crate) mod encoder;
mod encoding;
mod kernel_limits;
mod kernels;
mod round0_desc;
mod round12_descs;

pub(crate) use cont_backing::*;
pub(crate) use cont_descs::*;
pub(crate) use encoding::*;
pub(crate) use kernel_limits::*;
pub(crate) use kernels::*;
pub(crate) use round0_desc::*;

pub(in crate::prover::gkr::backward) use round12_descs::{
    build_flat_round1_unified_desc, build_flat_round2_unified_desc,
};

#[cfg(test)]
mod tests;
