//! fwd-VM v2: the production forward-VM interpreter path.
//!
//! Task 7 (this module bring-up) defines the descriptor ABI ([`desc`]); Task 8
//! adds the CUDA kernel bindings and Task 9 the lowering that assembles
//! [`desc::FwdVmDesc`] from a compiled `gkr_eval_isa::fwd` layer.

// Consumed by Tasks 8/9; nothing outside the ABI definition exists yet.
#[allow(dead_code)]
pub(crate) mod desc;
