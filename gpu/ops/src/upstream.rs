//! Upstream re-export manifest for `gpu_ops`.
//!
//! `gpu_ops` is GPU-substrate math: production code imports field types from
//! `gpu_core::primitives::field`. Only the test suites reference the `field`
//! crate's trait items, via this shim.

#[cfg(test)]
pub(crate) use field::{Field, FieldExtension};
