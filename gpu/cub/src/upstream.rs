//! Upstream re-export manifest for `gpu_cub`.
//!
//! Production code is `gpu_core`-only. Only the test suites reference the
//! `field` crate's trait items, via this shim.

#[cfg(test)]
pub(crate) use field::Field;
