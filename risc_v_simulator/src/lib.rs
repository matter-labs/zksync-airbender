//! Temporary compatibility wrapper around `riscv_transpiler`.
//!
//! Existing workspace imports still resolve through this crate, but the shared
//! definitions now live in `riscv_transpiler` so we can invert the dependency
//! direction without a repo-wide import rewrite.

pub use riscv_transpiler::abstractions;
pub use riscv_transpiler::cycle;
pub use riscv_transpiler::machine_mode_only_unrolled;
