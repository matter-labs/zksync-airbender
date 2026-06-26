#![no_std]
#![no_main]

// Unified full-statement verifier (base layer) RISC-V binary. Unlike the per-circuit bins, this
// uses the `full_statement_verifier` crate directly (no generated per-circuit module), so there is
// no `#[path]` import — just the shared FSV entry point.
include!("../common_fsv_unified_base.rs");
