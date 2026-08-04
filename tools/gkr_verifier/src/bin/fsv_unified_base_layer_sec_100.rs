#![no_std]
#![no_main]

// Unified full-statement verifier (base layer) RISC-V binary, 100-bit security. Uses the
// `full_statement_verifier` crate directly (no generated per-circuit module), so there is no
// `#[path]` import — just the shared FSV entry point wired to the sec_100 verifiers.
include!("../common_fsv_unified_base_sec_100.rs");
