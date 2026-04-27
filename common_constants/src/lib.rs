#![no_std]
#![cfg_attr(all(feature = "verifier_stats", not(target_arch = "riscv32")), feature(thread_local))]

pub mod circuit_families;
pub mod delegation_types;
pub mod rom;
#[cfg(feature = "verifier_stats")]
pub mod stats;
pub mod timestamps;

/// This module is meant to contain extensions that are outside of the proving path,
/// e.g. for development.
pub mod internal_features {
    /// Development-only CSR recognized by the transpiler-side cycle marker hooks.
    ///
    /// This is intended for local transpiler profiling only.
    ///
    /// The proving path rejects this CSR during replay/witness generation, so a
    /// program that contains it should be treated as a development artifact and
    /// must not be proved.
    pub const TRANSPILER_MARKER_CSR: u32 = 0x7ff;
}

pub use self::circuit_families::*;
pub use self::delegation_types::*;
pub use self::rom::*;
pub use self::timestamps::*;

pub const PC_STEP: usize = core::mem::size_of::<u32>();
pub const INITIAL_PC: u32 = 0;
pub const NON_DETERMINISM_CSR: u32 = 0x7c0;
pub const CYCLE_CSR_INDEX: u32 = 3072;
pub const DELEGATION_INVOCATION_OFFET: TimestampScalar = 1; // delegation register writes are 1 mod 4
pub const DELEGATION_EXECUTION_OFFET: TimestampScalar = 2; // delegation circuit writes are (1 + 2) mod 4
