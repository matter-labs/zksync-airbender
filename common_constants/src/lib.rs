#![no_std]

pub mod circuit_families;
pub mod delegation_types;
pub mod rom;
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
