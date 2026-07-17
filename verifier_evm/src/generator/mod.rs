//! GKR/WHIR verifier code generation from a circuit artifact.
//!
//! - [`circuit_yul::emit_circuit_yul`] emits the circuit-specific `circuit.yul` (the GKR
//!   per-layer sumcheck/gate Yul functions) as a String.
//! - [`generate_verifiers`] assembles the full GKR + WHIR + Registry Solidity sources by
//!   inlining that Yul into the hand-written templates and substituting the circuit-derived
//!   (and a few caller-supplied) constants.

mod circuit_yul;

pub use circuit_yul::emit_circuit_yul;

use cs::gkr_compiler::GKRCircuitArtifact;
use field::Proth120;

/// The three Solidity sources produced for a given circuit. Each is a complete, standalone
/// contract source string ready to be written to a file and compiled.
#[derive(Clone, Debug)]
pub struct GeneratedContracts {
    /// The GKR verifier (`gkr.sol` template with `circuit.yul` inlined + constants substituted).
    pub gkr_sol: String,
    /// The WHIR proximity-test verifier (`whir.sol`, artifact-derivable constants substituted).
    pub whir_sol: String,
    /// The `GkrWhirRegistry` cross-check contract (static; no circuit-specific constants).
    pub registry_sol: String,
}

// `generate_verifiers` is implemented in `assemble.rs`.
mod assemble;
pub use assemble::generate_verifiers;
