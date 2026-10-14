//! GKR/WHIR verifier code generation from a circuit artifact.
//!
//! - [`circuit_yul::emit_circuit_yul`] emits the circuit-specific `circuit.yul` (the GKR
//!   per-layer sumcheck/gate Yul functions) as a String.
//! - [`generate_verifier`] assembles the merged `GkrWhirVerifier` Solidity source: that Yul and
//!   the WHIR template's Yul are inlined into the hand-written GKR template and the
//!   circuit-derived (plus a few caller-supplied) constants substituted. GKR and WHIR are
//!   verified in ONE transaction, the GKR→WHIR handoff state passed in memory.

mod circuit_yul;
mod whir;

pub use circuit_yul::emit_circuit_yul;
pub use whir::WhirGenConfig;

// ── Transcript-preimage layout (bytes) ──────────────────────────────────────────────────────
// The GKR transcript preimage is `registers ‖ final_pc+timestamp ‖ top_bits
// (num_teardown_sets · 4) ‖ setup_cap ‖ memory_cap`. The fixed machine-state prefix (registers
// and final pc/ts) is a RISC-V ABI constant, not circuit-derived — but it's shared by the
// on-chain preimage handling (circuit.yul) and the calldata-size computation (assemble.rs), so
// it lives here once to keep the two in lockstep.
pub(crate) const PREIMAGE_REGISTERS_BYTES: usize = 384;
pub(crate) const PREIMAGE_FINAL_PC_TS_BYTES: usize = 12;
/// Byte offset of the inits/teardowns `top_bits` block within the preimage (after the fixed prefix).
pub(crate) const PREIMAGE_TOP_BITS_BYTE_OFFSET: usize =
    PREIMAGE_REGISTERS_BYTES + PREIMAGE_FINAL_PC_TS_BYTES;

// `generate_verifier` is implemented in `assemble.rs`.
mod assemble;
pub use assemble::generate_verifier;
