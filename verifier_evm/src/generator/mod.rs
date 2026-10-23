//! GKR/WHIR verifier code generation from a circuit artifact.
//!
//! - [`circuit_yul::emit_circuit_yul`] emits the circuit-specific `circuit.yul` (the GKR
//!   per-layer sumcheck/gate Yul functions) as a String.
//! - [`generate_verifier`] assembles the merged `GkrWhirVerifier` Solidity source: that Yul and
//!   the WHIR template's Yul are inlined into the hand-written GKR template and the
//!   circuit-derived (plus a few caller-supplied) constants substituted. GKR and WHIR are
//!   verified in ONE transaction, the GKR→WHIR handoff state passed in memory.
//!
//! Every value the templates need that is owned by the compiled circuit or the prover config
//! is a `__TEMPLATE_*` Solidity constant: the templates reference those by NAME everywhere
//! (Yul can only consume literal constants, so the generator assigns the literal once, in the
//! declaration) — no numeric assumption about caps, widths, output counts or heap offsets is
//! spelled out in the Solidity source. In the templates these constants hold the string
//! literal `"{unassigned}"`, which solc rejects for a numeric constant, so a generator that
//! forgets an assignment cannot produce a buildable verifier.

mod circuit_yul;
mod f1;
mod preprocess;
mod whir;

pub use circuit_yul::{emit_circuit_yul, emit_circuit_yul_with_stats, CircuitYulStats};
pub use whir::WhirGenConfig;
// `Lit` (below) is the generated-constant value+expression pair `WhirGenConfig::memory_regions`
// returns.

// ── Transcript-preimage layout (bytes) ──────────────────────────────────────────────────────
// The GKR transcript preimage is `registers ‖ final_pc+timestamp ‖ top_bits
// (num_teardown_sets · 4) ‖ setup_cap ‖ memory_cap`. The fixed machine-state prefix (registers
// and final pc/ts) is a RISC-V ABI constant, not circuit-derived; everything after it is sized by
// the circuit (teardown sets) and the prover config (merkle cap), so the offsets of the
// circuit-sized tail are generated (`__TEMPLATE_PREIMAGE_*`) from these shared definitions.
/// RISC-V register file size.
pub(crate) const NUM_REGISTERS: usize = 32;
/// Bytes per register in the preimage: `(value, ts_low, ts_high)` as three LE u32.
pub(crate) const PREIMAGE_REGISTER_STRIDE: usize = 12;
pub(crate) const PREIMAGE_REGISTERS_BYTES: usize = NUM_REGISTERS * PREIMAGE_REGISTER_STRIDE;
pub(crate) const PREIMAGE_FINAL_PC_TS_BYTES: usize = 12;
/// Byte offset of the inits/teardowns `top_bits` block within the preimage (after the fixed prefix).
pub(crate) const PREIMAGE_TOP_BITS_BYTE_OFFSET: usize =
    PREIMAGE_REGISTERS_BYTES + PREIMAGE_FINAL_PC_TS_BYTES;
/// Number of inits/teardowns RAM sets the GKR template pins as
/// `__TEMPLATE_INITS_TEARDOWNS_TOP_BITS_{0..N}` constants (one `uint8` each).
pub(crate) const NUM_INITS_TEARDOWNS_TOP_BITS: usize = 2;

/// A generated constant: its numeric value plus the human-readable numeric expression the
/// generator writes into the Solidity declaration (`32 * 7` rather than `224`). Inline assembly
/// accepts constant declarations whose RHS is a pure numeric expression, but NOT ones that
/// reference other constants (solc error 7615), so expressions are built from numbers only; the
/// value and the expression are always built together, so they cannot disagree. (No `/`:
/// Solidity folds literal division as a rational, so `119 / 16` is a type error — integer
/// divisions by powers of two are spelled as shifts.)
#[derive(Clone, Debug)]
pub struct Lit {
    pub value: u128,
    expr: String,
    /// Solidity precedence of the top-level operator (3 = atom, 2 = `*`, 1 = `+ -`, 0 = `<< >>`).
    prec: u8,
}

impl Lit {
    pub fn num(value: u128) -> Self {
        Self {
            value,
            expr: value.to_string(),
            prec: 3,
        }
    }
    /// `1 << log2`
    pub fn pow2(log2: u128) -> Self {
        assert!(log2 < 128);
        Self {
            value: 1u128 << log2,
            expr: format!("1 << {log2}"),
            prec: 0,
        }
    }
    fn bin(&self, op: &str, lvl: u8, rhs: &Lit, value: u128) -> Self {
        let associative = matches!(op, "+" | "*");
        // shifts: always parenthesize a compound left operand — `(104 + 16 - 1) >> 4` reads
        // as intended even though `>>` already binds loosest
        let l = if self.prec < lvl || (lvl == 0 && self.prec < 3) {
            format!("({})", self.expr)
        } else {
            self.expr.clone()
        };
        let r = if rhs.prec < lvl || (!associative && rhs.prec == lvl) {
            format!("({})", rhs.expr)
        } else {
            rhs.expr.clone()
        };
        Self {
            value,
            expr: format!("{l} {op} {r}"),
            prec: lvl,
        }
    }
    pub fn mul(&self, rhs: &Lit) -> Self {
        self.bin("*", 2, rhs, self.value * rhs.value)
    }
    /// `self >> log2` (integer division by a power of two).
    pub fn shr(&self, log2: u128) -> Self {
        self.bin(">>", 0, &Lit::num(log2), self.value >> log2)
    }
    pub fn add(&self, rhs: &Lit) -> Self {
        self.bin("+", 1, rhs, self.value + rhs.value)
    }
    pub fn sub(&self, rhs: &Lit) -> Self {
        self.bin("-", 1, rhs, self.value - rhs.value)
    }
    /// `32 * n` — a region of `n` 32-byte words.
    pub fn words(n: u128) -> Self {
        Lit::num(32).mul(&Lit::num(n))
    }
    pub fn expr(&self) -> &str {
        &self.expr
    }
}

/// The F1 verifier and the `SetupFrontier` data contract it reads.
#[derive(Clone, Debug)]
pub struct F1Contracts {
    /// The merged F1 `GkrWhirVerifier` source.
    pub verifier_sol: String,
    /// The `SetupFrontier` data contract source.
    pub setup_frontier_sol: String,
}

// `generate_verifier` is implemented in `assemble.rs`.
mod assemble;
pub use assemble::{generate_f1_verifier, generate_verifier};
