//! FROZEN backward coefficient-ISA format bounds (design §9.1-§9.4) and the
//! exact corpus maxima Task 3's census measured.
//!
//! Two kinds of number live here and they must never be blended:
//!
//!   * **Encoding limits** — what the wire format can express: thirteen
//!     coefficient bits, three opcode bits, 64 source windows, the 32,764-byte
//!     kernel-argument cap. These come from §9 and are not measurements.
//!   * **Corpus maxima** — what the production corpus actually needs, written as
//!     the EXACT observed value. Never rounded up for headroom: a constant that
//!     is larger than the measurement hides drift instead of reporting it.
//!
//! The maxima are further split into two named sets, because
//! `blake2_with_compression` is only CONDITIONALLY in scope (§3.1):
//!
//!   * [`in_scope`] — the mandatory production corpus. Every format/ABI decision
//!     in Tasks 4-9 is sized from HERE.
//!   * [`with_conditional_blake2`] — the same census including the conditional
//!     `blake2_with_compression` attempt. DIAGNOSTIC only. Sizing a descriptor
//!     from a blended maximum would silently pay for a circuit that may be
//!     excluded.
//!
//! One backward production lineage: an overflow of any bound here is a compiler
//! error. There is no extended record, no version field, and no fallback format.

use super::model::CoefficientRecipeId;

// ── Encoding limits (§9) ─────────────────────────────────────────────────────

/// `bits 0..12` of the u16 header (§9.2).
pub const HEADER_COEFFICIENT_BITS: u32 = 13;
/// `bits 13..15` of the u16 header (§9.2).
pub const HEADER_OPCODE_BITS: u32 = 3;

const _: () = assert!(HEADER_COEFFICIENT_BITS + HEADER_OPCODE_BITS == 16);

/// Coefficient encodings thirteen bits admit, INCLUDING the two reserved
/// literals. A layer's banked recipe count plus
/// [`CoefficientRecipeId::RESERVED`] must not exceed it.
pub const MAX_COEFFICIENT_ENCODINGS: usize = 1 << HEADER_COEFFICIENT_BITS;
const _: () = assert!(MAX_COEFFICIENT_ENCODINGS == 8_192);

/// Opcode values three bits admit, per regime.
pub const MAX_OPCODES_PER_REGIME: usize = 1 << HEADER_OPCODE_BITS;
const _: () = assert!(MAX_OPCODES_PER_REGIME == 8);

/// `source_window:6` of the input word (§9.4).
pub const MAX_SOURCE_WINDOWS: usize = 64;
/// `column:7` of the input word: a window covers at most this many contiguous
/// referenced columns (§9.4).
pub const SOURCE_WINDOW_COLUMNS: usize = 128;

/// u16 words one input contributes at MINIMUM: the input word itself, with no
/// fill destination and no Endpoint0/Delta plan (§9.1).
pub const WORDS_PER_INPUT_MIN: usize = 1;
/// u16 words one input contributes at MAXIMUM: the input word plus its single
/// canonical extension word (§9.4 `FillSource` destination lane / §9.5 plan).
pub const WORDS_PER_INPUT_MAX: usize = 2;
/// A move is `move_header`, `source_cell`, `destination_cell` (§9.6) — 6 bytes,
/// never extended.
pub const MOVE_WORDS: usize = 3;

/// The by-value kernel-argument cap the whole encoded program plus its descriptor
/// metadata must fit (§9.1). There is no device-pointer program representation.
pub const KERNEL_ARGUMENT_CEILING_BYTES: usize = 32_764;

// ── Frozen regime opcode tables (§6, §9.2) ───────────────────────────────────

/// Every semantic term category the two regimes can encode.
///
/// The opcode NUMBERS are frozen per regime by [`r0_opcode`] and
/// [`continuation_opcode`]; a category illegal in a regime has no opcode there.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TermCategory {
    C0LinearBf,
    C0LinearE4,
    C2ProductBfBf,
    C2ProductBfE4,
    C2ProductE4E4,
    DualProductE4,
    MoveBf,
    MoveE4,
}

impl TermCategory {
    pub fn is_legal_in(self, r0: bool) -> bool {
        if r0 { r0_opcode(self).is_some() } else { continuation_opcode(self).is_some() }
    }

    pub fn label(self) -> &'static str {
        match self {
            TermCategory::C0LinearBf => "C0LinearBF",
            TermCategory::C0LinearE4 => "C0LinearE4",
            TermCategory::C2ProductBfBf => "C2ProductBF_BF",
            TermCategory::C2ProductBfE4 => "C2ProductBF_E4",
            TermCategory::C2ProductE4E4 => "C2ProductE4_E4",
            TermCategory::DualProductE4 => "DualProductE4",
            TermCategory::MoveBf => "MoveBF",
            TermCategory::MoveE4 => "MoveE4",
        }
    }
}

/// FROZEN R0 opcode table (design §6, brief Task 3):
///
/// ```text
/// 0 C0LinearBF
/// 1 C0LinearE4
/// 2 C2ProductBF_BF
/// 3 C2ProductBF_E4
/// 4 C2ProductE4_E4
/// 5 MoveBF
/// 6 MoveE4
/// 7 invalid
/// ```
///
/// `None` = the category has no R0 encoding. Opcode 7 is deliberately left
/// invalid: no uncensused category is pre-allocated.
pub const fn r0_opcode(category: TermCategory) -> Option<u16> {
    match category {
        TermCategory::C0LinearBf => Some(0),
        TermCategory::C0LinearE4 => Some(1),
        TermCategory::C2ProductBfBf => Some(2),
        TermCategory::C2ProductBfE4 => Some(3),
        TermCategory::C2ProductE4E4 => Some(4),
        TermCategory::MoveBf => Some(5),
        TermCategory::MoveE4 => Some(6),
        TermCategory::DualProductE4 => None,
    }
}

/// FROZEN continuation opcode table (design §6, brief Task 3):
///
/// ```text
/// 0 C0LinearE4
/// 1 DualProductE4
/// 2 MoveE4
/// 3..7 invalid
/// ```
///
/// Opcodes 3..7 stay invalid because the full-corpus census measured
/// [`in_scope::MAX_CONTINUATION_STANDALONE_PRODUCTS`] `== 0`: continuation
/// lowering emits ONLY `C0Linear` and native `DualProduct`, so a standalone
/// continuation `C0Product`/`C2Product` is a structural compiler error, not an
/// opcode. If a future corpus makes one live, assign the OBSERVED category the
/// next opcode and pin its count — do not pre-allocate hypotheticals.
pub const fn continuation_opcode(category: TermCategory) -> Option<u16> {
    match category {
        TermCategory::C0LinearE4 => Some(0),
        TermCategory::DualProductE4 => Some(1),
        TermCategory::MoveE4 => Some(2),
        TermCategory::C0LinearBf
        | TermCategory::C2ProductBfBf
        | TermCategory::C2ProductBfE4
        | TermCategory::C2ProductE4E4
        | TermCategory::MoveBf => None,
    }
}

/// Live R0 opcodes: seven, exactly as §9.2 predicted.
pub const R0_LIVE_OPCODES: usize = 7;
/// Live continuation opcodes: three (§9.2 allows "at most five, including
/// standalone split forms only if their census is nonzero" — the census is zero).
pub const CONTINUATION_LIVE_OPCODES: usize = 3;

const _: () = assert!(R0_LIVE_OPCODES <= MAX_OPCODES_PER_REGIME);
const _: () = assert!(CONTINUATION_LIVE_OPCODES <= MAX_OPCODES_PER_REGIME);

// ── Schedule-independent stream bounds ───────────────────────────────────────

/// The MINIMUM u16 words any codec can encode this term population in: one
/// header plus one word per source input, no extension words, no fills, no plans
/// and no moves (§9.1).
///
/// This bounds from BELOW, so it is the only bound whose overflow is terminal:
/// paging, placement and the real encoder in Tasks 4-9 can only ADD words. It
/// counts the program stream alone — other by-value descriptor metadata is
/// additional, which keeps it a true lower bound.
pub const fn lower_bound_program_words(unary_terms: usize, binary_terms: usize) -> usize {
    unary_terms * (1 + WORDS_PER_INPUT_MIN) + binary_terms * (1 + 2 * WORDS_PER_INPUT_MIN)
}

/// The MAXIMUM u16 words any schedule can need: every input takes its single
/// canonical extension word, plus one 3-word move per projection a schedule could
/// choose to relocate (§9.4-§9.6).
///
/// Fitting here PROVES the coordinate fits before scheduling exists. A coordinate
/// that fits the lower bound but not this one is inconclusive at Task 3 and is
/// decided by Task 8's real encoder.
pub const fn upper_bound_program_words(
    unary_terms: usize,
    binary_terms: usize,
    reusable_projections: usize,
) -> usize {
    unary_terms * (1 + WORDS_PER_INPUT_MAX)
        + binary_terms * (1 + 2 * WORDS_PER_INPUT_MAX)
        + reusable_projections * MOVE_WORDS
}

pub const fn program_bytes(words: usize) -> usize {
    words * 2
}

// ── Measured corpus maxima ───────────────────────────────────────────────────

/// EXACT maxima over the MANDATORY production corpus: the 12 committed
/// `*_layout_gkr.json` layouts, all 57 backward-bearing layers, both regimes
/// (114 coordinates), including the eight layers the old static flat audit labels
/// unsupported.
///
/// Every format/ABI decision in Tasks 4-9 is sized from this module.
///
/// Pinned by `bwd_coeff_committed_layout_census` in
/// `tests/bwd_coeff_corpus.rs` and re-pinned over the complete corpus by
/// `bwd_coeff_complete_corpus_census` in the GPU crate.
pub mod in_scope {
    use super::*;

    /// `(circuit, layer, regime)` coordinates censused.
    pub const COORDINATES: usize = 114;
    /// Backward-bearing layers.
    pub const LAYERS: usize = 57;
    /// Committed layouts.
    pub const CIRCUITS: usize = 12;

    /// Largest per-layer banked coefficient-recipe count
    /// (`blake2_with_extended_control` L0 `Ext`).
    pub const MAX_COEFFICIENT_RECIPES: usize = 1138;
    /// Largest per-layer source-table size
    /// (`blake2_with_extended_control` L0 `R0`).
    pub const MAX_SOURCES: usize = 1062;
    /// Largest per-layer distinct-projection count
    /// (`blake2_with_extended_control` L0 `Ext`). Well below `2 * MAX_SOURCES`:
    /// most sources are used in only one of their two projections.
    pub const MAX_PROJECTIONS: usize = 1731;
    /// Largest per-layer term count (`blake2_with_extended_control` L0 `Ext`).
    pub const MAX_TERMS: usize = 1791;
    /// Largest monomial count a single pre-distribution product expanded to
    /// (design §5.4's distribution growth): `inits_and_teardowns` L0 in BOTH
    /// regimes and `unified_reduced_machine` L0 `Ext`.
    ///
    /// The two-monster `xprod_expanded = 0` result is indeed not a corpus-wide
    /// proof — §5.4 says so and this is the number that shows it. Atoms stay
    /// small ([`MAX_FRAGMENT_ATOMS`] `== 2`) but they are SUMS, so one
    /// two-atom product distributes into 46 normalized source-pair terms.
    pub const MAX_EXPANSION_FACTOR: usize = 46;
    /// Largest `atoms.len()` of a live fragment. Degree two is the relation
    /// bound (§5.4), and the corpus saturates it.
    pub const MAX_FRAGMENT_ATOMS: usize = 2;
    /// Largest per-layer source-window count under the fixed 128-column
    /// final-binding rule (`blake2_with_extended_control` L0 `R0`).
    ///
    /// This is the OBSERVED value, deliberately NOT rounded up to
    /// [`MAX_SOURCE_WINDOWS`]: a constant larger than the measurement would hide
    /// the drift it exists to catch.
    pub const MAX_SOURCE_WINDOWS_USED: usize = 17;
    /// Largest schedule-independent MINIMUM program stream, in bytes
    /// (`bigint_with_extended_control` L0 `Ext`). Program stream only.
    pub const MAX_LOWER_BOUND_PROGRAM_BYTES: usize = 9_780;
    /// Largest conservative MAXIMUM program stream, in bytes
    /// (`blake2_with_extended_control` L0 `Ext`). Program stream only; the
    /// remaining descriptor metadata is frozen in Tasks 8-9.
    pub const MAX_UPPER_BOUND_PROGRAM_BYTES: usize = 19_396;
    /// Standalone continuation product terms. ZERO — this is what keeps
    /// continuation opcodes 3..7 invalid.
    pub const MAX_CONTINUATION_STANDALONE_PRODUCTS: usize = 0;

    /// Every in-scope coordinate's UPPER bound fits, so no coordinate is left
    /// inconclusive for Task 8's real encoder — at the program-stream level.
    pub const INCONCLUSIVE_COORDINATES: usize = 0;
    /// Bytes the worst coordinate's conservative maximum leaves for the rest of
    /// the by-value descriptor metadata.
    pub const MIN_DESCRIPTOR_HEADROOM_BYTES: usize =
        KERNEL_ARGUMENT_CEILING_BYTES - MAX_UPPER_BOUND_PROGRAM_BYTES;

    // Every measured maximum must sit inside its encoding limit. These are
    // SEPARATE assertions on purpose: the measurement and the limit are different
    // kinds of fact and conflating them is how a descriptor ends up sized for a
    // number nobody measured.
    const _: () = assert!(
        MAX_COEFFICIENT_RECIPES + CoefficientRecipeId::RESERVED as usize
            <= MAX_COEFFICIENT_ENCODINGS
    );
    const _: () = assert!(MAX_SOURCE_WINDOWS_USED <= MAX_SOURCE_WINDOWS);
    const _: () = assert!(MAX_LOWER_BOUND_PROGRAM_BYTES <= KERNEL_ARGUMENT_CEILING_BYTES);
    const _: () = assert!(MAX_UPPER_BOUND_PROGRAM_BYTES <= KERNEL_ARGUMENT_CEILING_BYTES);
}

/// The same census INCLUDING the conditional `blake2_with_compression` attempt
/// (§3.1). DIAGNOSTIC ONLY — never size a format from these.
///
/// `get_blake2_with_compression_circuit_setup` compiles
/// `define_blake2_with_extended_control_delegation_circuit` at
/// `DOMAIN_SIZE_LOG2 = 20` with caches on, which is byte-for-byte the call that
/// generated the committed `blake2_with_extended_control_layout_gkr.json`. The
/// conditional circuit is therefore the SAME GKR circuit as an already-mandatory
/// one, and every maximum below equals its [`in_scope`] counterpart. The two sets
/// stay separate anyway: they are separate claims, and if the delegation wrapper
/// ever diverges from the committed layout this module is where it shows up.
pub mod with_conditional_blake2 {
    use super::*;

    /// 114 in-scope coordinates plus the conditional circuit's 16.
    pub const COORDINATES: usize = 130;
    /// 57 in-scope layers plus the conditional circuit's 8.
    pub const LAYERS: usize = 65;
    pub const CIRCUITS: usize = 13;

    pub const MAX_COEFFICIENT_RECIPES: usize = in_scope::MAX_COEFFICIENT_RECIPES;
    pub const MAX_SOURCES: usize = in_scope::MAX_SOURCES;
    pub const MAX_PROJECTIONS: usize = in_scope::MAX_PROJECTIONS;
    pub const MAX_TERMS: usize = in_scope::MAX_TERMS;
    pub const MAX_EXPANSION_FACTOR: usize = in_scope::MAX_EXPANSION_FACTOR;
    pub const MAX_FRAGMENT_ATOMS: usize = in_scope::MAX_FRAGMENT_ATOMS;
    pub const MAX_SOURCE_WINDOWS_USED: usize = in_scope::MAX_SOURCE_WINDOWS_USED;
    pub const MAX_LOWER_BOUND_PROGRAM_BYTES: usize = in_scope::MAX_LOWER_BOUND_PROGRAM_BYTES;
    pub const MAX_UPPER_BOUND_PROGRAM_BYTES: usize = in_scope::MAX_UPPER_BOUND_PROGRAM_BYTES;
    pub const MAX_CONTINUATION_STANDALONE_PRODUCTS: usize = 0;
    pub const INCONCLUSIVE_COORDINATES: usize = 0;

    /// Coordinates of the conditional circuit that failed a hard format bound.
    /// ZERO: `blake2_with_compression` compiles to the same GKR circuit as an
    /// already-mandatory one, so §3.1's whole-circuit exclusion is not triggered
    /// and the circuit stays conditionally retained pending Task 8's real-encoding
    /// decision.
    pub const CONDITIONAL_HARD_BOUND_FAILURES: usize = 0;

    const _: () = assert!(
        MAX_COEFFICIENT_RECIPES + CoefficientRecipeId::RESERVED as usize
            <= MAX_COEFFICIENT_ENCODINGS
    );
    const _: () = assert!(MAX_SOURCE_WINDOWS_USED <= MAX_SOURCE_WINDOWS);
    const _: () = assert!(MAX_LOWER_BOUND_PROGRAM_BYTES <= KERNEL_ARGUMENT_CEILING_BYTES);
    const _: () = assert!(MAX_UPPER_BOUND_PROGRAM_BYTES <= KERNEL_ARGUMENT_CEILING_BYTES);
}
