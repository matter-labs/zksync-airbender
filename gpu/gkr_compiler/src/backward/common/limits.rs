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
//! [`in_scope`] records the mandatory production corpus maxima used by the GPU
//! ABI.
//!
//! One backward production lineage: an overflow of any bound here is a compiler
//! error. There is no extended record, no version field, and no fallback format.

use gkr_eval_ir::FieldKind;

use super::model::{CoeffTerm, CoefficientRecipeId};

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

/// The Ext-regime GROUP HEADER control code (spec §4.4). NOT a term class: the
/// frozen class tables stay term-only, and decoders branch on this value at
/// continuation before category lookup. At R0 the same number is a live term
/// class (`C2ProductBfBf`), which is why decode needs regime context.
pub const LEAN_CONT_GROUP_HEADER_CLASS: u16 = 2;

/// Wire-level cap on one coordinate's immediate table (spec §4.5). The GPU
/// descriptor capacity `BWD_SEG_MAX_IMMEDIATES` mirror-asserts EQUAL to this —
/// the crates never import each other's constant.
pub const LEAN_MAX_IMMEDIATES: usize = 512;

/// `source_window:6` of the input word (§9.4).
pub const MAX_SOURCE_WINDOWS: usize = 64;
/// `column:7` of the input word: a window covers at most this many contiguous
/// referenced columns (§9.4).
pub const SOURCE_WINDOW_COLUMNS: usize = 128;

/// The by-value kernel-argument cap the whole encoded program plus its descriptor
/// metadata must fit (§9.1). There is no device-pointer program representation.
pub const KERNEL_ARGUMENT_CEILING_BYTES: usize = 32_764;

/// Alignment of the by-value launch descriptor, in bytes.
///
/// Sixteen, because an E4 value is four `BabyBear` limbs and the descriptor's
/// vector members are `16`-byte quantities; a `__grid_constant__` aggregate
/// therefore aligns to 16 and its trailing program array is padded to a multiple
/// of it. Task 9 mirrors this into CUDA — the constant lives here only so Task 8
/// can round the MEASURED program maximum up by exactly the ABI's requirement and
/// no further.
pub const DESCRIPTOR_ALIGNMENT_BYTES: usize = 16;
/// [`DESCRIPTOR_ALIGNMENT_BYTES`] in u16 program words: eight.
pub const DESCRIPTOR_ALIGNMENT_WORDS: usize = DESCRIPTOR_ALIGNMENT_BYTES / 2;
const _: () = assert!(DESCRIPTOR_ALIGNMENT_WORDS == 8);

/// Round a measured word count up to the descriptor's ABI alignment — the ONLY
/// rounding Task 8 applies to a measurement.
pub const fn align_program_words(words: usize) -> usize {
    words.div_ceil(DESCRIPTOR_ALIGNMENT_WORDS) * DESCRIPTOR_ALIGNMENT_WORDS
}

/// First target depth whose first physical access PUBLISHES (§10.2:
/// "target depth < 3: do not publish; target depth >= 3: publish on first
/// physical access").
///
/// One tunable constant, NOT a scheduling decision and NOT a search variable. It
/// is also the bound on the segmented executor's inline fold depth: at and past
/// it the JAOT prologue materializes instead. Mirrored into CUDA as
/// `BWD_COEFF_PUBLISH_TARGET_DEPTH`.
pub const PUBLISH_TARGET_DEPTH: u8 = 3;

const _: () = assert!(PUBLISH_TARGET_DEPTH == 3);

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
    /// Every category, for the exhaustive opcode-table checks below. Adding a
    /// variant without adding it here is a compile error
    /// ([`all_categories_are_listed`]).
    pub const ALL: [TermCategory; 8] = [
        TermCategory::C0LinearBf,
        TermCategory::C0LinearE4,
        TermCategory::C2ProductBfBf,
        TermCategory::C2ProductBfE4,
        TermCategory::C2ProductE4E4,
        TermCategory::DualProductE4,
        TermCategory::MoveBf,
        TermCategory::MoveE4,
    ];

    /// Const-comparable identity. Derived `PartialEq` is not `const`, and the
    /// opcode-table checks run at compile time.
    pub const fn tag(self) -> u8 {
        match self {
            TermCategory::C0LinearBf => 0,
            TermCategory::C0LinearE4 => 1,
            TermCategory::C2ProductBfBf => 2,
            TermCategory::C2ProductBfE4 => 3,
            TermCategory::C2ProductE4E4 => 4,
            TermCategory::DualProductE4 => 5,
            TermCategory::MoveBf => 6,
            TermCategory::MoveE4 => 7,
        }
    }

    pub fn is_legal_in(self, r0: bool) -> bool {
        if r0 {
            r0_opcode(self).is_some()
        } else {
            continuation_opcode(self).is_some()
        }
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

/// The category of one lowered term, exactly as
/// [`live_term_categories`](super::stats::live_term_categories) classifies it.
///
/// The classification is a pure function of the semantic term, so it lives with
/// [`TermCategory`] rather than with any one codec.
pub fn term_category(term: &CoeffTerm) -> TermCategory {
    match term {
        CoeffTerm::C0Linear {
            field: FieldKind::Base,
            ..
        } => TermCategory::C0LinearBf,
        CoeffTerm::C0Linear {
            field: FieldKind::Ext,
            ..
        } => TermCategory::C0LinearE4,
        CoeffTerm::C2Product {
            lhs_field,
            rhs_field,
            ..
        } => match (lhs_field, rhs_field) {
            (FieldKind::Base, FieldKind::Base) => TermCategory::C2ProductBfBf,
            (FieldKind::Ext, FieldKind::Ext) => TermCategory::C2ProductE4E4,
            _ => TermCategory::C2ProductBfE4,
        },
        CoeffTerm::DualProduct { .. } => TermCategory::DualProductE4,
    }
}

/// Whether the category is one of the two standalone cell-file moves (§9.6).
///
/// No live codec EMITS a move — the lean wire has no move form at all — but the
/// two `Move` rows are still part of the FROZEN opcode tables, and the lean
/// tables are defined as those tables with exactly the move rows deleted
/// (`lean::is_densified_frozen_table`). That definition needs this predicate.
pub const fn is_move(category: TermCategory) -> bool {
    matches!(category, TermCategory::MoveBf | TermCategory::MoveE4)
}

/// Source operands the category carries — `0` for a move, whose two words are
/// bare lanes rather than source records.
pub const fn category_arity(category: TermCategory) -> usize {
    match category {
        TermCategory::C0LinearBf | TermCategory::C0LinearE4 => 1,
        TermCategory::C2ProductBfBf
        | TermCategory::C2ProductBfE4
        | TermCategory::C2ProductE4E4
        | TermCategory::DualProductE4 => 2,
        TermCategory::MoveBf | TermCategory::MoveE4 => 0,
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
/// Opcodes 3..7 stay invalid because continuation lowering emits only
/// `C0Linear`, native `DualProduct`, and moves.
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

// ── The opcode numbers, pinned as data ───────────────────────────────────────
//
// The wire ABI is these NUMBERS. Task 9 emits CUDA static assertions against
// them, so a silent Rust-side renumber — reordering a match arm in
// `r0_opcode`/`continuation_opcode` — would become a Rust<->CUDA disagreement
// discovered on the GPU. The tables below are therefore the authority, and the
// compile-time checks that follow make the two encoder functions AGREE with them
// in both directions: every table row must be what the function returns, and
// every category the function encodes must appear in the table.

/// FROZEN R0 opcode assignment, `(opcode, category)`, in opcode order.
pub const R0_OPCODE_TABLE: &[(u16, TermCategory)] = &[
    (0, TermCategory::C0LinearBf),
    (1, TermCategory::C0LinearE4),
    (2, TermCategory::C2ProductBfBf),
    (3, TermCategory::C2ProductBfE4),
    (4, TermCategory::C2ProductE4E4),
    (5, TermCategory::MoveBf),
    (6, TermCategory::MoveE4),
    // 7 is deliberately invalid: no uncensused category is pre-allocated.
];

/// FROZEN continuation opcode assignment, `(opcode, category)`, in opcode order.
/// 3..7 are deliberately invalid — see [`continuation_opcode`].
pub const CONTINUATION_OPCODE_TABLE: &[(u16, TermCategory)] = &[
    (0, TermCategory::C0LinearE4),
    (1, TermCategory::DualProductE4),
    (2, TermCategory::MoveE4),
];

/// Live R0 opcodes: seven, exactly as §9.2 predicted. DERIVED from
/// [`R0_OPCODE_TABLE`], never hand-written.
pub const R0_LIVE_OPCODES: usize = R0_OPCODE_TABLE.len();
/// Live continuation opcodes: three (§9.2 allows "at most five, including
/// standalone split forms only if their census is nonzero" — the census is zero).
/// DERIVED from [`CONTINUATION_OPCODE_TABLE`].
pub const CONTINUATION_LIVE_OPCODES: usize = CONTINUATION_OPCODE_TABLE.len();

const _: () = assert!(R0_LIVE_OPCODES == 7);
const _: () = assert!(CONTINUATION_LIVE_OPCODES == 3);
const _: () = assert!(R0_LIVE_OPCODES <= MAX_OPCODES_PER_REGIME);
const _: () = assert!(CONTINUATION_LIVE_OPCODES <= MAX_OPCODES_PER_REGIME);

/// Table rows are dense from zero, in order, and inside the three opcode bits.
const fn table_is_canonical(table: &[(u16, TermCategory)]) -> bool {
    let mut i = 0;
    while i < table.len() {
        let (opcode, _) = table[i];
        if opcode as usize != i || opcode as usize >= MAX_OPCODES_PER_REGIME {
            return false;
        }
        i += 1;
    }
    true
}

/// The encoder function returns exactly the table's opcode for every table row.
const fn table_matches_encoder(table: &[(u16, TermCategory)], r0: bool) -> bool {
    let mut i = 0;
    while i < table.len() {
        let (opcode, category) = table[i];
        let encoded = if r0 {
            r0_opcode(category)
        } else {
            continuation_opcode(category)
        };
        let Some(encoded) = encoded else { return false };
        if encoded != opcode {
            return false;
        }
        i += 1;
    }
    true
}

const fn table_contains(table: &[(u16, TermCategory)], category: TermCategory) -> bool {
    let mut i = 0;
    while i < table.len() {
        let (_, listed) = table[i];
        if listed.tag() == category.tag() {
            return true;
        }
        i += 1;
    }
    false
}

/// Nothing the encoder function encodes is missing from the table — so adding an
/// arm to `r0_opcode`/`continuation_opcode` without pinning its number fails to
/// compile instead of silently entering the wire ABI.
const fn encoder_matches_table(table: &[(u16, TermCategory)], r0: bool) -> bool {
    let mut i = 0;
    while i < TermCategory::ALL.len() {
        let category = TermCategory::ALL[i];
        let encoded = if r0 {
            r0_opcode(category)
        } else {
            continuation_opcode(category)
        };
        if encoded.is_some() && !table_contains(table, category) {
            return false;
        }
        i += 1;
    }
    true
}

/// `TermCategory::ALL` really is every variant: the tags are `0..8`, distinct.
const fn all_categories_are_listed() -> bool {
    let mut seen = [false; 8];
    let mut i = 0;
    while i < TermCategory::ALL.len() {
        let tag = TermCategory::ALL[i].tag() as usize;
        if tag >= seen.len() || seen[tag] {
            return false;
        }
        seen[tag] = true;
        i += 1;
    }
    true
}

const _: () = assert!(all_categories_are_listed());
const _: () = assert!(table_is_canonical(R0_OPCODE_TABLE));
const _: () = assert!(table_is_canonical(CONTINUATION_OPCODE_TABLE));
const _: () = assert!(table_matches_encoder(R0_OPCODE_TABLE, true));
const _: () = assert!(table_matches_encoder(CONTINUATION_OPCODE_TABLE, false));
const _: () = assert!(encoder_matches_table(R0_OPCODE_TABLE, true));
const _: () = assert!(encoder_matches_table(CONTINUATION_OPCODE_TABLE, false));

// The individual numbers, spelled out, because these seven plus three values ARE
// the ABI Task 9 mirrors into CUDA. Redundant with the table by design: an editor
// changing one of them has to change two places that disagree loudly.
const _: () = assert!(matches!(r0_opcode(TermCategory::C0LinearBf), Some(0)));
const _: () = assert!(matches!(r0_opcode(TermCategory::C0LinearE4), Some(1)));
const _: () = assert!(matches!(r0_opcode(TermCategory::C2ProductBfBf), Some(2)));
const _: () = assert!(matches!(r0_opcode(TermCategory::C2ProductBfE4), Some(3)));
const _: () = assert!(matches!(r0_opcode(TermCategory::C2ProductE4E4), Some(4)));
const _: () = assert!(matches!(r0_opcode(TermCategory::MoveBf), Some(5)));
const _: () = assert!(matches!(r0_opcode(TermCategory::MoveE4), Some(6)));
const _: () = assert!(r0_opcode(TermCategory::DualProductE4).is_none());
const _: () = assert!(matches!(
    continuation_opcode(TermCategory::C0LinearE4),
    Some(0)
));
const _: () = assert!(matches!(
    continuation_opcode(TermCategory::DualProductE4),
    Some(1)
));
const _: () = assert!(matches!(continuation_opcode(TermCategory::MoveE4), Some(2)));
const _: () = assert!(continuation_opcode(TermCategory::C0LinearBf).is_none());
const _: () = assert!(continuation_opcode(TermCategory::C2ProductBfBf).is_none());
const _: () = assert!(continuation_opcode(TermCategory::C2ProductBfE4).is_none());
const _: () = assert!(continuation_opcode(TermCategory::C2ProductE4E4).is_none());
const _: () = assert!(continuation_opcode(TermCategory::MoveBf).is_none());

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
    /// Largest per-layer lean RECORD count: terms PLUS group headers (spec §4.4,
    /// §4.5). One header record per group, so a coordinate's record count is
    /// `terms + groups` and the program is `LEAN_WORDS_PER_TERM * records` words.
    ///
    /// A COMPILE-TIME literal standing in for a runtime measurement, which is what
    /// [`LEAN_MAX_REALIZED_PROGRAM_WORDS`]'s `const` identity needs — a `const _`
    /// assert cannot call the grouping transform.
    /// `bwd_lean_program_word_census_sizes_the_descriptor` in
    /// `tests/bwd_coeff_lean_artifact.rs` is the measurement behind it: it runs
    /// `group_coeff_layer -> order_atoms -> encode_program_atoms` over every corpus
    /// coordinate and asserts this literal EXACTLY. Moving it without re-running
    /// that gate is the one thing this constant is designed to make impossible.
    ///
    /// Strictly above [`MAX_TERMS`] because the worst coordinate groups: it is the
    /// same `blake2_with_extended_control` L0 `Ext` coordinate, whose 1,791 terms
    /// come with 365 group headers on top.
    pub const MAX_RECORDS: usize = 2156;
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
    // Every measured maximum must sit inside its encoding limit. These are
    // SEPARATE assertions on purpose: the measurement and the limit are different
    // kinds of fact and conflating them is how a descriptor ends up sized for a
    // number nobody measured.
    const _: () = assert!(
        MAX_COEFFICIENT_RECIPES + CoefficientRecipeId::RESERVED as usize
            <= MAX_COEFFICIENT_ENCODINGS
    );
    const _: () = assert!(MAX_SOURCE_WINDOWS_USED <= MAX_SOURCE_WINDOWS);
    // Every record is a term or a header, and the worst coordinate really does
    // group — a corpus that grouped nothing would leave these two equal.
    const _: () = assert!(MAX_RECORDS > MAX_TERMS);
}

// ── The segmented lean VM's measurements (lean design §4) ────────────────────
//
// The lean wire is FIXED at `LEAN_WORDS_PER_TERM` words per RECORD, so a lean
// program's length is `4 * records` and there is no bound/measurement gap to close:
// the record population IS the program length. These three numbers therefore replace
// the whole `lower_bound_program_words` / `upper_bound_program_words` /
// `in_scope::MAX_REALIZED_PROGRAM_WORDS` triple the cell-era codec needed, and
// nothing here is a schedule measurement — there is no schedule.

/// The largest lean program over the whole in-scope corpus, in u16 words.
///
/// A MEASUREMENT, pinned by `bwd_lean_program_word_census_sizes_the_descriptor` in
/// `tests/bwd_coeff_lean_artifact.rs`, and by construction it is
/// `LEAN_WORDS_PER_TERM * in_scope::MAX_RECORDS`: the fixed-width wire makes the
/// longest program the one with the most RECORDS
/// (`blake2_with_extended_control` L0 `Ext`). The identity is asserted below rather
/// than assumed, so a codec that stopped being fixed-width would trip here instead
/// of silently under-sizing the descriptor.
///
/// **Records, not terms** (spec §4.4): grouping emits one header record per group
/// on top of its member terms, so this is `4 * (terms + headers)` and strictly
/// larger than the `4 * MAX_TERMS` the pre-grouping wire measured. The constant is
/// stated over [`in_scope::MAX_RECORDS`] precisely so the const identity keeps
/// working across that change.
pub const LEAN_MAX_REALIZED_PROGRAM_WORDS: usize = 8_624;

/// The segmented descriptor's program array length, in u16 words:
/// [`LEAN_MAX_REALIZED_PROGRAM_WORDS`] rounded up to the descriptor's 16-byte ABI
/// alignment and NOT ONE WORD FURTHER.
///
/// The remaining `KERNEL_ARGUMENT_CEILING_BYTES - LEAN_DESCRIPTOR_PROGRAM_BYTES` is
/// deliberately not claimed as headroom: a by-value array of this length rides in
/// every launch descriptor, so an unearned word is unearned kernel-argument budget
/// in every launch, forever. If a future circuit needs more, this constant is
/// re-measured and moved — a deliberate act with a test behind it, which
/// speculative headroom would have hidden.
pub const LEAN_DESCRIPTOR_PROGRAM_WORDS: usize = 8_624;
/// [`LEAN_DESCRIPTOR_PROGRAM_WORDS`] in bytes: 16-byte aligned by construction.
pub const LEAN_DESCRIPTOR_PROGRAM_BYTES: usize = 17_248;

// The measurement is the fixed-width identity over RECORDS, the array is the
// measurement rounded up by strictly less than one alignment quantum, and the whole
// array fits the by-value cap with room for the rest of the descriptor.
const _: () = assert!(
    LEAN_MAX_REALIZED_PROGRAM_WORDS == super::lean::LEAN_WORDS_PER_TERM * in_scope::MAX_RECORDS
);
const _: () =
    assert!(LEAN_DESCRIPTOR_PROGRAM_WORDS == align_program_words(LEAN_MAX_REALIZED_PROGRAM_WORDS));
const _: () =
    assert!(LEAN_DESCRIPTOR_PROGRAM_BYTES == program_bytes(LEAN_DESCRIPTOR_PROGRAM_WORDS));
const _: () = assert!(
    LEAN_DESCRIPTOR_PROGRAM_WORDS - LEAN_MAX_REALIZED_PROGRAM_WORDS < DESCRIPTOR_ALIGNMENT_WORDS
);
const _: () = assert!(LEAN_DESCRIPTOR_PROGRAM_BYTES < KERNEL_ARGUMENT_CEILING_BYTES);
