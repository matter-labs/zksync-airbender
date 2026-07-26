//! The canonical u16 wire format (design §9), its validator (§12.1), and the
//! disassembler.
//!
//! This module is the **ABI**. Every shift, mask and numeric code below is
//! mirrored into CUDA static assertions, so nothing here may be changed without
//! changing the GPU side in the same commit. The opcode NUMBERS are not defined
//! here — they are frozen in [`super::limits`] and consumed through
//! [`R0_OPCODE_TABLE`] / [`CONTINUATION_OPCODE_TABLE`].
//!
//! # The word stream (§9.1)
//!
//! ```text
//! u16 header
//! u16 input_0
//! [u16 input_0_extension]
//! [u16 input_1]
//! [u16 input_1_extension]
//! ```
//!
//! The opcode fixes the number of input records; each input's MODE fixes whether
//! its single extension word follows. There is no end opcode: the descriptor
//! supplies `num_words`, which is `EncodedProgram::words.len()`.
//!
//! # Bit layouts
//!
//! ```text
//! header       [ opcode:3 | coefficient:13 ]                bits 13..15 / 0..12
//! input word   [ column:7 | window:6 | first_access:1 | mode:2 ]
//!                                                          bits 9..15 / 3..8 / 2 / 0..1
//! cell single  [ 0:8 | lane:6 | mode:2 ]                    bits 8..15 / 2..7 / 0..1
//! cell pair    [ delta_lane:6 | 0:2 | endpoint0_lane:6 | mode:2 ]
//!                                                          bits 10..15 / 8..9 / 2..7 / 0..1
//! plan word    [ delta_lane:6 | delta_act:2 | e0_lane:6 | e0_act:2 ]
//!                                                          bits 10..15 / 8..9 / 2..7 / 0..1
//! lane word    [ 0:10 | lane:6 ]                            bits 6..15 / 0..5
//! ```
//!
//! The `cell pair` and `plan` words deliberately share one lane geometry
//! ([`CELL_ENDPOINT0_LANE_SHIFT`] `==` [`PLAN_ENDPOINT0_LANE_SHIFT`] and
//! [`CELL_DELTA_LANE_SHIFT`] `==` [`PLAN_DELTA_LANE_SHIFT`], asserted below), so
//! a decoder needs ONE pair-of-lanes extractor rather than two.
//!
//! The `lane word` form is used in all three places a bare lane is encoded: a
//! `FillSource` destination and both move operands (§9.6: "six-bit BF lane
//! indices, remaining bits zero").
//!
//! ## Two properties a bit table alone does not convey
//!
//! Both produce a Rust↔CUDA disagreement that only shows up on the GPU, so they
//! are stated here as constraints rather than left to be inferred.
//!
//! **1. Bit 2 is a mode-discriminated overlay.** The same physical bit means four
//! different things depending on which of the six word forms it sits in, and the
//! form is fixed by the opcode plus (for extension words) the preceding input
//! word's mode — never by the word's own content:
//!
//! ```text
//! source-bearing input word   bit 2 = first_access          (window at bits 3..8)
//! cell word (either form)     bit 2 = Endpoint0 lane bit 0  (lane at bits 2..7)
//! plan word                   bit 2 = Endpoint0 lane bit 0  (lane at bits 2..7)
//! bare lane word              bit 2 = lane bit 2            (lane at bits 0..5)
//! ```
//!
//! A decoder that extracts `first_access` before dispatching on the mode reads a
//! lane bit as a materialization flag.
//!
//! **2. The packed pair `Cell` form is opcode-scoped, not payload-detectable.**
//! `DualProductE4` — and only `DualProductE4` — reads bits 10..15 of a `Cell` word
//! as the `Delta` lane. Under every other opcode those bits are reserved and MUST
//! be zero, so `Cell` lane 0 with a nonzero high payload is a rejected program,
//! not a pair. There is no tag in the word distinguishing the two forms; the
//! opcode is the only discriminator.
//!
//! # Operand width is a function of `(opcode, position)`
//!
//! A resident [`CellRead`] carries no window, so its width cannot come from the
//! source-window descriptor; and even a source-bearing operand's width is not the
//! window's backing field (a continuation program folds a base matrix to `Ext`).
//! The width therefore comes from the opcode alone — see [`operand_width`]. The
//! one consequence for the encoder is that `C2ProductBF_E4` covers BOTH mixed
//! field orders, so a mixed product's BF factor is emitted FIRST
//! ([`program_records`]). Multiplication is commutative and the two slots of a
//! two-slot `C2Product` are always distinct sources, so that is a canonical
//! spelling of a commutative operation, not a reordering of the program.
//!
//! # Squared terms
//!
//! [`term_slots`] deduplicates a repeated operand: `C2Product { lhs: d, rhs: d }`
//! and `DualProduct { lhs: s, rhs: s }` have ONE slot and therefore one
//! [`ValueUse`]. §9.1 nevertheless makes arity a function of the opcode, and the
//! frozen opcode tables have no squared category. The canonical encoding is
//! therefore:
//!
//! > A binary record whose two input records are **byte-identical** denotes a
//! > squared term: the two operand positions share ONE physical resolution, which
//! > is performed exactly once.
//!
//! That discriminator is sound and complete: two DISTINCT slots of one term always
//! consume distinct sources (both operands of a `C2Product` are `Delta`
//! projections, so `lhs == rhs` iff the sources are equal), distinct sources have
//! distinct `(window, column)` coordinates, and a resident lane holds one value at
//! a time — so distinct slots can never encode to the same word. Re-executing the
//! second copy is NOT permitted (a plan may legitimately read a lane and then
//! overwrite it), which is why the rule fixes the resolution count rather than
//! leaving it to the decoder.
//!
//! # What is deliberately NOT here
//!
//! The launch descriptor and its size census (Task 8), the budget sweep, and any
//! peephole. `c_init` is descriptor metadata (§9.3) and rides on
//! [`EncodedProgram`] only so the encoded interpreter can start `acc_c0` where the
//! semantic one does.

use std::collections::HashMap;
use std::fmt::Write as _;

use cs::gkr_compiler::dag_ir::{BwdRegime, FieldKind};

use super::bind::CoeffSourceBinding;
use super::limits::{
    CONTINUATION_OPCODE_TABLE, HEADER_COEFFICIENT_BITS, HEADER_OPCODE_BITS,
    KERNEL_ARGUMENT_CEILING_BYTES, MAX_COEFFICIENT_ENCODINGS, MAX_SOURCE_WINDOWS,
    R0_OPCODE_TABLE, SOURCE_WINDOW_COLUMNS, TermCategory, continuation_opcode, r0_opcode,
};
use super::model::{
    CoeffLayer, CoeffTerm, CoefficientRecipeId, NormalizedCoefficientRecipe, ProjectionId, SourceId,
};
use super::place::{CellRead, CoeffPlacement, PlanAction, ScheduledInstr, ValueUse};
use super::schedule::{CellBudget, LANES_PER_CELL, ScheduleError, SlotKind, ValueWidth, term_slots};

// ── Frozen bit geometry (§9.2, §9.4, §9.5, §9.6) ─────────────────────────────

/// `header` bits 0..12 (§9.2).
pub const HEADER_COEFFICIENT_SHIFT: u32 = 0;
/// Mask of [`HEADER_COEFFICIENT_SHIFT`], pre-shift.
pub const HEADER_COEFFICIENT_MASK: u16 = (1 << HEADER_COEFFICIENT_BITS) - 1;
/// `header` bits 13..15 (§9.2).
pub const HEADER_OPCODE_SHIFT: u32 = HEADER_COEFFICIENT_BITS;
/// Mask of [`HEADER_OPCODE_SHIFT`], pre-shift.
pub const HEADER_OPCODE_MASK: u16 = (1 << HEADER_OPCODE_BITS) - 1;

/// Input word bits 0..1: the mode (§9.4, "The low two bits select the input
/// mode").
pub const INPUT_MODE_SHIFT: u32 = 0;
/// Mask of [`INPUT_MODE_SHIFT`], pre-shift.
pub const INPUT_MODE_MASK: u16 = 0x3;
/// Input word bit 2: `first_access` (§9.4, §10.3).
pub const INPUT_FIRST_ACCESS_SHIFT: u32 = 2;
/// Input word bits 3..8: the source window (§9.4).
pub const INPUT_WINDOW_SHIFT: u32 = 3;
/// Mask of [`INPUT_WINDOW_SHIFT`], pre-shift.
pub const INPUT_WINDOW_MASK: u16 = 0x3f;
/// Input word bits 9..15: the window-relative column (§9.4).
pub const INPUT_COLUMN_SHIFT: u32 = 9;
/// Mask of [`INPUT_COLUMN_SHIFT`], pre-shift.
pub const INPUT_COLUMN_MASK: u16 = 0x7f;

/// Every physical index in the format is a six-bit BF lane (§9.4, §9.6).
pub const LANE_BITS: u32 = 6;
/// Mask of a six-bit lane index, pre-shift.
pub const LANE_MASK: u16 = (1 << LANE_BITS) - 1;

/// `Cell` payload: the single / `Endpoint0` lane, bits 2..7 (§9.4).
pub const CELL_ENDPOINT0_LANE_SHIFT: u32 = 2;
/// `Cell` payload: the packed native-dual `Delta` lane, bits 10..15 (§9.5).
pub const CELL_DELTA_LANE_SHIFT: u32 = 10;

/// Plan word bits 0..1: the `Endpoint0` action (§9.5).
pub const PLAN_ENDPOINT0_ACTION_SHIFT: u32 = 0;
/// Plan word bits 2..7: the `Endpoint0` physical lane (§9.5).
pub const PLAN_ENDPOINT0_LANE_SHIFT: u32 = 2;
/// Plan word bits 8..9: the `Delta` action (§9.5).
pub const PLAN_DELTA_ACTION_SHIFT: u32 = 8;
/// Plan word bits 10..15: the `Delta` physical lane (§9.5).
pub const PLAN_DELTA_LANE_SHIFT: u32 = 10;
/// Mask of a plan action, pre-shift.
pub const PLAN_ACTION_MASK: u16 = 0x3;

/// A bare lane word (`FillSource` destination, both move operands): bits 0..5.
pub const LANE_WORD_SHIFT: u32 = 0;

// The pair-carrying words share ONE lane geometry, on purpose.
const _: () = assert!(CELL_ENDPOINT0_LANE_SHIFT == PLAN_ENDPOINT0_LANE_SHIFT);
const _: () = assert!(CELL_DELTA_LANE_SHIFT == PLAN_DELTA_LANE_SHIFT);
// The input word is exactly saturated: nothing is spare, which is why the width
// of a resident operand has to come from the opcode.
const _: () = assert!(INPUT_COLUMN_SHIFT + 7 == 16);
const _: () = assert!(SOURCE_WINDOW_COLUMNS == (INPUT_COLUMN_MASK as usize) + 1);
const _: () = assert!(MAX_SOURCE_WINDOWS == (INPUT_WINDOW_MASK as usize) + 1);
// Six lane bits address the largest legal cell file exactly (c16 = 64 BF lanes).
const _: () = assert!((LANE_MASK as u32) + 1 == CellBudget::MAX_CELLS as u32 * LANES_PER_CELL);

// ── Frozen numeric codes ─────────────────────────────────────────────────────

/// Input mode `00` (§9.4): resolve from source, retain nothing.
pub const MODE_DIRECT_SOURCE: u16 = 0;
/// Input mode `01` (§9.4): read resident lane(s), resolve nothing.
pub const MODE_CELL: u16 = 1;
/// Input mode `10` (§9.4): resolve the requested projection and retain it.
pub const MODE_FILL_SOURCE: u16 = 2;
/// Input mode `11` (§9.4): one `Endpoint0`/`Delta` plan (§9.5).
pub const MODE_PLANNED_SOURCE: u16 = 3;

/// Plan action `00` (§9.5).
pub const ACTION_DIRECT: u16 = 0;
/// Plan action `01` (§9.5).
pub const ACTION_USE_RESIDENT: u16 = 1;
/// Plan action `10` (§9.5).
pub const ACTION_FILL: u16 = 2;
/// Plan action `11` (§9.5) — the format's fourth action. A coefficient plan always
/// names both halves of the pair, so a valid program never contains it and
/// [`validate_program`] rejects it ([`CoeffCodecError::PlanActionInvalid`]).
pub const ACTION_INVALID: u16 = 3;

// ── Opcode-derived static properties ─────────────────────────────────────────

/// What the term reads through one operand slot — a function of the opcode alone.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum OperandRole {
    /// A `C0Linear` operand: `Endpoint0` only. Never a plan (§8, §9.5).
    Endpoint0,
    /// A `C2Product` operand: `Delta`, with the co-produced `Endpoint0` available
    /// for retention through a plan.
    Delta,
    /// A native dual factor: both projections, one physical resolution.
    Pair,
}

/// The frozen opcode table of one regime (§9.2).
pub const fn opcode_table(regime: BwdRegime) -> &'static [(u16, TermCategory)] {
    match regime {
        BwdRegime::R0 => R0_OPCODE_TABLE,
        BwdRegime::Ext => CONTINUATION_OPCODE_TABLE,
    }
}

/// The wire opcode of `category` in `regime`, or `None` when the category has no
/// encoding there.
pub fn opcode_of(regime: BwdRegime, category: TermCategory) -> Option<u16> {
    match regime {
        BwdRegime::R0 => r0_opcode(category),
        BwdRegime::Ext => continuation_opcode(category),
    }
}

/// The category a wire opcode names in `regime`, or `None` for a dead opcode.
pub fn category_of(regime: BwdRegime, opcode: u16) -> Option<TermCategory> {
    opcode_table(regime).iter().find(|(o, _)| *o == opcode).map(|(_, c)| *c)
}

/// Whether the opcode is one of the two standalone cell-file moves (§9.6).
pub const fn is_move(category: TermCategory) -> bool {
    matches!(category, TermCategory::MoveBf | TermCategory::MoveE4)
}

/// Input RECORDS the opcode carries (§9.1) — `0` for a move, whose two words are
/// bare lanes rather than input records.
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

/// The role every operand of the opcode plays; `None` for a move.
pub const fn category_role(category: TermCategory) -> Option<OperandRole> {
    match category {
        TermCategory::C0LinearBf | TermCategory::C0LinearE4 => Some(OperandRole::Endpoint0),
        TermCategory::C2ProductBfBf
        | TermCategory::C2ProductBfE4
        | TermCategory::C2ProductE4E4 => Some(OperandRole::Delta),
        TermCategory::DualProductE4 => Some(OperandRole::Pair),
        TermCategory::MoveBf | TermCategory::MoveE4 => None,
    }
}

/// The storage width of operand `position`, or `None` when the opcode has no such
/// operand.
///
/// THE ABI RULE that makes a resident operand decodable: `C2ProductBF_E4` is
/// `(BF, E4)` in that order, and the encoder normalizes a mixed product's slot
/// order to match (module doc).
pub const fn operand_width(category: TermCategory, position: usize) -> Option<ValueWidth> {
    match (category, position) {
        (TermCategory::C0LinearBf, 0) => Some(ValueWidth::Bf),
        (TermCategory::C0LinearE4, 0) => Some(ValueWidth::E4),
        (TermCategory::C2ProductBfBf, 0 | 1) => Some(ValueWidth::Bf),
        (TermCategory::C2ProductBfE4, 0) => Some(ValueWidth::Bf),
        (TermCategory::C2ProductBfE4, 1) => Some(ValueWidth::E4),
        (TermCategory::C2ProductE4E4, 0 | 1) => Some(ValueWidth::E4),
        (TermCategory::DualProductE4, 0 | 1) => Some(ValueWidth::E4),
        _ => None,
    }
}

/// The width a move relocates (§9.6: the opcode, not the operand, carries it).
pub const fn move_width(category: TermCategory) -> Option<ValueWidth> {
    match category {
        TermCategory::MoveBf => Some(ValueWidth::Bf),
        TermCategory::MoveE4 => Some(ValueWidth::E4),
        _ => None,
    }
}

/// The category of one lowered term, exactly as
/// [`live_term_categories`](super::stats::live_term_categories) classifies it.
pub fn term_category(term: &CoeffTerm) -> TermCategory {
    match term {
        CoeffTerm::C0Linear { field: FieldKind::Base, .. } => TermCategory::C0LinearBf,
        CoeffTerm::C0Linear { field: FieldKind::Ext, .. } => TermCategory::C0LinearE4,
        CoeffTerm::C2Product { lhs_field, rhs_field, .. } => match (lhs_field, rhs_field) {
            (FieldKind::Base, FieldKind::Base) => TermCategory::C2ProductBfBf,
            (FieldKind::Ext, FieldKind::Ext) => TermCategory::C2ProductE4E4,
            _ => TermCategory::C2ProductBfE4,
        },
        CoeffTerm::DualProduct { .. } => TermCategory::DualProductE4,
    }
}

// ── Decoded records ──────────────────────────────────────────────────────────

/// One bound source coordinate, as it appears on the wire (§9.4).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SourceCoord {
    pub window: u8,
    /// Offset from the window's `first_column`, `< 128`.
    pub column: u8,
    pub first_access: bool,
}

/// A decoded `Cell` payload (§9.4, §9.5). The `Pair` form is opcode-scoped: only a
/// native dual factor has one.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DecodedCell {
    Single { lane: u16 },
    Pair { endpoint0_lane: u16, delta_lane: u16 },
}

/// One decoded input record — the wire twin of [`ValueUse`], addressing windows
/// and columns instead of [`SourceId`]s.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DecodedUse {
    Direct { coord: SourceCoord },
    Cell(DecodedCell),
    Fill { coord: SourceCoord, dst_lane: u16 },
    Planned { coord: SourceCoord, endpoint0: PlanAction, delta: PlanAction },
}

impl DecodedUse {
    /// The coordinate this record resolves, or `None` for a resident read.
    pub fn coord(&self) -> Option<SourceCoord> {
        match *self {
            DecodedUse::Direct { coord }
            | DecodedUse::Fill { coord, .. }
            | DecodedUse::Planned { coord, .. } => Some(coord),
            DecodedUse::Cell(_) => None,
        }
    }

    /// u16 words this record occupies: the input word plus its single canonical
    /// extension, if any (§9.4, §9.5).
    pub fn words(&self) -> usize {
        match self {
            DecodedUse::Direct { .. } | DecodedUse::Cell(_) => 1,
            DecodedUse::Fill { .. } | DecodedUse::Planned { .. } => 2,
        }
    }
}

/// One decoded instruction.
///
/// `uses` is DEDUPLICATED exactly as [`ScheduledInstr::Term::uses`] is: a squared
/// binary term carries ONE use and is emitted twice (module doc).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DecodedInstr {
    Term { category: TermCategory, coefficient: CoefficientRecipeId, uses: Vec<DecodedUse> },
    Move { category: TermCategory, from_lane: u16, to_lane: u16 },
}

impl DecodedInstr {
    /// `true` when this is a binary term whose two operand positions share one
    /// physical resolution.
    pub fn is_squared(&self) -> bool {
        match self {
            DecodedInstr::Term { category, uses, .. } => {
                category_arity(*category) == 2 && uses.len() == 1
            }
            DecodedInstr::Move { .. } => false,
        }
    }

    /// u16 words this instruction occupies.
    pub fn words(&self) -> usize {
        match self {
            DecodedInstr::Term { category, uses, .. } => {
                let per = uses.iter().map(DecodedUse::words).sum::<usize>();
                let repeats = category_arity(*category) - uses.len();
                // A squared term repeats its single record verbatim.
                1 + per + repeats * uses.first().map_or(0, DecodedUse::words)
            }
            DecodedInstr::Move { .. } => 3,
        }
    }
}

// ── The program ──────────────────────────────────────────────────────────────

/// One encoded backward coefficient program.
///
/// `words` is the §9.1 stream and `words.len()` is the descriptor's `num_words`.
/// `regime` and `budget` are the specialization the stream is only meaningful
/// under, and `c_init` is §9.3's descriptor coefficient index.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EncodedProgram {
    pub regime: BwdRegime,
    pub budget: CellBudget,
    pub c_init: Option<CoefficientRecipeId>,
    pub words: Vec<u16>,
}

impl EncodedProgram {
    pub fn bytes(&self) -> usize {
        self.words.len() * 2
    }

    /// BF lanes the cell file holds: `4 * cells`.
    pub fn lanes(&self) -> u32 {
        self.budget.lanes()
    }
}

// ── Errors ───────────────────────────────────────────────────────────────────

/// The canonical form a non-canonical plan word should have used (§9.5).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ShortestForm {
    /// `{Direct, Direct}` is [`MODE_DIRECT_SOURCE`].
    DirectSource,
    /// A single requested-projection fill is [`MODE_FILL_SOURCE`].
    FillSource,
    /// A resident single projection is [`MODE_CELL`], single form.
    CellSingle,
    /// A fully resident native-dual pair is [`MODE_CELL`], packed form.
    CellPair,
}

/// Everything the codec, its validator and the encoded interpreter can reject.
///
/// Every variant is derivable from the inputs; the module contains no `assert!`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CoeffCodecError {
    // ── encoder side ─────────────────────────────────────────────────────
    /// The category has no opcode in this regime (§9.2's frozen tables).
    CategoryNotEncodable { regime: BwdRegime, category: TermCategory },
    /// The coefficient index does not fit thirteen bits (§9.2).
    CoefficientIndexOverflow { index: u32 },
    /// A placed program and its layer disagree about the regime.
    RegimeMismatch { declared: BwdRegime, found: BwdRegime },
    /// A source-bearing use has no bound coordinate — binding and placement
    /// describe different programs.
    UnboundInput { instr: u32, slot: u8 },
    /// The placed use count is not the term's deduplicated slot count.
    SlotCountMismatch { instr: u32, slots: usize, uses: usize },
    /// A placed [`ValueUse`] does not name the projection or source of the slot it
    /// fills. The wire says only "the role's projection", so a use that retains or
    /// reads a DIFFERENT projection would encode to a record that silently means
    /// something else.
    UseSlotMismatch { instr: u32, slot: u8 },
    /// A slot's source field is not the width the opcode assigns to its emitted
    /// position (§10.1: "BF helpers never carry E4 temporaries").
    ///
    /// DEFENCE IN DEPTH, deliberately unreachable today: [`term_slots`] already
    /// rejects a term whose operand field disagrees with its source
    /// (`ScheduleError::OperandFieldConflict`), and it runs first. Keep it — the
    /// wire's whole width story rests on `(opcode, position)`, so if a future
    /// lowering stops enforcing the agreement this is the guard that notices.
    OperandWidthMismatch { instr: u32, position: usize, expected: ValueWidth },
    /// A `C2ProductBF_E4` record does not have exactly one BF and one E4 slot, so
    /// the mixed normalization has nothing to normalize.
    ///
    /// DEFENCE IN DEPTH, deliberately unreachable today: the category is DERIVED
    /// from the two operand fields ([`term_category`]), and a squared product
    /// cannot be mixed because one source has one field. Keep it for the same
    /// reason as [`CoeffCodecError::OperandWidthMismatch`].
    ///
    /// [`encode_instrs`] also raises it for the converse shape — a mixed category
    /// carrying §9.1's SQUARED form, i.e. one record standing in for both
    /// positions. That would encode cleanly and then ask a resolver to produce one
    /// coordinate at two different widths, and it is the only place that shape is
    /// rejected, so the GPU executor's mixed branch relies on it.
    MixedProductNotMixed { instr: u32 },
    /// An operand's fill writes lanes a LATER operand of the same term reads.
    ///
    /// §12.2's `FillClobbersTermInput` proves this for the placement, but it scopes
    /// "later" to later BINDING slots — and [`program_records`] emits a mixed
    /// product's BF factor first, so a transposed term's fill can execute before
    /// the read it reclaims and escape that clause. The order the hazard is about
    /// is the EMITTED one, so the check belongs here, where the transposition is
    /// introduced.
    FillClobbersLaterOperand { at: usize, lane: u16 },
    /// Two DISTINCT operand slots encode to byte-identical input records, which
    /// the squared discriminator (module doc) would read as one resolution.
    ///
    /// Unreachable from a certified placement — distinct slots consume distinct
    /// sources, distinct sources have distinct coordinates, and one lane holds one
    /// value at a time — so this guards the discriminator against a program no
    /// pass should have produced rather than a legal encoding.
    AmbiguousRepeatedRecord { at: usize },
    /// The program stream alone exceeds the by-value kernel-argument cap (§9.1).
    ProgramExceedsKernelArgumentCap { bytes: usize },
    /// [`term_slots`] rejected the layer — a projection in a role its opcode
    /// cannot consume, an unknown source, or an operand field that disagrees with
    /// its source. Reachable: `rejects_a_layer_term_slots_refuses` drives it.
    Schedule(ScheduleError),

    // ── wire structure ───────────────────────────────────────────────────
    /// The opcode is dead in this regime (§12.1: "every opcode is live for its
    /// regime").
    InvalidOpcode { at: usize, opcode: u16, regime: BwdRegime },
    /// The stream ended in the middle of a record's mandatory words.
    TruncatedRecord { at: usize },
    /// The stream ended before a mode's required extension word (§12.1: "every
    /// required extension is present and in bounds").
    MissingExtension { at: usize, mode: u16 },
    /// The stream holds more records than the program has instructions.
    TrailingWords { consumed: usize, words: usize },
    /// The stream holds fewer records than the program has instructions.
    TruncatedProgram { records: usize, expected: usize },
    /// A decoded record is not the record the placement lowers to.
    RecordMismatch { index: usize },
    /// A move header's coefficient bits are not canonical zero (§9.2).
    MoveCoefficientNotZero { at: usize, bits: u16 },
    /// A required-zero payload bit is set (§9.4: "remaining payload bits are
    /// zero"; §9.5: "every invalid/unused field is zero").
    ReservedBitsSet { at: usize, word: u16 },
    /// The re-encoding of a decoded record is not the bytes it was decoded from.
    /// The catch-all behind the named canonical rules.
    NonCanonicalEncoding { at: usize },

    // ── coefficients ─────────────────────────────────────────────────────
    /// The coefficient index addresses neither a reserved literal nor a bank
    /// entry.
    CoefficientOutOfRange { at: usize, index: u32, bank: usize },
    /// A banked recipe evaluates to zero (§9.2: "Zero is not an instruction
    /// coefficient").
    EncodedZeroCoefficient { index: u32 },
    /// A banked recipe is `+1` or `-1`, which must use its reserved index instead
    /// of an ordinary E4 multiplication (§9.2, §12.1).
    OrdinaryMultiplicationByOne { index: u32, negated: bool },

    // ── source coordinates ───────────────────────────────────────────────
    /// The window index is past the bound window table (§9.4's `source_window:6`).
    SourceWindowOutOfRange { at: usize, window: u8, windows: usize },
    /// The coordinate names an unassigned column of a bound window.
    UnboundSourceCoordinate { at: usize, window: u8, column: u8 },

    // ── lanes ────────────────────────────────────────────────────────────
    /// An E4 lane is not four-lane-aligned (§9.4, §12.1).
    MisalignedE4Lane { at: usize, lane: u16 },
    /// A lane (or an E4 quad) does not fit `4 * cells` (§12.1).
    LaneOutOfBudget { at: usize, lane: u16, lanes: u32 },

    // ── mode legality and canonical form ─────────────────────────────────
    /// `PlannedSource` on an `Endpoint0`-only use (§8, §9.5).
    PlannedOnEndpoint0 { at: usize },
    /// `FillSource` on a native dual factor: the pair's mixed retention has to go
    /// through a plan, which is also the only form that says WHICH projection a
    /// lane holds (§9.5).
    FillOnDualFactor { at: usize },
    /// The packed pair `Cell` form on a single-projection use, or the single form
    /// on a native dual factor (§9.5: the pair form is opcode-scoped).
    CellFormNotOpcodeScoped { at: usize },
    /// The fourth plan action appears (see [`ACTION_INVALID`]).
    PlanActionInvalid { at: usize },
    /// A `Direct` or `Invalid` action has a nonzero lane field (§9.5).
    NonZeroLaneOnAction { at: usize, action: u16, lane: u16 },
    /// A plan spells a record that has a shorter canonical encoding (§9.5).
    NonCanonicalPlan { at: usize, shortest: ShortestForm },

    // ── encoded execution ────────────────────────────────────────────────
    /// A resident read found no value in the lane.
    CellNotResident { lane: u16 },
    /// A resident read found a value of the other width in the lane.
    CellWidthMismatch { lane: u16, expected: ValueWidth },
    /// A resident `Endpoint0` disagrees with the value the source resolves — the
    /// lane does not hold the projection the plan claims.
    ResidentValueMismatch { lane: u16 },
}

impl From<ScheduleError> for CoeffCodecError {
    fn from(e: ScheduleError) -> Self {
        CoeffCodecError::Schedule(e)
    }
}

// ── Word helpers ─────────────────────────────────────────────────────────────

fn header_word(opcode: u16, coefficient: u16) -> u16 {
    (coefficient & HEADER_COEFFICIENT_MASK) << HEADER_COEFFICIENT_SHIFT
        | (opcode & HEADER_OPCODE_MASK) << HEADER_OPCODE_SHIFT
}

fn header_opcode(word: u16) -> u16 {
    (word >> HEADER_OPCODE_SHIFT) & HEADER_OPCODE_MASK
}

fn header_coefficient(word: u16) -> u16 {
    (word >> HEADER_COEFFICIENT_SHIFT) & HEADER_COEFFICIENT_MASK
}

fn source_word(coord: SourceCoord, mode: u16) -> u16 {
    (mode & INPUT_MODE_MASK) << INPUT_MODE_SHIFT
        | (coord.first_access as u16) << INPUT_FIRST_ACCESS_SHIFT
        | ((coord.window as u16) & INPUT_WINDOW_MASK) << INPUT_WINDOW_SHIFT
        | ((coord.column as u16) & INPUT_COLUMN_MASK) << INPUT_COLUMN_SHIFT
}

fn input_mode(word: u16) -> u16 {
    (word >> INPUT_MODE_SHIFT) & INPUT_MODE_MASK
}

fn decode_source_word(word: u16) -> SourceCoord {
    SourceCoord {
        window: (((word >> INPUT_WINDOW_SHIFT) & INPUT_WINDOW_MASK) as u8),
        column: (((word >> INPUT_COLUMN_SHIFT) & INPUT_COLUMN_MASK) as u8),
        first_access: ((word >> INPUT_FIRST_ACCESS_SHIFT) & 1) != 0,
    }
}

fn cell_single_word(lane: u16) -> u16 {
    MODE_CELL << INPUT_MODE_SHIFT | (lane & LANE_MASK) << CELL_ENDPOINT0_LANE_SHIFT
}

fn cell_pair_word(endpoint0_lane: u16, delta_lane: u16) -> u16 {
    MODE_CELL << INPUT_MODE_SHIFT
        | (endpoint0_lane & LANE_MASK) << CELL_ENDPOINT0_LANE_SHIFT
        | (delta_lane & LANE_MASK) << CELL_DELTA_LANE_SHIFT
}

fn lane_word(lane: u16) -> u16 {
    (lane & LANE_MASK) << LANE_WORD_SHIFT
}

fn action_code(action: PlanAction) -> u16 {
    match action {
        PlanAction::Direct => ACTION_DIRECT,
        PlanAction::UseResident { .. } => ACTION_USE_RESIDENT,
        PlanAction::Fill { .. } => ACTION_FILL,
        PlanAction::Invalid => ACTION_INVALID,
    }
}

fn plan_word(endpoint0: PlanAction, delta: PlanAction) -> u16 {
    action_code(endpoint0) << PLAN_ENDPOINT0_ACTION_SHIFT
        | (endpoint0.lane().unwrap_or(0) & LANE_MASK) << PLAN_ENDPOINT0_LANE_SHIFT
        | action_code(delta) << PLAN_DELTA_ACTION_SHIFT
        | (delta.lane().unwrap_or(0) & LANE_MASK) << PLAN_DELTA_LANE_SHIFT
}

fn decode_action(word: u16, action_shift: u32, lane_shift: u32) -> (u16, u16) {
    ((word >> action_shift) & PLAN_ACTION_MASK, (word >> lane_shift) & LANE_MASK)
}

// ── Lane checks ──────────────────────────────────────────────────────────────

/// Lanes one operand record WRITES, as `(lane, width)` pairs.
fn written_lanes(use_: &DecodedUse) -> Vec<u16> {
    match *use_ {
        DecodedUse::Fill { dst_lane, .. } => vec![dst_lane],
        DecodedUse::Planned { endpoint0, delta, .. } => [endpoint0, delta]
            .into_iter()
            .filter_map(|a| match a {
                PlanAction::Fill { lane } => Some(lane),
                _ => None,
            })
            .collect(),
        DecodedUse::Direct { .. } | DecodedUse::Cell(_) => Vec::new(),
    }
}

/// Lanes one operand record READS.
fn read_lanes(use_: &DecodedUse) -> Vec<u16> {
    match *use_ {
        DecodedUse::Cell(DecodedCell::Single { lane }) => vec![lane],
        DecodedUse::Cell(DecodedCell::Pair { endpoint0_lane, delta_lane }) => {
            vec![endpoint0_lane, delta_lane]
        }
        DecodedUse::Planned { endpoint0, delta, .. } => [endpoint0, delta]
            .into_iter()
            .filter_map(|a| match a {
                PlanAction::UseResident { lane } => Some(lane),
                _ => None,
            })
            .collect(),
        DecodedUse::Direct { .. } | DecodedUse::Fill { .. } => Vec::new(),
    }
}

/// No operand's fill may write lanes a LATER operand of the same term reads
/// ([`CoeffCodecError::FillClobbersLaterOperand`]).
///
/// Scoped to EMITTED order and to DISTINCT operands only. Within one record a
/// plan legitimately reads a lane and then reclaims it (§8's read-then-write
/// phases), and a squared term performs its single resolution once (§9.1 as
/// amended), so neither is a hazard.
fn check_operand_hazards(
    at: usize,
    category: TermCategory,
    uses: &[DecodedUse],
) -> Result<(), CoeffCodecError> {
    for (position, writer) in uses.iter().enumerate() {
        let written = written_lanes(writer);
        if written.is_empty() {
            continue;
        }
        let Some(write_width) = operand_width(category, position) else { continue };
        for (later, reader) in uses.iter().enumerate().skip(position + 1) {
            let Some(read_width) = operand_width(category, later) else { continue };
            for &w in &written {
                for r in read_lanes(reader) {
                    let (ws, we) = (u32::from(w), u32::from(w) + write_width.lanes());
                    let (rs, re) = (u32::from(r), u32::from(r) + read_width.lanes());
                    if ws < re && rs < we {
                        return Err(CoeffCodecError::FillClobbersLaterOperand { at, lane: w });
                    }
                }
            }
        }
    }
    Ok(())
}

fn check_lane(at: usize, lane: u16, width: ValueWidth, lanes: u32) -> Result<(), CoeffCodecError> {
    if width == ValueWidth::E4 && u32::from(lane) % LANES_PER_CELL != 0 {
        return Err(CoeffCodecError::MisalignedE4Lane { at, lane });
    }
    if u32::from(lane) + width.lanes() > lanes {
        return Err(CoeffCodecError::LaneOutOfBudget { at, lane, lanes });
    }
    Ok(())
}

// ── Placement -> records ─────────────────────────────────────────────────────

/// The wire records one placed, bound program lowers to — the semantic half of
/// encoding, with no bit twiddling.
///
/// This is where the two spellings the wire fixes are applied: a mixed product's
/// BF factor is emitted first, and a squared term keeps its single deduplicated
/// use (module doc).
pub fn program_records(
    layer: &CoeffLayer,
    placement: &CoeffPlacement,
    binding: &CoeffSourceBinding,
) -> Result<Vec<DecodedInstr>, CoeffCodecError> {
    if placement.regime != layer.regime {
        return Err(CoeffCodecError::RegimeMismatch {
            declared: placement.regime,
            found: layer.regime,
        });
    }
    let mut coords: HashMap<(u32, u8), SourceCoord> = HashMap::with_capacity(binding.uses.len());
    for bound in &binding.uses {
        coords.insert(
            (bound.instr, bound.slot),
            SourceCoord {
                window: bound.window,
                column: bound.column,
                first_access: bound.first_access,
            },
        );
    }

    let regime = layer.regime;
    let mut out = Vec::with_capacity(placement.instrs.len());
    for (index, instr) in placement.instrs.iter().enumerate() {
        let index = index as u32;
        match instr {
            ScheduledInstr::MoveBF { from_lane, to_lane, .. } => out.push(DecodedInstr::Move {
                category: encodable(regime, TermCategory::MoveBf)?,
                from_lane: *from_lane,
                to_lane: *to_lane,
            }),
            ScheduledInstr::MoveE4 { from_lane, to_lane, .. } => out.push(DecodedInstr::Move {
                category: encodable(regime, TermCategory::MoveE4)?,
                from_lane: *from_lane,
                to_lane: *to_lane,
            }),
            ScheduledInstr::Term { term, coefficient, uses } => {
                let semantic = layer
                    .terms
                    .get(term.0 as usize)
                    .ok_or(ScheduleError::UnknownTerm { term: *term })?;
                let category = encodable(regime, term_category(semantic))?;
                let slots = term_slots(layer, semantic)?;
                if slots.len() != uses.len() {
                    return Err(CoeffCodecError::SlotCountMismatch {
                        instr: index,
                        slots: slots.len(),
                        uses: uses.len(),
                    });
                }
                let order = emission_order(layer, index, category, &slots)?;
                let mut records = Vec::with_capacity(order.len());
                for (position, &slot) in order.iter().enumerate() {
                    let width = operand_width(category, position)
                        .ok_or(CoeffCodecError::MixedProductNotMixed { instr: index })?;
                    check_slot_width(layer, index, position, slots[slot], width)?;
                    records.push(record_of(
                        &uses[slot],
                        slots[slot],
                        coords.get(&(index, slot as u8)).copied(),
                        index,
                        slot as u8,
                    )?);
                }
                out.push(DecodedInstr::Term {
                    category,
                    coefficient: *coefficient,
                    uses: records,
                });
            }
        }
    }
    Ok(out)
}

fn encodable(regime: BwdRegime, category: TermCategory) -> Result<TermCategory, CoeffCodecError> {
    if opcode_of(regime, category).is_none() {
        return Err(CoeffCodecError::CategoryNotEncodable { regime, category });
    }
    Ok(category)
}

/// Slot indices in EMISSION order.
///
/// Identity everywhere except a two-slot `C2ProductBF_E4`, whose BF slot is
/// emitted first so [`operand_width`] is total (module doc).
fn emission_order(
    layer: &CoeffLayer,
    instr: u32,
    category: TermCategory,
    slots: &[SlotKind],
) -> Result<Vec<usize>, CoeffCodecError> {
    if category != TermCategory::C2ProductBfE4 {
        return Ok((0..slots.len()).collect());
    }
    if slots.len() != 2 {
        // A squared product cannot be mixed: one source has one field.
        return Err(CoeffCodecError::MixedProductNotMixed { instr });
    }
    let field = |index: usize| -> Result<FieldKind, CoeffCodecError> {
        layer
            .source(slots[index].source())
            .map(|s| s.field)
            .ok_or(CoeffCodecError::UnboundInput { instr, slot: index as u8 })
    };
    match (field(0)?, field(1)?) {
        (FieldKind::Base, FieldKind::Ext) => Ok(vec![0, 1]),
        (FieldKind::Ext, FieldKind::Base) => Ok(vec![1, 0]),
        _ => Err(CoeffCodecError::MixedProductNotMixed { instr }),
    }
}

fn check_slot_width(
    layer: &CoeffLayer,
    instr: u32,
    position: usize,
    slot: SlotKind,
    expected: ValueWidth,
) -> Result<(), CoeffCodecError> {
    let field = layer
        .source(slot.source())
        .map(|s| s.field)
        .ok_or(CoeffCodecError::UnboundInput { instr, slot: position as u8 })?;
    if ValueWidth::of(field) != expected {
        return Err(CoeffCodecError::OperandWidthMismatch { instr, position, expected });
    }
    Ok(())
}

/// One placed [`ValueUse`] as a wire record.
///
/// The wire names the ROLE's projection and nothing finer, so this also proves the
/// use really is about the slot's own projection and source — otherwise the record
/// would encode a different program than the one placement decided.
fn record_of(
    use_: &ValueUse,
    kind: SlotKind,
    coord: Option<SourceCoord>,
    instr: u32,
    slot: u8,
) -> Result<DecodedUse, CoeffCodecError> {
    let need = || coord.ok_or(CoeffCodecError::UnboundInput { instr, slot });
    let mismatch = CoeffCodecError::UseSlotMismatch { instr, slot };
    let own = |p: ProjectionId| -> Result<(), CoeffCodecError> {
        match kind {
            SlotKind::Endpoint0Only(q) | SlotKind::DeltaOnly(q) if p == q => Ok(()),
            _ => Err(mismatch.clone()),
        }
    };
    // The source a use names, when it names one, must be the slot's own.
    let named = match *use_ {
        ValueUse::Direct { source } | ValueUse::PlannedDelta { source, .. } => Some(source),
        ValueUse::Fill { projection, .. } => Some(projection.source),
        ValueUse::Cell(CellRead::Pair { source, .. }) => Some(source),
        ValueUse::Cell(CellRead::Single { .. }) => None,
    };
    if named.is_some_and(|source| source != kind.source()) {
        return Err(mismatch);
    }
    Ok(match *use_ {
        ValueUse::Direct { .. } => DecodedUse::Direct { coord: need()? },
        ValueUse::Fill { projection, dst_lane } => {
            own(projection)?;
            DecodedUse::Fill { coord: need()?, dst_lane }
        }
        ValueUse::Cell(CellRead::Single { projection, lane }) => {
            own(projection)?;
            DecodedUse::Cell(DecodedCell::Single { lane })
        }
        ValueUse::Cell(CellRead::Pair { endpoint0_lane, delta_lane, .. }) => {
            if !matches!(kind, SlotKind::DualFactor(_)) {
                return Err(mismatch);
            }
            DecodedUse::Cell(DecodedCell::Pair { endpoint0_lane, delta_lane })
        }
        ValueUse::PlannedDelta { endpoint0, delta, .. } => {
            if matches!(kind, SlotKind::Endpoint0Only(_)) {
                return Err(CoeffCodecError::PlannedOnEndpoint0 { at: 0 });
            }
            DecodedUse::Planned { coord: need()?, endpoint0, delta }
        }
    })
}

// ── Records -> words ─────────────────────────────────────────────────────────

/// Encode decoded records into the §9.1 word stream.
///
/// Every structural and canonical rule §12.1 lists is enforced HERE as well as in
/// [`decode_program`], so an encoder fed a bad placement fails at compile time
/// rather than producing a stream only the validator rejects.
pub fn encode_instrs(
    regime: BwdRegime,
    budget: CellBudget,
    instrs: &[DecodedInstr],
) -> Result<Vec<u16>, CoeffCodecError> {
    let lanes = budget.lanes();
    let mut out = Vec::new();
    for (index, instr) in instrs.iter().enumerate() {
        let index = index as u32;
        match instr {
            DecodedInstr::Move { category, from_lane, to_lane } => {
                let width = move_width(*category)
                    .ok_or(CoeffCodecError::CategoryNotEncodable { regime, category: *category })?;
                let opcode = opcode_of(regime, *category).ok_or(
                    CoeffCodecError::CategoryNotEncodable { regime, category: *category },
                )?;
                out.push(header_word(opcode, 0));
                let at = out.len();
                check_lane(at, *from_lane, width, lanes)?;
                out.push(lane_word(*from_lane));
                let at = out.len();
                check_lane(at, *to_lane, width, lanes)?;
                out.push(lane_word(*to_lane));
            }
            DecodedInstr::Term { category, coefficient, uses } => {
                let opcode = opcode_of(regime, *category).ok_or(
                    CoeffCodecError::CategoryNotEncodable { regime, category: *category },
                )?;
                if coefficient.0 >= MAX_COEFFICIENT_ENCODINGS as u32 {
                    return Err(CoeffCodecError::CoefficientIndexOverflow { index: coefficient.0 });
                }
                let arity = category_arity(*category);
                if uses.is_empty() || uses.len() > arity {
                    return Err(CoeffCodecError::SlotCountMismatch {
                        instr: index,
                        slots: arity,
                        uses: uses.len(),
                    });
                }
                // §9.1's squared form repeats ONE record at every position, so a
                // MIXED-width opcode can never be squared: its positions disagree
                // about the operand's width and one record cannot be both. As
                // [`CoeffCodecError::MixedProductNotMixed`] says, lowering cannot
                // produce this — the category is derived from the operand fields —
                // so this is DEFENCE IN DEPTH against a hand-built instruction.
                //
                // It is load-bearing defence, though: unchecked, such a term
                // encodes cleanly and then means "resolve this coordinate once at
                // BF and consume it as an E4", which no resolver can honour. This
                // is the ONLY check for it, and it is what lets the GPU executor's
                // mixed branch carry none (§12.1: release kernels trust validated
                // artifacts).
                if uses.len() < arity
                    && (1..arity).any(|position| {
                        operand_width(*category, position) != operand_width(*category, 0)
                    })
                {
                    return Err(CoeffCodecError::MixedProductNotMixed { instr: index });
                }
                out.push(header_word(opcode, coefficient.0 as u16));
                let mut spans: Vec<std::ops::Range<usize>> = Vec::with_capacity(arity);
                for position in 0..arity {
                    // A squared term repeats its single record verbatim.
                    let use_ = &uses[position.min(uses.len() - 1)];
                    let width = operand_width(*category, position)
                        .ok_or(CoeffCodecError::MixedProductNotMixed { instr: index })?;
                    let role = category_role(*category).ok_or(
                        CoeffCodecError::CategoryNotEncodable { regime, category: *category },
                    )?;
                    let start = out.len();
                    encode_use(&mut out, use_, role, width, lanes)?;
                    spans.push(start..out.len());
                }
                // Byte-identical records mean "squared" on the wire, so two
                // DISTINCT slots must never encode identically.
                if uses.len() == 2 && out[spans[0].clone()] == out[spans[1].clone()] {
                    return Err(CoeffCodecError::AmbiguousRepeatedRecord { at: spans[1].start });
                }
                check_operand_hazards(spans[0].start, *category, uses)?;
            }
        }
    }
    if out.len() * 2 > KERNEL_ARGUMENT_CEILING_BYTES {
        return Err(CoeffCodecError::ProgramExceedsKernelArgumentCap { bytes: out.len() * 2 });
    }
    Ok(out)
}

fn encode_use(
    out: &mut Vec<u16>,
    use_: &DecodedUse,
    role: OperandRole,
    width: ValueWidth,
    lanes: u32,
) -> Result<(), CoeffCodecError> {
    let at = out.len();
    match *use_ {
        DecodedUse::Direct { coord } => {
            check_coord(at, coord)?;
            out.push(source_word(coord, MODE_DIRECT_SOURCE));
        }
        DecodedUse::Cell(DecodedCell::Single { lane }) => {
            if role == OperandRole::Pair {
                return Err(CoeffCodecError::CellFormNotOpcodeScoped { at });
            }
            check_lane(at, lane, width, lanes)?;
            out.push(cell_single_word(lane));
        }
        DecodedUse::Cell(DecodedCell::Pair { endpoint0_lane, delta_lane }) => {
            if role != OperandRole::Pair {
                return Err(CoeffCodecError::CellFormNotOpcodeScoped { at });
            }
            check_lane(at, endpoint0_lane, width, lanes)?;
            check_lane(at, delta_lane, width, lanes)?;
            out.push(cell_pair_word(endpoint0_lane, delta_lane));
        }
        DecodedUse::Fill { coord, dst_lane } => {
            if role == OperandRole::Pair {
                return Err(CoeffCodecError::FillOnDualFactor { at });
            }
            check_coord(at, coord)?;
            check_lane(at + 1, dst_lane, width, lanes)?;
            out.push(source_word(coord, MODE_FILL_SOURCE));
            out.push(lane_word(dst_lane));
        }
        DecodedUse::Planned { coord, endpoint0, delta } => {
            if role == OperandRole::Endpoint0 {
                return Err(CoeffCodecError::PlannedOnEndpoint0 { at });
            }
            check_coord(at, coord)?;
            check_plan(at + 1, role, width, lanes, endpoint0, delta)?;
            out.push(source_word(coord, MODE_PLANNED_SOURCE));
            out.push(plan_word(endpoint0, delta));
        }
    }
    Ok(())
}

fn check_coord(at: usize, coord: SourceCoord) -> Result<(), CoeffCodecError> {
    if usize::from(coord.window) >= MAX_SOURCE_WINDOWS {
        return Err(CoeffCodecError::SourceWindowOutOfRange {
            at,
            window: coord.window,
            windows: MAX_SOURCE_WINDOWS,
        });
    }
    if usize::from(coord.column) >= SOURCE_WINDOW_COLUMNS {
        return Err(CoeffCodecError::UnboundSourceCoordinate {
            at,
            window: coord.window,
            column: coord.column,
        });
    }
    Ok(())
}

/// The plan's legality (§9.5) and its canonical minimality (§12.1: "the cheapest
/// legal input encoding is used").
fn check_plan(
    at: usize,
    role: OperandRole,
    width: ValueWidth,
    lanes: u32,
    endpoint0: PlanAction,
    delta: PlanAction,
) -> Result<(), CoeffCodecError> {
    for action in [endpoint0, delta] {
        if action == PlanAction::Invalid {
            return Err(CoeffCodecError::PlanActionInvalid { at });
        }
        if let Some(lane) = action.lane() {
            check_lane(at, lane, width, lanes)?;
        }
    }
    let resident = |a: PlanAction| matches!(a, PlanAction::UseResident { .. });
    let fill = |a: PlanAction| matches!(a, PlanAction::Fill { .. });
    if endpoint0 == PlanAction::Direct && delta == PlanAction::Direct {
        return Err(CoeffCodecError::NonCanonicalPlan { at, shortest: ShortestForm::DirectSource });
    }
    if role == OperandRole::Pair && resident(endpoint0) && resident(delta) {
        return Err(CoeffCodecError::NonCanonicalPlan { at, shortest: ShortestForm::CellPair });
    }
    if role == OperandRole::Delta {
        if endpoint0 == PlanAction::Direct && fill(delta) {
            // Resolve and retain only the requested projection: `FillSource`.
            return Err(CoeffCodecError::NonCanonicalPlan {
                at,
                shortest: ShortestForm::FillSource,
            });
        }
        if resident(delta) && !fill(endpoint0) {
            // The requested projection is already resident and the endpoint is
            // touched for nothing: `Cell`, single form.
            return Err(CoeffCodecError::NonCanonicalPlan {
                at,
                shortest: ShortestForm::CellSingle,
            });
        }
    }
    Ok(())
}

/// Encode one placed, bound program.
pub fn encode_program(
    layer: &CoeffLayer,
    placement: &CoeffPlacement,
    binding: &CoeffSourceBinding,
) -> Result<EncodedProgram, CoeffCodecError> {
    let records = program_records(layer, placement, binding)?;
    let words = encode_instrs(layer.regime, placement.request.budget, &records)?;
    Ok(EncodedProgram {
        regime: layer.regime,
        budget: placement.request.budget,
        c_init: layer.c_init,
        words,
    })
}

// ── Words -> records ─────────────────────────────────────────────────────────

/// Decode and structurally validate the whole word stream (§12.1).
///
/// The stream must end exactly at `program.words.len()`; a record that overruns it
/// is [`CoeffCodecError::TruncatedRecord`] or
/// [`CoeffCodecError::MissingExtension`].
pub fn decode_program(
    program: &EncodedProgram,
    binding: &CoeffSourceBinding,
) -> Result<Vec<DecodedInstr>, CoeffCodecError> {
    let words = &program.words;
    let lanes = program.lanes();
    let mut out = Vec::new();
    let mut i = 0usize;
    while i < words.len() {
        let header = words[i];
        let at = i;
        i += 1;
        let opcode = header_opcode(header);
        let category = category_of(program.regime, opcode).ok_or(
            CoeffCodecError::InvalidOpcode { at, opcode, regime: program.regime },
        )?;
        if is_move(category) {
            let bits = header_coefficient(header);
            if bits != 0 {
                return Err(CoeffCodecError::MoveCoefficientNotZero { at, bits });
            }
            let width = move_width(category).expect("a move category has a move width");
            let lane = |i: &mut usize| -> Result<u16, CoeffCodecError> {
                let at = *i;
                let word = *words.get(at).ok_or(CoeffCodecError::TruncatedRecord { at })?;
                *i += 1;
                let value = (word >> LANE_WORD_SHIFT) & LANE_MASK;
                if word != lane_word(value) {
                    return Err(CoeffCodecError::ReservedBitsSet { at, word });
                }
                check_lane(at, value, width, lanes)?;
                Ok(value)
            };
            let from_lane = lane(&mut i)?;
            let to_lane = lane(&mut i)?;
            out.push(DecodedInstr::Move { category, from_lane, to_lane });
            continue;
        }

        let coefficient = CoefficientRecipeId(u32::from(header_coefficient(header)));
        let arity = category_arity(category);
        let role = category_role(category).expect("a term category has a role");
        let mut records: Vec<(DecodedUse, &[u16])> = Vec::with_capacity(arity);
        for position in 0..arity {
            let start = i;
            let width = operand_width(category, position).expect("arity bounds the position");
            let use_ = decode_use(words, &mut i, role, width, lanes, binding)?;
            records.push((use_, &words[start..i]));
        }
        // Byte-identical input records denote a squared term: ONE resolution.
        let first = at + 1;
        let uses: Vec<DecodedUse> = if arity == 2 && records[0].1 == records[1].1 {
            vec![records[0].0]
        } else {
            records.iter().map(|(u, _)| *u).collect()
        };
        check_operand_hazards(first, category, &uses)?;
        out.push(DecodedInstr::Term { category, coefficient, uses });
    }
    Ok(out)
}

fn decode_use(
    words: &[u16],
    i: &mut usize,
    role: OperandRole,
    width: ValueWidth,
    lanes: u32,
    binding: &CoeffSourceBinding,
) -> Result<DecodedUse, CoeffCodecError> {
    let at = *i;
    let word = *words.get(at).ok_or(CoeffCodecError::TruncatedRecord { at })?;
    *i += 1;
    let mode = input_mode(word);
    let extension = |i: &mut usize| -> Result<(usize, u16), CoeffCodecError> {
        let at = *i;
        let word = *words.get(at).ok_or(CoeffCodecError::MissingExtension { at, mode })?;
        *i += 1;
        Ok((at, word))
    };
    match mode {
        MODE_DIRECT_SOURCE => {
            let coord = bound_coord(at, word, binding)?;
            Ok(DecodedUse::Direct { coord })
        }
        MODE_CELL => {
            let endpoint0_lane = (word >> CELL_ENDPOINT0_LANE_SHIFT) & LANE_MASK;
            if role == OperandRole::Pair {
                let delta_lane = (word >> CELL_DELTA_LANE_SHIFT) & LANE_MASK;
                if word != cell_pair_word(endpoint0_lane, delta_lane) {
                    return Err(CoeffCodecError::ReservedBitsSet { at, word });
                }
                check_lane(at, endpoint0_lane, width, lanes)?;
                check_lane(at, delta_lane, width, lanes)?;
                return Ok(DecodedUse::Cell(DecodedCell::Pair { endpoint0_lane, delta_lane }));
            }
            if word != cell_single_word(endpoint0_lane) {
                return Err(CoeffCodecError::ReservedBitsSet { at, word });
            }
            check_lane(at, endpoint0_lane, width, lanes)?;
            Ok(DecodedUse::Cell(DecodedCell::Single { lane: endpoint0_lane }))
        }
        MODE_FILL_SOURCE => {
            if role == OperandRole::Pair {
                return Err(CoeffCodecError::FillOnDualFactor { at });
            }
            let coord = bound_coord(at, word, binding)?;
            let (ext_at, ext) = extension(i)?;
            let dst_lane = (ext >> LANE_WORD_SHIFT) & LANE_MASK;
            if ext != lane_word(dst_lane) {
                return Err(CoeffCodecError::ReservedBitsSet { at: ext_at, word: ext });
            }
            check_lane(ext_at, dst_lane, width, lanes)?;
            Ok(DecodedUse::Fill { coord, dst_lane })
        }
        _ => {
            if role == OperandRole::Endpoint0 {
                return Err(CoeffCodecError::PlannedOnEndpoint0 { at });
            }
            let coord = bound_coord(at, word, binding)?;
            let (plan_at, plan) = extension(i)?;
            let endpoint0 = plan_action(
                plan_at,
                decode_action(plan, PLAN_ENDPOINT0_ACTION_SHIFT, PLAN_ENDPOINT0_LANE_SHIFT),
            )?;
            let delta = plan_action(
                plan_at,
                decode_action(plan, PLAN_DELTA_ACTION_SHIFT, PLAN_DELTA_LANE_SHIFT),
            )?;
            check_plan(plan_at, role, width, lanes, endpoint0, delta)?;
            Ok(DecodedUse::Planned { coord, endpoint0, delta })
        }
    }
}

fn plan_action(at: usize, (action, lane): (u16, u16)) -> Result<PlanAction, CoeffCodecError> {
    match action {
        ACTION_DIRECT | ACTION_INVALID if lane != 0 => {
            Err(CoeffCodecError::NonZeroLaneOnAction { at, action, lane })
        }
        ACTION_DIRECT => Ok(PlanAction::Direct),
        ACTION_USE_RESIDENT => Ok(PlanAction::UseResident { lane }),
        ACTION_FILL => Ok(PlanAction::Fill { lane }),
        _ => Err(CoeffCodecError::PlanActionInvalid { at }),
    }
}

fn bound_coord(
    at: usize,
    word: u16,
    binding: &CoeffSourceBinding,
) -> Result<SourceCoord, CoeffCodecError> {
    let coord = decode_source_word(word);
    if usize::from(coord.window) >= binding.windows.len() {
        return Err(CoeffCodecError::SourceWindowOutOfRange {
            at,
            window: coord.window,
            windows: binding.windows.len(),
        });
    }
    if binding.resolve(coord.window, coord.column).is_none() {
        return Err(CoeffCodecError::UnboundSourceCoordinate {
            at,
            window: coord.window,
            column: coord.column,
        });
    }
    Ok(coord)
}

/// The [`SourceId`] a decoded coordinate names.
pub fn coord_source(binding: &CoeffSourceBinding, coord: SourceCoord) -> Option<SourceId> {
    binding.resolve(coord.window, coord.column)
}

// ── Validation ───────────────────────────────────────────────────────────────

/// Decode `program` and prove every §12.1 structural and canonical property.
///
/// On top of [`decode_program`] this checks the coefficient bank (in range, no
/// zero, no ordinary `+1`/`-1`) and re-encodes every decoded record, so an
/// accepted program is byte-for-byte the ONLY encoding of the records it decodes
/// to.
pub fn validate_program(
    program: &EncodedProgram,
    binding: &CoeffSourceBinding,
    bank: &[NormalizedCoefficientRecipe],
) -> Result<Vec<DecodedInstr>, CoeffCodecError> {
    let instrs = decode_program(program, binding)?;
    let mut at = 0usize;
    if let Some(id) = program.c_init {
        check_coefficient(at, id, bank)?;
    }
    for instr in &instrs {
        if let DecodedInstr::Term { coefficient, .. } = instr {
            check_coefficient(at, *coefficient, bank)?;
        }
        at += instr.words();
    }
    let round_trip = encode_instrs(program.regime, program.budget, &instrs)?;
    if round_trip != program.words {
        let at = round_trip
            .iter()
            .zip(&program.words)
            .position(|(a, b)| a != b)
            .unwrap_or(round_trip.len().min(program.words.len()));
        return Err(CoeffCodecError::NonCanonicalEncoding { at });
    }
    if program.bytes() > KERNEL_ARGUMENT_CEILING_BYTES {
        return Err(CoeffCodecError::ProgramExceedsKernelArgumentCap { bytes: program.bytes() });
    }
    Ok(instrs)
}

fn check_coefficient(
    at: usize,
    id: CoefficientRecipeId,
    bank: &[NormalizedCoefficientRecipe],
) -> Result<(), CoeffCodecError> {
    let Some(index) = id.bank_index() else {
        // A reserved literal is always canonical.
        return Ok(());
    };
    let Some(recipe) = bank.get(index) else {
        return Err(CoeffCodecError::CoefficientOutOfRange { at, index: id.0, bank: bank.len() });
    };
    if recipe.is_zero() {
        return Err(CoeffCodecError::EncodedZeroCoefficient { index: id.0 });
    }
    if recipe.is_one() {
        return Err(CoeffCodecError::OrdinaryMultiplicationByOne { index: id.0, negated: false });
    }
    if recipe.is_neg_one() {
        return Err(CoeffCodecError::OrdinaryMultiplicationByOne { index: id.0, negated: true });
    }
    Ok(())
}

/// Prove the encoded program IS the encoding of this placement and binding.
///
/// The only place a declared record count exists, hence the only place trailing
/// words are distinguishable from a longer legitimate program.
pub fn certify_encoding(
    layer: &CoeffLayer,
    placement: &CoeffPlacement,
    binding: &CoeffSourceBinding,
    program: &EncodedProgram,
) -> Result<(), CoeffCodecError> {
    let expected = program_records(layer, placement, binding)?;
    let decoded = validate_program(program, binding, &layer.coefficients)?;
    if decoded.len() > expected.len() {
        let consumed = expected.iter().map(DecodedInstr::words).sum();
        return Err(CoeffCodecError::TrailingWords { consumed, words: program.words.len() });
    }
    if decoded.len() < expected.len() {
        return Err(CoeffCodecError::TruncatedProgram {
            records: decoded.len(),
            expected: expected.len(),
        });
    }
    for (index, (a, b)) in decoded.iter().zip(&expected).enumerate() {
        if a != b {
            return Err(CoeffCodecError::RecordMismatch { index });
        }
    }
    Ok(())
}

// ── Disassembler ─────────────────────────────────────────────────────────────

fn width_tag(width: ValueWidth) -> &'static str {
    match width {
        ValueWidth::Bf => "bf",
        ValueWidth::E4 => "e4",
    }
}

fn role_tag(role: OperandRole) -> &'static str {
    match role {
        OperandRole::Endpoint0 => "e0",
        OperandRole::Delta => "d",
        OperandRole::Pair => "pair",
    }
}

fn coefficient_tag(id: CoefficientRecipeId) -> String {
    match id.bank_index() {
        None if id == CoefficientRecipeId::ONE => "+1".to_string(),
        None => "-1".to_string(),
        Some(index) => format!("#{index}"),
    }
}

fn action_tag(action: PlanAction) -> String {
    match action {
        PlanAction::Direct => "direct".to_string(),
        PlanAction::UseResident { lane } => format!("resident l{lane}"),
        PlanAction::Fill { lane } => format!("fill l{lane}"),
        PlanAction::Invalid => "invalid".to_string(),
    }
}

fn source_tag(binding: &CoeffSourceBinding, coord: SourceCoord) -> String {
    let source = match coord_source(binding, coord) {
        Some(SourceId(id)) => format!("s{id}"),
        None => "s?".to_string(),
    };
    let procedural = binding
        .windows
        .get(usize::from(coord.window))
        .is_some_and(|w| w.is_procedural());
    format!(
        "{source}(w{}c{}){}{}",
        coord.window,
        coord.column,
        if coord.first_access { "!" } else { "." },
        if procedural { " proc" } else { "" },
    )
}

fn use_tag(
    binding: &CoeffSourceBinding,
    use_: &DecodedUse,
    role: OperandRole,
    width: ValueWidth,
) -> String {
    let head = format!("{}:{}", role_tag(role), width_tag(width));
    match *use_ {
        DecodedUse::Direct { coord } => {
            format!("{head} {} direct", source_tag(binding, coord))
        }
        DecodedUse::Cell(DecodedCell::Single { lane }) => {
            format!("{head} resident l{lane}")
        }
        DecodedUse::Cell(DecodedCell::Pair { endpoint0_lane, delta_lane }) => {
            format!("{head} resident e0=l{endpoint0_lane} d=l{delta_lane}")
        }
        DecodedUse::Fill { coord, dst_lane } => {
            format!("{head} {} fill l{dst_lane}", source_tag(binding, coord))
        }
        DecodedUse::Planned { coord, endpoint0, delta } => {
            format!(
                "{head} {} plan e0={} d={}",
                source_tag(binding, coord),
                action_tag(endpoint0),
                action_tag(delta),
            )
        }
    }
}

/// Render one encoded program as text: a header line, then exactly ONE line per
/// semantic term or move.
///
/// The format is pinned by a test, so it cannot drift silently. Per line:
/// the word offset, the mnemonic, the coefficient recipe (`+1` / `-1` / `#bank`),
/// then each operand as `role:width source(window,column)first-access action
/// lane`. `!` marks a first access, `.` a later one, and a procedural window is
/// tagged `proc`. A squared term prints its single resolution once, tagged
/// `squared`.
pub fn disassemble(
    program: &EncodedProgram,
    binding: &CoeffSourceBinding,
) -> Result<String, CoeffCodecError> {
    let instrs = decode_program(program, binding)?;
    let regime = match program.regime {
        BwdRegime::R0 => "R0",
        BwdRegime::Ext => "Ext",
    };
    let mut out = String::new();
    let c_init = match program.c_init {
        Some(id) => coefficient_tag(id),
        None => "none".to_string(),
    };
    let _ = writeln!(
        out,
        "; program regime={regime} budget=c{} lanes={} words={} bytes={} c_init={c_init}",
        program.budget.cells(),
        program.lanes(),
        program.words.len(),
        program.bytes(),
    );
    let mut at = 0usize;
    for instr in &instrs {
        match instr {
            DecodedInstr::Move { category, from_lane, to_lane } => {
                let _ = writeln!(
                    out,
                    "{at:04}  {:<14}  l{from_lane} -> l{to_lane}",
                    category.label()
                );
            }
            DecodedInstr::Term { category, coefficient, uses } => {
                let role = category_role(*category).expect("a term category has a role");
                let arity = category_arity(*category);
                let operands: Vec<String> = (0..uses.len())
                    .map(|position| {
                        let width =
                            operand_width(*category, position).expect("arity bounds the position");
                        use_tag(binding, &uses[position], role, width)
                    })
                    .collect();
                let squared = if arity > uses.len() { "  [squared]" } else { "" };
                let _ = writeln!(
                    out,
                    "{at:04}  {:<14}  k={:<5}  {}{squared}",
                    category.label(),
                    coefficient_tag(*coefficient),
                    operands.join("  |  "),
                );
            }
        }
        at += instr.words();
    }
    Ok(out)
}
