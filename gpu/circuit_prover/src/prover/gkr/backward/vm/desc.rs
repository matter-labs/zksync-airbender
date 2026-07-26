//! Backward coefficient-term ISA: the by-value launch descriptor and the frozen
//! u16 wire format (design §9, §10.2, §11).
//!
//! THIS FILE IS ONE HALF OF AN ABI. Its CUDA half is
//! `native/prover/gkr/backward/coefficient_vm.cuh`, which carries the same
//! numeric literals under `static_assert`. Neither half may move without the
//! other in the same commit, and both fail to BUILD — not to test — when they
//! disagree: the CUDA `static_assert`s fire during `cargo check` (the build
//! script runs nvcc) and the Rust `const _: () = assert!(...)` blocks fire in
//! the same pass.
//!
//! Every literal below is additionally tied to its AUTHORITY in `gkr_eval_isa`,
//! so the two languages cannot agree with each other while disagreeing with the
//! compiler that produced the program:
//!
//!   * opcode numbers → `bwd::coeff::limits::{r0_opcode, continuation_opcode}`,
//!     which `limits` already pins in both directions against
//!     `R0_OPCODE_TABLE` / `CONTINUATION_OPCODE_TABLE`;
//!   * shifts, masks, modes and plan actions → `bwd::coeff::encode`;
//!   * the two array capacities → `bwd::coeff::limits::in_scope`; and
//!   * the reserved coefficient literals → `model::CoefficientRecipeId`.
//!
//! The program stream is embedded BY VALUE. There is no device program pointer,
//! no format version and no compatibility path (§9.1). An overflow of a cap
//! here requires a tighter encoding, never a second storage path.

use gkr_eval_isa::bwd::coeff::encode::{
    ACTION_DIRECT, ACTION_FILL, ACTION_INVALID, ACTION_USE_RESIDENT, CELL_DELTA_LANE_SHIFT,
    CELL_ENDPOINT0_LANE_SHIFT, HEADER_COEFFICIENT_MASK, HEADER_COEFFICIENT_SHIFT,
    HEADER_OPCODE_MASK, HEADER_OPCODE_SHIFT, INPUT_COLUMN_MASK, INPUT_COLUMN_SHIFT,
    INPUT_FIRST_ACCESS_SHIFT, INPUT_MODE_MASK, INPUT_MODE_SHIFT, INPUT_WINDOW_MASK,
    INPUT_WINDOW_SHIFT, LANE_BITS, LANE_MASK, LANE_WORD_SHIFT, MODE_CELL, MODE_DIRECT_SOURCE,
    MODE_FILL_SOURCE, MODE_PLANNED_SOURCE, PLAN_ACTION_MASK, PLAN_DELTA_ACTION_SHIFT,
    PLAN_DELTA_LANE_SHIFT, PLAN_ENDPOINT0_ACTION_SHIFT, PLAN_ENDPOINT0_LANE_SHIFT,
};
use gkr_eval_isa::bwd::coeff::limits::{
    continuation_opcode, in_scope, r0_opcode, TermCategory, DESCRIPTOR_ALIGNMENT_BYTES,
    HEADER_COEFFICIENT_BITS, HEADER_OPCODE_BITS, KERNEL_ARGUMENT_CEILING_BYTES,
    MAX_COEFFICIENT_ENCODINGS, MAX_SOURCE_WINDOWS, SOURCE_WINDOW_COLUMNS,
};
use gkr_eval_isa::bwd::coeff::model::CoefficientRecipeId;
use gkr_eval_isa::bwd::coeff::schedule::{CellBudget, LANES_PER_CELL, PUBLISH_TARGET_DEPTH};
use gkr_eval_isa::fwd::source::KIND_ORDER;

use crate::primitives::field::E4;
use crate::prover::gkr::backward::GkrEqSizes;

// ── By-value capacities (§9.1, Task 8's measured corpus maxima) ──────────────

/// The by-value kernel-argument cap. `size_of::<BwdCoeffDesc>() <=
/// BWD_COEFF_DESC_CAP` is the FINAL authority on the descriptor's shape.
pub(crate) const BWD_COEFF_DESC_CAP: usize = 32_764;
/// Descriptor alignment. Load-bearing rather than cosmetic: it is what places
/// [`BwdCoeffDesc::program`] on a 16-byte boundary, which is the only reason
/// Task 8's one-word round-up of the measured program maximum buys anything
/// (§9.1: "the implementation may buffer the stream through aligned wide
/// loads"). Pinned by `descriptor_alignment_is_load_bearing`.
pub(crate) const BWD_COEFF_DESC_ALIGN: usize = 16;
/// Live source-window slots. The EXACT measured corpus maximum, deliberately
/// NOT the 64 windows the `source_window:6` coordinate can express — see
/// [`BWD_COEFF_MAX_ENCODABLE_SOURCE_WINDOWS`] for that separate claim.
pub(crate) const BWD_COEFF_SOURCE_WINDOW_CAP: usize = 17;
/// The by-value program array, in u16 words: the measured maximum 5,759 words
/// (`blake2_with_extended_control` L0 `Ext` at **c3**, not at c16 — program
/// length is not monotone in the cell budget) plus exactly one word of 16-byte
/// alignment. Not a headroom allowance: every unearned word is unearned
/// kernel-argument budget in every launch, forever.
pub(crate) const BWD_COEFF_PROGRAM_WORD_CAP: usize = 5_760;
/// [`BWD_COEFF_PROGRAM_WORD_CAP`] in bytes.
pub(crate) const BWD_COEFF_PROGRAM_BYTE_CAP: usize = 2 * BWD_COEFF_PROGRAM_WORD_CAP;

const _: () = {
    assert!(BWD_COEFF_DESC_CAP == KERNEL_ARGUMENT_CEILING_BYTES);
    assert!(BWD_COEFF_DESC_ALIGN == DESCRIPTOR_ALIGNMENT_BYTES);
    assert!(BWD_COEFF_SOURCE_WINDOW_CAP == in_scope::MAX_SOURCE_WINDOWS_USED);
    assert!(BWD_COEFF_PROGRAM_WORD_CAP == in_scope::DESCRIPTOR_PROGRAM_WORDS);
    assert!(BWD_COEFF_PROGRAM_BYTE_CAP == in_scope::DESCRIPTOR_PROGRAM_BYTES);
    // The array is the MEASUREMENT rounded up by strictly less than one
    // alignment quantum, so it can never silently drift into headroom.
    assert!(BWD_COEFF_PROGRAM_WORD_CAP >= in_scope::MAX_REALIZED_PROGRAM_WORDS);
    assert!(
        (BWD_COEFF_PROGRAM_WORD_CAP - in_scope::MAX_REALIZED_PROGRAM_WORDS) * 2
            < BWD_COEFF_DESC_ALIGN
    );
    assert!(BWD_COEFF_PROGRAM_BYTE_CAP % BWD_COEFF_DESC_ALIGN == 0);
};

// ── Frozen wire format (§9.2, §9.4, §9.5, §9.6) ──────────────────────────────
//
// ```text
// header       [ opcode:3 @13 | coefficient:13 @0 ]
// input word   [ column:7 @9 | window:6 @3 | first_access:1 @2 | mode:2 @0 ]
// cell single  [ 0:8 @8 | lane:6 @2 | mode:2 @0 ]
// cell pair    [ delta_lane:6 @10 | 0:2 @8 | e0_lane:6 @2 | mode:2 @0 ]
// plan word    [ delta_lane:6 @10 | delta_act:2 @8 | e0_lane:6 @2 | e0_act:2 @0 ]
// lane word    [ 0:10 @6 | lane:6 @0 ]
// ```

pub(crate) const BWD_COEFF_HEADER_COEFFICIENT_BITS: u32 = 13;
pub(crate) const BWD_COEFF_HEADER_COEFFICIENT_SHIFT: u32 = 0;
pub(crate) const BWD_COEFF_HEADER_COEFFICIENT_MASK: u16 = 0x1fff;
pub(crate) const BWD_COEFF_HEADER_OPCODE_BITS: u32 = 3;
pub(crate) const BWD_COEFF_HEADER_OPCODE_SHIFT: u32 = 13;
pub(crate) const BWD_COEFF_HEADER_OPCODE_MASK: u16 = 0x7;

pub(crate) const BWD_COEFF_INPUT_MODE_SHIFT: u32 = 0;
pub(crate) const BWD_COEFF_INPUT_MODE_MASK: u16 = 0x3;
pub(crate) const BWD_COEFF_INPUT_FIRST_ACCESS_SHIFT: u32 = 2;
pub(crate) const BWD_COEFF_INPUT_WINDOW_SHIFT: u32 = 3;
pub(crate) const BWD_COEFF_INPUT_WINDOW_MASK: u16 = 0x3f;
pub(crate) const BWD_COEFF_INPUT_COLUMN_SHIFT: u32 = 9;
pub(crate) const BWD_COEFF_INPUT_COLUMN_MASK: u16 = 0x7f;

pub(crate) const BWD_COEFF_LANE_BITS: u32 = 6;
pub(crate) const BWD_COEFF_LANE_MASK: u16 = 0x3f;
pub(crate) const BWD_COEFF_LANES_PER_CELL: u32 = 4;
pub(crate) const BWD_COEFF_MIN_BUDGET_CELLS: u32 = 2;
pub(crate) const BWD_COEFF_MAX_BUDGET_CELLS: u32 = 16;

pub(crate) const BWD_COEFF_CELL_ENDPOINT0_LANE_SHIFT: u32 = 2;
pub(crate) const BWD_COEFF_CELL_DELTA_LANE_SHIFT: u32 = 10;
pub(crate) const BWD_COEFF_PLAN_ENDPOINT0_ACTION_SHIFT: u32 = 0;
pub(crate) const BWD_COEFF_PLAN_ENDPOINT0_LANE_SHIFT: u32 = 2;
pub(crate) const BWD_COEFF_PLAN_DELTA_ACTION_SHIFT: u32 = 8;
pub(crate) const BWD_COEFF_PLAN_DELTA_LANE_SHIFT: u32 = 10;
pub(crate) const BWD_COEFF_PLAN_ACTION_MASK: u16 = 0x3;
pub(crate) const BWD_COEFF_LANE_WORD_SHIFT: u32 = 0;

pub(crate) const BWD_COEFF_MODE_DIRECT_SOURCE: u16 = 0;
pub(crate) const BWD_COEFF_MODE_CELL: u16 = 1;
pub(crate) const BWD_COEFF_MODE_FILL_SOURCE: u16 = 2;
pub(crate) const BWD_COEFF_MODE_PLANNED_SOURCE: u16 = 3;

pub(crate) const BWD_COEFF_ACTION_DIRECT: u16 = 0;
pub(crate) const BWD_COEFF_ACTION_USE_RESIDENT: u16 = 1;
pub(crate) const BWD_COEFF_ACTION_FILL: u16 = 2;
pub(crate) const BWD_COEFF_ACTION_INVALID: u16 = 3;

/// Windows the `source_window:6` coordinate can express. An ENCODING limit, a
/// different kind of fact from [`BWD_COEFF_SOURCE_WINDOW_CAP`], which is a
/// measurement. Conflating the two is how a descriptor ends up sized for a
/// number nobody measured.
pub(crate) const BWD_COEFF_MAX_ENCODABLE_SOURCE_WINDOWS: usize = 64;
/// Columns one window can cover (`column:7`).
pub(crate) const BWD_COEFF_SOURCE_WINDOW_COLUMNS: usize = 128;
/// Coefficient encodings thirteen bits admit, including the two reserved ones.
pub(crate) const BWD_COEFF_MAX_COEFFICIENT_ENCODINGS: usize = 8_192;

/// Reserved coefficient index for the literal `+1` (§9.2).
pub(crate) const BWD_COEFF_INDEX_ONE: u16 = 0;
/// Reserved coefficient index for the literal `-1` (§9.2).
pub(crate) const BWD_COEFF_INDEX_NEG_ONE: u16 = 1;
/// Bank entry `i` is coefficient index `BWD_COEFF_INDEX_RESERVED + i`.
pub(crate) const BWD_COEFF_INDEX_RESERVED: u16 = 2;

// The wire format, tied to its authority in `gkr_eval_isa::bwd::coeff::encode`.
const _: () = {
    assert!(BWD_COEFF_HEADER_COEFFICIENT_BITS == HEADER_COEFFICIENT_BITS);
    assert!(BWD_COEFF_HEADER_COEFFICIENT_SHIFT == HEADER_COEFFICIENT_SHIFT);
    assert!(BWD_COEFF_HEADER_COEFFICIENT_MASK == HEADER_COEFFICIENT_MASK);
    assert!(BWD_COEFF_HEADER_OPCODE_BITS == HEADER_OPCODE_BITS);
    assert!(BWD_COEFF_HEADER_OPCODE_SHIFT == HEADER_OPCODE_SHIFT);
    assert!(BWD_COEFF_HEADER_OPCODE_MASK == HEADER_OPCODE_MASK);
    assert!(BWD_COEFF_HEADER_COEFFICIENT_BITS + BWD_COEFF_HEADER_OPCODE_BITS == 16);

    assert!(BWD_COEFF_INPUT_MODE_SHIFT == INPUT_MODE_SHIFT);
    assert!(BWD_COEFF_INPUT_MODE_MASK == INPUT_MODE_MASK);
    assert!(BWD_COEFF_INPUT_FIRST_ACCESS_SHIFT == INPUT_FIRST_ACCESS_SHIFT);
    assert!(BWD_COEFF_INPUT_WINDOW_SHIFT == INPUT_WINDOW_SHIFT);
    assert!(BWD_COEFF_INPUT_WINDOW_MASK == INPUT_WINDOW_MASK);
    assert!(BWD_COEFF_INPUT_COLUMN_SHIFT == INPUT_COLUMN_SHIFT);
    assert!(BWD_COEFF_INPUT_COLUMN_MASK == INPUT_COLUMN_MASK);
    // The input word is exactly saturated, which is WHY a resident operand's
    // width comes from the opcode instead of from its window descriptor.
    assert!(BWD_COEFF_INPUT_COLUMN_SHIFT + 7 == 16);

    assert!(BWD_COEFF_LANE_BITS == LANE_BITS);
    assert!(BWD_COEFF_LANE_MASK == LANE_MASK);
    assert!(BWD_COEFF_LANES_PER_CELL == LANES_PER_CELL);
    assert!(BWD_COEFF_MIN_BUDGET_CELLS == CellBudget::MIN_CELLS as u32);
    assert!(BWD_COEFF_MAX_BUDGET_CELLS == CellBudget::MAX_CELLS as u32);
    // Six lane bits address the largest legal cell file exactly: c16 = 64 BF
    // lanes. `c16` is 64 BF lanes because a cell is four of them.
    assert!(
        BWD_COEFF_LANE_MASK as u32 + 1 == BWD_COEFF_MAX_BUDGET_CELLS * BWD_COEFF_LANES_PER_CELL
    );

    assert!(BWD_COEFF_CELL_ENDPOINT0_LANE_SHIFT == CELL_ENDPOINT0_LANE_SHIFT);
    assert!(BWD_COEFF_CELL_DELTA_LANE_SHIFT == CELL_DELTA_LANE_SHIFT);
    assert!(BWD_COEFF_PLAN_ENDPOINT0_ACTION_SHIFT == PLAN_ENDPOINT0_ACTION_SHIFT);
    assert!(BWD_COEFF_PLAN_ENDPOINT0_LANE_SHIFT == PLAN_ENDPOINT0_LANE_SHIFT);
    assert!(BWD_COEFF_PLAN_DELTA_ACTION_SHIFT == PLAN_DELTA_ACTION_SHIFT);
    assert!(BWD_COEFF_PLAN_DELTA_LANE_SHIFT == PLAN_DELTA_LANE_SHIFT);
    assert!(BWD_COEFF_PLAN_ACTION_MASK == PLAN_ACTION_MASK);
    assert!(BWD_COEFF_LANE_WORD_SHIFT == LANE_WORD_SHIFT);
    // The pair-carrying words share ONE lane geometry on purpose: a decoder
    // needs one pair-of-lanes extractor, not two.
    assert!(BWD_COEFF_CELL_ENDPOINT0_LANE_SHIFT == BWD_COEFF_PLAN_ENDPOINT0_LANE_SHIFT);
    assert!(BWD_COEFF_CELL_DELTA_LANE_SHIFT == BWD_COEFF_PLAN_DELTA_LANE_SHIFT);

    assert!(BWD_COEFF_MODE_DIRECT_SOURCE == MODE_DIRECT_SOURCE);
    assert!(BWD_COEFF_MODE_CELL == MODE_CELL);
    assert!(BWD_COEFF_MODE_FILL_SOURCE == MODE_FILL_SOURCE);
    assert!(BWD_COEFF_MODE_PLANNED_SOURCE == MODE_PLANNED_SOURCE);
    assert!(BWD_COEFF_ACTION_DIRECT == ACTION_DIRECT);
    assert!(BWD_COEFF_ACTION_USE_RESIDENT == ACTION_USE_RESIDENT);
    assert!(BWD_COEFF_ACTION_FILL == ACTION_FILL);
    assert!(BWD_COEFF_ACTION_INVALID == ACTION_INVALID);
    // The four modes and the four actions exactly cover their two bits.
    assert!(BWD_COEFF_MODE_PLANNED_SOURCE == BWD_COEFF_INPUT_MODE_MASK);
    assert!(BWD_COEFF_ACTION_INVALID == BWD_COEFF_PLAN_ACTION_MASK);

    assert!(BWD_COEFF_MAX_ENCODABLE_SOURCE_WINDOWS == MAX_SOURCE_WINDOWS);
    assert!(BWD_COEFF_SOURCE_WINDOW_COLUMNS == SOURCE_WINDOW_COLUMNS);
    assert!(BWD_COEFF_MAX_COEFFICIENT_ENCODINGS == MAX_COEFFICIENT_ENCODINGS);
    assert!(BWD_COEFF_MAX_ENCODABLE_SOURCE_WINDOWS == BWD_COEFF_INPUT_WINDOW_MASK as usize + 1);
    assert!(BWD_COEFF_SOURCE_WINDOW_COLUMNS == BWD_COEFF_INPUT_COLUMN_MASK as usize + 1);
    assert!(BWD_COEFF_MAX_COEFFICIENT_ENCODINGS == 1 << BWD_COEFF_HEADER_COEFFICIENT_BITS);
    // The measured window maximum must fit the coordinate that encodes it.
    assert!(BWD_COEFF_SOURCE_WINDOW_CAP <= BWD_COEFF_MAX_ENCODABLE_SOURCE_WINDOWS);

    assert!(BWD_COEFF_INDEX_ONE as u32 == CoefficientRecipeId::ONE.0);
    assert!(BWD_COEFF_INDEX_NEG_ONE as u32 == CoefficientRecipeId::NEG_ONE.0);
    assert!(BWD_COEFF_INDEX_RESERVED as u32 == CoefficientRecipeId::RESERVED);
};

// ── ABI FACT 1: bit 2 is a MODE-DISCRIMINATED OVERLAY ────────────────────────
//
// One physical bit means four different things depending on which of the six
// word forms it sits in, and the FORM is fixed by the opcode plus (for an
// extension word) the preceding input word's mode — never by the word's own
// content:
//
// ```text
// source-bearing input word   bit 2 = first_access          (window at 3..8)
// cell word (either form)     bit 2 = Endpoint0 lane bit 0  (lane   at 2..7)
// plan word                   bit 2 = Endpoint0 lane bit 0  (lane   at 2..7)
// bare lane word              bit 2 = lane bit 2            (lane   at 0..5)
// ```
//
// A decoder that extracts `first_access` BEFORE dispatching on the mode reads a
// lane bit as a materialization flag. The collision is pinned here so it cannot
// be "fixed" into a non-overlapping layout on one side only.
const _: () = {
    assert!(BWD_COEFF_INPUT_FIRST_ACCESS_SHIFT == BWD_COEFF_CELL_ENDPOINT0_LANE_SHIFT);
    assert!(BWD_COEFF_INPUT_FIRST_ACCESS_SHIFT == BWD_COEFF_PLAN_ENDPOINT0_LANE_SHIFT);
    assert!(BWD_COEFF_INPUT_FIRST_ACCESS_SHIFT >= BWD_COEFF_LANE_WORD_SHIFT);
    assert!(BWD_COEFF_INPUT_FIRST_ACCESS_SHIFT < BWD_COEFF_LANE_WORD_SHIFT + BWD_COEFF_LANE_BITS);
    // ... and it is genuinely an overlay, not an accident of a spare bit: the
    // window field starts one bit above it in the only form that reads it as a
    // flag.
    assert!(BWD_COEFF_INPUT_WINDOW_SHIFT == BWD_COEFF_INPUT_FIRST_ACCESS_SHIFT + 1);
};

// ── Frozen opcode tables (§6, §9.2) ──────────────────────────────────────────

pub(crate) const BWD_COEFF_R0_OP_C0_LINEAR_BF: u16 = 0;
pub(crate) const BWD_COEFF_R0_OP_C0_LINEAR_E4: u16 = 1;
pub(crate) const BWD_COEFF_R0_OP_C2_PRODUCT_BF_BF: u16 = 2;
pub(crate) const BWD_COEFF_R0_OP_C2_PRODUCT_BF_E4: u16 = 3;
pub(crate) const BWD_COEFF_R0_OP_C2_PRODUCT_E4_E4: u16 = 4;
pub(crate) const BWD_COEFF_R0_OP_MOVE_BF: u16 = 5;
pub(crate) const BWD_COEFF_R0_OP_MOVE_E4: u16 = 6;
pub(crate) const BWD_COEFF_R0_LIVE_OPCODES: usize = 7;

pub(crate) const BWD_COEFF_EXT_OP_C0_LINEAR_E4: u16 = 0;
pub(crate) const BWD_COEFF_EXT_OP_DUAL_PRODUCT_E4: u16 = 1;
pub(crate) const BWD_COEFF_EXT_OP_MOVE_E4: u16 = 2;
pub(crate) const BWD_COEFF_EXT_LIVE_OPCODES: usize = 3;

/// The frozen R0 opcode of `category`. Panicking rather than `Option` so the
/// const assertions below read as equalities; a category with no R0 encoding is
/// a compile error at the call site, not a runtime `None`.
const fn r0_op(category: TermCategory) -> u16 {
    match r0_opcode(category) {
        Some(opcode) => opcode,
        None => panic!("category has no R0 opcode"),
    }
}

/// The frozen continuation opcode of `category`; see [`r0_op`].
const fn ext_op(category: TermCategory) -> u16 {
    match continuation_opcode(category) {
        Some(opcode) => opcode,
        None => panic!("category has no continuation opcode"),
    }
}

const _: () = {
    assert!(BWD_COEFF_R0_OP_C0_LINEAR_BF == r0_op(TermCategory::C0LinearBf));
    assert!(BWD_COEFF_R0_OP_C0_LINEAR_E4 == r0_op(TermCategory::C0LinearE4));
    assert!(BWD_COEFF_R0_OP_C2_PRODUCT_BF_BF == r0_op(TermCategory::C2ProductBfBf));
    assert!(BWD_COEFF_R0_OP_C2_PRODUCT_BF_E4 == r0_op(TermCategory::C2ProductBfE4));
    assert!(BWD_COEFF_R0_OP_C2_PRODUCT_E4_E4 == r0_op(TermCategory::C2ProductE4E4));
    assert!(BWD_COEFF_R0_OP_MOVE_BF == r0_op(TermCategory::MoveBf));
    assert!(BWD_COEFF_R0_OP_MOVE_E4 == r0_op(TermCategory::MoveE4));
    // R0 has no native dual factor, and opcode 7 stays unallocated.
    assert!(r0_opcode(TermCategory::DualProductE4).is_none());
    assert!(BWD_COEFF_R0_LIVE_OPCODES == gkr_eval_isa::bwd::coeff::limits::R0_LIVE_OPCODES);
    assert!(BWD_COEFF_R0_LIVE_OPCODES <= BWD_COEFF_HEADER_OPCODE_MASK as usize + 1);

    assert!(BWD_COEFF_EXT_OP_C0_LINEAR_E4 == ext_op(TermCategory::C0LinearE4));
    assert!(BWD_COEFF_EXT_OP_DUAL_PRODUCT_E4 == ext_op(TermCategory::DualProductE4));
    assert!(BWD_COEFF_EXT_OP_MOVE_E4 == ext_op(TermCategory::MoveE4));
    // Continuation lowering emits ONLY C0Linear and native DualProduct, so a
    // standalone continuation product is a structural error, not an opcode.
    assert!(continuation_opcode(TermCategory::C0LinearBf).is_none());
    assert!(continuation_opcode(TermCategory::C2ProductBfBf).is_none());
    assert!(continuation_opcode(TermCategory::C2ProductBfE4).is_none());
    assert!(continuation_opcode(TermCategory::C2ProductE4E4).is_none());
    assert!(continuation_opcode(TermCategory::MoveBf).is_none());
    assert!(in_scope::MAX_CONTINUATION_STANDALONE_PRODUCTS == 0);
    assert!(
        BWD_COEFF_EXT_LIVE_OPCODES == gkr_eval_isa::bwd::coeff::limits::CONTINUATION_LIVE_OPCODES
    );
    assert!(BWD_COEFF_EXT_LIVE_OPCODES <= BWD_COEFF_HEADER_OPCODE_MASK as usize + 1);
};

// ── Operand shape: arity, role and per-position width (§6, §9.1) ─────────────
//
// The CUDA half decodes an operand's WIDTH from `(opcode, position)` and from
// nothing else — a resident `Cell` operand carries no window, so its width
// cannot come from a source descriptor, and even a source-bearing operand's
// width is not its window's backing field (a continuation program folds a base
// matrix into E4). These mirrors exist so the device's opcode-shape table is
// pinned against `gkr_eval_isa`'s, not merely against a comment.

pub(crate) const BWD_COEFF_ROLE_ENDPOINT0: u32 = 0;
pub(crate) const BWD_COEFF_ROLE_DELTA: u32 = 1;
pub(crate) const BWD_COEFF_ROLE_PAIR: u32 = 2;
/// Not a role: the opcode is a standalone cell-file move (§9.6), whose two
/// words are bare lanes rather than input records.
pub(crate) const BWD_COEFF_ROLE_MOVE: u32 = 3;

/// Both opcode tables are dense from zero, so liveness is one comparison.
pub(crate) const fn bwd_coeff_opcode_is_live(regime_is_r0: bool, opcode: u16) -> bool {
    (opcode as usize)
        < if regime_is_r0 {
            BWD_COEFF_R0_LIVE_OPCODES
        } else {
            BWD_COEFF_EXT_LIVE_OPCODES
        }
}

pub(crate) const fn bwd_coeff_is_move(regime_is_r0: bool, opcode: u16) -> bool {
    if regime_is_r0 {
        opcode == BWD_COEFF_R0_OP_MOVE_BF || opcode == BWD_COEFF_R0_OP_MOVE_E4
    } else {
        opcode == BWD_COEFF_EXT_OP_MOVE_E4
    }
}

/// The width a move relocates: §9.6 puts it on the OPCODE, since both operands
/// are bare six-bit BF lanes either way.
pub(crate) const fn bwd_coeff_move_is_e4(regime_is_r0: bool, opcode: u16) -> bool {
    if regime_is_r0 {
        opcode == BWD_COEFF_R0_OP_MOVE_E4
    } else {
        opcode == BWD_COEFF_EXT_OP_MOVE_E4
    }
}

pub(crate) const fn bwd_coeff_role(regime_is_r0: bool, opcode: u16) -> u32 {
    if bwd_coeff_is_move(regime_is_r0, opcode) {
        return BWD_COEFF_ROLE_MOVE;
    }
    if regime_is_r0 {
        if opcode == BWD_COEFF_R0_OP_C0_LINEAR_BF || opcode == BWD_COEFF_R0_OP_C0_LINEAR_E4 {
            BWD_COEFF_ROLE_ENDPOINT0
        } else {
            BWD_COEFF_ROLE_DELTA
        }
    } else if opcode == BWD_COEFF_EXT_OP_C0_LINEAR_E4 {
        BWD_COEFF_ROLE_ENDPOINT0
    } else {
        BWD_COEFF_ROLE_PAIR
    }
}

/// Input RECORDS the opcode carries (§9.1); zero for a move.
pub(crate) const fn bwd_coeff_arity(regime_is_r0: bool, opcode: u16) -> usize {
    match bwd_coeff_role(regime_is_r0, opcode) {
        BWD_COEFF_ROLE_MOVE => 0,
        BWD_COEFF_ROLE_ENDPOINT0 => 1,
        _ => 2,
    }
}

/// Storage width of operand `position`: `true` = E4. Only meaningful below the
/// opcode's arity.
pub(crate) const fn bwd_coeff_operand_is_e4(
    regime_is_r0: bool,
    opcode: u16,
    position: usize,
) -> bool {
    if !regime_is_r0 {
        // Every live continuation operand is E4.
        return true;
    }
    match opcode {
        BWD_COEFF_R0_OP_C0_LINEAR_E4 | BWD_COEFF_R0_OP_C2_PRODUCT_E4_E4 => true,
        BWD_COEFF_R0_OP_C2_PRODUCT_BF_E4 => position == 1,
        _ => false,
    }
}

const _: () = {
    use gkr_eval_isa::bwd::coeff::encode::{
        category_arity, category_role, is_move, move_width, operand_width, OperandRole,
    };
    use gkr_eval_isa::bwd::coeff::schedule::ValueWidth;

    /// The mirror's answers for one `(regime, opcode)`, against `gkr_eval_isa`'s
    /// for the category that opcode names.
    const fn check(regime_is_r0: bool, opcode: u16, category: TermCategory) {
        assert!(bwd_coeff_opcode_is_live(regime_is_r0, opcode));
        assert!(bwd_coeff_is_move(regime_is_r0, opcode) == is_move(category));
        let role = bwd_coeff_role(regime_is_r0, opcode);
        match category_role(category) {
            None => assert!(role == BWD_COEFF_ROLE_MOVE),
            Some(OperandRole::Endpoint0) => assert!(role == BWD_COEFF_ROLE_ENDPOINT0),
            Some(OperandRole::Delta) => assert!(role == BWD_COEFF_ROLE_DELTA),
            Some(OperandRole::Pair) => assert!(role == BWD_COEFF_ROLE_PAIR),
        }
        let arity = bwd_coeff_arity(regime_is_r0, opcode);
        assert!(arity == category_arity(category));
        match move_width(category) {
            None => assert!(!bwd_coeff_is_move(regime_is_r0, opcode)),
            Some(width) => assert!(
                bwd_coeff_move_is_e4(regime_is_r0, opcode) == matches!(width, ValueWidth::E4)
            ),
        }
        let mut position = 0;
        while position < arity {
            let is_e4 = bwd_coeff_operand_is_e4(regime_is_r0, opcode, position);
            match operand_width(category, position) {
                Some(ValueWidth::E4) => assert!(is_e4),
                Some(ValueWidth::Bf) => assert!(!is_e4),
                None => panic!("arity bounds the position"),
            }
            position += 1;
        }
    }

    check(true, BWD_COEFF_R0_OP_C0_LINEAR_BF, TermCategory::C0LinearBf);
    check(true, BWD_COEFF_R0_OP_C0_LINEAR_E4, TermCategory::C0LinearE4);
    check(
        true,
        BWD_COEFF_R0_OP_C2_PRODUCT_BF_BF,
        TermCategory::C2ProductBfBf,
    );
    check(
        true,
        BWD_COEFF_R0_OP_C2_PRODUCT_BF_E4,
        TermCategory::C2ProductBfE4,
    );
    check(
        true,
        BWD_COEFF_R0_OP_C2_PRODUCT_E4_E4,
        TermCategory::C2ProductE4E4,
    );
    check(true, BWD_COEFF_R0_OP_MOVE_BF, TermCategory::MoveBf);
    check(true, BWD_COEFF_R0_OP_MOVE_E4, TermCategory::MoveE4);
    check(
        false,
        BWD_COEFF_EXT_OP_C0_LINEAR_E4,
        TermCategory::C0LinearE4,
    );
    check(
        false,
        BWD_COEFF_EXT_OP_DUAL_PRODUCT_E4,
        TermCategory::DualProductE4,
    );
    check(false, BWD_COEFF_EXT_OP_MOVE_E4, TermCategory::MoveE4);

    // The dead slots stay dead on this side too.
    assert!(!bwd_coeff_opcode_is_live(true, 7));
    assert!(!bwd_coeff_opcode_is_live(false, 3));
};

// ── ABI FACT 2: the packed pair `Cell` form is OPCODE-SCOPED ─────────────────

/// Whether a `Cell` word under this `(regime, opcode)` reads bits 10..15 as a
/// packed `Delta` lane.
///
/// `DualProductE4` — and only `DualProductE4` — does. Under every other opcode
/// those bits are reserved and MUST be zero, so a `Cell` word naming lane 0 with
/// a nonzero high payload is a REJECTED program, not a pair. There is no tag in
/// the word: the opcode is the only discriminator, which is why this predicate
/// takes one and why no decode site may sniff the payload instead. Mirrored by
/// `bwd_coeff_cell_word_is_pair_form` in `coefficient_vm.cuh`.
pub(crate) const fn bwd_coeff_cell_word_is_pair_form(regime_is_r0: bool, opcode: u16) -> bool {
    !regime_is_r0 && opcode == BWD_COEFF_EXT_OP_DUAL_PRODUCT_E4
}

const _: () = {
    assert!(bwd_coeff_cell_word_is_pair_form(
        false,
        BWD_COEFF_EXT_OP_DUAL_PRODUCT_E4
    ));
    assert!(!bwd_coeff_cell_word_is_pair_form(
        false,
        BWD_COEFF_EXT_OP_C0_LINEAR_E4
    ));
    assert!(!bwd_coeff_cell_word_is_pair_form(
        false,
        BWD_COEFF_EXT_OP_MOVE_E4
    ));
    // R0 has no native dual factor. In particular an R0 opcode that happens to
    // be numerically equal to the continuation dual opcode is NOT a pair form.
    assert!(!bwd_coeff_cell_word_is_pair_form(
        true,
        BWD_COEFF_R0_OP_C0_LINEAR_E4
    ));
    assert!(!bwd_coeff_cell_word_is_pair_form(
        true,
        BWD_COEFF_R0_OP_C2_PRODUCT_E4_E4
    ));
};

// ── Source-window origin (§10.2) ─────────────────────────────────────────────

/// Window origin: a base-field matrix backing.
pub(crate) const BWD_COEFF_ORIGIN_READ_BASE: u8 = 0;
/// Window origin: an extension-field matrix backing.
pub(crate) const BWD_COEFF_ORIGIN_READ_EXT: u8 = 1;
/// Window origin: a procedurally produced (virtual-setup) source. Row-dependent
/// and never materialized from a matrix.
pub(crate) const BWD_COEFF_ORIGIN_PROCEDURAL: u8 = 2;

pub(crate) const BWD_COEFF_PROCEDURAL_RANGE_CHECK_16_BITS: u8 = 0;
pub(crate) const BWD_COEFF_PROCEDURAL_RANGE_CHECK_TIMESTAMP: u8 = 1;
pub(crate) const BWD_COEFF_PROCEDURAL_INITS_AND_TEARDOWNS_LOW: u8 = 2;
pub(crate) const BWD_COEFF_PROCEDURAL_INITS_AND_TEARDOWNS_HIGH: u8 = 3;
/// A window whose origin is a real matrix carries no procedural kind. Zero would
/// alias [`BWD_COEFF_PROCEDURAL_RANGE_CHECK_16_BITS`], so the absent marker is
/// `0xff` and [`BwdCoeffSourceWindow::default`] uses it.
pub(crate) const BWD_COEFF_PROCEDURAL_NONE: u8 = 0xff;
/// Procedural kinds the format admits.
pub(crate) const BWD_COEFF_PROCEDURAL_KINDS: usize = 4;

/// §10.2's static materialization policy: publish on first physical access iff
/// `target_depth >= BWD_COEFF_PUBLISH_TARGET_DEPTH`. One tunable constant, not
/// a scheduling decision or a genome.
pub(crate) const BWD_COEFF_PUBLISH_TARGET_DEPTH: u8 = 3;

const _: () = {
    use crate::upstream::VirtualSetupKind::*;
    assert!(BWD_COEFF_PROCEDURAL_KINDS == KIND_ORDER.len());
    assert!(matches!(
        KIND_ORDER[BWD_COEFF_PROCEDURAL_RANGE_CHECK_16_BITS as usize],
        RangeCheck16Bits
    ));
    assert!(matches!(
        KIND_ORDER[BWD_COEFF_PROCEDURAL_RANGE_CHECK_TIMESTAMP as usize],
        RangeCheckTimestamp
    ));
    assert!(matches!(
        KIND_ORDER[BWD_COEFF_PROCEDURAL_INITS_AND_TEARDOWNS_LOW as usize],
        InitsAndTeardownsLow
    ));
    assert!(matches!(
        KIND_ORDER[BWD_COEFF_PROCEDURAL_INITS_AND_TEARDOWNS_HIGH as usize],
        InitsAndTeardownsHigh
    ));
    assert!(BWD_COEFF_PROCEDURAL_NONE as usize >= BWD_COEFF_PROCEDURAL_KINDS);
    assert!(BWD_COEFF_PUBLISH_TARGET_DEPTH == PUBLISH_TARGET_DEPTH);
};

// ── Launch geometry (§11) ────────────────────────────────────────────────────

/// ONE thread per logical row, [`BWD_COEFF_ROWS_PER_BLOCK`] rows per block.
/// There is no two-half role split, no shuffle and no paired-lane scheme.
pub(crate) const BWD_COEFF_THREADS_PER_BLOCK: u32 = 128;
/// Logical rows one block evaluates. Equal to the block width by construction.
pub(crate) const BWD_COEFF_ROWS_PER_BLOCK: u32 = BWD_COEFF_THREADS_PER_BLOCK;
pub(crate) const BWD_COEFF_WARP_LANES: u32 = 32;
pub(crate) const BWD_COEFF_FOLD_FACTOR_CAP: usize = 10;
/// D0..D3: the bounded lazy-fold depths the resolver retains.
pub(crate) const BWD_COEFF_MAX_FOLD_DEPTH: u8 = 3;

/// The descriptor-only sentinel meaning "this layer has no `c_init`" (§5.3).
///
/// It is NOT a program coefficient encoding: thirteen coefficient bits top out
/// at [`BWD_COEFF_MAX_COEFFICIENT_ENCODINGS`] `- 1`, so no header can ever name
/// it. Asserted below so nobody later reads it as one.
pub(crate) const BWD_COEFF_C_INIT_NONE: u16 = u16::MAX;

const _: () = {
    assert!(BWD_COEFF_THREADS_PER_BLOCK % BWD_COEFF_WARP_LANES == 0);
    assert!(BWD_COEFF_ROWS_PER_BLOCK == BWD_COEFF_THREADS_PER_BLOCK);
    assert!(BWD_COEFF_C_INIT_NONE == u16::MAX);
    assert!(BWD_COEFF_MAX_COEFFICIENT_ENCODINGS - 1 < BWD_COEFF_C_INIT_NONE as usize);
};

// ── Descriptor ───────────────────────────────────────────────────────────────

/// One live source window (§10.2): read backing and stride, publish backing and
/// stride, backing depth, target depth, origin field, materialize flag, and the
/// procedural source kind where applicable.
///
/// A window covers at most [`BWD_COEFF_SOURCE_WINDOW_COLUMNS`] contiguous
/// referenced columns of ONE logical backing. `read_base` / `publish_base`
/// already point at the window's FIRST column, so a bound coordinate resolves to
/// `read_base + column * read_stride_bytes`.
///
/// `origin` is the BACKING field, not the width of the values read through the
/// window: a continuation program folds a base matrix into E4, and operand width
/// comes from the opcode.
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub(crate) struct BwdCoeffSourceWindow {
    pub read_base: *const u8,
    pub publish_base: *mut u8,
    pub read_stride_bytes: u32,
    pub publish_stride_bytes: u32,
    pub backing_depth: u8,
    pub target_depth: u8,
    pub origin: u8,
    pub materialize: u8,
    pub procedural_kind: u8,
    pub reserved: [u8; 3],
}

impl Default for BwdCoeffSourceWindow {
    /// A dead slot. `procedural_kind` is [`BWD_COEFF_PROCEDURAL_NONE`], NOT
    /// zero — zero is a live kind.
    fn default() -> Self {
        Self {
            read_base: std::ptr::null(),
            publish_base: std::ptr::null_mut(),
            read_stride_bytes: 0,
            publish_stride_bytes: 0,
            backing_depth: 0,
            target_depth: 0,
            origin: BWD_COEFF_ORIGIN_READ_BASE,
            materialize: 0,
            procedural_kind: BWD_COEFF_PROCEDURAL_NONE,
            reserved: [0; 3],
        }
    }
}

/// The complete by-value launch descriptor, passed as a single
/// `__grid_constant__` kernel parameter.
///
/// `program` is embedded, never pointed to (§9.1). The one pointer to
/// coefficient DATA is the sanctioned exception: it is read only by the
/// `DevicePointer` bank specialization and ignored by the `Constant` one.
#[repr(C, align(16))]
#[derive(Clone, Copy)]
pub(crate) struct BwdCoeffDesc {
    /// Evaluated E4 coefficients for the `DevicePointer` bank specialization.
    /// The `Constant` specialization ignores it.
    pub coefficients: *const E4,
    pub round_challenges: *const E4,
    /// Production factored-eq low table; high tables remain in `ab_gkr_eq_high`.
    pub eq_low: *const E4,
    /// `2 * logical_rows` entries: `eq * acc_c0` in `[0, logical_rows)` and
    /// `eq * acc_c2` in `[logical_rows, 2 * logical_rows)`.
    pub contributions: *mut E4,
    pub source_windows: [BwdCoeffSourceWindow; BWD_COEFF_SOURCE_WINDOW_CAP],
    pub eq_sizes: GkrEqSizes,
    /// u16 words of `program` this launch executes. There is no end opcode.
    pub num_words: u32,
    pub n_source_windows: u32,
    pub n_round_challenges: u32,
    /// Bank entries behind [`BWD_COEFF_INDEX_RESERVED`].
    pub n_coefficients: u32,
    /// Rows this launch evaluates, one per thread. Also the contribution
    /// half-stride: the incumbent `acc_size`.
    pub logical_rows: u32,
    /// Private cell file per thread, in E4 cells (c2..c16). Dynamic shared
    /// memory is exactly `cell_budget * size_of::<E4>() * threads_per_block`.
    pub cell_budget: u32,
    /// Coefficient index of the per-thread `acc_c0` initializer, or
    /// [`BWD_COEFF_C_INIT_NONE`].
    pub c_init: u16,
    /// Explicit: keeps `program` 16-byte aligned. Never read by the kernel.
    pub pad: [u16; 5],
    pub program: [u16; BWD_COEFF_PROGRAM_WORD_CAP],
}

impl BwdCoeffDesc {
    /// An empty descriptor: null pointers, no windows, no program.
    ///
    /// `[u16; BWD_COEFF_PROGRAM_WORD_CAP]` is far past the arity `Default` is
    /// derived for, so this is written out rather than derived.
    pub(crate) fn empty() -> Self {
        Self {
            coefficients: std::ptr::null(),
            round_challenges: std::ptr::null(),
            eq_low: std::ptr::null(),
            contributions: std::ptr::null_mut(),
            source_windows: [BwdCoeffSourceWindow::default(); BWD_COEFF_SOURCE_WINDOW_CAP],
            eq_sizes: GkrEqSizes::zeroed(),
            num_words: 0,
            n_source_windows: 0,
            n_round_challenges: 0,
            n_coefficients: 0,
            logical_rows: 0,
            cell_budget: 0,
            c_init: BWD_COEFF_C_INIT_NONE,
            pad: [0; 5],
            program: [0; BWD_COEFF_PROGRAM_WORD_CAP],
        }
    }
}

// The layout, pinned against the same literals `coefficient_vm.cuh`
// `static_assert`s. A change to either struct fails one of the two builds.
const _: () = {
    use core::mem::{align_of, offset_of, size_of};

    assert!(size_of::<BwdCoeffSourceWindow>() == 32);
    assert!(align_of::<BwdCoeffSourceWindow>() == 8);
    assert!(offset_of!(BwdCoeffSourceWindow, read_base) == 0);
    assert!(offset_of!(BwdCoeffSourceWindow, publish_base) == 8);
    assert!(offset_of!(BwdCoeffSourceWindow, read_stride_bytes) == 16);
    assert!(offset_of!(BwdCoeffSourceWindow, publish_stride_bytes) == 20);
    assert!(offset_of!(BwdCoeffSourceWindow, backing_depth) == 24);
    assert!(offset_of!(BwdCoeffSourceWindow, target_depth) == 25);
    assert!(offset_of!(BwdCoeffSourceWindow, origin) == 26);
    assert!(offset_of!(BwdCoeffSourceWindow, materialize) == 27);
    assert!(offset_of!(BwdCoeffSourceWindow, procedural_kind) == 28);
    assert!(offset_of!(BwdCoeffSourceWindow, reserved) == 29);

    assert!(size_of::<BwdCoeffDesc>() == 12_144);
    assert!(align_of::<BwdCoeffDesc>() == BWD_COEFF_DESC_ALIGN);
    // The FINAL authority on the descriptor's shape (§9.1).
    assert!(size_of::<BwdCoeffDesc>() <= BWD_COEFF_DESC_CAP);
    assert!(offset_of!(BwdCoeffDesc, coefficients) == 0);
    assert!(offset_of!(BwdCoeffDesc, round_challenges) == 8);
    assert!(offset_of!(BwdCoeffDesc, eq_low) == 16);
    assert!(offset_of!(BwdCoeffDesc, contributions) == 24);
    assert!(offset_of!(BwdCoeffDesc, source_windows) == 32);
    assert!(offset_of!(BwdCoeffDesc, eq_sizes) == 576);
    assert!(offset_of!(BwdCoeffDesc, num_words) == 588);
    assert!(offset_of!(BwdCoeffDesc, n_source_windows) == 592);
    assert!(offset_of!(BwdCoeffDesc, n_round_challenges) == 596);
    assert!(offset_of!(BwdCoeffDesc, n_coefficients) == 600);
    assert!(offset_of!(BwdCoeffDesc, logical_rows) == 604);
    assert!(offset_of!(BwdCoeffDesc, cell_budget) == 608);
    assert!(offset_of!(BwdCoeffDesc, c_init) == 612);
    assert!(offset_of!(BwdCoeffDesc, pad) == 614);
    assert!(offset_of!(BwdCoeffDesc, program) == 624);
    // The whole point of the 16-byte descriptor alignment: the program stream
    // starts on a 16-byte boundary and can be buffered through wide loads.
    assert!(offset_of!(BwdCoeffDesc, program) % BWD_COEFF_DESC_ALIGN == 0);
    // The program is the descriptor's tail: nothing follows it, so its size and
    // the descriptor's size move together.
    assert!(
        size_of::<BwdCoeffDesc>() == offset_of!(BwdCoeffDesc, program) + BWD_COEFF_PROGRAM_BYTE_CAP
    );
};
