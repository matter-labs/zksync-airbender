#pragma once

// Backward coefficient-term ISA: the by-value launch descriptor and the frozen
// u16 wire format (design sections 9, 10.2 and 11).
//
// THIS FILE IS ONE HALF OF AN ABI. Every constant, field, offset and size below
// is mirrored by Rust `BwdCoeffDesc` in
// `src/prover/gkr/backward/vm/desc.rs`, which carries the same numeric literals
// under `const _: () = assert!(...)` and additionally ties each of them to its
// authority in the `gkr_eval_isa` crate:
//
//   * the opcode numbers to `bwd::coeff::limits::{R0,CONTINUATION}_OPCODE_TABLE`;
//   * the shifts/masks/modes/actions to `bwd::coeff::encode`; and
//   * the two array capacities to `bwd::coeff::limits::in_scope`.
//
// Nothing here may change without changing the Rust side in the same commit;
// both sides fail to BUILD (not to test) when they disagree.
//
// The program stream is embedded BY VALUE. There is no device program pointer,
// no format version and no compatibility path (section 9.1).

#include "flat.cuh"

namespace airbender::prover::gkr {

// ── By-value capacities (section 9.1, Task 8's measured corpus maxima) ───────

// `gkr_eval_isa::bwd::coeff::limits::KERNEL_ARGUMENT_CEILING_BYTES`.
constexpr u32 BWD_COEFF_DESC_CAP = 32764;
// `gkr_eval_isa::bwd::coeff::limits::DESCRIPTOR_ALIGNMENT_BYTES`. Load-bearing:
// it is what puts `bwd_coeff_desc::program` on a 16-byte boundary so the stream
// may be buffered through aligned wide loads (section 9.1).
constexpr u32 BWD_COEFF_DESC_ALIGN = 16;
// `in_scope::MAX_SOURCE_WINDOWS_USED` — the EXACT measured corpus maximum, not
// the 64 the `source_window:6` coordinate can express. The encoding limit is
// asserted separately as BWD_COEFF_MAX_ENCODABLE_SOURCE_WINDOWS.
constexpr u32 BWD_COEFF_SOURCE_WINDOW_CAP = 17;
// `in_scope::DESCRIPTOR_PROGRAM_WORDS` — the measured maximum 5,759 words
// (`blake2_with_extended_control` L0 Ext at c3, NOT at c16: program length is
// not monotone in the budget) rounded up by exactly one word of 16-byte
// alignment. Not a headroom allowance.
constexpr u32 BWD_COEFF_PROGRAM_WORD_CAP = 5760;
constexpr u32 BWD_COEFF_PROGRAM_BYTE_CAP = 2 * BWD_COEFF_PROGRAM_WORD_CAP;

static_assert(BWD_COEFF_PROGRAM_BYTE_CAP == 11520, "program array byte size drift");
static_assert(BWD_COEFF_PROGRAM_BYTE_CAP % BWD_COEFF_DESC_ALIGN == 0, "program array is not a whole number of 16-byte quanta");

// ── Frozen wire format (section 9.2, 9.4, 9.5, 9.6) ─────────────────────────
//
// ```text
// header       [ opcode:3 @13 | coefficient:13 @0 ]
// input word   [ column:7 @9 | window:6 @3 | first_access:1 @2 | mode:2 @0 ]
// cell single  [ 0:8 @8 | lane:6 @2 | mode:2 @0 ]
// cell pair    [ delta_lane:6 @10 | 0:2 @8 | e0_lane:6 @2 | mode:2 @0 ]
// plan word    [ delta_lane:6 @10 | delta_act:2 @8 | e0_lane:6 @2 | e0_act:2 @0 ]
// lane word    [ 0:10 @6 | lane:6 @0 ]
// ```

constexpr u32 BWD_COEFF_HEADER_COEFFICIENT_BITS = 13;
constexpr u32 BWD_COEFF_HEADER_COEFFICIENT_SHIFT = 0;
constexpr u16 BWD_COEFF_HEADER_COEFFICIENT_MASK = (1u << BWD_COEFF_HEADER_COEFFICIENT_BITS) - 1;
constexpr u32 BWD_COEFF_HEADER_OPCODE_BITS = 3;
constexpr u32 BWD_COEFF_HEADER_OPCODE_SHIFT = BWD_COEFF_HEADER_COEFFICIENT_BITS;
constexpr u16 BWD_COEFF_HEADER_OPCODE_MASK = (1u << BWD_COEFF_HEADER_OPCODE_BITS) - 1;

static_assert(BWD_COEFF_HEADER_COEFFICIENT_BITS + BWD_COEFF_HEADER_OPCODE_BITS == 16, "the header must be exactly saturated");
static_assert(BWD_COEFF_HEADER_COEFFICIENT_MASK == 0x1fffu, "header coefficient mask drift");
// Derived, so it cannot drift on its own — but a DE-derivation to a literal
// would pass every other check here, so pin the value too.
static_assert(BWD_COEFF_HEADER_OPCODE_SHIFT == 13, "header opcode shift drift");
static_assert(BWD_COEFF_HEADER_OPCODE_MASK == 0x7u, "header opcode mask drift");

// Reserved coefficient indices (section 9.2). `CoefficientRecipeId::{ONE,
// NEG_ONE, RESERVED}`: index 0 is `+1`, index 1 is `-1`, and bank entry `i` is
// index `RESERVED + i`. Zero is not an instruction coefficient.
constexpr u16 BWD_COEFF_INDEX_ONE = 0;
constexpr u16 BWD_COEFF_INDEX_NEG_ONE = 1;
constexpr u16 BWD_COEFF_INDEX_RESERVED = 2;
// Coefficient encodings thirteen bits admit, INCLUDING the two reserved ones.
constexpr u32 BWD_COEFF_MAX_COEFFICIENT_ENCODINGS = 1u << BWD_COEFF_HEADER_COEFFICIENT_BITS;
static_assert(BWD_COEFF_MAX_COEFFICIENT_ENCODINGS == 8192, "coefficient encoding space drift");

constexpr u32 BWD_COEFF_INPUT_MODE_SHIFT = 0;
constexpr u16 BWD_COEFF_INPUT_MODE_MASK = 0x3;
constexpr u32 BWD_COEFF_INPUT_FIRST_ACCESS_SHIFT = 2;
constexpr u32 BWD_COEFF_INPUT_WINDOW_SHIFT = 3;
constexpr u16 BWD_COEFF_INPUT_WINDOW_MASK = 0x3f;
constexpr u32 BWD_COEFF_INPUT_COLUMN_SHIFT = 9;
constexpr u16 BWD_COEFF_INPUT_COLUMN_MASK = 0x7f;

// The input word is exactly saturated, which is WHY a resident operand's width
// has to come from the opcode rather than from its window.
static_assert(BWD_COEFF_INPUT_COLUMN_SHIFT + 7 == 16, "the input word must be exactly saturated");
// The coordinate can express 64 windows and 128 columns per window. These are
// ENCODING limits; the descriptor array is sized from the MEASURED maximum.
constexpr u32 BWD_COEFF_MAX_ENCODABLE_SOURCE_WINDOWS = BWD_COEFF_INPUT_WINDOW_MASK + 1;
constexpr u32 BWD_COEFF_SOURCE_WINDOW_COLUMNS = BWD_COEFF_INPUT_COLUMN_MASK + 1;
static_assert(BWD_COEFF_MAX_ENCODABLE_SOURCE_WINDOWS == 64, "source-window encoding limit drift");
static_assert(BWD_COEFF_SOURCE_WINDOW_COLUMNS == 128, "source-window column limit drift");
static_assert(BWD_COEFF_SOURCE_WINDOW_CAP <= BWD_COEFF_MAX_ENCODABLE_SOURCE_WINDOWS, "the measured window maximum must fit its encoding");

// Every physical index in the format is a six-bit BF lane; an E4 lane is
// four-aligned (sections 9.4, 9.6). Six bits address the largest legal cell
// file exactly: c16 = 16 cells * 4 lanes = 64 BF lanes.
constexpr u32 BWD_COEFF_LANE_BITS = 6;
constexpr u16 BWD_COEFF_LANE_MASK = (1u << BWD_COEFF_LANE_BITS) - 1;
constexpr u32 BWD_COEFF_LANES_PER_CELL = 4;
constexpr u32 BWD_COEFF_LANES_PER_CELL_LOG2 = 2;
static_assert(1u << BWD_COEFF_LANES_PER_CELL_LOG2 == BWD_COEFF_LANES_PER_CELL, "E4 cell lane count is not a power of two");
constexpr u32 BWD_COEFF_MIN_BUDGET_CELLS = 2;
constexpr u32 BWD_COEFF_MAX_BUDGET_CELLS = 16;
static_assert(BWD_COEFF_LANE_MASK + 1 == BWD_COEFF_MAX_BUDGET_CELLS * BWD_COEFF_LANES_PER_CELL, "six lane bits must address exactly the c16 cell file");

// Cell payload lanes (section 9.4 single form, section 9.5 packed pair form).
constexpr u32 BWD_COEFF_CELL_ENDPOINT0_LANE_SHIFT = 2;
constexpr u32 BWD_COEFF_CELL_DELTA_LANE_SHIFT = 10;
// Endpoint0/Delta plan word (section 9.5).
constexpr u32 BWD_COEFF_PLAN_ENDPOINT0_ACTION_SHIFT = 0;
constexpr u32 BWD_COEFF_PLAN_ENDPOINT0_LANE_SHIFT = 2;
constexpr u32 BWD_COEFF_PLAN_DELTA_ACTION_SHIFT = 8;
constexpr u32 BWD_COEFF_PLAN_DELTA_LANE_SHIFT = 10;
constexpr u16 BWD_COEFF_PLAN_ACTION_MASK = 0x3;
// A bare lane word: the `FillSource` destination AND both move operands.
constexpr u32 BWD_COEFF_LANE_WORD_SHIFT = 0;

// The pair-carrying words share ONE lane geometry on purpose: a decoder needs
// one pair-of-lanes extractor, not two.
static_assert(BWD_COEFF_CELL_ENDPOINT0_LANE_SHIFT == BWD_COEFF_PLAN_ENDPOINT0_LANE_SHIFT, "cell/plan Endpoint0 lane geometry diverged");
static_assert(BWD_COEFF_CELL_DELTA_LANE_SHIFT == BWD_COEFF_PLAN_DELTA_LANE_SHIFT, "cell/plan Delta lane geometry diverged");

// Input modes (section 9.4).
constexpr u16 BWD_COEFF_MODE_DIRECT_SOURCE = 0;
constexpr u16 BWD_COEFF_MODE_CELL = 1;
constexpr u16 BWD_COEFF_MODE_FILL_SOURCE = 2;
constexpr u16 BWD_COEFF_MODE_PLANNED_SOURCE = 3;
// Plan actions (section 9.5). `Invalid` is the format's fourth action and a
// valid program never contains it.
constexpr u16 BWD_COEFF_ACTION_DIRECT = 0;
constexpr u16 BWD_COEFF_ACTION_USE_RESIDENT = 1;
constexpr u16 BWD_COEFF_ACTION_FILL = 2;
constexpr u16 BWD_COEFF_ACTION_INVALID = 3;

static_assert(BWD_COEFF_MODE_PLANNED_SOURCE == BWD_COEFF_INPUT_MODE_MASK, "the four modes must exactly cover the two mode bits");
static_assert(BWD_COEFF_ACTION_INVALID == BWD_COEFF_PLAN_ACTION_MASK, "the four actions must exactly cover the two action bits");

// ── ABI FACT 1: bit 2 is a MODE-DISCRIMINATED OVERLAY ───────────────────────
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
// lane bit as a materialization flag. These static asserts pin the collision so
// the overlay cannot be "fixed" into a non-overlapping layout on one side only.
static_assert(BWD_COEFF_INPUT_FIRST_ACCESS_SHIFT == BWD_COEFF_CELL_ENDPOINT0_LANE_SHIFT,
              "first_access overlays Endpoint0 lane bit 0; the overlay is intentional and mode-discriminated");
static_assert(BWD_COEFF_INPUT_FIRST_ACCESS_SHIFT >= BWD_COEFF_LANE_WORD_SHIFT &&
                  BWD_COEFF_INPUT_FIRST_ACCESS_SHIFT < BWD_COEFF_LANE_WORD_SHIFT + BWD_COEFF_LANE_BITS,
              "first_access overlays a bare lane word's lane bit 2; the overlay is intentional and mode-discriminated");

// ── Frozen opcode tables (section 6, 9.2) ───────────────────────────────────
//
// R0 (`R0_OPCODE_TABLE`); opcode 7 is deliberately invalid — no uncensused
// category is pre-allocated.
constexpr u16 BWD_COEFF_R0_OP_C0_LINEAR_BF = 0;
constexpr u16 BWD_COEFF_R0_OP_C0_LINEAR_E4 = 1;
constexpr u16 BWD_COEFF_R0_OP_C2_PRODUCT_BF_BF = 2;
constexpr u16 BWD_COEFF_R0_OP_C2_PRODUCT_BF_E4 = 3;
constexpr u16 BWD_COEFF_R0_OP_C2_PRODUCT_E4_E4 = 4;
constexpr u16 BWD_COEFF_R0_OP_MOVE_BF = 5;
constexpr u16 BWD_COEFF_R0_OP_MOVE_E4 = 6;
constexpr u32 BWD_COEFF_R0_LIVE_OPCODES = 7;

// Continuation (`CONTINUATION_OPCODE_TABLE`); 3..7 stay invalid because the
// full-corpus census measured zero standalone continuation products.
constexpr u16 BWD_COEFF_EXT_OP_C0_LINEAR_E4 = 0;
constexpr u16 BWD_COEFF_EXT_OP_DUAL_PRODUCT_E4 = 1;
constexpr u16 BWD_COEFF_EXT_OP_MOVE_E4 = 2;
constexpr u32 BWD_COEFF_EXT_LIVE_OPCODES = 3;

static_assert(BWD_COEFF_R0_LIVE_OPCODES <= (BWD_COEFF_HEADER_OPCODE_MASK + 1u), "R0 opcode census exceeds three opcode bits");
static_assert(BWD_COEFF_EXT_LIVE_OPCODES <= (BWD_COEFF_HEADER_OPCODE_MASK + 1u), "continuation opcode census exceeds three opcode bits");

// ── ABI FACT 2: the packed pair `Cell` form is OPCODE-SCOPED ────────────────
//
// `DualProductE4` — and only `DualProductE4` — reads bits 10..15 of a `Cell`
// word as the `Delta` lane. Under every other opcode those bits are reserved
// and MUST be zero, so `Cell` lane 0 with a nonzero high payload is a rejected
// program, not a pair. There is no tag in the word: the OPCODE is the only
// discriminator, which is why this predicate takes one. Every `Cell` decode
// site must route through it rather than sniffing the payload.
constexpr bool bwd_coeff_cell_word_is_pair_form(const bool regime_is_r0, const u16 opcode) {
  return !regime_is_r0 && opcode == BWD_COEFF_EXT_OP_DUAL_PRODUCT_E4;
}

static_assert(bwd_coeff_cell_word_is_pair_form(false, BWD_COEFF_EXT_OP_DUAL_PRODUCT_E4), "the packed pair Cell form must be scoped to DualProductE4");
static_assert(!bwd_coeff_cell_word_is_pair_form(false, BWD_COEFF_EXT_OP_C0_LINEAR_E4), "only DualProductE4 may read a Cell word's high payload");
static_assert(!bwd_coeff_cell_word_is_pair_form(false, BWD_COEFF_EXT_OP_MOVE_E4), "only DualProductE4 may read a Cell word's high payload");
static_assert(!bwd_coeff_cell_word_is_pair_form(true, BWD_COEFF_R0_OP_C2_PRODUCT_E4_E4), "R0 has no native dual factor and therefore no packed pair Cell form");
// R0's DualProductE4 opcode does not exist; the value 1 is C0LinearE4 there.
static_assert(!bwd_coeff_cell_word_is_pair_form(true, BWD_COEFF_R0_OP_C0_LINEAR_E4),
              "an R0 opcode numerically equal to the continuation dual opcode is NOT a pair form");

// ── Operand shape: arity, role and per-position width (sections 6, 9.1) ─────
//
// Mirrors `gkr_eval_isa::bwd::coeff::encode::{category_arity, category_role,
// operand_width, move_width, is_move}`; `desc.rs` pins these exact numbers
// against those functions, so a divergence fails the Rust build.
//
// Operand width is a function of (OPCODE, POSITION) and of nothing else:
// `C2ProductBF_E4` fixes BF first and E4 second, and a resident `Cell` operand
// carries no window at all, so its width CANNOT come from a source descriptor.

constexpr u32 BWD_COEFF_ROLE_ENDPOINT0 = 0;
constexpr u32 BWD_COEFF_ROLE_DELTA = 1;
constexpr u32 BWD_COEFF_ROLE_PAIR = 2;
// Not a role: the opcode is a standalone cell-file move, whose two words are
// bare lanes rather than input records.
constexpr u32 BWD_COEFF_ROLE_MOVE = 3;

// Both opcode tables are dense from zero, so liveness is a single comparison.
constexpr bool bwd_coeff_opcode_is_live(const bool regime_is_r0, const u16 opcode) {
  return u32{opcode} < (regime_is_r0 ? BWD_COEFF_R0_LIVE_OPCODES : BWD_COEFF_EXT_LIVE_OPCODES);
}

constexpr bool bwd_coeff_is_move(const bool regime_is_r0, const u16 opcode) {
  return regime_is_r0 ? (opcode == BWD_COEFF_R0_OP_MOVE_BF || opcode == BWD_COEFF_R0_OP_MOVE_E4) : (opcode == BWD_COEFF_EXT_OP_MOVE_E4);
}

// The width a move relocates (section 9.6): the OPCODE carries it, not the
// operand, which is a bare six-bit BF lane either way.
constexpr bool bwd_coeff_move_is_e4(const bool regime_is_r0, const u16 opcode) {
  return regime_is_r0 ? opcode == BWD_COEFF_R0_OP_MOVE_E4 : opcode == BWD_COEFF_EXT_OP_MOVE_E4;
}

constexpr u32 bwd_coeff_role(const bool regime_is_r0, const u16 opcode) {
  if (bwd_coeff_is_move(regime_is_r0, opcode))
    return BWD_COEFF_ROLE_MOVE;
  if (regime_is_r0)
    return (opcode == BWD_COEFF_R0_OP_C0_LINEAR_BF || opcode == BWD_COEFF_R0_OP_C0_LINEAR_E4) ? BWD_COEFF_ROLE_ENDPOINT0 : BWD_COEFF_ROLE_DELTA;
  return opcode == BWD_COEFF_EXT_OP_C0_LINEAR_E4 ? BWD_COEFF_ROLE_ENDPOINT0 : BWD_COEFF_ROLE_PAIR;
}

// Input RECORDS the opcode carries (section 9.1); zero for a move.
constexpr u32 bwd_coeff_arity(const bool regime_is_r0, const u16 opcode) {
  switch (bwd_coeff_role(regime_is_r0, opcode)) {
  case BWD_COEFF_ROLE_MOVE:
    return 0;
  case BWD_COEFF_ROLE_ENDPOINT0:
    return 1;
  default:
    return 2;
  }
}

// Storage width of operand `position`: true = E4, false = BF. Only meaningful
// below the opcode's arity.
constexpr bool bwd_coeff_operand_is_e4(const bool regime_is_r0, const u16 opcode, const u32 position) {
  if (!regime_is_r0)
    return true; // Every live continuation operand is E4.
  switch (opcode) {
  case BWD_COEFF_R0_OP_C0_LINEAR_E4:
  case BWD_COEFF_R0_OP_C2_PRODUCT_E4_E4:
    return true;
  case BWD_COEFF_R0_OP_C2_PRODUCT_BF_E4:
    return position == 1;
  default:
    return false;
  }
}

static_assert(bwd_coeff_role(true, BWD_COEFF_R0_OP_C0_LINEAR_BF) == BWD_COEFF_ROLE_ENDPOINT0, "R0 C0LinearBF role drift");
static_assert(bwd_coeff_role(true, BWD_COEFF_R0_OP_C2_PRODUCT_BF_E4) == BWD_COEFF_ROLE_DELTA, "R0 C2ProductBF_E4 role drift");
static_assert(bwd_coeff_role(false, BWD_COEFF_EXT_OP_DUAL_PRODUCT_E4) == BWD_COEFF_ROLE_PAIR, "continuation DualProductE4 role drift");
static_assert(bwd_coeff_role(true, BWD_COEFF_R0_OP_MOVE_BF) == BWD_COEFF_ROLE_MOVE, "R0 MoveBF is not a term");
static_assert(bwd_coeff_arity(true, BWD_COEFF_R0_OP_C0_LINEAR_BF) == 1, "R0 C0LinearBF arity drift");
static_assert(bwd_coeff_arity(true, BWD_COEFF_R0_OP_C2_PRODUCT_E4_E4) == 2, "R0 C2ProductE4E4 arity drift");
static_assert(bwd_coeff_arity(false, BWD_COEFF_EXT_OP_MOVE_E4) == 0, "a move carries no input record");
// THE mixed-order rule: BF first, E4 second.
static_assert(!bwd_coeff_operand_is_e4(true, BWD_COEFF_R0_OP_C2_PRODUCT_BF_E4, 0), "C2ProductBF_E4 operand 0 must be BF");
static_assert(bwd_coeff_operand_is_e4(true, BWD_COEFF_R0_OP_C2_PRODUCT_BF_E4, 1), "C2ProductBF_E4 operand 1 must be E4");
static_assert(!bwd_coeff_operand_is_e4(true, BWD_COEFF_R0_OP_C2_PRODUCT_BF_BF, 1), "C2ProductBFBF operand 1 must be BF");
static_assert(bwd_coeff_operand_is_e4(false, BWD_COEFF_EXT_OP_DUAL_PRODUCT_E4, 0), "continuation operands are E4");
static_assert(bwd_coeff_move_is_e4(true, BWD_COEFF_R0_OP_MOVE_E4) && !bwd_coeff_move_is_e4(true, BWD_COEFF_R0_OP_MOVE_BF), "R0 move width drift");
static_assert(bwd_coeff_opcode_is_live(true, 6) && !bwd_coeff_opcode_is_live(true, 7), "R0 opcode 7 is deliberately dead");
static_assert(bwd_coeff_opcode_is_live(false, 2) && !bwd_coeff_opcode_is_live(false, 3), "continuation opcodes 3..7 are deliberately dead");

// ── Decoded input word (sections 9.4, 9.5) ──────────────────────────────────
//
// Pure bit extraction: no bounds check, no canonical-form check and no
// resolution. Release kernels trust validated artifacts (section 12); the
// checks live in the host validator and in the validation-only probe kernel
// declared at the bottom of this header.
//
// The ONE thing this must get right is ABI FACT 1: `first_access` is read only
// in the source-bearing branch, AFTER the mode dispatch, because in a `Cell`
// word bit 2 is the Endpoint0 lane's bit 0.
struct bwd_coeff_input {
  u16 mode;
  u16 window;
  u16 column;
  // `Cell` Endpoint0 lane, or a plan's Endpoint0 lane. Zero otherwise.
  u16 endpoint0_lane;
  // Packed-pair `Cell` Delta lane, or a plan's Delta lane. Zero otherwise.
  u16 delta_lane;
  // Plan actions (`BWD_COEFF_ACTION_*`); zero (`Direct`) outside a plan.
  u16 endpoint0_action;
  u16 delta_action;
  // `FillSource` destination lane; zero otherwise.
  u16 dst_lane;
  bool first_access;
  // u16 words this record occupies: 1 for `DirectSource`/`Cell`, 2 otherwise.
  u32 words;
};

// `cell_is_pair_form` MUST come from `bwd_coeff_cell_word_is_pair_form` — the
// opcode is the only discriminator (ABI FACT 2); the payload never is.
DEVICE_FORCEINLINE bwd_coeff_input bwd_coeff_decode_input(const u16 *program, const u32 pc, const bool cell_is_pair_form) {
  bwd_coeff_input in{};
  const u16 word = program[pc];
  in.mode = word & BWD_COEFF_INPUT_MODE_MASK;
  in.words = 1;
  if (in.mode == BWD_COEFF_MODE_CELL) {
    in.endpoint0_lane = (word >> BWD_COEFF_CELL_ENDPOINT0_LANE_SHIFT) & BWD_COEFF_LANE_MASK;
    if (cell_is_pair_form)
      in.delta_lane = (word >> BWD_COEFF_CELL_DELTA_LANE_SHIFT) & BWD_COEFF_LANE_MASK;
    return in;
  }
  in.first_access = ((word >> BWD_COEFF_INPUT_FIRST_ACCESS_SHIFT) & 1u) != 0;
  in.window = (word >> BWD_COEFF_INPUT_WINDOW_SHIFT) & BWD_COEFF_INPUT_WINDOW_MASK;
  in.column = (word >> BWD_COEFF_INPUT_COLUMN_SHIFT) & BWD_COEFF_INPUT_COLUMN_MASK;
  if (in.mode == BWD_COEFF_MODE_DIRECT_SOURCE)
    return in;
  const u16 extension = program[pc + 1];
  in.words = 2;
  if (in.mode == BWD_COEFF_MODE_FILL_SOURCE) {
    in.dst_lane = (extension >> BWD_COEFF_LANE_WORD_SHIFT) & BWD_COEFF_LANE_MASK;
    return in;
  }
  in.endpoint0_action = (extension >> BWD_COEFF_PLAN_ENDPOINT0_ACTION_SHIFT) & BWD_COEFF_PLAN_ACTION_MASK;
  in.endpoint0_lane = (extension >> BWD_COEFF_PLAN_ENDPOINT0_LANE_SHIFT) & BWD_COEFF_LANE_MASK;
  in.delta_action = (extension >> BWD_COEFF_PLAN_DELTA_ACTION_SHIFT) & BWD_COEFF_PLAN_ACTION_MASK;
  in.delta_lane = (extension >> BWD_COEFF_PLAN_DELTA_LANE_SHIFT) & BWD_COEFF_LANE_MASK;
  return in;
}

// ── Source-window origin (section 10.2) ─────────────────────────────────────
//
// The BACKING field of the window's matrix — NOT the width of the values read
// through it, which comes from the opcode: a continuation program folds a base
// matrix into E4.
constexpr u8 BWD_COEFF_ORIGIN_READ_BASE = 0;
constexpr u8 BWD_COEFF_ORIGIN_READ_EXT = 1;
constexpr u8 BWD_COEFF_ORIGIN_PROCEDURAL = 2;

// Procedural (virtual-setup) source kinds, in `gkr_eval_isa::fwd::source::
// KIND_ORDER` order. `BWD_COEFF_PROCEDURAL_NONE` marks a window whose origin is
// a real matrix.
constexpr u8 BWD_COEFF_PROCEDURAL_RANGE_CHECK_16_BITS = 0;
constexpr u8 BWD_COEFF_PROCEDURAL_RANGE_CHECK_TIMESTAMP = 1;
constexpr u8 BWD_COEFF_PROCEDURAL_INITS_AND_TEARDOWNS_LOW = 2;
constexpr u8 BWD_COEFF_PROCEDURAL_INITS_AND_TEARDOWNS_HIGH = 3;
constexpr u8 BWD_COEFF_PROCEDURAL_NONE = 0xff;

// The four kinds are contiguous in BOTH numbering schemes, so the translation to
// the incumbent `gkr_base_source_kind` the shared `gkr_virtual_base_value`
// helper takes is one addition. Asserted, because a reordering on either side
// would silently swap two procedural columns.
static_assert(GKR_BASE_SOURCE_VIRTUAL_RANGE_CHECK_TIMESTAMP == GKR_BASE_SOURCE_VIRTUAL_RANGE_CHECK_16_BITS + 1, "virtual kind order drift");
static_assert(GKR_BASE_SOURCE_VIRTUAL_INITS_AND_TEARDOWNS_LOW == GKR_BASE_SOURCE_VIRTUAL_RANGE_CHECK_16_BITS + 2, "virtual kind order drift");
static_assert(GKR_BASE_SOURCE_VIRTUAL_INITS_AND_TEARDOWNS_HIGH == GKR_BASE_SOURCE_VIRTUAL_RANGE_CHECK_16_BITS + 3, "virtual kind order drift");
static_assert(BWD_COEFF_PROCEDURAL_RANGE_CHECK_TIMESTAMP == BWD_COEFF_PROCEDURAL_RANGE_CHECK_16_BITS + 1, "procedural kind order drift");
static_assert(BWD_COEFF_PROCEDURAL_INITS_AND_TEARDOWNS_LOW == BWD_COEFF_PROCEDURAL_RANGE_CHECK_16_BITS + 2, "procedural kind order drift");
static_assert(BWD_COEFF_PROCEDURAL_INITS_AND_TEARDOWNS_HIGH == BWD_COEFF_PROCEDURAL_RANGE_CHECK_16_BITS + 3, "procedural kind order drift");

constexpr gkr_base_source_kind bwd_coeff_procedural_source_kind(const u8 procedural_kind) {
  return static_cast<gkr_base_source_kind>(GKR_BASE_SOURCE_VIRTUAL_RANGE_CHECK_16_BITS + procedural_kind);
}

// Section 10.2's static materialization policy: publish on first physical
// access iff `target_depth >= BWD_COEFF_PUBLISH_TARGET_DEPTH`. One tunable
// constant, not a scheduling decision.
constexpr u8 BWD_COEFF_PUBLISH_TARGET_DEPTH = 3;

// ── Launch geometry (section 11) ────────────────────────────────────────────
//
// ONE thread per logical row, 128 logical rows per block. There is no two-half
// role split, no shuffle and no paired-lane scheme.
constexpr u32 BWD_COEFF_THREADS_PER_BLOCK = 128;
constexpr u32 BWD_COEFF_ROWS_PER_BLOCK = BWD_COEFF_THREADS_PER_BLOCK;
constexpr u32 BWD_COEFF_WARP_LANES = 32;
constexpr u32 BWD_COEFF_WARP_SHIFT = 5;
constexpr u32 BWD_COEFF_LANE_INDEX_MASK = BWD_COEFF_WARP_LANES - 1;
constexpr u32 BWD_COEFF_FOLD_FACTOR_CAP = 10;
constexpr u32 BWD_COEFF_MAX_FOLD_DEPTH = 3;

// `ab_gkr_bwd_coeff_build_fold_factors_kernel` fills TWO weight groups: slots
// 0..1 are the depth-ONE weights (a backing that is one fold behind) and slots
// 2.. the depth-`fold_depth` weights (a backing that never caught up). Those are
// the only two catch-up distances the bank can express, so a window's
// `target_depth - backing_depth` must be 0, 1 or the launch's fold depth —
// `lower_bwd_coeff` rejects anything else rather than let a release kernel
// silently weight a depth-2 catch-up with depth-3 factors.
constexpr u32 BWD_COEFF_FOLD_FACTOR_SHALLOW_BASE = 0;
constexpr u32 BWD_COEFF_FOLD_FACTOR_DEEP_BASE = 2;
static_assert(BWD_COEFF_FOLD_FACTOR_DEEP_BASE + (1u << BWD_COEFF_MAX_FOLD_DEPTH) == BWD_COEFF_FOLD_FACTOR_CAP,
              "the fold-factor bank must hold exactly the depth-1 pair plus one full depth-D3 leaf table");

static_assert(1u << BWD_COEFF_WARP_SHIFT == BWD_COEFF_WARP_LANES, "warp layout drift");
// Same reason as BWD_COEFF_HEADER_OPCODE_SHIFT: derived constants still get a
// literal pin, so a de-derivation cannot slip through.
static_assert(BWD_COEFF_ROWS_PER_BLOCK == 128, "rows per block drift");
static_assert(BWD_COEFF_LANE_INDEX_MASK == 31, "warp lane index mask drift");
static_assert(BWD_COEFF_THREADS_PER_BLOCK % BWD_COEFF_WARP_LANES == 0, "a block must be a whole number of warps");

// `c_init` is descriptor metadata (section 9.3): a coefficient index into the
// same launch-wide bank, or this sentinel when the layer has none. It is NOT a
// program coefficient encoding — thirteen coefficient bits cannot reach it.
constexpr u16 BWD_COEFF_C_INIT_NONE = 0xffff;
static_assert(BWD_COEFF_MAX_COEFFICIENT_ENCODINGS - 1 < BWD_COEFF_C_INIT_NONE, "the absent-c_init sentinel must be unreachable as a coefficient index");

// ── Descriptor ──────────────────────────────────────────────────────────────

// One live source window (section 10.2): read backing and stride, publish
// backing and stride, backing depth, target depth, origin field, materialize
// flag, and the procedural source kind where applicable.
//
// A window covers at most BWD_COEFF_SOURCE_WINDOW_COLUMNS contiguous referenced
// columns of ONE logical backing; `*_base` already points at the window's first
// column, so a bound coordinate resolves to `read_base + column * read_stride_bytes`.
struct bwd_coeff_source_window {
  const char *read_base;
  char *publish_base;
  u32 read_stride_bytes;
  u32 publish_stride_bytes;
  u8 backing_depth;
  u8 target_depth;
  u8 origin;
  u8 materialize;
  u8 procedural_kind;
  u8 reserved[3];
};

static_assert(sizeof(bwd_coeff_source_window) == 32, "bwd_coeff_source_window ABI size drift");
static_assert(alignof(bwd_coeff_source_window) == 8, "bwd_coeff_source_window ABI alignment drift");
static_assert(__builtin_offsetof(bwd_coeff_source_window, read_base) == 0, "read_base ABI offset drift");
static_assert(__builtin_offsetof(bwd_coeff_source_window, publish_base) == 8, "publish_base ABI offset drift");
static_assert(__builtin_offsetof(bwd_coeff_source_window, read_stride_bytes) == 16, "read_stride_bytes ABI offset drift");
static_assert(__builtin_offsetof(bwd_coeff_source_window, publish_stride_bytes) == 20, "publish_stride_bytes ABI offset drift");
static_assert(__builtin_offsetof(bwd_coeff_source_window, backing_depth) == 24, "backing_depth ABI offset drift");
static_assert(__builtin_offsetof(bwd_coeff_source_window, target_depth) == 25, "target_depth ABI offset drift");
static_assert(__builtin_offsetof(bwd_coeff_source_window, origin) == 26, "origin ABI offset drift");
static_assert(__builtin_offsetof(bwd_coeff_source_window, materialize) == 27, "materialize ABI offset drift");
static_assert(__builtin_offsetof(bwd_coeff_source_window, procedural_kind) == 28, "procedural_kind ABI offset drift");
static_assert(__builtin_offsetof(bwd_coeff_source_window, reserved) == 29, "reserved ABI offset drift");

// The complete by-value launch descriptor. Passed as a single
// `__grid_constant__` kernel parameter; `program` is embedded, never pointed to.
//
// `alignas(BWD_COEFF_DESC_ALIGN)` plus `pad` is what makes `offsetof(program)`
// a multiple of 16.
struct alignas(BWD_COEFF_DESC_ALIGN) bwd_coeff_desc {
  // Evaluated E4 coefficients. Read ONLY by the DevicePointer specialization;
  // the Constant specialization ignores it and reads ab_gkr_flat_coefficients.
  // This is the sanctioned exception to "by value": it is coefficient DATA, not
  // program storage.
  const e4 *coefficients;
  const e4 *round_challenges;
  // Production factored-eq low table; high tables remain in ab_gkr_eq_high.
  const e4 *eq_low;
  // 2 * logical_rows entries: acc_c0 * eq in [0, logical_rows), acc_c2 * eq in
  // [logical_rows, 2 * logical_rows).
  e4 *contributions;
  bwd_coeff_source_window source_windows[BWD_COEFF_SOURCE_WINDOW_CAP];
  gkr_eq_sizes eq_sizes;
  // u16 words of `program` this launch executes. There is no end opcode.
  u32 num_words;
  u32 n_source_windows;
  u32 n_round_challenges;
  // Bank entries behind BWD_COEFF_INDEX_RESERVED; index `i` is bank entry
  // `i - BWD_COEFF_INDEX_RESERVED`.
  u32 n_coefficients;
  // Rows this launch evaluates, one per thread. Also the contribution
  // half-stride above.
  u32 logical_rows;
  // Private cell file per thread, in E4 cells. Dynamic shared memory is exactly
  // `cell_budget * sizeof(e4) * blockDim.x`.
  u32 cell_budget;
  // Coefficient index of the per-thread acc_c0 initializer, or
  // BWD_COEFF_C_INIT_NONE.
  u16 c_init;
  // Explicit: keeps `program` 16-byte aligned. Never read.
  u16 pad[5];
  u16 program[BWD_COEFF_PROGRAM_WORD_CAP];
};

static_assert(sizeof(bwd_coeff_desc) == 12144, "bwd_coeff_desc/BwdCoeffDesc ABI size drift");
static_assert(alignof(bwd_coeff_desc) == BWD_COEFF_DESC_ALIGN, "bwd_coeff_desc ABI alignment drift");
// The final authority on the by-value budget (section 9.1). An overflow needs a
// tighter encoding, never a second storage path.
static_assert(sizeof(bwd_coeff_desc) <= BWD_COEFF_DESC_CAP, "bwd_coeff_desc exceeds the __grid_constant__ parameter budget");
static_assert(__builtin_offsetof(bwd_coeff_desc, coefficients) == 0, "coefficients ABI offset drift");
static_assert(__builtin_offsetof(bwd_coeff_desc, round_challenges) == 8, "round_challenges ABI offset drift");
static_assert(__builtin_offsetof(bwd_coeff_desc, eq_low) == 16, "eq_low ABI offset drift");
static_assert(__builtin_offsetof(bwd_coeff_desc, contributions) == 24, "contributions ABI offset drift");
static_assert(__builtin_offsetof(bwd_coeff_desc, source_windows) == 32, "source_windows ABI offset drift");
static_assert(__builtin_offsetof(bwd_coeff_desc, eq_sizes) == 576, "eq_sizes ABI offset drift");
static_assert(__builtin_offsetof(bwd_coeff_desc, num_words) == 588, "num_words ABI offset drift");
static_assert(__builtin_offsetof(bwd_coeff_desc, n_source_windows) == 592, "n_source_windows ABI offset drift");
static_assert(__builtin_offsetof(bwd_coeff_desc, n_round_challenges) == 596, "n_round_challenges ABI offset drift");
static_assert(__builtin_offsetof(bwd_coeff_desc, n_coefficients) == 600, "n_coefficients ABI offset drift");
static_assert(__builtin_offsetof(bwd_coeff_desc, logical_rows) == 604, "logical_rows ABI offset drift");
static_assert(__builtin_offsetof(bwd_coeff_desc, cell_budget) == 608, "cell_budget ABI offset drift");
static_assert(__builtin_offsetof(bwd_coeff_desc, c_init) == 612, "c_init ABI offset drift");
static_assert(__builtin_offsetof(bwd_coeff_desc, pad) == 614, "pad ABI offset drift");
static_assert(__builtin_offsetof(bwd_coeff_desc, program) == 624, "program ABI offset drift");
static_assert(__builtin_offsetof(bwd_coeff_desc, program) % BWD_COEFF_DESC_ALIGN == 0,
              "the program stream must start 16-byte aligned so it can be buffered through wide loads");
// The by-value program is the descriptor's whole tail: nothing follows it, so
// its size and the descriptor's size move together.
static_assert(sizeof(bwd_coeff_desc) == __builtin_offsetof(bwd_coeff_desc, program) + BWD_COEFF_PROGRAM_BYTE_CAP,
              "the program array must be the descriptor tail");

// ── Validation-only source probe (sections 10, 12) ──────────────────────────
//
// Section 12 sanctions "host artifact checks and validation-only test kernels";
// release kernels trust their descriptor. This is that test kernel: it drives
// the SAME typed resolvers the release executors use, one value use at a time,
// and writes out both projections of every operand instead of accumulating
// them. It is what lets Task 10's source resolution be tested against the CPU
// oracle BEFORE Task 11's header decode and arithmetic loop exist.
//
// It is never launched by production code.
struct bwd_coeff_probe_record {
  // The regime opcode of the term whose operands this record resolves. It fixes
  // the arity, the role and the per-position width exactly as a decoded header
  // would; the probe does not decode headers (that is Task 11).
  u16 opcode;
  // Index into `bwd_coeff_desc::program` of this record's FIRST input word.
  u16 word;
};

static_assert(sizeof(bwd_coeff_probe_record) == 4, "bwd_coeff_probe_record ABI size drift");
static_assert(alignof(bwd_coeff_probe_record) == 2, "bwd_coeff_probe_record ABI alignment drift");

// Operand positions the probe reports per record. Two covers every live opcode.
constexpr u32 BWD_COEFF_PROBE_OPERANDS = 2;

// Sticky error bits, `atomicOr`-ed into the probe's single error word.
constexpr u32 BWD_COEFF_PROBE_ERR_DEAD_OPCODE = 1u << 0;
constexpr u32 BWD_COEFF_PROBE_ERR_MOVE_OPCODE = 1u << 1;
constexpr u32 BWD_COEFF_PROBE_ERR_PROGRAM_OUT_OF_RANGE = 1u << 2;
constexpr u32 BWD_COEFF_PROBE_ERR_WINDOW_OUT_OF_RANGE = 1u << 3;
constexpr u32 BWD_COEFF_PROBE_ERR_LANE_OUT_OF_BUDGET = 1u << 4;
constexpr u32 BWD_COEFF_PROBE_ERR_MISALIGNED_E4_LANE = 1u << 5;
constexpr u32 BWD_COEFF_PROBE_ERR_MODE_ILLEGAL_FOR_ROLE = 1u << 6;
constexpr u32 BWD_COEFF_PROBE_ERR_PLAN_ACTION_INVALID = 1u << 7;
constexpr u32 BWD_COEFF_PROBE_ERR_UNSUPPORTED_FOLD_DELTA = 1u << 8;

} // namespace airbender::prover::gkr

// Runtime transcript-derived fold weights (section 10.2). Stream-ordered
// constant memory, filled by the prelude kernel below.
EXTERN __device__ __constant__ e4 ab_gkr_bwd_coeff_fold_factors[airbender::prover::gkr::BWD_COEFF_FOLD_FACTOR_CAP];

EXTERN __global__ void ab_gkr_bwd_coeff_build_fold_factors_kernel(const e4 *round_challenges, u32 target_depth, u32 fold_depth, e4 *fold_factors);

// Release executors. The specialization triple is (Regime, FoldDepth,
// CoeffBank); FoldDepth is continuation-only, and the cell budget is runtime
// launch metadata rather than a specialization axis, so one instantiation
// covers c2 through c16.
EXTERN __global__ void ab_gkr_bwd_coeff_r0_const_kernel(const __grid_constant__ airbender::prover::gkr::bwd_coeff_desc desc);
EXTERN __global__ void ab_gkr_bwd_coeff_r0_ptr_kernel(const __grid_constant__ airbender::prover::gkr::bwd_coeff_desc desc);
EXTERN __global__ void ab_gkr_bwd_coeff_ext_d0_const_kernel(const __grid_constant__ airbender::prover::gkr::bwd_coeff_desc desc);
EXTERN __global__ void ab_gkr_bwd_coeff_ext_d0_ptr_kernel(const __grid_constant__ airbender::prover::gkr::bwd_coeff_desc desc);
EXTERN __global__ void ab_gkr_bwd_coeff_ext_d1_const_kernel(const __grid_constant__ airbender::prover::gkr::bwd_coeff_desc desc);
EXTERN __global__ void ab_gkr_bwd_coeff_ext_d1_ptr_kernel(const __grid_constant__ airbender::prover::gkr::bwd_coeff_desc desc);
EXTERN __global__ void ab_gkr_bwd_coeff_ext_d2_const_kernel(const __grid_constant__ airbender::prover::gkr::bwd_coeff_desc desc);
EXTERN __global__ void ab_gkr_bwd_coeff_ext_d2_ptr_kernel(const __grid_constant__ airbender::prover::gkr::bwd_coeff_desc desc);
EXTERN __global__ void ab_gkr_bwd_coeff_ext_d3_const_kernel(const __grid_constant__ airbender::prover::gkr::bwd_coeff_desc desc);
EXTERN __global__ void ab_gkr_bwd_coeff_ext_d3_ptr_kernel(const __grid_constant__ airbender::prover::gkr::bwd_coeff_desc desc);

// The validation-only source probe. `regime_is_r0` and `fold_depth` are runtime
// here — the probe is not on any hot path, and one symbol keeps the test side
// from having to mirror the whole specialization matrix. `endpoint0_out` and
// `delta_out` each hold
// `n_records * BWD_COEFF_PROBE_OPERANDS * desc.logical_rows` values, indexed
// `(record * BWD_COEFF_PROBE_OPERANDS + position) * logical_rows + row`.
EXTERN __global__ void ab_gkr_bwd_coeff_source_probe_kernel(const __grid_constant__ airbender::prover::gkr::bwd_coeff_desc desc, u32 regime_is_r0,
                                                            u32 fold_depth, const airbender::prover::gkr::bwd_coeff_probe_record *records, u32 n_records,
                                                            e4 *endpoint0_out, e4 *delta_out, u32 *error);
