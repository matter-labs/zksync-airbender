#pragma once

// SEGMENTED lean VM: the by-value launch descriptors, the lean u16 wire, and the
// kernel matrix (segmented-lean-VM design sections 3, 4, 5, 7).
//
// THIS FILE IS ONE HALF OF AN ABI. Its Rust half is
// `src/prover/gkr/backward/vm/seg_desc.rs`, which carries the same field offsets
// and the same sizes under `const _: () = assert!(...)`, and additionally ties
// each capacity to its authority in the `gkr_eval_isa` crate. Neither half may
// move without the other in the same commit.
//
// WHAT ENFORCES THAT: the `static_assert`s below are CUDA-vs-CUDA and DO run
// under nvcc during `cargo check`, so a STRUCT layout edit here is a build
// failure; `seg_desc.rs`'s `const _: () = assert!(...)` blocks are
// Rust-vs-`gkr_eval_isa`. What neither compiler sees is an edit to a constant
// here that changes no layout — and that gap is closed by
// `seg_abi_tests::seg_cuda_constants_match_the_rust_mirror`, which reads THIS
// FILE as text and compares each mirrored literal against the Rust value. It is
// `#[cfg(test)]`, so `cargo check` alone does not run it; do not skip it after
// editing this header.
//
// # What this lineage does NOT carry
//
// No challenge pointer (fold challenges have exactly ONE authority, the
// `ab_gkr_main_layer_claim_point` `__constant__` symbol), no cell budget (there
// is no cell file and no residency), no program length (`list_offset[k]` IS the
// end of the stream) and no coefficient index on the seed path (`c_init` is
// resolved E4 limbs).
//
// # What it inherited from the retired cell-era lineage
//
// `bwd_coeff_source_window`, the origin / procedural-kind / publication
// constants, the lean header's two bit widths and the FROZEN cell-era opcode
// numbering were shared with `coefficient_vm.cuh`. That header is gone; they were
// rehomed here verbatim, keeping their `BWD_COEFF_` prefix so this half and
// `seg_desc.rs` stay word-for-word comparable across the move.

#include "flat.cuh"

namespace airbender::prover::gkr {

// ── Rehomed from the retired cell-era header ─────────────────────────────────
//
// Everything in this section was shared with `coefficient_vm.cuh` before that
// lineage was deleted. It is reproduced verbatim, prefix included, so the Rust
// half (`seg_desc.rs`, same names) and any reader of the old header recognize it
// unchanged.

// The lean header's two bit widths
// (`gkr_eval_isa::bwd::coeff::limits::{HEADER_COEFFICIENT_BITS, HEADER_OPCODE_BITS}`).
constexpr u32 BWD_COEFF_HEADER_COEFFICIENT_BITS = 13;
constexpr u32 BWD_COEFF_HEADER_OPCODE_BITS = 3;
// `gkr_eval_isa::bwd::coeff::limits::MAX_COEFFICIENT_ENCODINGS`: what thirteen
// coefficient bits can name, reserved literals included.
constexpr u32 BWD_COEFF_MAX_COEFFICIENT_ENCODINGS = 1u << BWD_COEFF_HEADER_COEFFICIENT_BITS;
static_assert(BWD_COEFF_MAX_COEFFICIENT_ENCODINGS == 8192, "coefficient encoding space drift");

// The FROZEN regime opcode numbering
// (`gkr_eval_isa::bwd::coeff::limits::{R0_OPCODE_TABLE, CONTINUATION_OPCODE_TABLE}`).
// No live kernel decodes these: the lean class tables below are DEFINED as this
// numbering with the `Move` rows deleted and the rest re-densified, and the
// `static_assert`s further down are what make that definition binding on both
// sides. They are reference data, not an opcode set.
constexpr u16 BWD_COEFF_R0_OP_C0_LINEAR_BF = 0;
constexpr u16 BWD_COEFF_R0_OP_C0_LINEAR_E4 = 1;
constexpr u16 BWD_COEFF_R0_OP_C2_PRODUCT_BF_BF = 2;
constexpr u16 BWD_COEFF_R0_OP_C2_PRODUCT_BF_E4 = 3;
constexpr u16 BWD_COEFF_R0_OP_C2_PRODUCT_E4_E4 = 4;
constexpr u16 BWD_COEFF_R0_OP_MOVE_BF = 5;
constexpr u16 BWD_COEFF_R0_OP_MOVE_E4 = 6;
constexpr u32 BWD_COEFF_R0_LIVE_OPCODES = 7;

constexpr u16 BWD_COEFF_EXT_OP_C0_LINEAR_E4 = 0;
constexpr u16 BWD_COEFF_EXT_OP_DUAL_PRODUCT_E4 = 1;
constexpr u16 BWD_COEFF_EXT_OP_MOVE_E4 = 2;
constexpr u32 BWD_COEFF_EXT_LIVE_OPCODES = 3;

static_assert(BWD_COEFF_R0_OP_MOVE_BF + 1 == BWD_COEFF_R0_OP_MOVE_E4, "the R0 move rows must stay adjacent");
static_assert(BWD_COEFF_R0_OP_MOVE_E4 + 1 == BWD_COEFF_R0_LIVE_OPCODES, "the R0 move rows must stay at the tail");
static_assert(BWD_COEFF_EXT_OP_MOVE_E4 + 1 == BWD_COEFF_EXT_LIVE_OPCODES, "the continuation move row must stay at the tail");

// ── Source-window origin (section 10.2) ─────────────────────────────────────
//
// The BACKING field of the window's matrix — NOT the width of the values read
// through it, which comes from the term class: a continuation program folds a
// base matrix into E4.
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
// D0..D3: the bounded lazy-fold depths the JAOT prologue materializes over.
constexpr u32 BWD_COEFF_MAX_FOLD_DEPTH = 3;

// One live source window (section 10.2): read backing and stride, publish
// backing and stride, backing depth, target depth, origin field, materialize
// flag, and the procedural source kind where applicable.
//
// `*_base` already points at the window's first column, so a bound coordinate
// resolves to `read_base + column * read_stride_bytes`.
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

// ── Capacities and launch geometry (section 3, 5) ────────────────────────────

// `gkr_eval_isa::bwd::coeff::limits::KERNEL_ARGUMENT_CEILING_BYTES`.
constexpr u32 BWD_SEG_DESC_CAP = 32764;
// `gkr_eval_isa::bwd::coeff::limits::DESCRIPTOR_ALIGNMENT_BYTES`. Load-bearing:
// it is what puts `bwd_seg_desc::program` — the descriptor's FIRST field — on a
// 16-byte boundary, which is the only reason the lean census's one-word round-up
// buys anything.
constexpr u32 BWD_SEG_DESC_ALIGN = 16;

// Warps a block may run, i.e. the largest legal `K` of the round-robin term
// split. One warp per term list, `blockDim == 32 * k`, so `K` tops out exactly
// where the CUDA block does.
constexpr u32 BWD_SEG_MAX_K = 32;
constexpr u32 BWD_SEG_MAX_THREADS_PER_BLOCK = 1024;
// Lane = row inside the 32-row tile; `tile_row0 = blockIdx.x * 32`.
constexpr u32 BWD_SEG_WARP_LANES = 32;
constexpr u32 BWD_SEG_WARP_SHIFT = 5;
constexpr u32 BWD_SEG_LANE_INDEX_MASK = BWD_SEG_WARP_LANES - 1;

static_assert(BWD_SEG_MAX_K * BWD_SEG_WARP_LANES == BWD_SEG_MAX_THREADS_PER_BLOCK, "one warp per list, and the block is the cap");
static_assert(1u << BWD_SEG_WARP_SHIFT == BWD_SEG_WARP_LANES, "warp layout drift");
static_assert(BWD_SEG_LANE_INDEX_MASK == 31, "warp lane index mask drift");

// Slots in this lineage's OWN `__constant__` coefficient bank
// (`ab_gkr_bwd_seg_coeff_bank`, declared at the bottom of this header). No
// `backward::flat` symbol is involved.
//
// RR ruling 2026-07-27: the two reserved literal ids are MATERIALIZED at the bank
// head — `bank[0] = ONE`, `bank[1] = NEG_ONE`, banked recipes from index
// `CoefficientRecipeId::RESERVED` on — so the executor resolves EVERY coefficient
// with one uniform `bank[coeff_idx]` load: no ±ONE fast path, no branch, no offset
// subtraction. Host lowering owns the materialization; wire coefficient ids are
// reserved-INCLUSIVE and this side indexes raw.
//
// That reserved count is `gkr_eval_isa::bwd::coeff::model::CoefficientRecipeId::
// RESERVED`, pinned at 2 by `seg_abi_tests::seg_coefficient_bank_materializes_the_
// reserved_literals`. (It used to be spelled `BWD_COEFF_INDEX_RESERVED` in the
// cell-era header; that constant no longer exists on either side.)
//
// Sized from the census (1,138 recipes + 2 literals = 1,140), rounded up so the
// bank is exactly 18 KiB of the 64 KB per-module `__constant__` budget.
constexpr u32 BWD_SEG_CONST_BANK = 1152;
// Source-table slots: the census maximum of 1,062 rounded up to a multiple of 16
// so both source-indexed arrays are a whole number of 16-byte lines.
constexpr u32 BWD_SEG_MAX_SOURCES = 1072;
// `gkr_eval_isa::bwd::coeff::limits::LEAN_DESCRIPTOR_PROGRAM_WORDS` — the
// measured maximum 8,624 words (4 words x 2,156 RECORDS: 1,791 terms plus 365
// group headers, `blake2_with_extended_control` L0 Ext) which is already a whole
// number of 16-byte quanta. Not a headroom allowance.
constexpr u32 BWD_SEG_PROGRAM_WORD_CAP = 8624;
constexpr u32 BWD_SEG_PROGRAM_BYTE_CAP = 2 * BWD_SEG_PROGRAM_WORD_CAP;
// `in_scope::MAX_SOURCE_WINDOWS_USED`: the EXACT measured corpus maximum,
// deliberately not the 64 windows the wire could name.
constexpr u32 BWD_SEG_SOURCE_WINDOW_CAP = 17;
// `gkr_eval_isa::bwd::coeff::limits::LEAN_MAX_IMMEDIATES` — the WIRE cap on one
// coordinate's immediate table, not a measurement. The Rust half carries the
// build-time mirror assert (it may import the ISA crate; this side cannot), and
// `seg_abi_tests`' header-text matcher compares this literal against it.
constexpr u32 BWD_SEG_MAX_IMMEDIATES = 512;

static_assert(BWD_SEG_PROGRAM_BYTE_CAP == 17248, "program array byte size drift");
static_assert(BWD_SEG_PROGRAM_BYTE_CAP % BWD_SEG_DESC_ALIGN == 0, "the program array is not a whole number of 16-byte quanta");
static_assert(BWD_SEG_CONST_BANK * sizeof(e4) == 18 * 1024, "coefficient bank size drift");
static_assert(BWD_SEG_CONST_BANK * sizeof(e4) <= 64 * 1024, "the coefficient bank exceeds the per-module __constant__ budget");
// Every bank slot must be nameable by the thirteen coefficient bits of the lean
// header, reserved literals included.
static_assert(BWD_SEG_CONST_BANK <= BWD_COEFF_MAX_COEFFICIENT_ENCODINGS, "a bank slot the wire cannot name");
static_assert(BWD_SEG_MAX_SOURCES % 16 == 0, "the source arrays are not whole 16-byte lines");
static_assert(BWD_SEG_SOURCE_WINDOW_CAP == 17, "source window capacity drift");
static_assert(BWD_SEG_MAX_IMMEDIATES == 512, "immediate table capacity drift");

// ── The lean wire (section 4) ───────────────────────────────────────────────
//
// ```text
// word0 = [class:3 @13 | coeff_idx:13 @0]
// word1 = source_a           (slot into bwd_seg_desc::source)
// word2 = source_b           (slot, or BWD_SEG_SOURCE_NONE)
// word3 = 0                  (reserved; host-validated, never read here)
// ```
//
// HEADER-FIRST because each warp walks its own contiguous list strictly
// sequentially. The width is FIXED at four words even though the class already
// fixes the source count, which is what makes a term's address a shift and the
// round-robin K-split of the word stream positional.
//
// Mirrors `gkr_eval_isa::bwd::coeff::lean`.
constexpr u32 BWD_SEG_WORDS_PER_TERM = 4;
constexpr u32 BWD_SEG_COEFFICIENT_SHIFT = 0;
constexpr u16 BWD_SEG_COEFFICIENT_MASK = (1u << BWD_COEFF_HEADER_COEFFICIENT_BITS) - 1;
constexpr u32 BWD_SEG_CLASS_SHIFT = BWD_COEFF_HEADER_COEFFICIENT_BITS;
constexpr u16 BWD_SEG_CLASS_MASK = (1u << BWD_COEFF_HEADER_OPCODE_BITS) - 1;
// `source_b` of a one-source class. Never a slot: BWD_SEG_MAX_SOURCES stays
// strictly below it.
constexpr u16 BWD_SEG_SOURCE_NONE = 0xffff;

static_assert(BWD_SEG_CLASS_SHIFT == 13, "lean class shift drift");
static_assert(BWD_SEG_COEFFICIENT_MASK == 0x1fffu, "lean coefficient mask drift");
static_assert(BWD_SEG_CLASS_MASK == 0x7u, "lean class mask drift");
// The header is exactly saturated, which is what makes the class free.
static_assert(BWD_COEFF_HEADER_COEFFICIENT_BITS + BWD_COEFF_HEADER_OPCODE_BITS == 16, "the lean header must be exactly saturated");
static_assert(BWD_SEG_MAX_SOURCES < BWD_SEG_SOURCE_NONE, "a source slot could collide with the no-second-source sentinel");
static_assert(BWD_SEG_PROGRAM_WORD_CAP % BWD_SEG_WORDS_PER_TERM == 0, "the program array is not a whole number of fixed-width records");

// Lean class tables (`lean::LEAN_R0_OPCODES`, `lean::LEAN_CONT_OPCODES`): the
// FROZEN cell-era tables minus the two `Move` forms, re-densified. Same
// categories in the same relative order, so each lean class is its cell-era
// opcode shifted down past the deleted `Move` rows — which for both regimes is a
// shift of zero, because the `Move` rows are the TAIL of each table. The
// static_asserts below pin exactly that.
constexpr u16 BWD_SEG_R0_CLASS_C0_LINEAR_BF = 0;
constexpr u16 BWD_SEG_R0_CLASS_C0_LINEAR_E4 = 1;
constexpr u16 BWD_SEG_R0_CLASS_C2_PRODUCT_BF_BF = 2;
constexpr u16 BWD_SEG_R0_CLASS_C2_PRODUCT_BF_E4 = 3;
constexpr u16 BWD_SEG_R0_CLASS_C2_PRODUCT_E4_E4 = 4;
constexpr u32 BWD_SEG_R0_LIVE_CLASSES = 5;

constexpr u16 BWD_SEG_EXT_CLASS_C0_LINEAR_E4 = 0;
constexpr u16 BWD_SEG_EXT_CLASS_DUAL_PRODUCT_E4 = 1;
constexpr u32 BWD_SEG_EXT_LIVE_CLASSES = 2;

static_assert(BWD_SEG_R0_LIVE_CLASSES <= BWD_SEG_CLASS_MASK + 1u, "the R0 class census exceeds three class bits");
static_assert(BWD_SEG_EXT_LIVE_CLASSES <= BWD_SEG_CLASS_MASK + 1u, "the continuation class census exceeds three class bits");
// The lean tables are the cell-era tables with the `Move` rows deleted, and those
// rows sit at the tail, so every surviving class number is unchanged. A
// renumbering on either side would break these.
static_assert(BWD_SEG_R0_CLASS_C0_LINEAR_BF == BWD_COEFF_R0_OP_C0_LINEAR_BF, "R0 C0LinearBF class renumbered");
static_assert(BWD_SEG_R0_CLASS_C0_LINEAR_E4 == BWD_COEFF_R0_OP_C0_LINEAR_E4, "R0 C0LinearE4 class renumbered");
static_assert(BWD_SEG_R0_CLASS_C2_PRODUCT_BF_BF == BWD_COEFF_R0_OP_C2_PRODUCT_BF_BF, "R0 C2ProductBF_BF class renumbered");
static_assert(BWD_SEG_R0_CLASS_C2_PRODUCT_BF_E4 == BWD_COEFF_R0_OP_C2_PRODUCT_BF_E4, "R0 C2ProductBF_E4 class renumbered");
static_assert(BWD_SEG_R0_CLASS_C2_PRODUCT_E4_E4 == BWD_COEFF_R0_OP_C2_PRODUCT_E4_E4, "R0 C2ProductE4_E4 class renumbered");
static_assert(BWD_SEG_EXT_CLASS_C0_LINEAR_E4 == BWD_COEFF_EXT_OP_C0_LINEAR_E4, "continuation C0LinearE4 class renumbered");
static_assert(BWD_SEG_EXT_CLASS_DUAL_PRODUCT_E4 == BWD_COEFF_EXT_OP_DUAL_PRODUCT_E4, "continuation DualProductE4 class renumbered");
// The lean tables are exactly the live cell-era opcodes minus the moves.
static_assert(BWD_SEG_R0_LIVE_CLASSES + 2 == BWD_COEFF_R0_LIVE_OPCODES, "R0 lean table is not the frozen table minus its two moves");
static_assert(BWD_SEG_EXT_LIVE_CLASSES + 1 == BWD_COEFF_EXT_LIVE_OPCODES, "continuation lean table is not the frozen table minus its move");

// ── The grouped wire (grouped-coefficient-eval spec section 4.4) ─────────────
//
// A coefficient GROUP is one CONTROL record followed by its `N` member records,
// contiguous, inside ONE warp's list (host lowering deals whole atoms). The header
// is NOT a term:
//
// ```text
// word0 = [class = BWD_SEG_EXT_CLASS_GROUP_HEADER @13 | core coeff_idx:13 @0]
// word1 = N, the member count (>= 2)
// word2 = flags: bit 0 = the core multiplies into acc_c0, bit 1 = into acc_c2
// word3 = 0
// ```
//
// Each member is an ordinary term record whose thirteen coefficient bits carry an
// IMMEDIATE id instead of a recipe id, so the group spends ONE `e4 x e4` core
// multiply per accumulator side for its whole run instead of one per member.
//
// Mirrors `gkr_eval_isa::bwd::coeff::limits::LEAN_CONT_GROUP_HEADER_CLASS` and
// `gkr_eval_isa::bwd::coeff::lean::{LEAN_GROUP_FLAG_C0, LEAN_GROUP_FLAG_C2}`.
constexpr u16 BWD_SEG_EXT_CLASS_GROUP_HEADER = 2;
constexpr u16 BWD_SEG_GROUP_FLAG_C0 = 1;
constexpr u16 BWD_SEG_GROUP_FLAG_C2 = 2;
constexpr u16 BWD_SEG_GROUP_FLAG_MASK = BWD_SEG_GROUP_FLAG_C0 | BWD_SEG_GROUP_FLAG_C2;

// The two properties that make the control code decodable, restating `lean.rs`'s
// own const asserts: it is FREE in the continuation table (nothing else can be read
// as a header), and it is TAKEN in the R0 table (which is why groups are
// continuation-only and why the R0 executor has no header branch at all).
static_assert(BWD_SEG_EXT_CLASS_GROUP_HEADER >= BWD_SEG_EXT_LIVE_CLASSES, "the group control code collides with a live continuation class");
static_assert(BWD_SEG_EXT_CLASS_GROUP_HEADER < BWD_SEG_R0_LIVE_CLASSES,
              "the group control code is a dead R0 class, so nothing would stop an R0 program from carrying a header");
static_assert(BWD_SEG_EXT_CLASS_GROUP_HEADER <= BWD_SEG_CLASS_MASK, "the group control code does not fit the three class bits");
static_assert(BWD_SEG_GROUP_FLAG_MASK == 3, "group flag mask drift");

// The two RESERVED immediate ids (`model::ImmediateId`): a member's coefficient
// field is an immediate id, `0` is `+1`, `1` is `-1`, and `id >= RESERVED` indexes
// `bwd_seg_desc::immediates[id - RESERVED]`. The two literals consume no table slot
// and cost no multiplication — an add and a sub respectively.
constexpr u16 BWD_SEG_IMMEDIATE_ONE = 0;
constexpr u16 BWD_SEG_IMMEDIATE_NEG_ONE = 1;
constexpr u16 BWD_SEG_IMMEDIATE_RESERVED = 2;

static_assert(BWD_SEG_IMMEDIATE_NEG_ONE == BWD_SEG_IMMEDIATE_ONE + 1, "the reserved immediate ids must be adjacent");
static_assert(BWD_SEG_IMMEDIATE_RESERVED == BWD_SEG_IMMEDIATE_NEG_ONE + 1, "the reserved immediate ids must be the head of the id space");
// Every immediate id a member can carry must be nameable by the thirteen
// coefficient bits, reserved literals included — the same bound the coefficient
// bank is held to.
static_assert(BWD_SEG_IMMEDIATE_RESERVED + BWD_SEG_MAX_IMMEDIATES <= BWD_COEFF_MAX_COEFFICIENT_ENCODINGS, "an immediate id the wire cannot name");

// ── Source classes (section 4) ──────────────────────────────────────────────
//
// How the operand behind ONE wire source slot is produced at ONE round. This is
// NOT the wire's three-bit TERM class: the term class fixes an operation's
// projection and arity, this fixes where its operand comes from.
//
// The AUTHORITY for these five numbers is Rust's `seg_lower::SourceClass`, which
// carries them as enum discriminants and asserts them; this is the byte they
// travel in.
constexpr u8 BWD_SEG_SOURCE_CLASS_BF_DIRECT = 0;
constexpr u8 BWD_SEG_SOURCE_CLASS_BF_INLINE_D1 = 1;
constexpr u8 BWD_SEG_SOURCE_CLASS_BF_INLINE_D2 = 2;
constexpr u8 BWD_SEG_SOURCE_CLASS_E4_DIRECT = 3;
constexpr u8 BWD_SEG_SOURCE_CLASS_PROCEDURAL_INLINE = 4;
constexpr u32 BWD_SEG_SOURCE_CLASSES = 5;

static_assert(BWD_SEG_SOURCE_CLASS_BF_DIRECT == 0, "source class BfDirect drift");
static_assert(BWD_SEG_SOURCE_CLASS_BF_INLINE_D1 == 1, "source class BfInlineD1 drift");
static_assert(BWD_SEG_SOURCE_CLASS_BF_INLINE_D2 == 2, "source class BfInlineD2 drift");
static_assert(BWD_SEG_SOURCE_CLASS_E4_DIRECT == 3, "source class E4Direct drift");
static_assert(BWD_SEG_SOURCE_CLASS_PROCEDURAL_INLINE == 4, "source class ProceduralInline drift");
static_assert(BWD_SEG_SOURCE_CLASSES == 5, "source class count drift");
static_assert(BWD_SEG_SOURCE_CLASSES <= 256, "a source class must fit its byte");

// Fold depths. The PROLOGUE materializes at up to
// `BWD_SEG_MAX_FOLD_DEPTH` (the depth-3 pyramid); the EVAL loop's inline classes
// never exceed `BWD_SEG_MAX_INLINE_FOLD_DEPTH`, because the assignment matrix
// publishes at depth 3 instead of inlining it (`assign_class`, and
// `BWD_COEFF_PUBLISH_TARGET_DEPTH` is the same 3).
constexpr u32 BWD_SEG_MAX_FOLD_DEPTH = BWD_COEFF_MAX_FOLD_DEPTH;
constexpr u32 BWD_SEG_MAX_INLINE_FOLD_DEPTH = 2;

static_assert(BWD_SEG_MAX_FOLD_DEPTH == 3, "max fold depth drift");
static_assert(BWD_SEG_MAX_FOLD_DEPTH == BWD_COEFF_PUBLISH_TARGET_DEPTH,
              "the publication threshold is what bounds the inline depth: at and past it the prologue materializes");
static_assert(BWD_SEG_MAX_INLINE_FOLD_DEPTH + 1 == BWD_SEG_MAX_FOLD_DEPTH, "the inline depth cap must be one below the publication threshold");

// Fold-weight bank (flat fold, spec 2026-07-28): slots hold only q >= 1 per
// delta — the q = 0 coefficient is the difference form's implicit 1 — in
// PHYSICAL-offset order (challenge j on bit (delta-1-j) of q; the bit reversal
// is baked in by the prelude's store permutation, never applied in a kernel).
constexpr u32 BWD_SEG_FOLD_WEIGHT_SLOTS = 11;
constexpr u32 BWD_SEG_FOLD_WEIGHT_BASE_D1 = 0;
constexpr u32 BWD_SEG_FOLD_WEIGHT_BASE_D2 = 1;
constexpr u32 BWD_SEG_FOLD_WEIGHT_BASE_D3 = 4;
static_assert(BWD_SEG_FOLD_WEIGHT_BASE_D2 == BWD_SEG_FOLD_WEIGHT_BASE_D1 + 1, "D1 stores one slot");
static_assert(BWD_SEG_FOLD_WEIGHT_BASE_D3 == BWD_SEG_FOLD_WEIGHT_BASE_D2 + 3, "D2 stores three slots");
static_assert(BWD_SEG_FOLD_WEIGHT_SLOTS == BWD_SEG_FOLD_WEIGHT_BASE_D3 + 7, "D3 stores seven slots");

// ── Source table ────────────────────────────────────────────────────────────

// One entry of the per-launch source table: which window a source reads through,
// which column of it, and how THIS round resolves it.
//
// `source_class` is Rust's `class` field (C++ cannot spell that name); the
// offsets are what the ABI pins, not the spelling.
// `alignas(4)` STATES the record's own requirement: `&source[slot]` must be 0 mod 4
// for a 32-bit load of this 4-byte record to be aligned at all. It used to also MOVE
// the array — `list_offset[BWD_SEG_MAX_K + 1]` is 33 x u16 = 66 bytes, which put the
// whole descriptor tail at 2 mod 4, so the array start needed two bytes of padding in
// front of it. `num_immediates` is the FIFTH u16 of the count block and brings the
// tail back to 0 mod 4, so the array is now naturally aligned and the declaration
// costs nothing. It stays because the record's alignment must not be an accident of
// the fields that happen to precede it: the only implicit padding left in the
// descriptor is the four bytes before `window` (asserted below).
//
// WHAT THIS DOES NOT BUY, measured rather than predicted: on CUDA 13.3 the
// alignment alone does NOT collapse the record read into one 32-bit `LDC`.
// `cont_const_epi_plane`'s record reads are instruction-for-instruction identical
// before and after — `LDC.U8` + `LDC.U8` + `LDC.U16` where all three fields are
// live, `LDC.U8` + `LDC.U16` where the class is dead — with only the base offset
// shifted 0x442a -> 0x442c, and all twenty device-linked symbols keep their exact
// register counts. Collapsing the loads needs the record to be READ as one word (a
// `u32` load plus shifts, which changes the ABI's access pattern rather than its
// layout); this annotation is only what makes such a read LEGAL.
struct alignas(4) bwd_seg_source_record {
  // Slot in `bwd_seg_desc::window`.
  u8 window;
  // One of the `BWD_SEG_SOURCE_CLASS_*` values.
  u8 source_class;
  // Column WITHIN the window: the address is
  // `read_base + column * read_stride_bytes`.
  u16 column;
};

static_assert(sizeof(bwd_seg_source_record) == 4, "bwd_seg_source_record/BwdSegSourceRecord ABI size drift");
static_assert(alignof(bwd_seg_source_record) == 4, "bwd_seg_source_record ABI alignment drift");
static_assert(__builtin_offsetof(bwd_seg_source_record, window) == 0, "window ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_source_record, source_class) == 1, "class ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_source_record, column) == 2, "column ABI offset drift");

// ── The inline-program descriptor (section 3) ───────────────────────────────

// The complete by-value launch descriptor, passed as a single
// `__grid_constant__` kernel parameter.
//
// Field order is the ABI. `program` sits at offset 0 — 16-byte aligned by the
// descriptor's own alignment, at no cost in padding — and the launch tail's
// pointers land naturally aligned after the arrays. FOUR bytes of implicit
// padding precede `window` (the source array is 4-byte-aligned, the window array
// 8-byte-aligned); rustc inserts the same gap by the same rule and both sides
// assert every offset, so it needs no explicit field.
struct alignas(BWD_SEG_DESC_ALIGN) bwd_seg_desc {
  // The lean term stream, embedded by value. Warp `w` walks
  // `program[list_offset[w] .. list_offset[w + 1]]`.
  u16 program[BWD_SEG_PROGRAM_WORD_CAP];
  // `k + 1` word offsets into `program`; `list_offset[k]` is the END of the
  // stream, which is why the descriptor needs no program-length field.
  u16 list_offset[BWD_SEG_MAX_K + 1];
  // Term lists, i.e. warps in the block. `blockDim == 32 * k`.
  u16 k;
  // Lean RECORDS across all `k` lists — terms PLUS the one header record per
  // group the grouped wire spends (section 4.4), so
  // `list_offset[k] == LEAN_WORDS_PER_TERM * record_count`. Never read by the
  // executor (the list offsets bound every walk); host lowering keeps it for the
  // validator and the disassembler.
  u16 record_count;
  // Live entries of `source`. Never read by the executor: every slot a wire
  // record names is bounds-checked host-side
  // (`BwdSegLowerError::SourceSlotOutOfRange`).
  u16 num_sources;
  // Leading entries of `fold_source` the JAOT prologue folds.
  u16 num_foldable;
  // Live entries of `immediates`; zero for an ungrouped program.
  u16 num_immediates;
  // Source slots the prologue folds, in FOLD order: warp `w` takes
  // `s = w, w + k, w + 2k, ...`. The order is a performance contract
  // (section 7) — the sources the eval loop touches EARLIEST are folded LAST, so
  // they are the warmest in L1 when eval starts. The kernel just walks it.
  u16 fold_source[BWD_SEG_MAX_SOURCES];
  // The per-launch source table; entries at and past `num_sources` are
  // zero-filled and never read.
  bwd_seg_source_record source[BWD_SEG_MAX_SOURCES];
  // Live source windows, IMPORTED from the cell-era descriptor rather than
  // forked, so both lineages share one window layout and one publication policy.
  bwd_coeff_source_window window[BWD_SEG_SOURCE_WINDOW_CAP];
  // The per-thread `acc_c0` seed as RESOLVED E4 limbs in their IN-MEMORY
  // (Montgomery) representation, all-zero when the layer has none. Zero is a
  // safe "absent" value — an additive identity, not a sentinel — so there is no
  // `*_NONE` constant here and no bank lookup on the seed path.
  u32 c_init[4];
  // This launch's immediate table (section 4.5): the BASE-field scalars a grouped
  // member record multiplies its group's shared core coefficient by, in the
  // encoder's ascending-deduplicated order, as raw limbs in their IN-MEMORY
  // (Montgomery) representation — the same convention as `c_init`, so no
  // conversion happens here. Indexed by the `ImmediateId` a member record carries
  // in its coefficient field; entries at and past `num_immediates` are zero-filled
  // and never read, and the `±1` immediates are reserved wire ids that consume no
  // slot. Placed after `c_init` so the pointer tail keeps its natural alignment:
  // 512 words is 2 KiB, a whole number of 16-byte quanta.
  u32 immediates[BWD_SEG_MAX_IMMEDIATES];
  // Evaluated E4 coefficients for the `ptr` loader specialization; the `const`
  // loader reads `ab_gkr_bwd_seg_coeff_bank` and ignores this. Reserved-inclusive
  // either way: `[ONE, NEG_ONE, recipes...]`.
  const e4 *coefficients;
  // Production factored-eq low table; high tables remain in `ab_gkr_eq_high`.
  const e4 *eq_low;
  // `2 * logical_rows` entries: `eq * acc_c0` in `[0, logical_rows)` and
  // `eq * acc_c2` in `[logical_rows, 2 * logical_rows)`.
  e4 *contributions;
  gkr_eq_sizes eq_sizes;
  // Bank entries, reserved literals included. Never read by the executor: a
  // coefficient id past the payload is a host rejection
  // (`BwdSegLowerError::CoefficientIndexPastBank`), and the device indexes raw.
  u32 n_coefficients;
  // Rows this launch evaluates. Also the contribution half-stride and the
  // endpoint half-stride of every target-depth backing.
  u32 logical_rows;
  // Explicit: makes the SIZE a multiple of the alignment without implicit
  // trailing padding the two languages would have to agree on. Never read.
  u32 pad[1];
};

static_assert(sizeof(bwd_seg_desc) == 26416, "bwd_seg_desc/BwdSegDesc ABI size drift");
static_assert(alignof(bwd_seg_desc) == BWD_SEG_DESC_ALIGN, "bwd_seg_desc ABI alignment drift");
// The final authority on the descriptor's shape. An overflow needs a tighter
// encoding, never a second storage path.
static_assert(sizeof(bwd_seg_desc) <= BWD_SEG_DESC_CAP, "bwd_seg_desc exceeds the __grid_constant__ parameter budget");
static_assert(__builtin_offsetof(bwd_seg_desc, program) == 0, "program ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_desc, list_offset) == 17248, "list_offset ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_desc, k) == 17314, "k ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_desc, record_count) == 17316, "record_count ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_desc, num_sources) == 17318, "num_sources ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_desc, num_foldable) == 17320, "num_foldable ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_desc, num_immediates) == 17322, "num_immediates ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_desc, fold_source) == 17324, "fold_source ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_desc, source) == 19468, "source ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_desc, window) == 23760, "window ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_desc, c_init) == 24304, "c_init ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_desc, immediates) == 24320, "immediates ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_desc, coefficients) == 26368, "coefficients ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_desc, eq_low) == 26376, "eq_low ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_desc, contributions) == 26384, "contributions ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_desc, eq_sizes) == 26392, "eq_sizes ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_desc, n_coefficients) == 26404, "n_coefficients ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_desc, logical_rows) == 26408, "logical_rows ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_desc, pad) == 26412, "pad ABI offset drift");
// The program stream starts 16-byte aligned so it can be buffered through wide
// loads, and `pad` is the tail that makes the size a whole number of quanta.
static_assert(__builtin_offsetof(bwd_seg_desc, program) % BWD_SEG_DESC_ALIGN == 0, "the program stream must start 16-byte aligned");
static_assert(__builtin_offsetof(bwd_seg_desc, pad) + sizeof(u32) == sizeof(bwd_seg_desc), "pad must be the descriptor tail");
static_assert(sizeof(bwd_seg_desc) % BWD_SEG_DESC_ALIGN == 0, "the descriptor size must be a whole number of alignment quanta");
// The four-byte gap is implicit on BOTH sides, so it is asserted rather than
// spelled: this is the arithmetic that proves it is exactly four.
static_assert(__builtin_offsetof(bwd_seg_desc, window) - (__builtin_offsetof(bwd_seg_desc, source) + sizeof(bwd_seg_desc::source)) == 4,
              "the implicit gap before `window` is not the four bytes both halves assert");

// ── The device-program A/B twin (section 5) ─────────────────────────────────

// `bwd_seg_desc` field-for-field, with the inline `program` array REPLACED by a
// device pointer and its length. Dropping the array is the whole point: keeping
// it and merely not reading it would leave 17,248 bytes resident in every
// launch's parameter space and measure nothing.
struct alignas(BWD_SEG_DESC_ALIGN) bwd_seg_progptr_desc {
  // Device-resident lean term stream, `program_words` u16 words long.
  const u16 *program;
  u32 program_words;
  // Offsets index the DEVICE stream here; otherwise as `bwd_seg_desc`.
  u16 list_offset[BWD_SEG_MAX_K + 1];
  u16 k;
  u16 record_count;
  u16 num_sources;
  u16 num_foldable;
  u16 num_immediates;
  u16 fold_source[BWD_SEG_MAX_SOURCES];
  bwd_seg_source_record source[BWD_SEG_MAX_SOURCES];
  bwd_coeff_source_window window[BWD_SEG_SOURCE_WINDOW_CAP];
  u32 c_init[4];
  // Inline in BOTH twins: only the PROGRAM moves to device memory in this A/B, so
  // the immediate table stays by value and the comparison isolates the program.
  u32 immediates[BWD_SEG_MAX_IMMEDIATES];
  const e4 *coefficients;
  const e4 *eq_low;
  e4 *contributions;
  gkr_eq_sizes eq_sizes;
  u32 n_coefficients;
  u32 logical_rows;
  // Three words rather than one: the head is 12 bytes here instead of 17,248, so
  // the tail lands elsewhere modulo 16.
  u32 pad[3];
};

static_assert(sizeof(bwd_seg_progptr_desc) == 9184, "bwd_seg_progptr_desc/BwdSegProgPtrDesc ABI size drift");
static_assert(alignof(bwd_seg_progptr_desc) == BWD_SEG_DESC_ALIGN, "bwd_seg_progptr_desc ABI alignment drift");
static_assert(sizeof(bwd_seg_progptr_desc) <= BWD_SEG_DESC_CAP, "bwd_seg_progptr_desc exceeds the __grid_constant__ parameter budget");
static_assert(__builtin_offsetof(bwd_seg_progptr_desc, program) == 0, "progptr program ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_progptr_desc, program_words) == 8, "progptr program_words ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_progptr_desc, list_offset) == 12, "progptr list_offset ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_progptr_desc, k) == 78, "progptr k ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_progptr_desc, record_count) == 80, "progptr record_count ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_progptr_desc, num_sources) == 82, "progptr num_sources ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_progptr_desc, num_foldable) == 84, "progptr num_foldable ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_progptr_desc, num_immediates) == 86, "progptr num_immediates ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_progptr_desc, fold_source) == 88, "progptr fold_source ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_progptr_desc, source) == 2232, "progptr source ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_progptr_desc, window) == 6520, "progptr window ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_progptr_desc, c_init) == 7064, "progptr c_init ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_progptr_desc, immediates) == 7080, "progptr immediates ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_progptr_desc, coefficients) == 9128, "progptr coefficients ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_progptr_desc, eq_low) == 9136, "progptr eq_low ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_progptr_desc, contributions) == 9144, "progptr contributions ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_progptr_desc, eq_sizes) == 9152, "progptr eq_sizes ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_progptr_desc, n_coefficients) == 9164, "progptr n_coefficients ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_progptr_desc, logical_rows) == 9168, "progptr logical_rows ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_progptr_desc, pad) == 9172, "progptr pad ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_progptr_desc, pad) + 3 * sizeof(u32) == sizeof(bwd_seg_progptr_desc), "progptr pad must be the descriptor tail");
static_assert(sizeof(bwd_seg_progptr_desc) % BWD_SEG_DESC_ALIGN == 0, "the progptr descriptor size must be a whole number of alignment quanta");
// The A/B twin really drops the array rather than leaving it resident.
static_assert(sizeof(bwd_seg_desc) - sizeof(bwd_seg_progptr_desc) >= BWD_SEG_PROGRAM_BYTE_CAP - BWD_SEG_DESC_ALIGN,
              "the progptr twin must actually drop the by-value program");
// No gap here: the progptr `source` array ends exactly at `window`.
static_assert(__builtin_offsetof(bwd_seg_progptr_desc, window) - (__builtin_offsetof(bwd_seg_progptr_desc, source) + sizeof(bwd_seg_progptr_desc::source)) == 0,
              "the progptr `source` array must end exactly at `window`, with no gap");

// ── Epilogue specialization (section 3) ─────────────────────────────────────
//
// The cross-warp reduction the eval loop's per-warp partials need. NO default is
// pre-committed: all three are compiled and the A/B decides.
enum bwd_seg_epilogue : u32 {
  // Serial read-modify-write through ONE 32-lane (acc_c0, acc_c2) plane pair:
  // K - 1 barriers, ~1 KiB of shared memory.
  BWD_SEG_EPILOGUE_STAGED = 0,
  // Incumbent-style `[K - 1][32]` plane REUSED for c0 then c2: 3 barriers,
  // ~15.5 KiB at K = 32.
  BWD_SEG_EPILOGUE_PLANE = 1,
  // Both planes at once: 1 barrier, ~31 KiB at K = 32, which eats the L1
  // carveout.
  BWD_SEG_EPILOGUE_WIDE = 2,
};

// Shared-memory bytes each epilogue needs at `k` warps. The Rust launcher
// computes the same three numbers; they are the dynamic-smem argument of the
// launch, so a disagreement is an out-of-bounds shared access rather than a
// build failure — which is why they are spelled once here and mirrored there.
constexpr u32 bwd_seg_epilogue_smem_bytes(const u32 epilogue, const u32 k) {
  if (k < 2)
    return 0; // K == 1: warp 0's register partials ARE the block result.
  switch (epilogue) {
  case BWD_SEG_EPILOGUE_STAGED:
    return 2 * BWD_SEG_WARP_LANES * static_cast<u32>(sizeof(e4));
  case BWD_SEG_EPILOGUE_PLANE:
    return (k - 1) * BWD_SEG_WARP_LANES * static_cast<u32>(sizeof(e4));
  default:
    return 2 * (k - 1) * BWD_SEG_WARP_LANES * static_cast<u32>(sizeof(e4));
  }
}

static_assert(bwd_seg_epilogue_smem_bytes(BWD_SEG_EPILOGUE_STAGED, 1) == 0, "K == 1 needs no plane");
static_assert(bwd_seg_epilogue_smem_bytes(BWD_SEG_EPILOGUE_STAGED, BWD_SEG_MAX_K) == 1024, "staged plane pair size drift");
static_assert(bwd_seg_epilogue_smem_bytes(BWD_SEG_EPILOGUE_PLANE, BWD_SEG_MAX_K) == 15872, "plane size drift");
static_assert(bwd_seg_epilogue_smem_bytes(BWD_SEG_EPILOGUE_WIDE, BWD_SEG_MAX_K) == 31744, "wide plane pair size drift");
// Every variant stays inside the 48 KB a block gets without an opt-in carveout.
static_assert(bwd_seg_epilogue_smem_bytes(BWD_SEG_EPILOGUE_WIDE, BWD_SEG_MAX_K) <= 48 * 1024, "the wide epilogue exceeds the default shared-memory limit");

// ── AccPlacement: the design's register fallback ladder, measured ────────────
//
// Design section 6 states the ladder for a loop that lands above the 40-register
// target: (a) both accumulators in registers, (b) ONE per thread in shared
// memory, (c) both. (b) and (c) buy registers with a `ld.shared` + `st.shared`
// pair on every term that touches the accumulator, so they are only ever worth it
// if the occupancy gain dominates — which is a measurement, not a prediction, and
// is why all three are compiled rather than one being chosen up front.
//
// The carveout is PER THREAD and laid out `[word][lane]`: word `w` of thread `t`
// sits at `words[w * threads + t]`, so the 32 lanes of a warp touch 32 CONSECUTIVE
// 4-byte banks in every one of the four accesses. Conflict-free — but so is the
// `e4`-per-thread layout, because an `LDS.128`/`STS.128` issues in quarter-warp
// phases of 8 lanes x 16 B, each covering all 32 banks exactly once. The
// transposition therefore avoids no conflict; it costs four shared accesses and
// three runtime address adds per term where one of each would do. Re-addressing is
// parked (audit I-4, spec section 8).
enum : u32 {
  // (a): both accumulators stay in registers. The default and the only placement
  // the fifteen release symbols use.
  BWD_SEG_ACC_IN_REGISTERS = 0,
  // (b): `acc_c2` per thread in shared memory.
  BWD_SEG_ACC_C2_SMEM = 1,
  // (c): both accumulators per thread in shared memory.
  BWD_SEG_ACC_BOTH_SMEM = 2,
};

// Accumulators this placement keeps in shared memory, per thread.
constexpr u32 bwd_seg_acc_smem_slots(const u32 placement) {
  switch (placement) {
  case BWD_SEG_ACC_C2_SMEM:
    return 1;
  case BWD_SEG_ACC_BOTH_SMEM:
    return 2;
  default:
    return 0;
  }
}

// Shared-memory bytes the accumulator carveout needs at `k` warps. Mirrored by
// the Rust launcher for the same reason `bwd_seg_epilogue_smem_bytes` is: it is a
// launch argument, so a disagreement is an out-of-bounds access, not a build
// failure.
constexpr u32 bwd_seg_acc_smem_bytes(const u32 placement, const u32 k) {
  return bwd_seg_acc_smem_slots(placement) * static_cast<u32>(sizeof(e4)) * k * BWD_SEG_WARP_LANES;
}

// Total dynamic shared memory: the epilogue's planes, then the accumulator
// carveout. The accumulators sit AFTER the planes so the epilogue's own addressing
// is untouched by the placement.
constexpr u32 bwd_seg_dynamic_smem_bytes(const u32 epilogue, const u32 placement, const u32 k) {
  return bwd_seg_epilogue_smem_bytes(epilogue, k) + bwd_seg_acc_smem_bytes(placement, k);
}

static_assert(bwd_seg_acc_smem_bytes(BWD_SEG_ACC_IN_REGISTERS, BWD_SEG_MAX_K) == 0, "the register placement must carve out nothing");
static_assert(bwd_seg_acc_smem_bytes(BWD_SEG_ACC_C2_SMEM, 4) == 2048, "acc_c2 carveout size drift at the measured K");
static_assert(bwd_seg_acc_smem_bytes(BWD_SEG_ACC_BOTH_SMEM, 4) == 4096, "both-accumulator carveout size drift at the measured K");
static_assert(bwd_seg_acc_smem_bytes(BWD_SEG_ACC_BOTH_SMEM, BWD_SEG_MAX_K) == 32768, "both-accumulator carveout size drift at the maximum K");
// The widest rung the matrix can launch still fits the default 48 KB block budget,
// so no opt-in carveout is needed for any of them.
static_assert(bwd_seg_dynamic_smem_bytes(BWD_SEG_EPILOGUE_PLANE, BWD_SEG_ACC_BOTH_SMEM, BWD_SEG_MAX_K) <= 48 * 1024,
              "the widest accumulator rung exceeds the default shared-memory limit");

} // namespace airbender::prover::gkr

// This lineage's OWN coefficient bank. Stream-ordered `__constant__` memory,
// uploaded by the host with the reserved-inclusive payload
// `[ONE, NEG_ONE, recipes...]` and indexed RAW by the wire's thirteen-bit
// coefficient id. Declared at global scope (NTT pattern) so the `const` loader
// can name the symbol directly, which is what LDC emission requires.
EXTERN __device__ __constant__ e4 ab_gkr_bwd_seg_coeff_bank[airbender::prover::gkr::BWD_SEG_CONST_BANK];

// The ONE authority on fold challenges, which is why this lineage's descriptor
// carries no challenge pointer: the incumbent main-layer claim point, DEFINED by
// `round1_flat_warp_split.cu` and declared identically by `continuation.cuh`. The
// fold-weight prelude reads index `round - delta + j` — front-indexed, so a
// delta-step catch-up at round `r` reads `[r - delta, r)`, which is the span host
// lowering bounds with `claim_point.len() >= round`. No executor kernel reads it:
// the weights the folds consume are the prelude's product of these challenges.
EXTERN __device__ __constant__ e4 ab_gkr_main_layer_claim_point[airbender::prover::gkr::GKR_MAIN_LAYER_CLAIM_POINT_LEN];

// The flat fold's weight table: one entry per (delta, q >= 1) pair, in the
// physical-offset order the prelude's store permutation fixes. Built ONCE per
// round from the claim point by `ab_gkr_bwd_seg_build_fold_weights_kernel`
// below, which writes it through this symbol's own address — device code cannot
// name a `__constant__` as a store target. Declared at global scope for the same
// reason the coefficient bank is: the fold names the symbol directly, which is
// what LDC emission requires.
EXTERN __device__ __constant__ e4 ab_gkr_bwd_seg_fold_weights[airbender::prover::gkr::BWD_SEG_FOLD_WEIGHT_SLOTS];

// ── The kernel matrix (section 3, 5) ────────────────────────────────────────
//
// Four axes, only the listed cells instantiated:
//
//   family          r0 | cont
//   coeff loader    const (the `__constant__` bank) | ptr (`desc.coefficients`)
//   program source  inline (`desc.program`) | devptr (cont + const only)
//   epilogue        staged | plane | wide
//
// The register lever on these symbols is `__maxnreg__`, not `__launch_bounds__`:
// one symbol serves every `K in 1..32`, so `maxT` would have to be 1024, which
// pins `minB = 1` and a 64-register budget — `__launch_bounds__(1024, 1)` is a
// NO-OP here and never bought anything. The declarations carry no qualifier
// because a `__global__` attribute belongs on the DEFINITION; the pins and the
// swept continuation budget live in `segmented_vm.cu`'s kernel matrix, which
// states the band arithmetic each number comes from.
EXTERN __global__ void ab_gkr_bwd_seg_r0_const_epi_staged_kernel(const __grid_constant__ airbender::prover::gkr::bwd_seg_desc desc);
EXTERN __global__ void ab_gkr_bwd_seg_r0_const_epi_plane_kernel(const __grid_constant__ airbender::prover::gkr::bwd_seg_desc desc);
EXTERN __global__ void ab_gkr_bwd_seg_r0_const_epi_wide_kernel(const __grid_constant__ airbender::prover::gkr::bwd_seg_desc desc);
EXTERN __global__ void ab_gkr_bwd_seg_r0_ptr_epi_staged_kernel(const __grid_constant__ airbender::prover::gkr::bwd_seg_desc desc);
EXTERN __global__ void ab_gkr_bwd_seg_r0_ptr_epi_plane_kernel(const __grid_constant__ airbender::prover::gkr::bwd_seg_desc desc);
EXTERN __global__ void ab_gkr_bwd_seg_r0_ptr_epi_wide_kernel(const __grid_constant__ airbender::prover::gkr::bwd_seg_desc desc);
EXTERN __global__ void ab_gkr_bwd_seg_cont_const_epi_staged_kernel(const __grid_constant__ airbender::prover::gkr::bwd_seg_desc desc);
EXTERN __global__ void ab_gkr_bwd_seg_cont_const_epi_plane_kernel(const __grid_constant__ airbender::prover::gkr::bwd_seg_desc desc);
EXTERN __global__ void ab_gkr_bwd_seg_cont_const_epi_wide_kernel(const __grid_constant__ airbender::prover::gkr::bwd_seg_desc desc);
EXTERN __global__ void ab_gkr_bwd_seg_cont_ptr_epi_staged_kernel(const __grid_constant__ airbender::prover::gkr::bwd_seg_desc desc);
EXTERN __global__ void ab_gkr_bwd_seg_cont_ptr_epi_plane_kernel(const __grid_constant__ airbender::prover::gkr::bwd_seg_desc desc);
EXTERN __global__ void ab_gkr_bwd_seg_cont_ptr_epi_wide_kernel(const __grid_constant__ airbender::prover::gkr::bwd_seg_desc desc);
EXTERN __global__ void ab_gkr_bwd_seg_cont_const_progptr_epi_staged_kernel(const __grid_constant__ airbender::prover::gkr::bwd_seg_progptr_desc desc);
EXTERN __global__ void ab_gkr_bwd_seg_cont_const_progptr_epi_plane_kernel(const __grid_constant__ airbender::prover::gkr::bwd_seg_progptr_desc desc);
EXTERN __global__ void ab_gkr_bwd_seg_cont_const_progptr_epi_wide_kernel(const __grid_constant__ airbender::prover::gkr::bwd_seg_progptr_desc desc);

// The fold-weight prelude — the one launched symbol that is not a matrix cell.
// `fold_weights` is `ab_gkr_bwd_seg_fold_weights`' own device address, so the
// kernel's only formals are that alias and the round it builds for.
EXTERN __global__ void ab_gkr_bwd_seg_build_fold_weights_kernel(e4 *fold_weights, u32 round);
