#pragma once

// CUDA half of the segmented backward VM ABI.

#include "../support/eq_inline.cuh"
#include "../support/kernel_helpers.cuh"

namespace airbender::gkr {

constexpr u32 BWD_COEFF_HEADER_COEFFICIENT_BITS = 13;
constexpr u32 BWD_COEFF_HEADER_OPCODE_BITS = 3;
// What thirteen coefficient bits can name, reserved literals included.
constexpr u32 BWD_COEFF_MAX_COEFFICIENT_ENCODINGS = 1u << BWD_COEFF_HEADER_COEFFICIENT_BITS;
static_assert(BWD_COEFF_MAX_COEFFICIENT_ENCODINGS == 8192, "coefficient encoding space drift");

// ── Source-window origin ────────────────────────────────────────────────────
//
// The BACKING field of the window's matrix — NOT the width of the values read
// through it, which comes from the term class: a continuation program folds a
// base matrix into E4.
constexpr u8 BWD_COEFF_ORIGIN_READ_BASE = 0;
constexpr u8 BWD_COEFF_ORIGIN_READ_EXT = 1;
constexpr u8 BWD_COEFF_ORIGIN_PROCEDURAL = 2;

// Procedural source kinds follow the Rust `KIND_ORDER`. NONE marks a real matrix.
constexpr u8 BWD_COEFF_PROCEDURAL_RANGE_CHECK_16_BITS = 0;
constexpr u8 BWD_COEFF_PROCEDURAL_RANGE_CHECK_TIMESTAMP = 1;
constexpr u8 BWD_COEFF_PROCEDURAL_INITS_AND_TEARDOWNS_LOW = 2;
constexpr u8 BWD_COEFF_PROCEDURAL_INITS_AND_TEARDOWNS_HIGH = 3;
constexpr u8 BWD_COEFF_PROCEDURAL_NONE = 0xff;

// Both kind ranges are contiguous, allowing translation by one offset.
static_assert(GKR_BASE_SOURCE_VIRTUAL_RANGE_CHECK_TIMESTAMP == GKR_BASE_SOURCE_VIRTUAL_RANGE_CHECK_16_BITS + 1, "virtual kind order drift");
static_assert(GKR_BASE_SOURCE_VIRTUAL_INITS_AND_TEARDOWNS_LOW == GKR_BASE_SOURCE_VIRTUAL_RANGE_CHECK_16_BITS + 2, "virtual kind order drift");
static_assert(GKR_BASE_SOURCE_VIRTUAL_INITS_AND_TEARDOWNS_HIGH == GKR_BASE_SOURCE_VIRTUAL_RANGE_CHECK_16_BITS + 3, "virtual kind order drift");
static_assert(BWD_COEFF_PROCEDURAL_RANGE_CHECK_TIMESTAMP == BWD_COEFF_PROCEDURAL_RANGE_CHECK_16_BITS + 1, "procedural kind order drift");
static_assert(BWD_COEFF_PROCEDURAL_INITS_AND_TEARDOWNS_LOW == BWD_COEFF_PROCEDURAL_RANGE_CHECK_16_BITS + 2, "procedural kind order drift");
static_assert(BWD_COEFF_PROCEDURAL_INITS_AND_TEARDOWNS_HIGH == BWD_COEFF_PROCEDURAL_RANGE_CHECK_16_BITS + 3, "procedural kind order drift");

constexpr gkr_base_source_kind bwd_coeff_procedural_source_kind(const u8 procedural_kind) {
  return static_cast<gkr_base_source_kind>(GKR_BASE_SOURCE_VIRTUAL_RANGE_CHECK_16_BITS + procedural_kind);
}

// Publish on first physical access at or beyond this depth.
constexpr u8 BWD_COEFF_PUBLISH_TARGET_DEPTH = 3;
// D0..D3: the bounded lazy-fold depths the JAOT prologue materializes over.
constexpr u32 BWD_COEFF_MAX_FOLD_DEPTH = 3;

// One addressing slot: a backing's base pointer and its column stride, plus the
// two facts that are properties of the BACKING rather than of a source — which
// kind of leaves it holds, and the procedural kind when it holds none.
//
// Sources and destinations index the same table. A fold buffer is a base and a
// stride like any other backing, so it needs no separate array; a destination
// slot's base includes the round's slot offset within its region.
struct bwd_seg_addr_slot {
  const char *base;
  u8 log2_stride;
  u8 origin;
  u8 procedural_kind;
  u8 reserved[5];
};

static_assert(sizeof(bwd_seg_addr_slot) == 16, "bwd_seg_addr_slot ABI size drift");
static_assert(alignof(bwd_seg_addr_slot) == 8, "bwd_seg_addr_slot ABI alignment drift");
static_assert(__builtin_offsetof(bwd_seg_addr_slot, base) == 0, "base ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_addr_slot, log2_stride) == 8, "log2_stride ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_addr_slot, origin) == 9, "origin ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_addr_slot, procedural_kind) == 10, "procedural_kind ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_addr_slot, reserved) == 11, "reserved ABI offset drift");

// One addressing lane: `slot:6 << 7 | column:7`, so the table has exactly as many
// slots as 6 bits address and a slot covers exactly as many columns as 7 bits do.
// `BWD_SEG_ADDR_NONE` means "this source has no destination this round".
constexpr u16 BWD_SEG_ADDR_NONE = 0xffff;
constexpr u32 BWD_SEG_ADDR_COLUMN_BITS = 7;
constexpr u32 BWD_SEG_ADDR_COLUMN_MASK = (1u << BWD_SEG_ADDR_COLUMN_BITS) - 1u;

DEVICE_FORCEINLINE u32 bwd_seg_lane_slot(const u16 lane) { return u32{lane} >> BWD_SEG_ADDR_COLUMN_BITS; }
DEVICE_FORCEINLINE u32 bwd_seg_lane_column(const u16 lane) { return u32{lane} & BWD_SEG_ADDR_COLUMN_MASK; }

// ── Capacities and launch geometry ──────────────────────────────────────────

constexpr u32 BWD_SEG_DESC_CAP = 32764;
// Keeps the inline program 16-byte aligned.
constexpr u32 BWD_SEG_DESC_ALIGN = 16;

constexpr u32 BWD_SEG_MAX_K = 16;
// Lane = row inside the 32-row tile; `tile_row0 = blockIdx.x * 32`.
constexpr u32 BWD_SEG_WARP_LANES = 32;
constexpr u32 BWD_SEG_WARP_SHIFT = 5;
constexpr u32 BWD_SEG_LANE_INDEX_MASK = BWD_SEG_WARP_LANES - 1;

static_assert(BWD_SEG_MAX_K * BWD_SEG_WARP_LANES == 512, "one warp per list");
static_assert(1u << BWD_SEG_WARP_SHIFT == BWD_SEG_WARP_LANES, "warp layout drift");
constexpr u32 BWD_SEG_MAX_PLANE_SMEM_BYTES = (BWD_SEG_MAX_K - 1) * BWD_SEG_WARP_LANES * sizeof(e4);
static_assert(BWD_SEG_MAX_PLANE_SMEM_BYTES == 7680, "segmented VM shared-memory formula drift");
static_assert(BWD_SEG_MAX_PLANE_SMEM_BYTES <= 48 * 1024, "segmented VM exceeds default shared-memory limit");
static_assert(BWD_SEG_LANE_INDEX_MASK == 31, "warp lane index mask drift");

// Coefficient-bank slots, including the two reserved literal ids.
constexpr u32 BWD_SEG_CONST_BANK = 1152;

// `bwd_seg_desc::c_init_coeff` for a layer with no `acc_c0` seed. A sentinel is
// unavoidable: `0` is `ONE`, a perfectly legal seed id. `u32` max rather than the
// first unused thirteen-bit id, so a truncation cannot turn absence into a live id.
constexpr u32 BWD_SEG_C_INIT_NONE = 0xffffffffu;
// Source-table slots: the census maximum of 1,062 rounded up to a multiple of 16
// so both source-indexed arrays are a whole number of 16-byte lines.
constexpr u32 BWD_SEG_MAX_SOURCES = 1072;
// Maximum program size in the retained circuit corpus.
constexpr u32 BWD_SEG_PROGRAM_WORD_CAP = 6472;
constexpr u32 BWD_SEG_PROGRAM_BYTE_CAP = 2 * BWD_SEG_PROGRAM_WORD_CAP;
// The table holds exactly what a 6-bit slot field addresses: no less, no more.
constexpr u32 BWD_SEG_ADDR_SLOTS = 64;
// Wire cap for one coordinate's immediate table.
constexpr u32 BWD_SEG_MAX_IMMEDIATES = 512;

static_assert(BWD_SEG_PROGRAM_BYTE_CAP == 12944, "program array byte size drift");
static_assert(BWD_SEG_PROGRAM_BYTE_CAP % BWD_SEG_DESC_ALIGN == 0, "the program array is not a whole number of 16-byte quanta");
static_assert(BWD_SEG_CONST_BANK * sizeof(e4) == 18 * 1024, "coefficient bank size drift");
static_assert(BWD_SEG_CONST_BANK * sizeof(e4) <= 64 * 1024, "the coefficient bank exceeds the per-module __constant__ budget");
// Every bank slot must be nameable by the thirteen coefficient bits of the lean
// header, reserved literals included.
static_assert(BWD_SEG_CONST_BANK <= BWD_COEFF_MAX_COEFFICIENT_ENCODINGS, "a bank slot the wire cannot name");
static_assert(BWD_SEG_MAX_SOURCES % 16 == 0, "the source arrays are not whole 16-byte lines");
static_assert(BWD_SEG_ADDR_SLOTS == 64, "address slot capacity drift");
static_assert(BWD_SEG_MAX_IMMEDIATES == 512, "immediate table capacity drift");

// ── The lean wire ───────────────────────────────────────────────────────────
//
// ```text
// word0 = [class:3 @13 | coeff_idx:13 @0]
// word1 = source_a           (slot into bwd_seg_desc::source)
// word2 = source_b           (slot, or BWD_SEG_SOURCE_NONE)
// ```
//
// Each warp walks one contiguous list.
//
constexpr u32 BWD_SEG_WORDS_PER_TERM = 3;
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

// Lean class tables (`lean::LEAN_R0_OPCODES`, `lean::LEAN_CONT_OPCODES`).
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
// ── The grouped wire ────────────────────────────────────────────────────────
//
// A coefficient GROUP is one CONTROL record followed by its `N` member records,
// contiguous, inside ONE warp's list (host lowering deals whole atoms). The header
// is NOT a term:
//
// ```text
// word0 = [class = BWD_SEG_EXT_CLASS_GROUP_HEADER @13 | core coeff_idx:13 @0]
// word1 = N, the member count (>= 2)
// word2 = flags: bit 0 = the core multiplies into acc_c0, bit 1 = into acc_c2
// ```
//
// Each member is an ordinary term record whose thirteen coefficient bits carry an
// IMMEDIATE id instead of a recipe id, so the group spends ONE `e4 x e4` core
// multiply per accumulator side for its whole run instead of one per member.
//
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

// ── Source classes ──────────────────────────────────────────────────────────
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

// Fold-weight slots hold q >= 1 per delta; q = 0 is the implicit coefficient 1.
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
struct alignas(2) bwd_seg_source_record {
  // READ address, as a lane into `bwd_seg_desc::slot`.
  u16 src;
  // Destination address in the same encoding, or `BWD_SEG_ADDR_NONE`.
  u16 cache;
  // One of the `BWD_SEG_SOURCE_CLASS_*` values.
  u8 source_class;
  // This round's fold depth for this source (`target_depth - backing_depth`).
  // Per SOURCE, not per slot: two artifact windows may read the same matrix at
  // different depths.
  u8 delta;
};

static_assert(sizeof(bwd_seg_source_record) == 6, "bwd_seg_source_record/BwdSegSourceRecord ABI size drift");
static_assert(alignof(bwd_seg_source_record) == 2, "bwd_seg_source_record ABI alignment drift");
static_assert(__builtin_offsetof(bwd_seg_source_record, src) == 0, "src ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_source_record, cache) == 2, "cache ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_source_record, source_class) == 4, "class ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_source_record, delta) == 5, "delta ABI offset drift");

// The complete by-value launch descriptor, passed as a single
// `__grid_constant__` kernel parameter.
struct alignas(BWD_SEG_DESC_ALIGN) bwd_seg_desc {
  // The lean term stream, embedded by value. Warp `w` walks
  // `program[list_offset[w] .. list_offset[w + 1]]`.
  u16 program[BWD_SEG_PROGRAM_WORD_CAP];
  // `k + 1` word offsets into `program`; `list_offset[k]` is the END of the
  // stream, which is why the descriptor needs no program-length field.
  u16 list_offset[BWD_SEG_MAX_K + 1];
  // Term lists, i.e. warps in the block. `blockDim == 32 * k`.
  u16 k;
  // Leading entries of `fold_source` the JAOT prologue folds.
  u16 num_foldable;
  // Source slots the prologue folds; warp `w` takes `w, w + k, ...`.
  u16 fold_source[BWD_SEG_MAX_SOURCES];
  bwd_seg_source_record source[BWD_SEG_MAX_SOURCES];
  // Live source windows.
  bwd_seg_addr_slot slot[BWD_SEG_ADDR_SLOTS];
  // The per-thread `acc_c0` seed as a COEFFICIENT ID, or `BWD_SEG_C_INIT_NONE`
  // when the layer has none.
  u32 c_init_coeff;
  // Base-field scalars referenced by grouped terms.
  u32 immediates[BWD_SEG_MAX_IMMEDIATES];
  // Production factored-eq low table; high tables remain in `ab_gkr_eq_high`.
  const e4 *eq_low;
  // Interleaved c0/c2 partials, two entries per warp row.
  e4 *contributions;
  gkr_eq_sizes eq_sizes;
  // Rows this launch evaluates.
  u32 logical_rows;
};

static_assert(sizeof(bwd_seg_desc) == 24672, "bwd_seg_desc/BwdSegDesc ABI size drift");
static_assert(alignof(bwd_seg_desc) == BWD_SEG_DESC_ALIGN, "bwd_seg_desc ABI alignment drift");
// The final authority on the descriptor's shape. An overflow needs a tighter
// encoding, never a second storage path.
static_assert(sizeof(bwd_seg_desc) <= BWD_SEG_DESC_CAP, "bwd_seg_desc exceeds the __grid_constant__ parameter budget");
static_assert(__builtin_offsetof(bwd_seg_desc, program) == 0, "program ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_desc, list_offset) == 12944, "list_offset ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_desc, k) == 12978, "k ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_desc, num_foldable) == 12980, "num_foldable ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_desc, fold_source) == 12982, "fold_source ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_desc, source) == 15126, "source ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_desc, slot) == 21560, "slot ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_desc, c_init_coeff) == 22584, "c_init_coeff ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_desc, immediates) == 22588, "immediates ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_desc, eq_low) == 24640, "eq_low ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_desc, contributions) == 24648, "contributions ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_desc, eq_sizes) == 24656, "eq_sizes ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_desc, logical_rows) == 24668, "logical_rows ABI offset drift");
static_assert(__builtin_offsetof(bwd_seg_desc, program) % BWD_SEG_DESC_ALIGN == 0, "the program stream must start 16-byte aligned");
static_assert(sizeof(bwd_seg_desc) % BWD_SEG_DESC_ALIGN == 0, "the descriptor size must be a whole number of alignment quanta");
static_assert(__builtin_offsetof(bwd_seg_desc, slot) - (__builtin_offsetof(bwd_seg_desc, source) + sizeof(bwd_seg_desc::source)) == 2,
              "the implicit gap before `slot` must match Rust");

} // namespace airbender::gkr

// Stream-ordered coefficient bank.
EXTERN __device__ __constant__ e4 ab_gkr_bwd_seg_coeff_bank[airbender::gkr::BWD_SEG_CONST_BANK];

// Main-layer fold challenges, defined in `segmented_vm.cu`.
EXTERN __device__ __constant__ e4 ab_gkr_main_layer_claim_point[airbender::gkr::GKR_MAIN_LAYER_CLAIM_POINT_LEN];

// One entry per (delta, q >= 1). Built once per round by `ab_gkr_bwd_seg_build_fold_weights_kernel` through this symbol's own address — device code cannot
// name a `__constant__` as a store target. Global scope is what LDC emission requires.
EXTERN __device__ __constant__ e4 ab_gkr_bwd_seg_fold_weights[airbender::gkr::BWD_SEG_FOLD_WEIGHT_SLOTS];

// ── Kernels ─────────────────────────────────────────────────────────────────
//
EXTERN __global__ void ab_gkr_bwd_seg_r0_const_epi_plane_kernel(const __grid_constant__ airbender::gkr::bwd_seg_desc desc);
EXTERN __global__ void ab_gkr_bwd_seg_cont_const_epi_plane_kernel(const __grid_constant__ airbender::gkr::bwd_seg_desc desc);

EXTERN __global__ void ab_gkr_bwd_seg_build_fold_weights_kernel(e4 *fold_weights, u32 round);
