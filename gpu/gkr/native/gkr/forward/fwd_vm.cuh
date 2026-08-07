#pragma once

// CUDA half of the forward VM descriptor ABI.

#include "../eval_vm_isa.cuh"
#include "../support/kernel_helpers.cuh"

namespace airbender::gkr {

// --- caps (census maxima: lanes 6574, consts 27, arg-e4 7, const-e4 1, descs 296)
constexpr u32 FWD_VM_PROGRAM_CAP = 12288;      // u16 lanes, 24 KB inline
constexpr u32 FWD_VM_CONST_CAP = 64;           // compiled + runtime bf constants
constexpr u32 FWD_VM_ARG_DERIVED_E4_CAP = 12;  // schedule-time derived e4 values
constexpr u32 FWD_VM_DESC_CAP = 370;           // packed special descriptors
constexpr u32 FWD_VM_CONST_DERIVED_E4_CAP = 8; // Includes the optional decoder fill.
constexpr u32 FWD_VM_SOURCE_WINDOW_COUNT = 64;
constexpr u32 FWD_VM_DST_SLOT_COUNT = 16;
constexpr u32 FWD_VM_MAPPING_ARENA_COUNT = 3; // generic_family / range_check_16 / timestamp

static_assert(FWD_VM_SOURCE_WINDOW_COUNT == 1u << FWD_VM_SOURCE_WINDOW_BITS, "source-window field width drift");
static_assert(FWD_VM_DST_SLOT_COUNT == 1u << FWD_VM_DST_SLOT_BITS, "destination-slot field width drift");

// --- special-descriptor strategy kinds (descs[i] kind field) -----------------
constexpr u32 SD_SINGLE_COLUMN = 0;  // PeekSingleColumn: lift(mapping[row])
constexpr u32 SD_AGGREGATE = 1;      // PeekAggregate: table[mapping[row]]
constexpr u32 SD_SETUP = 2;          // PeekSetup: row < table_len ? table[row] : 0
constexpr u32 SD_DECODER = 3;        // PeekDecoder: mask[row] != 0 ? table[mapping[row]]
                                     //                            : const_derived_e4[last]
constexpr u32 SD_VIRTUAL = 4;        // VirtualSetup: lift(n(vkind, gid)), no memory reads
constexpr u32 SD_INITS_TOP_BITS = 5; // runtime init/teardown address prefix

// --- mapping-arena selectors (descs[i] arena field) ---------------------------
// Index into fwd_vm_desc::mapping_arena; the arena is column-major with column
// stride `count` u32 elements: column c = mapping_arena[a] + c * count.

// --- packed per-descriptor u32 -----------------------------------------------
// { kind:3 [0..3) | arena:2 [3..5) | set_index:16 [5..21) | vkind:3 [21..24) |
//   rsvd:8 [24..32) } — set_index needs 16 bits (blake2 L0 has 208 generic
// sets); vkind is the native `gkr_base_source_kind` value (2..=5) stored
// VERBATIM (../support/descriptors.cuh:12-18; pinned by Rust const asserts).
constexpr u32 FWD_VM_DESC_KIND_SHIFT = 0;
constexpr u32 FWD_VM_DESC_KIND_MASK = 0x7;
constexpr u32 FWD_VM_DESC_ARENA_SHIFT = 3;
constexpr u32 FWD_VM_DESC_ARENA_MASK = 0x3;
constexpr u32 FWD_VM_DESC_SET_INDEX_SHIFT = 5;
constexpr u32 FWD_VM_DESC_SET_INDEX_MASK = 0xffff;
constexpr u32 FWD_VM_DESC_VKIND_SHIFT = 21;
constexpr u32 FWD_VM_DESC_VKIND_MASK = 0x7;

struct fwd_vm_desc {
  // schedule-time-known derived e4 values, inline (16-aligned e4 first: zero padding)
  e4 arg_derived_e4[FWD_VM_ARG_DERIVED_E4_CAP]; // offset 0, 192 B

  char *source_base[FWD_VM_SOURCE_WINDOW_COUNT]; // 192
  char *dst_base[FWD_VM_DST_SLOT_COUNT];         // 704

  // special-descriptor header (all schedule-time-known). Every desc mapping is
  // a COLUMN of one of these 3 contiguous u32 arenas (GpuGKRLookupMappings,
  // column-major, stride = `count`); the e4 table is the ONE shared
  // generic-lookup arena per layer (contents runtime-filled); mask
  // (execute-predicate column) is a per-circuit singleton. The decoder FILL
  // value occupies the final `ab_gkr_fwd_vm_const_derived_e4` bank slot.
  const u32 *mapping_arena[FWD_VM_MAPPING_ARENA_COUNT]; // 832
  const e4 *table;                                      // 856
  const bf *mask;                                       // 864, or null

  // program header
  u32 n_instr; // 872

  // column geometry, continued
  u32 source_stride_bytes[FWD_VM_SOURCE_WINDOW_COUNT]; // 876
  u32 dst_stride_bytes[FWD_VM_DST_SLOT_COUNT];         // 1132

  // banks, inline (schedule-time known)
  bf consts[FWD_VM_CONST_CAP]; // 1196, Montgomery

  // special descriptors
  u32 table_len; // 1452

  // per-desc packed u32 (bit split above)
  u32 descs[FWD_VM_DESC_CAP]; // 1456, 1,480 B

  // geometry
  u32 count; // 2936: rows (= trace_len = mapping-arena column stride)

  // program, inline 16-bit wire lanes
  u16 program[FWD_VM_PROGRAM_CAP]; // 2940, 24,576 B
};

static_assert(sizeof(fwd_vm_desc) == 27520, "fwd_vm_desc/FwdVmDesc ABI size drift");
static_assert(sizeof(fwd_vm_desc) <= 32764, "fwd_vm_desc exceeds the __grid_constant__ param budget");
static_assert(alignof(fwd_vm_desc) == 16, "fwd_vm_desc alignment drift (e4 is __align__(16))");
static_assert(__builtin_offsetof(fwd_vm_desc, arg_derived_e4) == 0, "arg_derived_e4 ABI offset drift");

} // namespace airbender::gkr
