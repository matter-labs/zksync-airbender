#pragma once

// fwd-VM v2 descriptor ABI (Task 7): ONE struct, passed by value as a
// `__grid_constant__` kernel parameter (param-space limit 32,764 B). Mirrored
// field-for-field by Rust `FwdVmDesc`
// (`gpu/circuit_prover/src/prover/gkr/forward/vm/desc.rs`) with an exact-size
// static assert on both sides — if the two sides ever disagree on the size,
// that is a real ABI bug, not a number to reconcile by picking two values.
//
// Field ORDER deviates from the spec-§2 sketch on purpose: `e4` is
// `__align__(16)`, so fields are grouped by descending alignment
// (e4 -> pointers -> u32 -> u16) to keep the layout free of INTERNAL padding
// and the exact-size assert stable (27,452 field bytes + 4 B tail padding to
// the 16-B alignment = 27,456). Same members, same semantics.
//
// Caps come from the corpus census (`gkr_eval_isa/tests/fwd_vm_desc_census.rs`,
// maxima across all 11 committed with-caches fixtures) + margin. Overflow
// policy: program overflow falls back to `program_ldg`; every other cap is a
// hard lowering error (no fallback).

#include "../eval_vm_isa.cuh"
#include "flat.cuh"

namespace airbender::prover::gkr {

// --- caps (census maxima: lanes 6574, consts 27, arg-e4 7, const-e4 1, descs 296)
constexpr u32 FWD_VM_PROGRAM_CAP = 12288;      // u16 lanes, 24 KB inline
constexpr u32 FWD_VM_CONST_CAP = 40;           // bf constants
constexpr u32 FWD_VM_ARG_DERIVED_E4_CAP = 12;  // schedule-time derived e4 values
constexpr u32 FWD_VM_DESC_CAP = 370;           // packed special descriptors
constexpr u32 FWD_VM_CONST_DERIVED_E4_CAP = 8; // Task-8 __constant__ e4 bank (not in this struct);
                                               // also hosts the decoder fill (see fill_bank_idx)
constexpr u32 FWD_VM_FILL_BANK_NONE = ~0u;     // fill_bank_idx sentinel: layer has no SD_DECODER desc
constexpr u32 FWD_VM_SOURCE_WINDOW_COUNT = 64;
constexpr u32 FWD_VM_DST_SLOT_COUNT = 16;
constexpr u32 FWD_VM_MAPPING_ARENA_COUNT = 3; // generic_family / range_check_16 / timestamp

static_assert(FWD_VM_SOURCE_WINDOW_COUNT == 1u << FWD_VM_SOURCE_WINDOW_BITS, "source-window field width drift");
static_assert(FWD_VM_DST_SLOT_COUNT == 1u << FWD_VM_DST_SLOT_BITS, "destination-slot field width drift");

// --- special-descriptor strategy kinds (descs[i] kind field) -----------------
constexpr u32 SD_SINGLE_COLUMN = 0; // PeekSingleColumn: lift(mapping[row])
constexpr u32 SD_AGGREGATE = 1;     // PeekAggregate: table[mapping[row]]
constexpr u32 SD_SETUP = 2;         // PeekSetup: row < table_len ? table[row] : 0
constexpr u32 SD_DECODER = 3;       // PeekDecoder: mask[row] != 0 ? table[mapping[row]]
                                    //                            : const_derived_e4[fill_bank_idx]
constexpr u32 SD_VIRTUAL = 4;       // VirtualSetup: lift(n(vkind, gid)), no memory reads

// --- mapping-arena selectors (descs[i] arena field) ---------------------------
// Index into fwd_vm_desc::mapping_arena; the arena is column-major with column
// stride `count` u32 elements: column c = mapping_arena[a] + c * count.
constexpr u32 FWD_VM_ARENA_GENERIC_FAMILY = 0;
constexpr u32 FWD_VM_ARENA_RANGE_CHECK_16 = 1;
constexpr u32 FWD_VM_ARENA_TIMESTAMP = 2;

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

  // program oversize fallback; null when the program is inline (expected always)
  const u16 *program_ldg; // 192

  char *source_base[FWD_VM_SOURCE_WINDOW_COUNT]; // 200
  char *dst_base[FWD_VM_DST_SLOT_COUNT];         // 712

  // special-descriptor header (all schedule-time-known). Every desc mapping is
  // a COLUMN of one of these 3 contiguous u32 arenas (GpuGKRLookupMappings,
  // column-major, stride = `count`); the e4 table is the ONE shared
  // generic-lookup arena per layer (contents runtime-filled); mask
  // (execute-predicate column) is a per-circuit singleton. The decoder FILL
  // value (also a per-circuit singleton, runtime challenge-dependent) is NOT
  // pointed to from here — it lives in the `ab_gkr_fwd_vm_const_derived_e4`
  // bank at `fill_bank_idx` (same class as a ConstDerivedE4).
  const u32 *mapping_arena[FWD_VM_MAPPING_ARENA_COUNT]; // 840
  const e4 *table;                                      // 864
  const bf *mask;                                       // 872, or null

  // program header
  u32 n_instr;       // 880
  u32 program_lanes; // 884

  // column geometry, continued
  u32 source_stride_bytes[FWD_VM_SOURCE_WINDOW_COUNT]; // 888
  u32 dst_stride_bytes[FWD_VM_DST_SLOT_COUNT];         // 1144

  // banks, inline (schedule-time known)
  u32 n_consts;                // 1208
  bf consts[FWD_VM_CONST_CAP]; // 1212, Montgomery
  u32 n_arg_derived_e4;        // 1372

  // special descriptors
  u32 n_descs;            // 1376
  u32 n_const_derived_e4; // 1380: used length of the Task-8 __constant__ bank
                          // (INCLUDING the appended decoder fill slot, if any);
                          // read only under VALIDATE
  u32 fill_bank_idx;      // 1384: const-derived-e4 bank slot of the decoder fill
                          // value, or FWD_VM_FILL_BANK_NONE when the layer has
                          // no SD_DECODER desc; read only on decoder-miss rows
  u32 table_len;          // 1388

  // per-desc packed u32 (bit split above)
  u32 descs[FWD_VM_DESC_CAP]; // 1392, 1,480 B

  // geometry
  u32 count; // 2872: rows (= trace_len = mapping-arena column stride)

  // program, inline 16-bit wire lanes (gkr_eval_isa::fwd::encode)
  u16 program[FWD_VM_PROGRAM_CAP]; // 2876, 24,576 B; field bytes end at 27,452
};

static_assert(sizeof(fwd_vm_desc) == 27456, "fwd_vm_desc/FwdVmDesc ABI size drift");
static_assert(sizeof(fwd_vm_desc) <= 32764, "fwd_vm_desc exceeds the __grid_constant__ param budget");
static_assert(alignof(fwd_vm_desc) == 16, "fwd_vm_desc alignment drift (e4 is __align__(16))");
static_assert(__builtin_offsetof(fwd_vm_desc, arg_derived_e4) == 0, "arg_derived_e4 ABI offset drift");
static_assert(__builtin_offsetof(fwd_vm_desc, n_arg_derived_e4) == 1372, "n_arg_derived_e4 ABI offset drift");
static_assert(__builtin_offsetof(fwd_vm_desc, n_const_derived_e4) == 1380, "n_const_derived_e4 ABI offset drift");

} // namespace airbender::prover::gkr
