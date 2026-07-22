#pragma once

// Backward-evaluation VM descriptor ABI. The descriptor is passed by value as
// a __grid_constant__ kernel parameter and is mirrored field-for-field by
// Rust BwdVmDesc in src/prover/gkr/backward/vm/desc.rs.

#include "../eval_vm_isa.cuh"
#include "flat.cuh"

namespace airbender::prover::gkr {

constexpr u32 BWD_VM_PROGRAM_CAP = 1744;
constexpr u32 BWD_VM_SOURCE_WINDOW_CAP = 4;
constexpr u32 BWD_VM_SPECIAL_CAP = 147;
constexpr u32 BWD_VM_COEFFICIENT_CAP = 145;
constexpr u32 BWD_VM_CELL_CAP = 18;

// These channels reuse existing exact shared ABI banks. Their add/sub census
// maxima are zero; the capacities are not growth margin.
constexpr u32 BWD_VM_BF_CONSTANT_CAP = 40;
constexpr u32 BWD_VM_ARG_DERIVED_E4_CAP = 12;
constexpr u32 BWD_VM_CONST_DERIVED_E4_CAP = 8;

constexpr u32 BWD_VM_SPECIAL_KIND_COEFFICIENT = 0;
constexpr u32 BWD_VM_SPECIAL_KIND_ACC_INIT = 1;
constexpr u32 BWD_VM_SPECIAL_KIND_VIRTUAL_SETUP = 2;
constexpr u32 BWD_VM_SPECIAL_KIND_BITS = 2;
constexpr u32 BWD_VM_SPECIAL_KIND_MASK = (1u << BWD_VM_SPECIAL_KIND_BITS) - 1;
constexpr u32 BWD_VM_SPECIAL_PAYLOAD_SHIFT = BWD_VM_SPECIAL_KIND_BITS;
constexpr u32 BWD_VM_SPECIAL_PAYLOAD_MASK = ~0u >> BWD_VM_SPECIAL_KIND_BITS;

constexpr u8 BWD_VM_ORIGIN_FIELD_BASE = 0;
constexpr u8 BWD_VM_ORIGIN_FIELD_EXT = 1;

constexpr u32 BWD_VM_VIRTUAL_RANGE_CHECK_16_BITS = 0;
constexpr u32 BWD_VM_VIRTUAL_RANGE_CHECK_TIMESTAMP = 1;
constexpr u32 BWD_VM_VIRTUAL_INITS_AND_TEARDOWNS_LOW = 2;
constexpr u32 BWD_VM_VIRTUAL_INITS_AND_TEARDOWNS_HIGH = 3;

struct bwd_vm_source_window {
  const char *read_base;
  char *publish_base;
  u32 read_stride_bytes;
  u32 publish_stride_bytes;
  u8 backing_depth;
  u8 target_depth;
  u8 origin_field;
  u8 materialize;
};

struct bwd_vm_special {
  u32 packed;
};

struct bwd_vm_desc {
  e4 arg_derived_e4[BWD_VM_ARG_DERIVED_E4_CAP];
  const e4 *round_challenges;
  const e4 *eq_low;
  e4 *contributions;
  bwd_vm_source_window source_windows[BWD_VM_SOURCE_WINDOW_CAP];
  gkr_eq_sizes eq_sizes;
  bf bf_constants[BWD_VM_BF_CONSTANT_CAP];
  bwd_vm_special specials[BWD_VM_SPECIAL_CAP];
  u32 n_instr;
  u32 program_lanes;
  u32 n_source_windows;
  u32 n_specials;
  u32 n_coefficients;
  u32 n_bf_constants;
  u32 n_arg_derived_e4;
  u32 n_const_derived_e4;
  u32 n_round_challenges;
  u32 logical_rows;
  u32 cell_count;
  u16 program[BWD_VM_PROGRAM_CAP];
};

static_assert(BWD_VM_COEFFICIENT_CAP <= FLAT_CONST_MAX, "coefficient census exceeds shared constant bank");

static_assert(sizeof(bwd_vm_source_window) == 32, "bwd_vm_source_window ABI size drift");
static_assert(alignof(bwd_vm_source_window) == 8, "bwd_vm_source_window ABI alignment drift");
static_assert(__builtin_offsetof(bwd_vm_source_window, read_base) == 0, "read_base ABI offset drift");
static_assert(__builtin_offsetof(bwd_vm_source_window, publish_base) == 8, "publish_base ABI offset drift");
static_assert(__builtin_offsetof(bwd_vm_source_window, read_stride_bytes) == 16, "read_stride_bytes ABI offset drift");
static_assert(__builtin_offsetof(bwd_vm_source_window, publish_stride_bytes) == 20, "publish_stride_bytes ABI offset drift");
static_assert(__builtin_offsetof(bwd_vm_source_window, backing_depth) == 24, "backing_depth ABI offset drift");
static_assert(__builtin_offsetof(bwd_vm_source_window, target_depth) == 25, "target_depth ABI offset drift");
static_assert(__builtin_offsetof(bwd_vm_source_window, origin_field) == 26, "origin_field ABI offset drift");
static_assert(__builtin_offsetof(bwd_vm_source_window, materialize) == 27, "materialize ABI offset drift");

static_assert(sizeof(bwd_vm_special) == 4, "bwd_vm_special ABI size drift");
static_assert(alignof(bwd_vm_special) == 4, "bwd_vm_special ABI alignment drift");
static_assert(__builtin_offsetof(bwd_vm_special, packed) == 0, "bwd_vm_special packed ABI offset drift");

static_assert(sizeof(bwd_vm_desc) == 4640, "bwd_vm_desc/BwdVmDesc ABI size drift");
static_assert(sizeof(bwd_vm_desc) <= 32764, "bwd_vm_desc exceeds the __grid_constant__ parameter budget");
static_assert(alignof(bwd_vm_desc) == 16, "bwd_vm_desc ABI alignment drift");
static_assert(__builtin_offsetof(bwd_vm_desc, arg_derived_e4) == 0, "arg_derived_e4 ABI offset drift");
static_assert(__builtin_offsetof(bwd_vm_desc, round_challenges) == 192, "round_challenges ABI offset drift");
static_assert(__builtin_offsetof(bwd_vm_desc, eq_low) == 200, "eq_low ABI offset drift");
static_assert(__builtin_offsetof(bwd_vm_desc, contributions) == 208, "contributions ABI offset drift");
static_assert(__builtin_offsetof(bwd_vm_desc, source_windows) == 216, "source_windows ABI offset drift");
static_assert(__builtin_offsetof(bwd_vm_desc, eq_sizes) == 344, "eq_sizes ABI offset drift");
static_assert(__builtin_offsetof(bwd_vm_desc, bf_constants) == 356, "bf_constants ABI offset drift");
static_assert(__builtin_offsetof(bwd_vm_desc, specials) == 516, "specials ABI offset drift");
static_assert(__builtin_offsetof(bwd_vm_desc, n_instr) == 1104, "n_instr ABI offset drift");
static_assert(__builtin_offsetof(bwd_vm_desc, program_lanes) == 1108, "program_lanes ABI offset drift");
static_assert(__builtin_offsetof(bwd_vm_desc, n_source_windows) == 1112, "n_source_windows ABI offset drift");
static_assert(__builtin_offsetof(bwd_vm_desc, n_specials) == 1116, "n_specials ABI offset drift");
static_assert(__builtin_offsetof(bwd_vm_desc, n_coefficients) == 1120, "n_coefficients ABI offset drift");
static_assert(__builtin_offsetof(bwd_vm_desc, n_bf_constants) == 1124, "n_bf_constants ABI offset drift");
static_assert(__builtin_offsetof(bwd_vm_desc, n_arg_derived_e4) == 1128, "n_arg_derived_e4 ABI offset drift");
static_assert(__builtin_offsetof(bwd_vm_desc, n_const_derived_e4) == 1132, "n_const_derived_e4 ABI offset drift");
static_assert(__builtin_offsetof(bwd_vm_desc, n_round_challenges) == 1136, "n_round_challenges ABI offset drift");
static_assert(__builtin_offsetof(bwd_vm_desc, logical_rows) == 1140, "logical_rows ABI offset drift");
static_assert(__builtin_offsetof(bwd_vm_desc, cell_count) == 1144, "cell_count ABI offset drift");
static_assert(__builtin_offsetof(bwd_vm_desc, program) == 1148, "program ABI offset drift");

} // namespace airbender::prover::gkr

// Existing stream-ordered constant-memory symbols. The coefficient symbol is
// declared by flat.cuh; ConstDerivedE4 reuses the forward VM's 8-slot bank.
EXTERN __device__ __constant__ e4 ab_gkr_fwd_vm_const_derived_e4[airbender::prover::gkr::BWD_VM_CONST_DERIVED_E4_CAP];
