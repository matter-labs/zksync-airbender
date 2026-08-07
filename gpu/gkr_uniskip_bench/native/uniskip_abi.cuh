#pragma once

#include "common.cuh"
#include "primitives/field.cuh"
#include "primitives/memory.cuh"

using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;

namespace airbender::gkr_uniskip_bench {

// k is FIXED at 4: 16 taps on H, plus the 16 cells of the odd coset gamma*H.
// Shaped so k=3/5 stays a one-line change, but nothing here is parameterized.
constexpr u32 UNISKIP_TAPS = 16;
constexpr u32 UNISKIP_CELLS = 32; // 0..15 = H (direct taps), 16..31 = coset

// Launch geometry: warp w owns cells 4w..4w+3.
constexpr u32 UNISKIP_THREADS_PER_BLOCK = 256;
constexpr u32 UNISKIP_WARPS_PER_BLOCK = 8;
constexpr u32 UNISKIP_CELLS_PER_WARP = 4;

static_assert(UNISKIP_CELLS == 2 * UNISKIP_TAPS);
static_assert(UNISKIP_WARPS_PER_BLOCK * 32 == UNISKIP_THREADS_PER_BLOCK);
static_assert(UNISKIP_WARPS_PER_BLOCK * UNISKIP_CELLS_PER_WARP == UNISKIP_CELLS);

constexpr u32 UNISKIP_WINDOWS = 6;
constexpr u32 UNISKIP_SOURCE_CAPACITY = 64;   // default census 59 sources; generator rejects > 64
constexpr u32 UNISKIP_PROGRAM_CAPACITY = 256; // default census 175 terms
constexpr u32 UNISKIP_COEFF_BANK = 128;
constexpr u32 UNISKIP_EQ_HIGH = 256;

// term classes. Groups ARE modeled (they shape the coefficient-FMA count);
// procedural synthesis is not — its 4 known occurrences are ordinary BF terms
// reading a dedicated setup-like window (natural-index synthesis = Task 6).
constexpr u16 UNISKIP_CLASS_LINEAR_BF = 0;
constexpr u16 UNISKIP_CLASS_LINEAR_E4 = 1;
constexpr u16 UNISKIP_CLASS_PRODUCT_BF_BF = 2;
constexpr u16 UNISKIP_CLASS_PRODUCT_BF_E4 = 3;
constexpr u16 UNISKIP_CLASS_PRODUCT_E4_E4 = 4;
// group: header record (coeff = core coeff-bank id, source_a = arity N >= 2),
// followed by N member records — BF linear/product classes whose `coeff` field
// carries an IMMEDIATE id instead of a bank id (0 = +1, 1 = -1, id >= 2 indexes
// desc.immediates[id - 2]). Members sum immediate-scaled per cell; the group costs
// ONE e4 coeff-bank FMA per cell for the whole run.
constexpr u16 UNISKIP_CLASS_GROUP_BF = 5;
constexpr u16 UNISKIP_IMMEDIATE_ONE = 0;
constexpr u16 UNISKIP_IMMEDIATE_NEG_ONE = 1;
constexpr u16 UNISKIP_IMMEDIATE_RESERVED = 2;
constexpr u32 UNISKIP_MAX_IMMEDIATES = 16;

// v1 source classes; v2 adds LDE_ON_READ / PUBLISHED without touching term execution
constexpr u8 UNISKIP_SRC_BF_GLOBAL = 0;
constexpr u8 UNISKIP_SRC_E4_GLOBAL = 1;

// `source_b` of a class with no second operand, and of a group header. Never read.
constexpr u16 UNISKIP_SOURCE_UNUSED = 0xffff;

struct alignas(8) uniskip_term {
  u16 term_class;
  u16 coeff;
  u16 source_a;
  u16 source_b;
};
struct alignas(4) uniskip_source_record {
  u16 addr; /* window:6 | column:7 */
  u8 source_class;
  u8 reserved;
};
struct alignas(8) uniskip_base_record {
  const u8 *base;
};
// Factored eq: the low `low` bits of a row index eq_low, the next `high[1]` bits
// index high table 1, the top `high[0]` bits index high table 0.
struct uniskip_eq_sizes {
  u32 high[2];
  u32 low;
};

struct alignas(16) uniskip_vm_desc {
  uniskip_term program[UNISKIP_PROGRAM_CAPACITY];
  uniskip_source_record source[UNISKIP_SOURCE_CAPACITY];
  uniskip_base_record tap_bases[UNISKIP_WINDOWS];
  uniskip_base_record coset_bases[UNISKIP_WINDOWS];
  bf immediates[UNISKIP_MAX_IMMEDIATES]; // device repr; host uploads via the same
                                         // canonical->device conversion as init.
                                         // Rust mirror stays raw u32 with layout asserts.
  const e4 *eq_low;
  e4 *partials;
  u32 record_count;
  u32 num_sources;
  u32 log_rows;
  uniskip_eq_sizes eq_sizes;
};
// Windows are FIELD-HOMOGENEOUS by construction: one typed base per window means
// mixed BF/E4 columns would have incompatible strides. The generator emits
// homogeneous windows; a test checks every operand's required type against its
// source_class, and every window's sources share one class.

static_assert(sizeof(uniskip_term) == 8);
static_assert(sizeof(uniskip_source_record) == 4);
static_assert(sizeof(uniskip_base_record) == 8);
static_assert(sizeof(uniskip_eq_sizes) == 12);
static_assert(offsetof(uniskip_vm_desc, program) == 0);
static_assert(offsetof(uniskip_vm_desc, source) == 2048);
static_assert(offsetof(uniskip_vm_desc, tap_bases) == 2304);
static_assert(offsetof(uniskip_vm_desc, coset_bases) == 2352);
static_assert(offsetof(uniskip_vm_desc, immediates) == 2400);
static_assert(offsetof(uniskip_vm_desc, eq_low) == 2464);
static_assert(offsetof(uniskip_vm_desc, partials) == 2472);
static_assert(offsetof(uniskip_vm_desc, record_count) == 2480);
static_assert(offsetof(uniskip_vm_desc, num_sources) == 2484);
static_assert(offsetof(uniskip_vm_desc, log_rows) == 2488);
static_assert(offsetof(uniskip_vm_desc, eq_sizes) == 2492);
static_assert(sizeof(uniskip_vm_desc) == 2512);
// Passed by value as a `__grid_constant__` kernel parameter.
static_assert(sizeof(uniskip_vm_desc) <= 32764);

// ADDRESSING BOUND. `addr` names at most 2^7 columns of UNISKIP_TAPS planes each,
// so the accessor's element index `(plane << log_rows) + row` spans
// UNISKIP_LOG_ADDRESSABLE_PLANES + log_rows bits. `load()` takes a 32-bit unsigned
// offset and NARROWS the size_t computed below, so the index is only safe while
// log_rows <= UNISKIP_MAX_LOG_ROWS. That is a stated invariant, enforced host-side
// by Geometry::new (src/geometry.rs, same two constants); the size_t arithmetic here
// still matters — it keeps the plane product out of 16-bit.
constexpr u32 UNISKIP_LOG_ADDRESSABLE_PLANES = 11;
constexpr u32 UNISKIP_ELEMENT_INDEX_BITS = 32;
constexpr u32 UNISKIP_MAX_LOG_ROWS = UNISKIP_ELEMENT_INDEX_BITS - UNISKIP_LOG_ADDRESSABLE_PLANES;
static_assert((1u << UNISKIP_LOG_ADDRESSABLE_PLANES) == 128 * UNISKIP_TAPS);
static_assert(UNISKIP_MAX_LOG_ROWS == 21);

// The ONE source accessor: every operand read in every kernel goes through it,
// so v2 (LDE-on-read / published sources) only swaps this body.
template <typename T> DEVICE_FORCEINLINE T uniskip_source_value(const uniskip_vm_desc &desc, const u16 source_id, const u32 cell, const u32 row) {
  const uniskip_source_record rec = desc.source[source_id];
  const u32 window = rec.addr >> 7;
  const size_t column = rec.addr & 0x7f; // widen BEFORE the shift
  const bool coset = cell >= UNISKIP_TAPS;
  const T *base = reinterpret_cast<const T *>((coset ? desc.coset_bases : desc.tap_bases)[window].base); // typed BEFORE element arithmetic
  const size_t plane = column * UNISKIP_TAPS + (coset ? cell - UNISKIP_TAPS : cell);
  return load<T, ld_modifier::ca>(base, (plane << desc.log_rows) + row);
}

} // namespace airbender::gkr_uniskip_bench

EXTERN __device__ __constant__ e4 ab_gkr_uniskip_coeff_bank[airbender::gkr_uniskip_bench::UNISKIP_COEFF_BANK];
EXTERN __device__ __constant__ e4 ab_gkr_uniskip_eq_high[2 * airbender::gkr_uniskip_bench::UNISKIP_EQ_HIGH];
EXTERN __device__ __constant__ bf ab_gkr_uniskip_lde_matrix[airbender::gkr_uniskip_bench::UNISKIP_TAPS * airbender::gkr_uniskip_bench::UNISKIP_TAPS];
EXTERN __device__ __constant__ e4 ab_gkr_uniskip_fold_weights[airbender::gkr_uniskip_bench::UNISKIP_TAPS];

static_assert(sizeof(ab_gkr_uniskip_coeff_bank) + sizeof(ab_gkr_uniskip_eq_high) + sizeof(ab_gkr_uniskip_lde_matrix) + sizeof(ab_gkr_uniskip_fold_weights) <=
              64 * 1024);
