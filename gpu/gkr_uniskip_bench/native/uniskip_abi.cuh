#pragma once

#include "common.cuh"
#include "primitives/field.cuh"
#include "primitives/memory.cuh"

using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;
using namespace ::airbender::primitives::ptx;

namespace airbender::gkr_uniskip_bench {

// k is FIXED at 4: 16 taps on H, plus the 16 cells of the odd coset gamma*H.
// Nothing here is parameterized on k and changing it is NOT a one-line edit. A k change touches, independently: UNISKIP_TAPS,
// UNISKIP_CELLS, UNISKIP_WARPS_PER_BLOCK and UNISKIP_CELLS_PER_WARP below plus the static_asserts tying them together; the same
// four constants in `src/abi.rs`; the generator indices in `src/domain.rs` (`omega16` = TWO_ADICITY_GENERATORS[4], `gamma` =
// TWO_ADICITY_GENERATORS[5], and the `omega16` name); and the k=4 literals in the domain and geometry tests. See README.md.
constexpr u32 UNISKIP_TAPS = 16;
constexpr u32 UNISKIP_CELLS = 32; // 0..15 = H (direct taps), 16..31 = coset

// Launch geometry: warp w owns cells 4w..4w+3.
constexpr u32 UNISKIP_THREADS_PER_BLOCK = 256;
constexpr u32 UNISKIP_WARPS_PER_BLOCK = 8;
constexpr u32 UNISKIP_CELLS_PER_WARP = 4;
// Rows an eval block covers: one lane per row, every warp of the block on the same
// 32 rows. Mirrored by `abi::UNISKIP_ROWS_PER_BLOCK`.
constexpr u32 UNISKIP_ROWS_PER_BLOCK = UNISKIP_THREADS_PER_BLOCK / UNISKIP_WARPS_PER_BLOCK;

static_assert(UNISKIP_CELLS == 2 * UNISKIP_TAPS);
static_assert(UNISKIP_WARPS_PER_BLOCK * 32 == UNISKIP_THREADS_PER_BLOCK);
static_assert(UNISKIP_WARPS_PER_BLOCK * UNISKIP_CELLS_PER_WARP == UNISKIP_CELLS);
static_assert(UNISKIP_ROWS_PER_BLOCK == 32); // one warp-wide row tile, so lane == row offset

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

} // namespace airbender::gkr_uniskip_bench

EXTERN __device__ __constant__ e4 ab_gkr_uniskip_coeff_bank[airbender::gkr_uniskip_bench::UNISKIP_COEFF_BANK];
EXTERN __device__ __constant__ e4 ab_gkr_uniskip_eq_high[2 * airbender::gkr_uniskip_bench::UNISKIP_EQ_HIGH];
EXTERN __device__ __constant__ bf ab_gkr_uniskip_lde_matrix[airbender::gkr_uniskip_bench::UNISKIP_TAPS * airbender::gkr_uniskip_bench::UNISKIP_TAPS];
EXTERN __device__ __constant__ e4 ab_gkr_uniskip_fold_weights[airbender::gkr_uniskip_bench::UNISKIP_TAPS];

static_assert(sizeof(ab_gkr_uniskip_coeff_bank) + sizeof(ab_gkr_uniskip_eq_high) + sizeof(ab_gkr_uniskip_lde_matrix) + sizeof(ab_gkr_uniskip_fold_weights) <=
              64 * 1024);

namespace airbender::gkr_uniskip_bench {

// The ONE source accessor for TERM EXECUTION: every operand read in the eval kernel
// goes through it, so v2 (LDE-on-read / published sources) only swaps this body. The
// LDE and fold kernels deliberately do NOT use it — they are bulk per-column plane
// sweeps and inline their own tap addressing.
template <typename T> DEVICE_FORCEINLINE T uniskip_source_value(const uniskip_vm_desc &desc, const u16 source_id, const u32 cell, const u32 row) {
  const uniskip_source_record rec = desc.source[source_id];
  const u32 window = rec.addr >> 7;
  const size_t column = rec.addr & 0x7f; // widen BEFORE the shift
  const bool coset = cell >= UNISKIP_TAPS;
  const T *base = reinterpret_cast<const T *>((coset ? desc.coset_bases : desc.tap_bases)[window].base); // typed BEFORE element arithmetic
  const size_t plane = column * UNISKIP_TAPS + (coset ? cell - UNISKIP_TAPS : cell);
  return load<T, ld_modifier::ca>(base, (plane << desc.log_rows) + row);
}

// SOURCE-RESOLUTION SELECTOR. An empty derived class: same members, same layout,
// same 2512-byte `__grid_constant__` parameter, so the host wire struct is shared.
// Its only job is to re-bind `uniskip_source_value` overload resolution inside the
// eval body, which is why term execution needs no per-mode spelling.
struct uniskip_fused_desc : uniskip_vm_desc {};
static_assert(sizeof(uniskip_fused_desc) == sizeof(uniskip_vm_desc));
static_assert(alignof(uniskip_fused_desc) == alignof(uniskip_vm_desc));
static_assert(offsetof(uniskip_fused_desc, program) == 0);
static_assert(offsetof(uniskip_fused_desc, eq_sizes) == 2492);

// The `bf` limbs of a source value, flat. The coset dot is `bf`-linear per limb, so
// it treats a `bf` source as one limb and an `e4` source as four.
template <typename T> struct uniskip_flat_limbs;
template <> struct uniskip_flat_limbs<bf> {
  static constexpr u32 COUNT = 1;
  static DEVICE_FORCEINLINE u32 raw(const bf &v, const u32) { return bf::into_raw_u32(v); }
  static DEVICE_FORCEINLINE bf pack(const bf limbs[COUNT]) { return limbs[0]; }
};
template <> struct uniskip_flat_limbs<e4> {
  static constexpr u32 COUNT = 4;
  static DEVICE_FORCEINLINE u32 raw(const e4 &v, const u32 i) { return bf::into_raw_u32(v.base_coefficient_from_flat_idx(i)); }
  static DEVICE_FORCEINLINE e4 pack(const bf limbs[COUNT]) { return e4(limbs); }
};

// Taps per wide chunk. Montgomery reduction is linear mod p, so
// `red(sum a_i b_i) == sum red(a_i b_i)` and the chunked dot is bit-identical to a
// per-tap `fma` chain — it just pays one reduction per chunk instead of per tap.
// The bound is `bf::red_wide`'s ~4p^2 input range: 4*(p-1)^2 = 1.62e19 < 2^64.
constexpr u32 UNISKIP_DOT_CHUNK = 4;
static_assert(UNISKIP_TAPS % UNISKIP_DOT_CHUNK == 0);

// LDE-ON-READ. Same (source, cell, row) contract as the accessor above, with the
// coset materialization absorbed: `desc.coset_bases` is never read and need not
// exist. An H cell is the direct tap load; coset cell `UNISKIP_TAPS + c` is the dot
// of the source's 16 taps with row `c` of the coset LDE matrix, accumulated wide in
// `UNISKIP_DOT_CHUNK`-tap chunks. The matrix entry is warp-uniform, so `__constant__`
// broadcasts it.
template <typename T> DEVICE_FORCEINLINE T uniskip_source_value(const uniskip_fused_desc &desc, const u16 source_id, const u32 cell, const u32 row) {
  using limbs_of = uniskip_flat_limbs<T>;
  constexpr u32 LIMBS = limbs_of::COUNT;
  const uniskip_source_record rec = desc.source[source_id];
  const u32 window = rec.addr >> 7;
  const size_t column = rec.addr & 0x7f;                                    // widen BEFORE the shift
  const T *base = reinterpret_cast<const T *>(desc.tap_bases[window].base); // typed BEFORE element arithmetic
  const size_t plane = column * UNISKIP_TAPS;
  if (cell < UNISKIP_TAPS)
    return load<T, ld_modifier::ca>(base, ((plane + cell) << desc.log_rows) + row);
  const bf *weights = &ab_gkr_uniskip_lde_matrix[(cell - UNISKIP_TAPS) * UNISKIP_TAPS];
  bf acc[LIMBS];
#pragma unroll
  for (u32 l = 0; l < LIMBS; ++l)
    acc[l] = bf::ZERO();
#pragma unroll
  for (u32 chunk = 0; chunk < UNISKIP_TAPS; chunk += UNISKIP_DOT_CHUNK) {
    u64 wide[LIMBS];
#pragma unroll
    for (u32 l = 0; l < LIMBS; ++l)
      wide[l] = 0;
#pragma unroll
    for (u32 j = 0; j < UNISKIP_DOT_CHUNK; ++j) {
      const u32 t = chunk + j;
      const T tap = load<T, ld_modifier::ca>(base, ((plane + t) << desc.log_rows) + row);
      const u32 weight = bf::into_raw_u32(weights[t]);
#pragma unroll
      for (u32 l = 0; l < LIMBS; ++l)
        wide[l] = mad_wide(limbs_of::raw(tap, l), weight, wide[l]);
    }
#pragma unroll
    for (u32 l = 0; l < LIMBS; ++l)
      acc[l] = bf::add(acc[l], bf::red_wide(wide[l]));
  }
  return limbs_of::pack(acc);
}

// CELL MAP. Which of the 32 cells warp `w` owns. `block` (INTERLEAVE = false) is the
// v1 map, cells 4w..4w+3, so warps 0-3 are all-H and warps 4-7 all-coset — under
// LDE-on-read the coset warps carry every recompute. `interleave` gives warp `w` the
// cells {w, w+8, w+16, w+24}, 2 H and 2 coset each. Both are bijections onto
// 0..UNISKIP_CELLS and `q` is cell-indexed, so the oracle is unaffected.
template <bool INTERLEAVE> DEVICE_FORCEINLINE u32 uniskip_first_cell(const u32 warp) { return INTERLEAVE ? warp : warp * UNISKIP_CELLS_PER_WARP; }
template <bool INTERLEAVE> constexpr u32 uniskip_cell_stride() { return INTERLEAVE ? UNISKIP_WARPS_PER_BLOCK : 1; }

} // namespace airbender::gkr_uniskip_bench
