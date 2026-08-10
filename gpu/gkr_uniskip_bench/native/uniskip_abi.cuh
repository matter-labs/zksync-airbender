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
// `cache_slot` was v1's `reserved` byte. The struct is still 4 bytes and the wire is
// unchanged; only the byte's meaning is new: it names the first UNISKIP_CACHE unit of
// this source's shared-memory coset slab, or UNISKIP_CACHE_SLOT_NONE when the source
// is uncached and resolves through the Task 1 recompute path. Only the fused-cached
// accessor reads it; every other mode leaves it at the sentinel.
struct alignas(4) uniskip_source_record {
  u16 addr; /* window:6 | column:7 */
  u8 source_class;
  u8 cache_slot;
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

// SHARED-MEMORY SOURCE CACHE (fused-cached mode). The pool is a flat array of
// fixed-size UNITS; one unit holds ONE `bf` plane of one source's coset slab for the
// block's 32-row tile — UNISKIP_TAPS coset cells x UNISKIP_ROWS_PER_BLOCK rows. A `bf`
// source therefore occupies one unit and an `e4` source four consecutive ones (one per
// limb), which is what makes the slab byte cost exactly proportional to the field
// class's component width and the read path uniform in the limb count.
constexpr u32 UNISKIP_CACHE_UNIT_WORDS = UNISKIP_TAPS * UNISKIP_ROWS_PER_BLOCK;
constexpr u32 UNISKIP_CACHE_UNITS = 16;
constexpr u32 UNISKIP_CACHE_POOL_WORDS = UNISKIP_CACHE_UNITS * UNISKIP_CACHE_UNIT_WORDS;
constexpr u8 UNISKIP_CACHE_SLOT_NONE = 0xff;
// Inverse (unit -> source) plan, so the tile-start fill iterates UNITS and not the
// whole source table: `source_id | limb << 8`, or UNISKIP_CACHE_FILL_NONE for a free
// unit. Host-precomputed; see `src/cache.rs`.
constexpr u16 UNISKIP_CACHE_FILL_NONE = 0xffff;

// ---------------------------------------------------------------------------------------
// v3 R4 COSET CACHE. A different cache from the v2 shared pool above and deliberately not
// sharing its constants: this one is PER-THREAD LOCAL memory holding produced coset PAIRS,
// where a unit is one `bf` source's `c[2]` (8 B) and an `e4` source's span is four units
// laid out c-object-major, `[c[0] 16 B][c[1] 16 B]`. It rides the same `cache_slot` byte.
// The Rust mirror is `src/coset_cache.rs`; keep the two in step - the static_asserts here
// and the layout tests there are the only guard.
// ---------------------------------------------------------------------------------------
constexpr u32 UNISKIP_COSET_UNIT_BYTES = 8;
constexpr u32 UNISKIP_COSET_E4_UNITS = 4;
// The frame is sized ONCE at the default census's all-59 footprint so every cached arm
// compiles to one body with one static frame; varying it per arm would confound codegen
// with footprint. The host validator rejects a program that needs more.
constexpr u32 UNISKIP_COSET_FRAME_UNITS = 92;
static_assert(UNISKIP_COSET_FRAME_UNITS * UNISKIP_COSET_UNIT_BYTES == 736);
// `cache_slot` encodes the BASE alone, so bases stay representable for any frame up to 256
// units; only 0xff itself collides with the sentinel, which the host validator rejects.
static_assert(UNISKIP_COSET_FRAME_UNITS <= 256, "a base unit must fit `cache_slot`");

// One prologue row: the SEMANTIC source id the resolver consumes (columns are neither
// unique nor sufficient) plus its base unit. Mirrors `coset_cache::PrologueEntry`.
// `reserved` carries the R7 prologue owner warp (0..UNISKIP_SEG_K), stamped by the harness
// after descriptor build; the builder always emits 0 and no pre-R7 consumer reads it beyond
// the builder-zero test.
struct alignas(4) uniskip_prologue_entry {
  u16 source;
  u8 base;
  u8 reserved;
};
static_assert(sizeof(uniskip_prologue_entry) == 4);
static_assert(alignof(uniskip_prologue_entry) == 4);

// The prologue table, walked E4 rows first then BF rows - the pinned production order.
// Capacity is the frame: every admitted source consumes at least one unit, so no legal
// plan can have more rows than units.
struct alignas(16) uniskip_cache_desc {
  uniskip_prologue_entry entry[UNISKIP_COSET_FRAME_UNITS];
  u32 count; // rows to walk; the kernel branches per row on the record's class
  u32 e4_count;
  u32 bf_count;
  u32 reserved;
};
static_assert(sizeof(uniskip_cache_desc) == 4 * UNISKIP_COSET_FRAME_UNITS + 16);
static_assert(offsetof(uniskip_cache_desc, count) == 4 * UNISKIP_COSET_FRAME_UNITS);
static_assert(UNISKIP_SOURCE_CAPACITY <= 0x100, "the fill entry packs a source id in its low byte");
static_assert(UNISKIP_CACHE_UNITS < UNISKIP_CACHE_SLOT_NONE, "a unit index must fit `cache_slot` beside its sentinel");
// The fill assigns one lane per (unit, row) and strides by the block, so the two must
// divide; with 16 units it is exactly two lanes per thread, warp `w` filling units
// `w` and `w + 8`.
static_assert((UNISKIP_CACHE_UNITS * UNISKIP_ROWS_PER_BLOCK) % UNISKIP_THREADS_PER_BLOCK == 0);
// Static shared memory is capped at 48 KB per block without an opt-in, and the pool is
// the only shared allocation the eval kernel makes (the cell reduction is `shfl`-only).
static_assert(UNISKIP_CACHE_POOL_WORDS * sizeof(u32) <= 48 * 1024);

constexpr u32 UNISKIP_SEG_K = 4;
constexpr u32 UNISKIP_SEG_COHORT_ROWS = 4;
constexpr u32 UNISKIP_SEG_COHORTS = 4; // 16 rows/block at 128 threads
struct alignas(16) uniskip_seg_desc {
  u16 list_offset[UNISKIP_SEG_K + 1]; // record indices into program[], atom boundaries
  u16 reserved0[3];
  u64 slab_base;         // carrier G: device scratch base; 0 under S/recompute
  u32 slab_stride_words; // carrier G: per-block region stride in u32 words
  u32 reserved1;
};
static_assert(sizeof(uniskip_seg_desc) == 32, "seg desc ABI size drift");
static_assert(sizeof(uniskip_vm_desc) + sizeof(uniskip_cache_desc) + sizeof(uniskip_seg_desc) <= 32764, "seg launch parameter budget");

// v3 R3 WINDOW SIDE DESCRIPTOR — the device twin of `abi::UniskipWindowDesc`. It is a
// SEPARATE parameter from `uniskip_vm_desc`: the control wire format is untouched, so an
// arm without a window is byte-for-byte the R2 kernel. One tag byte per record position,
// operand A in the low nibble and operand B in the high; within a nibble `0` is none,
// `1 + slot` is fill and `1 + UNISKIP_WINDOW_SLOTS + slot` is reuse (see
// `src/window.rs::WindowTag::encode`). The kernel reads `tags` only — `slot_source` and
// `slot_count` are carried for wire symmetry with the host validator, which checks
// against them, and cost 16 B of cmem.
constexpr u32 UNISKIP_WINDOW_SLOTS = 4;
struct alignas(16) uniskip_window_desc {
  u8 tags[UNISKIP_PROGRAM_CAPACITY];
  u16 slot_source[UNISKIP_WINDOW_SLOTS];
  u32 slot_count;
};
static_assert(sizeof(uniskip_window_desc) == 272);
static_assert(alignof(uniskip_window_desc) == 16);
static_assert(offsetof(uniskip_window_desc, tags) == 0);
static_assert(offsetof(uniskip_window_desc, slot_source) == 256);
static_assert(offsetof(uniskip_window_desc, slot_count) == 264);
static_assert(sizeof(uniskip_window_desc) + sizeof(uniskip_vm_desc) <= 32764, "both descriptors are by-value kernel parameters");
// A slot index and both tag kinds must fit one nibble.
static_assert(1 + 2 * UNISKIP_WINDOW_SLOTS <= 16);

} // namespace airbender::gkr_uniskip_bench

EXTERN __device__ __constant__ e4 ab_gkr_uniskip_coeff_bank[airbender::gkr_uniskip_bench::UNISKIP_COEFF_BANK];
EXTERN __device__ __constant__ e4 ab_gkr_uniskip_eq_high[2 * airbender::gkr_uniskip_bench::UNISKIP_EQ_HIGH];
EXTERN __device__ __constant__ bf ab_gkr_uniskip_lde_matrix[airbender::gkr_uniskip_bench::UNISKIP_TAPS * airbender::gkr_uniskip_bench::UNISKIP_TAPS];
EXTERN __device__ __constant__ e4 ab_gkr_uniskip_fold_weights[airbender::gkr_uniskip_bench::UNISKIP_TAPS];
EXTERN __device__ __constant__ u16 ab_gkr_uniskip_cache_fill[airbender::gkr_uniskip_bench::UNISKIP_CACHE_UNITS];

static_assert(sizeof(ab_gkr_uniskip_coeff_bank) + sizeof(ab_gkr_uniskip_eq_high) + sizeof(ab_gkr_uniskip_lde_matrix) + sizeof(ab_gkr_uniskip_fold_weights) +
                  sizeof(ab_gkr_uniskip_cache_fill) <=
              64 * 1024);

namespace airbender::gkr_uniskip_bench {

// The ONE source accessor for TERM EXECUTION: every operand read in the eval kernel
// goes through it, so v2 (LDE-on-read / published sources) only swaps this body. The
// LDE and fold kernels deliberately do NOT use it — they are bulk per-column plane
// sweeps and inline their own tap addressing.
//
// The trailing `bf *` is the fused-cached mode's shared-memory pool. Every mode spells
// the call identically, so term execution stays one text; the modes that resolve
// without a cache ignore it.
template <typename T> DEVICE_FORCEINLINE T uniskip_source_value(const uniskip_vm_desc &desc, bf *, const u16 source_id, const u32 cell, const u32 row) {
  const uniskip_source_record rec = desc.source[source_id];
  const u32 window = rec.addr >> 7;
  const size_t column = rec.addr & 0x7f; // widen BEFORE the shift
  const bool coset = cell >= UNISKIP_TAPS;
  const T *base = reinterpret_cast<const T *>((coset ? desc.coset_bases : desc.tap_bases)[window].base); // typed BEFORE element arithmetic
  const size_t plane = column * UNISKIP_TAPS + (coset ? cell - UNISKIP_TAPS : cell);
  return load<T, ld_modifier::ca>(base, (plane << desc.log_rows) + row);
}

// SOURCE-RESOLUTION SELECTORS. Empty derived classes: same members, same layout,
// same 2512-byte `__grid_constant__` parameter, so the host wire struct is shared.
// Their only job is to re-bind `uniskip_source_value` overload resolution inside the
// eval body, which is why term execution needs no per-mode spelling.
struct uniskip_fused_desc : uniskip_vm_desc {};
struct uniskip_cached_desc : uniskip_vm_desc {};
static_assert(sizeof(uniskip_fused_desc) == sizeof(uniskip_vm_desc));
static_assert(alignof(uniskip_fused_desc) == alignof(uniskip_vm_desc));
static_assert(offsetof(uniskip_fused_desc, program) == 0);
static_assert(offsetof(uniskip_fused_desc, eq_sizes) == 2492);
static_assert(sizeof(uniskip_cached_desc) == sizeof(uniskip_vm_desc));
static_assert(alignof(uniskip_cached_desc) == alignof(uniskip_vm_desc));
static_assert(offsetof(uniskip_cached_desc, eq_sizes) == 2492);

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

// LDE-ON-READ, the two halves the fused and fused-cached accessors share.
// `uniskip_tap_read` is the direct load of an H cell; `uniskip_coset_recompute` is the
// dot of the source's 16 taps with row `coset_row` of the coset LDE matrix, per `bf`
// limb, accumulated wide in `UNISKIP_DOT_CHUNK`-tap chunks. The matrix entry is
// warp-uniform, so `__constant__` broadcasts it.
template <typename T> DEVICE_FORCEINLINE T uniskip_tap_read(const uniskip_vm_desc &desc, const uniskip_source_record rec, const u32 cell, const u32 row) {
  const u32 window = rec.addr >> 7;
  const size_t column = rec.addr & 0x7f;                                    // widen BEFORE the shift
  const T *base = reinterpret_cast<const T *>(desc.tap_bases[window].base); // typed BEFORE element arithmetic
  return load<T, ld_modifier::ca>(base, ((column * UNISKIP_TAPS + cell) << desc.log_rows) + row);
}

template <typename T>
DEVICE_FORCEINLINE T uniskip_coset_recompute(const uniskip_vm_desc &desc, const uniskip_source_record rec, const u32 coset_row, const u32 row) {
  using limbs_of = uniskip_flat_limbs<T>;
  constexpr u32 LIMBS = limbs_of::COUNT;
  const u32 window = rec.addr >> 7;
  const size_t column = rec.addr & 0x7f;
  const T *base = reinterpret_cast<const T *>(desc.tap_bases[window].base);
  const size_t plane = column * UNISKIP_TAPS;
  const bf *weights = &ab_gkr_uniskip_lde_matrix[coset_row * UNISKIP_TAPS];
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

// FUSED (rung 2a): the coset materialization is absorbed, so `desc.coset_bases` is
// never read and need not exist.
template <typename T> DEVICE_FORCEINLINE T uniskip_source_value(const uniskip_fused_desc &desc, bf *, const u16 source_id, const u32 cell, const u32 row) {
  const uniskip_source_record rec = desc.source[source_id];
  if (cell < UNISKIP_TAPS)
    return uniskip_tap_read<T>(desc, rec, cell, row);
  return uniskip_coset_recompute<T>(desc, rec, cell - UNISKIP_TAPS, row);
}

// FUSED-CACHED (rung 2b): identical to the fused accessor except that a coset cell of
// a source the host assigned a slot reads the block's shared-memory slab instead of
// re-running the dot. `row & (UNISKIP_ROWS_PER_BLOCK - 1)` is the lane, because a
// block's rows are `blockIdx.x * UNISKIP_ROWS_PER_BLOCK + lane` and the tile is
// exactly one warp wide. An `e4` source's four limbs live in four consecutive units,
// so the limb walk is one unit stride.
template <typename T>
DEVICE_FORCEINLINE T uniskip_source_value(const uniskip_cached_desc &desc, bf *cache, const u16 source_id, const u32 cell, const u32 row) {
  using limbs_of = uniskip_flat_limbs<T>;
  constexpr u32 LIMBS = limbs_of::COUNT;
  const uniskip_source_record rec = desc.source[source_id];
  if (cell < UNISKIP_TAPS)
    return uniskip_tap_read<T>(desc, rec, cell, row);
  if (rec.cache_slot == UNISKIP_CACHE_SLOT_NONE)
    return uniskip_coset_recompute<T>(desc, rec, cell - UNISKIP_TAPS, row);
  const bf *slab =
      cache + u32{rec.cache_slot} * UNISKIP_CACHE_UNIT_WORDS + (cell - UNISKIP_TAPS) * UNISKIP_ROWS_PER_BLOCK + (row & (UNISKIP_ROWS_PER_BLOCK - 1));
  bf limbs[LIMBS];
#pragma unroll
  for (u32 l = 0; l < LIMBS; ++l)
    limbs[l] = slab[l * UNISKIP_CACHE_UNIT_WORDS];
  return limbs_of::pack(limbs);
}

// TILE-START COOPERATIVE FILL. One lane owns (unit, row) and is ROW-SHAPED — it loads
// that row's 16 taps once and emits all 16 coset cells from registers, so a slab costs
// 16 tap loads per row rather than the 256 a per-cell fill would issue (v2 Task 0's
// result, applied inside the kernel). Lane == row inside the tile, so both the tap
// loads and the slab stores are warp-contiguous; with UNISKIP_CACHE_UNITS = 16 warp `w`
// fills units `w` and `w + 8`. The outer loop is NOT unrolled on purpose: each
// iteration holds 16 taps live, and unrolling would double that against the eval body's
// own register ceiling. Callers must `__syncthreads()` before the first cached read.
DEVICE_FORCEINLINE void uniskip_cache_fill(const uniskip_vm_desc &desc, bf *cache) {
  constexpr u32 LANES = UNISKIP_CACHE_UNITS * UNISKIP_ROWS_PER_BLOCK;
#pragma unroll 1
  for (u32 idx = threadIdx.x; idx < LANES; idx += UNISKIP_THREADS_PER_BLOCK) {
    const u32 unit = idx / UNISKIP_ROWS_PER_BLOCK;
    const u32 entry = ab_gkr_uniskip_cache_fill[unit];
    if (entry == UNISKIP_CACHE_FILL_NONE)
      continue;
    const u32 lane = idx % UNISKIP_ROWS_PER_BLOCK;
    const uniskip_source_record rec = desc.source[entry & 0xff];
    const u32 limb = entry >> 8;
    const u32 width = rec.source_class == UNISKIP_SRC_E4_GLOBAL ? uniskip_flat_limbs<e4>::COUNT : uniskip_flat_limbs<bf>::COUNT;
    const u32 window = rec.addr >> 7;
    const size_t column = rec.addr & 0x7f;
    const u64 row = blockIdx.x * u64{UNISKIP_ROWS_PER_BLOCK} + lane;
    // The whole element index goes into the POINTER (64-bit); what is left is the
    // plane stride, which the addressing bound keeps inside `load`'s 32-bit offset.
    const bf *taps = reinterpret_cast<const bf *>(desc.tap_bases[window].base) + ((((column * UNISKIP_TAPS) << desc.log_rows) + row) * width + limb);
    const u32 plane = width << desc.log_rows;
    bf tap[UNISKIP_TAPS];
#pragma unroll
    for (u32 t = 0; t < UNISKIP_TAPS; ++t)
      tap[t] = load<bf, ld_modifier::ca>(taps, t * plane);
    bf *slab = cache + unit * UNISKIP_CACHE_UNIT_WORDS + lane;
#pragma unroll
    for (u32 c = 0; c < UNISKIP_TAPS; ++c) {
      const bf *weights = &ab_gkr_uniskip_lde_matrix[c * UNISKIP_TAPS];
      bf acc = bf::ZERO();
#pragma unroll
      for (u32 chunk = 0; chunk < UNISKIP_TAPS; chunk += UNISKIP_DOT_CHUNK) {
        u64 wide = 0;
#pragma unroll
        for (u32 j = 0; j < UNISKIP_DOT_CHUNK; ++j)
          wide = mad_wide(bf::into_raw_u32(tap[chunk + j]), bf::into_raw_u32(weights[chunk + j]), wide);
        acc = bf::add(acc, bf::red_wide(wide));
      }
      slab[c * UNISKIP_ROWS_PER_BLOCK] = acc;
    }
  }
}

// CELL MAP. Which of the 32 cells warp `w` owns. `block` (INTERLEAVE = false) is the
// v1 map, cells 4w..4w+3, so warps 0-3 are all-H and warps 4-7 all-coset — under
// LDE-on-read the coset warps carry every recompute. `interleave` gives warp `w` the
// cells {w, w+8, w+16, w+24}, 2 H and 2 coset each. Both are bijections onto
// 0..UNISKIP_CELLS and `q` is cell-indexed, so the oracle is unaffected.
template <bool INTERLEAVE> DEVICE_FORCEINLINE u32 uniskip_first_cell(const u32 warp) { return INTERLEAVE ? warp : warp * UNISKIP_CELLS_PER_WARP; }
template <bool INTERLEAVE> constexpr u32 uniskip_cell_stride() { return INTERLEAVE ? UNISKIP_WARPS_PER_BLOCK : 1; }

} // namespace airbender::gkr_uniskip_bench
