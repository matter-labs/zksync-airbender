#pragma once

#include "common.cuh"
#include "flat_backward.cuh" // flat_c0_ref, flat_c1_pair, coeff_loader_ptr

EXTERN __device__ __constant__ e4 ab_gkr_round2_challenges[3];
EXTERN __device__ __constant__ e4 ab_gkr_main_layer_claim_point[airbender::prover::gkr::GKR_MAIN_LAYER_CLAIM_POINT_LEN];

namespace airbender::prover::gkr {

// Maximum coefficient count that fits in __constant__ memory.
// 1024 entries = 16KB of E4 values.
constexpr unsigned FLAT_CONT_CONST_MAX = 1024;

// Maximum array sizes for the flat continuation static description.
// The entire struct is passed as __grid_constant__ (~28KB budget).
constexpr unsigned FLAT_CONT_MAX_SOURCES = 512;
constexpr unsigned FLAT_CONT_MAX_C0_ONLY_LINEAR = 640;
constexpr unsigned FLAT_CONT_MAX_UNIFIED_QUADRATIC = 4608;
constexpr unsigned FLAT_CONT_MAX_UNIFIED_LINEAR = 128;
constexpr unsigned FLAT_CONT_MAX_CONSTANT = 64;

// Term types for the unified term array.
constexpr u16 TERM_TYPE_CONSTANT = 0;
constexpr u16 TERM_TYPE_C0_ONLY_LINEAR = 1;
constexpr u16 TERM_TYPE_UNIFIED_QUADRATIC = 2;
constexpr u16 TERM_TYPE_UNIFIED_LINEAR = 3;

// Unified term entry: mixes all term types in a single array.
// coeff_idx maps into the typed coefficient layout in __constant__ memory.
struct flat_unified_term {
  u16 source_a;
  u16 source_b;
  u16 term_type;
  u16 coeff_idx;
};

// flat_round1_unified_desc: defined below, after round 1/2 source types.

// Compact source descriptor for continuing sources (round 3+).
// Stores only what varies per source — fold_stride (this_layer_size) and
// next_layer_size are uniform within a step and passed as kernel parameters.
//
// Encoding: previous_layer_start == null means !first_access (read from cache).
//           previous_layer_start != null means first_access (fold and cache).
template <typename E> struct flat_continuing_source_entry {
  const E *previous_layer_start;
  E *this_layer_cache_start;
};

// Static description for GKR backward rounds 1+ (continuation rounds).
// All sources are extension field after folding. Term categories:
//   c0_only_linear:      c0 += k*f0;                    c1 += k*f1 [explicit only]
//   unified_quadratic:   c0 += k*f0a*f0b;  c1 += k*f1a*f1b [always]
//   unified_linear:      c0 += k*f0;       c1 += k*f1_or_delta [always]
//   constant:            c0 += k;           c1 += k [explicit only]
template <typename E> struct flat_continuation_static_desc {
  flat_continuing_source_entry<E> sources[FLAT_CONT_MAX_SOURCES];
  u32 num_sources;

  flat_c0_ref c0_only_linear[FLAT_CONT_MAX_C0_ONLY_LINEAR];
  u32 num_c0_only_linear;

  flat_c1_pair unified_quadratic[FLAT_CONT_MAX_UNIFIED_QUADRATIC];
  u32 num_unified_quadratic;

  flat_c0_ref unified_linear[FLAT_CONT_MAX_UNIFIED_LINEAR];
  u32 num_unified_linear;

  u32 num_constants;
};

// --- Source load helpers ---

// Fold-on-first-load for continuing sources.
// If first_access (prev != null): reads two values from previous layer,
// folds with challenge, writes to cache, returns folded value.
// If !first_access (prev == null): reads directly from cache.
template <typename E>
DEVICE_FORCEINLINE E flat_cont_fold_and_load(const flat_continuing_source_entry<E> &entry, const E &folding_challenge, const unsigned fold_stride,
                                             const unsigned index) {
  if (entry.previous_layer_start == nullptr) {
    return load<E, ld_modifier::ca>(entry.this_layer_cache_start, index);
  }
  const E f0 = load<E, ld_modifier::cs>(entry.previous_layer_start, index);
  const E f1 = load<E, ld_modifier::cs>(entry.previous_layer_start, fold_stride + index);
  const E folded = E::fma(folding_challenge, E::sub(f1, f0), f0);
  store<E, st_modifier::wb>(entry.this_layer_cache_start, folded, index);
  return folded;
}

// ===========================================================================
// Rounds 1 and 2: mixed base + extension sources
// ===========================================================================

// Maximum array sizes for base/ext split.
constexpr unsigned FLAT_CONT_MAX_BASE_SOURCES = 128;
constexpr unsigned FLAT_CONT_MAX_EXT_SOURCES = 384;

// Source index encoding: bit 15 = 1 means ext_sources[], bit 15 = 0 means base_sources[].
constexpr u16 FLAT_CONT_EXT_SOURCE_BIT = 0x8000;

// Unified tiled kernel constants.
constexpr unsigned FLAT_CONT_UNIFIED_SOURCE_GROUP_SIZE = 4;
constexpr unsigned FLAT_CONT_UNIFIED_MAX_GRID_DIM = (FLAT_CONT_MAX_BASE_SOURCES + FLAT_CONT_MAX_EXT_SOURCES) / FLAT_CONT_UNIFIED_SOURCE_GROUP_SIZE;
constexpr unsigned FLAT_CONT_UNIFIED_MAX_TERMS = 1024;
constexpr unsigned FLAT_CONT_UNIFIED_MAX_TILES = FLAT_CONT_UNIFIED_MAX_TERMS;
constexpr unsigned FLAT_CONT_UNIFIED_MAX_FOLD_SOURCES = FLAT_CONT_MAX_BASE_SOURCES + FLAT_CONT_MAX_EXT_SOURCES;

// --- Round 1 static description ---
// Base sources: gkr_base_after_one_source (self-contained, includes fold params).
// Ext sources: flat_continuing_source_entry (uses kernel-level fold_stride/next_layer_size).

template <typename B, typename E> struct flat_round1_static_desc {
  gkr_base_after_one_source<B, E> base_sources[FLAT_CONT_MAX_BASE_SOURCES];
  u32 num_base_sources;

  flat_continuing_source_entry<E> ext_sources[FLAT_CONT_MAX_EXT_SOURCES];
  u32 num_ext_sources;

  flat_c0_ref c0_only_linear[FLAT_CONT_MAX_C0_ONLY_LINEAR];
  u32 num_c0_only_linear;
  flat_c1_pair unified_quadratic[FLAT_CONT_MAX_UNIFIED_QUADRATIC];
  u32 num_unified_quadratic;
  flat_c0_ref unified_linear[FLAT_CONT_MAX_UNIFIED_LINEAR];
  u32 num_unified_linear;
  u32 num_constants;
};

// Combined descriptor for the unified round 1 kernel: sources + mixed terms
// with per-tile fold/compute metadata. Passed as a single __grid_constant__.
template <typename B, typename E> struct flat_round1_unified_desc {
  gkr_base_after_one_source<B, E> base_sources[FLAT_CONT_MAX_BASE_SOURCES];
  u32 num_base_sources;

  flat_continuing_source_entry<E> ext_sources[FLAT_CONT_MAX_EXT_SOURCES];
  u32 num_ext_sources;

  flat_unified_term terms[FLAT_CONT_UNIFIED_MAX_TERMS];
  u32 num_terms;

  // Tile metadata.
  u32 num_constant_terms;
  u32 num_tiles;
  u16 tile_term_offsets[FLAT_CONT_UNIFIED_MAX_TILES + 1];
  u16 tile_fold_offsets[FLAT_CONT_UNIFIED_MAX_TILES + 1];
  u16 fold_sources[FLAT_CONT_UNIFIED_MAX_FOLD_SOURCES];
};

// Phase C compact mirror of `flat_round1_unified_desc<bf, e4>`. Each base
// source's full struct collapses to a u16 (real path) or a u16 + side-array
// poly_idx (virtual path); each ext source's pair of pointers collapses to a
// u16. Layer-uniform metadata (`base_layer_half_size`, `next_layer_size`) is
// hoisted out of every per-source entry into descriptor-level u32s.
//
// Mirror of `gpu_prover::prover::gkr::backward_flat_compact::GpuFlatRound1UnifiedDescCompact`.
struct flat_round1_unified_desc_compact {
  gkr_dim_reducing_tables tables;

  // Per-launch uniform sizes hoisted from the legacy per-source entries.
  // `base_layer_half_size` is the offset between the two halves of the base
  // input poly that get folded together (in `bf` element units).
  // `next_layer_size` is the offset between the two halves of the cache
  // buffer (in `E` element units), and equals the kernel-level fold stride
  // for ext sources at sumcheck step 1.
  u32 base_layer_half_size;
  u32 next_layer_size;

  // Per-base-source u16 layout (matches the Rust packing helpers
  // `pack_cont_base_source_real` / `pack_cont_base_source_virtual`):
  //   bit 15      : first_access
  //   bit 14      : is_virtual
  //   bits 13..10 : ptr_idx (4 bits, 16 slots) — real path OR virtual_cache_slot
  //   bits 9..0   : poly_idx (10 bits, max 1024) — real OR low 3 bits = source_kind (virtual)
  gkr_source_record base_sources[FLAT_CONT_MAX_BASE_SOURCES];
  u32 num_base_sources;

  // Per-ext-source u16 layout (matches `pack_cont_ext_source`):
  //   bit 15      : first_access
  //   bits 14..11 : ptr_idx (4 bits, 16 slots)
  //   bits 10..0  : poly_idx (11 bits, max 2048)
  // The cache slot for each ext source is carried by the record's cache half.
  gkr_source_record ext_sources[FLAT_CONT_MAX_EXT_SOURCES];
  u32 num_ext_sources;

  flat_unified_term terms[FLAT_CONT_UNIFIED_MAX_TERMS];
  u32 num_terms;
  u32 num_constant_terms;
  u32 num_tiles;
  u16 tile_term_offsets[FLAT_CONT_UNIFIED_MAX_TILES + 1];
  u16 tile_fold_offsets[FLAT_CONT_UNIFIED_MAX_TILES + 1];
  u16 fold_sources[FLAT_CONT_UNIFIED_MAX_FOLD_SOURCES];
};

static_assert(sizeof(flat_round1_unified_desc_compact) <= 32 * 1024,
              "flat_round1_unified_desc_compact exceeds the 32 KB cudaLaunchKernelExC inline ceiling");

// Combined descriptor for the unified continuation kernel (rounds 3+):
// single source array + mixed terms with per-tile fold/compute metadata.
template <typename E> struct flat_continuation_unified_desc {
  flat_continuing_source_entry<E> sources[FLAT_CONT_MAX_SOURCES];
  u32 num_sources;

  flat_unified_term terms[FLAT_CONT_UNIFIED_MAX_TERMS];
  u32 num_terms;

  u32 num_constant_terms;
  u32 num_tiles;
  u16 tile_term_offsets[FLAT_CONT_UNIFIED_MAX_TILES + 1];
  u16 tile_fold_offsets[FLAT_CONT_UNIFIED_MAX_TILES + 1];
  u16 fold_sources[FLAT_CONT_UNIFIED_MAX_FOLD_SOURCES];
};

// Phase C compact mirror of `flat_continuation_unified_desc<e4>`. Each
// source's (prev, cache) pointer pair collapses to a single u16 packed as
// `(first_access << 15) | (ptr_idx << 11) | poly_idx` (4-bit ptr_idx,
// 11-bit poly_idx). The kernel resolves addresses via `tables` plus
// per-step uniform offsets.
//
// Mirror of `gpu_prover::prover::gkr::backward_flat_compact::GpuFlatContinuationUnifiedDescCompact`.
struct flat_continuation_unified_desc_compact {
  gkr_dim_reducing_tables tables;

  // Per-slot element offsets within each per-poly slot of the consolidated
  // folding backing. Phase A2-flat-base: base- and ext-derived sources have
  // different per-poly buffer sizes, so the offsets differ between slots.
  // Set by the encoder per launch step. Decoder: see
  // `flat_cont_resolve_compact` below.
  u32 prev_per_poly_offset[GKR_DIM_REDUCING_BASE_SLOTS];
  u32 cache_per_poly_offset[GKR_DIM_REDUCING_BASE_SLOTS];

  gkr_source_record sources[FLAT_CONT_MAX_SOURCES];
  u32 num_sources;

  flat_unified_term terms[FLAT_CONT_UNIFIED_MAX_TERMS];
  u32 num_terms;

  u32 num_constant_terms;
  u32 num_tiles;
  u16 tile_term_offsets[FLAT_CONT_UNIFIED_MAX_TILES + 1];
  u16 tile_fold_offsets[FLAT_CONT_UNIFIED_MAX_TILES + 1];
  u16 fold_sources[FLAT_CONT_UNIFIED_MAX_FOLD_SOURCES];
};

static_assert(sizeof(flat_continuation_unified_desc_compact) <= 32 * 1024,
              "flat_continuation_unified_desc_compact exceeds the 32 KB cudaLaunchKernelExC inline ceiling");

// --- Phase C compact load helpers (continuation rounds ≥ 3) ---
//
// Each `packed` u16 in `desc.sources[]` is:
//   bit 15      : first_access (1 = read prev, fold, write cache; 0 = read cache only)
//   bits 14..11 : ptr_idx (4 bits, 16 slots) into `tables.bases` / `tables.log2_stride`
//   bits 10..0  : poly_idx (11 bits, max 2048) within the chosen consolidated backing
//
// `prev` and `cache` derive from the same per-poly slot in the consolidated
// folding backing — the encoder bakes the per-step offsets into the desc.

template <typename E>
DEVICE_FORCEINLINE void flat_cont_resolve_compact(const flat_continuation_unified_desc_compact &desc, const gkr_source_record record, const E *&prev, E *&cache) {
  const bool first_access = (record.src & 0x8000u) != 0;
  const u32 ptr_idx = (record.src >> 11) & 0xFu;
  const u32 poly_idx = record.src & 0x07FFu;
  const u8 *base_u8 = desc.tables.bases[ptr_idx];
  const u32 log2_stride = desc.tables.log2_stride[ptr_idx];
  const E *poly_slot = reinterpret_cast<const E *>(base_u8) + (static_cast<size_t>(poly_idx) << log2_stride);
  prev = first_access ? poly_slot + desc.prev_per_poly_offset[ptr_idx] : nullptr;
  cache = const_cast<E *>(poly_slot) + desc.cache_per_poly_offset[ptr_idx];
}

// Mirror of `flat_cont_fold_and_load`, but resolves prev/cache via the
// compact descriptor's tables instead of legacy raw pointers.
template <typename E>
DEVICE_FORCEINLINE E flat_cont_fold_and_load_compact(const flat_continuation_unified_desc_compact &desc, const gkr_source_record record,
                                                      const E &folding_challenge, const unsigned fold_stride, const unsigned index) {
  const E *prev;
  E *cache;
  flat_cont_resolve_compact<E>(desc, record, prev, cache);
  if (prev == nullptr) {
    return load<E, ld_modifier::ca>(cache, index);
  }
  const E f0 = load<E, ld_modifier::cs>(prev, index);
  const E f1 = load<E, ld_modifier::cs>(prev, fold_stride + index);
  const E folded = E::fma(folding_challenge, E::sub(f1, f0), f0);
  store<E, st_modifier::wb>(cache, folded, index);
  return folded;
}

// Per-tile fold for the compact continuation descriptor.
template <typename E, unsigned NUM_WARPS>
DEVICE_FORCEINLINE void flat_cont_tile_fold_compact(const flat_continuation_unified_desc_compact &desc, const unsigned fold_start, const unsigned fold_end,
                                                     const unsigned fold_stride, const unsigned next_layer_size, const unsigned folding_challenge_slot,
                                                     const unsigned gid, const unsigned warp_id) {
  if (fold_start == fold_end)
    return;
  for (unsigned s = fold_start + warp_id; s < fold_end; s += NUM_WARPS) {
    const gkr_source_record record = desc.sources[desc.fold_sources[s]];
    flat_cont_fold_and_load_compact<E>(desc, record, ::ab_gkr_main_layer_claim_point[folding_challenge_slot], fold_stride, gid);
    flat_cont_fold_and_load_compact<E>(desc, record, ::ab_gkr_main_layer_claim_point[folding_challenge_slot], fold_stride, next_layer_size + gid);
  }
  __syncthreads();
}

// Cache-only load pair for the compact continuation descriptor.
template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void flat_cont_load_pair_cached_compact(const flat_continuation_unified_desc_compact &desc, const u16 source_idx,
                                                            const unsigned next_layer_size, const unsigned gid, E &f0, E &f1_or_delta) {
  const gkr_source_record record = desc.sources[source_idx];
  const u32 ptr_idx = (record.cache >> 11) & 0xFu;
  const u32 poly_idx = record.cache & 0x07FFu;
  const u8 *base_u8 = desc.tables.bases[ptr_idx];
  const u32 log2_stride = desc.tables.log2_stride[ptr_idx];
  const E *poly_slot = reinterpret_cast<const E *>(base_u8) + (static_cast<size_t>(poly_idx) << log2_stride);
  const E *cache = poly_slot + desc.cache_per_poly_offset[ptr_idx];
  f0 = load<E, ld_modifier::ca>(cache, gid);
  const E f1 = load<E, ld_modifier::ca>(cache, next_layer_size + gid);
  if constexpr (EXPLICIT_FORM) {
    f1_or_delta = f1;
  } else {
    f1_or_delta = E::sub(f1, f0);
  }
}

// Phase C compact round-2 descriptor. Identical shape to round 1 with an
// extra `base_quarter_size` u32 for the `base_after_two` semantics.
//
// Mirror of `gpu_prover::prover::gkr::backward_flat_compact::GpuFlatRound2UnifiedDescCompact`.
struct flat_round2_unified_desc_compact {
  gkr_dim_reducing_tables tables;

  u32 base_layer_half_size;
  u32 base_quarter_size;
  u32 next_layer_size;

  gkr_source_record base_sources[FLAT_CONT_MAX_BASE_SOURCES];
  u32 num_base_sources;

  gkr_source_record ext_sources[FLAT_CONT_MAX_EXT_SOURCES];
  u32 num_ext_sources;

  flat_unified_term terms[FLAT_CONT_UNIFIED_MAX_TERMS];
  u32 num_terms;
  u32 num_constant_terms;
  u32 num_tiles;
  u16 tile_term_offsets[FLAT_CONT_UNIFIED_MAX_TILES + 1];
  u16 tile_fold_offsets[FLAT_CONT_UNIFIED_MAX_TILES + 1];
  u16 fold_sources[FLAT_CONT_UNIFIED_MAX_FOLD_SOURCES];
};

static_assert(sizeof(flat_round2_unified_desc_compact) <= 32 * 1024,
              "flat_round2_unified_desc_compact exceeds the 32 KB cudaLaunchKernelExC inline ceiling");

} // namespace airbender::prover::gkr

// __constant__ coefficient symbol for continuation rounds.
// Separate from round 0's symbol to avoid coupling.
// Defined in main_backward_round3_compute_coeff.cu.
EXTERN __device__ __constant__ e4 ab_gkr_flat_continuation_coefficients[airbender::prover::gkr::FLAT_CONT_CONST_MAX];

namespace airbender::prover::gkr {

// Indexed __constant__ coefficient loader: reads by explicit index (not idx++).
struct coeff_loader_constant_indexed {
  DEVICE_FORCEINLINE e4 operator()(unsigned idx) const { return ::ab_gkr_flat_continuation_coefficients[idx]; }
};

// --- Unified tiled kernel: per-tile fold → sync → compute from cache ---

// Per-tile fold: fold sources from the fold_sources list, distributed across warps.
// Syncs after folding if any work was done.
template <typename E, unsigned NUM_WARPS>
DEVICE_FORCEINLINE void flat_round1_tile_fold(const flat_round1_unified_desc<bf, E> &desc, const unsigned fold_start, const unsigned fold_end,
                                              const E &folding_challenge, const unsigned fold_stride, const unsigned next_layer_size, const unsigned gid,
                                              const unsigned warp_id) {
  if (fold_start == fold_end)
    return;
  for (unsigned s = fold_start + warp_id; s < fold_end; s += NUM_WARPS) {
    const u16 src_idx = desc.fold_sources[s];
    if (src_idx & FLAT_CONT_EXT_SOURCE_BIT) {
      const auto &entry = desc.ext_sources[src_idx & ~FLAT_CONT_EXT_SOURCE_BIT];
      flat_cont_fold_and_load(entry, folding_challenge, fold_stride, gid);
      flat_cont_fold_and_load(entry, folding_challenge, fold_stride, next_layer_size + gid);
    } else {
      const auto &source = desc.base_sources[src_idx];
      gkr_get_base_after_one_value(source, folding_challenge, gid);
      gkr_get_base_after_one_value(source, folding_challenge, next_layer_size + gid);
    }
  }
  __syncthreads();
}

// Load pair from cache only (fold already done).
template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void flat_round1_load_pair_cached(const flat_round1_unified_desc<bf, E> &desc, const u16 source_idx, const unsigned next_layer_size,
                                                     const unsigned gid, E &f0, E &f1_or_delta) {
  const E *cache;
  if (source_idx & FLAT_CONT_EXT_SOURCE_BIT) {
    cache = desc.ext_sources[source_idx & ~FLAT_CONT_EXT_SOURCE_BIT].this_layer_cache_start;
  } else {
    cache = desc.base_sources[source_idx].this_layer_cache_start;
  }
  f0 = load<E, ld_modifier::ca>(cache, gid);
  const E f1 = load<E, ld_modifier::ca>(cache, next_layer_size + gid);
  if constexpr (EXPLICIT_FORM) {
    f1_or_delta = f1;
  } else {
    f1_or_delta = E::sub(f1, f0);
  }
}

// Process a range of unified terms from cache. Warp-split with interleaving.
template <typename E, bool EXPLICIT_FORM, unsigned NUM_WARPS>
DEVICE_FORCEINLINE void flat_round1_compute_unified(const flat_round1_unified_desc<bf, E> &desc, const unsigned term_start, const unsigned term_end,
                                                    const unsigned next_layer_size, const unsigned gid, const unsigned warp_id, E &c0, E &c1) {
  coeff_loader_constant_indexed coeff{};

  for (unsigned i = term_start + warp_id; i < term_end; i += NUM_WARPS) {
    const flat_unified_term t = desc.terms[i];
    const E k = coeff(t.coeff_idx);

    switch (t.term_type) {
    case TERM_TYPE_CONSTANT:
      c0 = E::add(c0, k);
      if constexpr (EXPLICIT_FORM)
        c1 = E::add(c1, k);
      break;
    case TERM_TYPE_C0_ONLY_LINEAR: {
      E f0, f1;
      flat_round1_load_pair_cached<E, EXPLICIT_FORM>(desc, t.source_a, next_layer_size, gid, f0, f1);
      c0 = E::fma(k, f0, c0);
      if constexpr (EXPLICIT_FORM)
        c1 = E::fma(k, f1, c1);
      break;
    }
    case TERM_TYPE_UNIFIED_QUADRATIC: {
      E a0, a1;
      flat_round1_load_pair_cached<E, EXPLICIT_FORM>(desc, t.source_a, next_layer_size, gid, a0, a1);
      E b0, b1;
      flat_round1_load_pair_cached<E, EXPLICIT_FORM>(desc, t.source_b, next_layer_size, gid, b0, b1);
      c0 = E::fma(k, E::mul(a0, b0), c0);
      c1 = E::fma(k, E::mul(a1, b1), c1);
      break;
    }
    case TERM_TYPE_UNIFIED_LINEAR: {
      E f0, f1;
      flat_round1_load_pair_cached<E, EXPLICIT_FORM>(desc, t.source_a, next_layer_size, gid, f0, f1);
      c0 = E::fma(k, f0, c0);
      c1 = E::fma(k, f1, c1);
      break;
    }
    }
  }
}

// ===========================================================================
// Phase C compact helpers for round 1: u16-encoded sources resolved through
// `desc.tables`. Mirror of the legacy round-1 helpers above; same algebra,
// different source resolution.
// ===========================================================================

// Resolve a base source's `(source_kind, base_input_start, this_layer_cache_start)`
// triple from a packed u16 plus the per-source position `idx` (used to look
// up the virtual cache poly_idx).
//
// Returns `source_kind` so the caller can branch real vs virtual; the real
// path uses `base_input_start`, the virtual path synthesizes via
// `gkr_virtual_base_value`.
template <typename E>
DEVICE_FORCEINLINE void flat_round1_resolve_base_compact(const flat_round1_unified_desc_compact &desc, const u32 idx,
                                                          gkr_base_source_kind &source_kind, bool &first_access,
                                                          const bf *&base_input_start, E *&this_layer_cache_start) {
  const gkr_source_record record = desc.base_sources[idx];
  first_access = (record.src & 0x8000u) != 0;
  const bool is_virtual = (record.cache & 0x8000u) != 0;
  const u32 cache_slot = (record.cache >> 11) & 0xFu;
  const u32 cache_poly_idx = record.cache & 0x07FFu;
  const u8 *cache_base_u8 = desc.tables.bases[cache_slot];
  const u32 cache_log2 = desc.tables.log2_stride[cache_slot];
  this_layer_cache_start = const_cast<E *>(reinterpret_cast<const E *>(cache_base_u8))
                           + (static_cast<size_t>(cache_poly_idx) << cache_log2);
  if (is_virtual) {
    base_input_start = nullptr;
    const u32 kind = record.src & 0x7u;
    source_kind = static_cast<gkr_base_source_kind>(kind);
  } else {
    const u32 src_slot = (record.src >> 11) & 0xFu;
    const u32 src_poly_idx = record.src & 0x07FFu;
    const u8 *src_base_u8 = desc.tables.bases[src_slot];
    const u32 src_log2 = desc.tables.log2_stride[src_slot];
    base_input_start = reinterpret_cast<const bf *>(src_base_u8) + (static_cast<size_t>(src_poly_idx) << src_log2);
    source_kind = GKR_BASE_SOURCE_REAL;
  }
}

// Mirror of `gkr_get_base_after_one_bf_value` — reads the bf value at `index`
// from a real source pointer or synthesizes it from a virtual kind.
DEVICE_FORCEINLINE bf flat_round1_get_base_bf_value_compact(const gkr_base_source_kind source_kind, const bf *base_input_start, const unsigned index) {
  if (source_kind == GKR_BASE_SOURCE_REAL)
    return load<bf, ld_modifier::cs>(base_input_start, index);
  return gkr_virtual_base_value(source_kind, index);
}

// Mirror of `gkr_get_base_after_one_value`. Folds the bf source pair at
// `(index, base_layer_half_size + index)` and writes the folded E value into
// the cache at `index` if `first_access` (matches legacy semantics).
template <typename E>
DEVICE_FORCEINLINE E flat_round1_get_base_value_compact(const flat_round1_unified_desc_compact &desc, const u32 idx,
                                                         const E first_folding_challenge, const unsigned index) {
  gkr_base_source_kind source_kind;
  bool first_access;
  const bf *base_input_start;
  E *this_layer_cache_start;
  flat_round1_resolve_base_compact<E>(desc, idx, source_kind, first_access, base_input_start, this_layer_cache_start);
  if (!first_access)
    return load<E, ld_modifier::cs>(this_layer_cache_start, index);

  const bf f0 = flat_round1_get_base_bf_value_compact(source_kind, base_input_start, index);
  const bf f1 = flat_round1_get_base_bf_value_compact(source_kind, base_input_start, desc.base_layer_half_size + index);
  const bf diff = bf::sub(f1, f0);
  const E folded = E::fma(first_folding_challenge, diff, f0);
  store<E, st_modifier::cs>(this_layer_cache_start, folded, index);
  return folded;
}

// Resolve an ext source's `(prev, cache)` pointers from a packed u16. The
// cache pointer derives from the record's cache half.
template <typename E>
DEVICE_FORCEINLINE void flat_round1_resolve_ext_compact(const flat_round1_unified_desc_compact &desc, const gkr_source_record record,
                                                         const E *&prev, E *&cache, bool &first_access) {
  first_access = (record.src & 0x8000u) != 0;
  const u32 ptr_idx = (record.src >> 11) & 0xFu;
  const u32 poly_idx = record.src & 0x07FFu;
  const u8 *src_base_u8 = desc.tables.bases[ptr_idx];
  const u32 src_log2 = desc.tables.log2_stride[ptr_idx];
  const E *src_poly = reinterpret_cast<const E *>(src_base_u8) + (static_cast<size_t>(poly_idx) << src_log2);
  prev = first_access ? src_poly : nullptr;
  const u32 cache_slot = (record.cache >> 11) & 0xFu;
  const u32 cache_poly_idx = record.cache & 0x07FFu;
  const u8 *cache_base_u8 = desc.tables.bases[cache_slot];
  const u32 cache_log2 = desc.tables.log2_stride[cache_slot];
  cache = const_cast<E *>(reinterpret_cast<const E *>(cache_base_u8))
          + (static_cast<size_t>(cache_poly_idx) << cache_log2);
}

// Mirror of `flat_cont_fold_and_load` for round 1 ext sources.
template <typename E>
DEVICE_FORCEINLINE E flat_round1_ext_fold_and_load_compact(const flat_round1_unified_desc_compact &desc, const gkr_source_record record,
                                                            const E &folding_challenge, const unsigned fold_stride, const unsigned index) {
  const E *prev;
  E *cache;
  bool first_access;
  flat_round1_resolve_ext_compact<E>(desc, record, prev, cache, first_access);
  if (!first_access)
    return load<E, ld_modifier::ca>(cache, index);
  const E f0 = load<E, ld_modifier::cs>(prev, index);
  const E f1 = load<E, ld_modifier::cs>(prev, fold_stride + index);
  const E folded = E::fma(folding_challenge, E::sub(f1, f0), f0);
  store<E, st_modifier::wb>(cache, folded, index);
  return folded;
}

// Per-tile fold for round 1 compact: dispatches on source type (base vs ext)
// via the legacy `FLAT_CONT_EXT_SOURCE_BIT` encoding in `fold_sources`.
template <typename E, unsigned NUM_WARPS>
DEVICE_FORCEINLINE void flat_round1_tile_fold_compact(const flat_round1_unified_desc_compact &desc, const unsigned fold_start, const unsigned fold_end,
                                                       const unsigned fold_stride, const unsigned next_layer_size, const unsigned gid, const unsigned warp_id) {
  if (fold_start == fold_end)
    return;
  for (unsigned s = fold_start + warp_id; s < fold_end; s += NUM_WARPS) {
    const u16 src_idx = desc.fold_sources[s];
    if (src_idx & FLAT_CONT_EXT_SOURCE_BIT) {
      const gkr_source_record ext_record = desc.ext_sources[src_idx & ~FLAT_CONT_EXT_SOURCE_BIT];
      flat_round1_ext_fold_and_load_compact<E>(desc, ext_record, ::ab_gkr_main_layer_claim_point[0], fold_stride, gid);
      flat_round1_ext_fold_and_load_compact<E>(desc, ext_record, ::ab_gkr_main_layer_claim_point[0], fold_stride, next_layer_size + gid);
    } else {
      flat_round1_get_base_value_compact<E>(desc, src_idx, ::ab_gkr_main_layer_claim_point[0], gid);
      flat_round1_get_base_value_compact<E>(desc, src_idx, ::ab_gkr_main_layer_claim_point[0], next_layer_size + gid);
    }
  }
  __syncthreads();
}

// Load pair from cache only (post-fold) for round 1 compact. Resolves the
// cache pointer for either base or ext source by inspecting `fold_sources`'s
// high bit.
template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void flat_round1_load_pair_cached_compact(const flat_round1_unified_desc_compact &desc, const u16 source_idx,
                                                              const unsigned next_layer_size, const unsigned gid, E &f0, E &f1_or_delta) {
  const E *cache;
  if (source_idx & FLAT_CONT_EXT_SOURCE_BIT) {
    const gkr_source_record ext_record = desc.ext_sources[source_idx & ~FLAT_CONT_EXT_SOURCE_BIT];
    const u32 cache_slot = (ext_record.cache >> 11) & 0xFu;
    const u32 poly_idx = ext_record.cache & 0x07FFu;
    const u8 *cache_base_u8 = desc.tables.bases[cache_slot];
    const u32 cache_log2 = desc.tables.log2_stride[cache_slot];
    cache = reinterpret_cast<const E *>(cache_base_u8) + (static_cast<size_t>(poly_idx) << cache_log2);
  } else {
    gkr_base_source_kind source_kind;
    bool first_access;
    const bf *base_input_start;
    E *cache_mut;
    flat_round1_resolve_base_compact<E>(desc, source_idx, source_kind, first_access, base_input_start, cache_mut);
    cache = cache_mut;
  }
  f0 = load<E, ld_modifier::ca>(cache, gid);
  const E f1 = load<E, ld_modifier::ca>(cache, next_layer_size + gid);
  if constexpr (EXPLICIT_FORM) {
    f1_or_delta = f1;
  } else {
    f1_or_delta = E::sub(f1, f0);
  }
}

// Process a range of unified terms from cache for round 1 compact. Mirrors
// `flat_round1_compute_unified` but loads via the compact decoder.
template <typename E, bool EXPLICIT_FORM, unsigned NUM_WARPS>
DEVICE_FORCEINLINE void flat_round1_compute_unified_compact(const flat_round1_unified_desc_compact &desc, const unsigned term_start, const unsigned term_end,
                                                             const unsigned next_layer_size, const unsigned gid, const unsigned warp_id, E &c0, E &c1) {
  coeff_loader_constant_indexed coeff{};

  for (unsigned i = term_start + warp_id; i < term_end; i += NUM_WARPS) {
    const flat_unified_term t = desc.terms[i];
    const E k = coeff(t.coeff_idx);

    switch (t.term_type) {
    case TERM_TYPE_CONSTANT:
      c0 = E::add(c0, k);
      if constexpr (EXPLICIT_FORM)
        c1 = E::add(c1, k);
      break;
    case TERM_TYPE_C0_ONLY_LINEAR: {
      E f0, f1;
      flat_round1_load_pair_cached_compact<E, EXPLICIT_FORM>(desc, t.source_a, next_layer_size, gid, f0, f1);
      c0 = E::fma(k, f0, c0);
      if constexpr (EXPLICIT_FORM)
        c1 = E::fma(k, f1, c1);
      break;
    }
    case TERM_TYPE_UNIFIED_QUADRATIC: {
      E a0, a1;
      flat_round1_load_pair_cached_compact<E, EXPLICIT_FORM>(desc, t.source_a, next_layer_size, gid, a0, a1);
      E b0, b1;
      flat_round1_load_pair_cached_compact<E, EXPLICIT_FORM>(desc, t.source_b, next_layer_size, gid, b0, b1);
      c0 = E::fma(k, E::mul(a0, b0), c0);
      c1 = E::fma(k, E::mul(a1, b1), c1);
      break;
    }
    case TERM_TYPE_UNIFIED_LINEAR: {
      E f0, f1;
      flat_round1_load_pair_cached_compact<E, EXPLICIT_FORM>(desc, t.source_a, next_layer_size, gid, f0, f1);
      c0 = E::fma(k, f0, c0);
      c1 = E::fma(k, f1, c1);
      break;
    }
    }
  }
}

// ===========================================================================
// Unified tiled helpers for continuation rounds (3+): single source array.
// ===========================================================================

// Per-tile fold for continuation: all sources are flat_continuing_source_entry.
template <typename E, unsigned NUM_WARPS>
DEVICE_FORCEINLINE void flat_cont_tile_fold(const flat_continuation_unified_desc<E> &desc, const unsigned fold_start, const unsigned fold_end,
                                            const E &folding_challenge, const unsigned fold_stride, const unsigned next_layer_size, const unsigned gid,
                                            const unsigned warp_id) {
  if (fold_start == fold_end)
    return;
  for (unsigned s = fold_start + warp_id; s < fold_end; s += NUM_WARPS) {
    const auto &entry = desc.sources[desc.fold_sources[s]];
    flat_cont_fold_and_load(entry, folding_challenge, fold_stride, gid);
    flat_cont_fold_and_load(entry, folding_challenge, fold_stride, next_layer_size + gid);
  }
  __syncthreads();
}

// Load pair from cache only for continuation unified desc.
template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void flat_cont_load_pair_cached(const flat_continuation_unified_desc<E> &desc, const u16 source_idx, const unsigned next_layer_size,
                                                   const unsigned gid, E &f0, E &f1_or_delta) {
  const E *cache = desc.sources[source_idx].this_layer_cache_start;
  f0 = load<E, ld_modifier::ca>(cache, gid);
  const E f1 = load<E, ld_modifier::ca>(cache, next_layer_size + gid);
  if constexpr (EXPLICIT_FORM) {
    f1_or_delta = f1;
  } else {
    f1_or_delta = E::sub(f1, f0);
  }
}

// Process a range of unified terms from cache for continuation. Warp-split with interleaving.
template <typename E, bool EXPLICIT_FORM, unsigned NUM_WARPS>
DEVICE_FORCEINLINE void flat_cont_compute_unified(const flat_continuation_unified_desc<E> &desc, const unsigned term_start, const unsigned term_end,
                                                  const unsigned next_layer_size, const unsigned gid, const unsigned warp_id, E &c0, E &c1) {
  coeff_loader_constant_indexed coeff{};

  for (unsigned i = term_start + warp_id; i < term_end; i += NUM_WARPS) {
    const flat_unified_term t = desc.terms[i];
    const E k = coeff(t.coeff_idx);

    switch (t.term_type) {
    case TERM_TYPE_CONSTANT:
      c0 = E::add(c0, k);
      if constexpr (EXPLICIT_FORM)
        c1 = E::add(c1, k);
      break;
    case TERM_TYPE_C0_ONLY_LINEAR: {
      E f0, f1;
      flat_cont_load_pair_cached<E, EXPLICIT_FORM>(desc, t.source_a, next_layer_size, gid, f0, f1);
      c0 = E::fma(k, f0, c0);
      if constexpr (EXPLICIT_FORM)
        c1 = E::fma(k, f1, c1);
      break;
    }
    case TERM_TYPE_UNIFIED_QUADRATIC: {
      E a0, a1;
      flat_cont_load_pair_cached<E, EXPLICIT_FORM>(desc, t.source_a, next_layer_size, gid, a0, a1);
      E b0, b1;
      flat_cont_load_pair_cached<E, EXPLICIT_FORM>(desc, t.source_b, next_layer_size, gid, b0, b1);
      c0 = E::fma(k, E::mul(a0, b0), c0);
      c1 = E::fma(k, E::mul(a1, b1), c1);
      break;
    }
    case TERM_TYPE_UNIFIED_LINEAR: {
      E f0, f1;
      flat_cont_load_pair_cached<E, EXPLICIT_FORM>(desc, t.source_a, next_layer_size, gid, f0, f1);
      c0 = E::fma(k, f0, c0);
      c1 = E::fma(k, f1, c1);
      break;
    }
    }
  }
}

// Compute path for the Phase C compact continuation descriptor, mirroring
// `flat_cont_compute_unified` but loading from compact-resolved cache.
template <typename E, bool EXPLICIT_FORM, unsigned NUM_WARPS>
DEVICE_FORCEINLINE void flat_cont_compute_unified_compact(const flat_continuation_unified_desc_compact &desc, const unsigned term_start, const unsigned term_end,
                                                           const unsigned next_layer_size, const unsigned gid, const unsigned warp_id, E &c0, E &c1) {
  coeff_loader_constant_indexed coeff{};

  for (unsigned i = term_start + warp_id; i < term_end; i += NUM_WARPS) {
    const flat_unified_term t = desc.terms[i];
    const E k = coeff(t.coeff_idx);

    switch (t.term_type) {
    case TERM_TYPE_CONSTANT:
      c0 = E::add(c0, k);
      if constexpr (EXPLICIT_FORM)
        c1 = E::add(c1, k);
      break;
    case TERM_TYPE_C0_ONLY_LINEAR: {
      E f0, f1;
      flat_cont_load_pair_cached_compact<E, EXPLICIT_FORM>(desc, t.source_a, next_layer_size, gid, f0, f1);
      c0 = E::fma(k, f0, c0);
      if constexpr (EXPLICIT_FORM)
        c1 = E::fma(k, f1, c1);
      break;
    }
    case TERM_TYPE_UNIFIED_QUADRATIC: {
      E a0, a1;
      flat_cont_load_pair_cached_compact<E, EXPLICIT_FORM>(desc, t.source_a, next_layer_size, gid, a0, a1);
      E b0, b1;
      flat_cont_load_pair_cached_compact<E, EXPLICIT_FORM>(desc, t.source_b, next_layer_size, gid, b0, b1);
      c0 = E::fma(k, E::mul(a0, b0), c0);
      c1 = E::fma(k, E::mul(a1, b1), c1);
      break;
    }
    case TERM_TYPE_UNIFIED_LINEAR: {
      E f0, f1;
      flat_cont_load_pair_cached_compact<E, EXPLICIT_FORM>(desc, t.source_a, next_layer_size, gid, f0, f1);
      c0 = E::fma(k, f0, c0);
      c1 = E::fma(k, f1, c1);
      break;
    }
    }
  }
}

// ===========================================================================
// Phase C compact helpers for round 2: same shape as round 1 with
// `base_after_two` semantics (two folds, four bf reads per cache write).
// ===========================================================================

// Resolve a base source's `(source_kind, base_input_start, this_layer_cache_start)`
// triple from a packed u16 plus the per-source position `idx`.
// Encoding identical to round 1.
template <typename E>
DEVICE_FORCEINLINE void flat_round2_resolve_base_compact(const flat_round2_unified_desc_compact &desc, const u32 idx,
                                                          gkr_base_source_kind &source_kind, bool &first_access,
                                                          const bf *&base_input_start, E *&this_layer_cache_start) {
  const gkr_source_record record = desc.base_sources[idx];
  first_access = (record.src & 0x8000u) != 0;
  const bool is_virtual = (record.cache & 0x8000u) != 0;
  const u32 cache_slot = (record.cache >> 11) & 0xFu;
  const u32 cache_poly_idx = record.cache & 0x07FFu;
  const u8 *cache_base_u8 = desc.tables.bases[cache_slot];
  const u32 cache_log2 = desc.tables.log2_stride[cache_slot];
  this_layer_cache_start = const_cast<E *>(reinterpret_cast<const E *>(cache_base_u8))
                           + (static_cast<size_t>(cache_poly_idx) << cache_log2);
  if (is_virtual) {
    base_input_start = nullptr;
    const u32 kind = record.src & 0x7u;
    source_kind = static_cast<gkr_base_source_kind>(kind);
  } else {
    const u32 src_slot = (record.src >> 11) & 0xFu;
    const u32 src_poly_idx = record.src & 0x07FFu;
    const u8 *src_base_u8 = desc.tables.bases[src_slot];
    const u32 src_log2 = desc.tables.log2_stride[src_slot];
    base_input_start = reinterpret_cast<const bf *>(src_base_u8) + (static_cast<size_t>(src_poly_idx) << src_log2);
    source_kind = GKR_BASE_SOURCE_REAL;
  }
}

// Folds the bf source quadruple at the base-after-two grid into a single E
// value and writes to the cache at `index` if `first_access`.
template <typename E>
DEVICE_FORCEINLINE E flat_round2_get_base_value_compact(const flat_round2_unified_desc_compact &desc, const u32 idx, const unsigned index) {
  gkr_base_source_kind source_kind;
  bool first_access;
  const bf *base_input_start;
  E *this_layer_cache_start;
  flat_round2_resolve_base_compact<E>(desc, idx, source_kind, first_access, base_input_start, this_layer_cache_start);
  if (!first_access)
    return load<E, ld_modifier::cs>(this_layer_cache_start, index);

  const bf f00 = flat_round1_get_base_bf_value_compact(source_kind, base_input_start, index);
  const bf f01 = flat_round1_get_base_bf_value_compact(source_kind, base_input_start, desc.base_layer_half_size + index);
  const bf f10 = flat_round1_get_base_bf_value_compact(source_kind, base_input_start, desc.base_quarter_size + index);
  const bf f11 = flat_round1_get_base_bf_value_compact(source_kind, base_input_start, desc.base_layer_half_size + desc.base_quarter_size + index);

  const bf c01 = bf::sub(f01, f00);
  const bf c10 = bf::sub(f10, f00);
  bf c11 = f00;
  c11 = bf::sub(c11, f01);
  c11 = bf::sub(c11, f10);
  c11 = bf::add(c11, f11);

  E result = E::mul(::ab_gkr_round2_challenges[0], c01);
  result = E::fma(::ab_gkr_round2_challenges[1], c10, result);
  result = E::fma(::ab_gkr_round2_challenges[2], c11, result);
  result = E::add(result, f00);

  store<E, st_modifier::cs>(this_layer_cache_start, result, index);
  return result;
}

// Round 2 ext source resolution: `previous_layer_start` and
// `this_layer_cache_start` BOTH live inside the consolidated ext-folding Arc
// (same poly slot) with `prev_sub_offset = 0` and
// `cache_sub_offset = size_after_one_fold = 2 * fold_stride = 4 * next_layer_size`
// (round-2 sumcheck-step-2 invariant; verified by the encoder).
//
// The kernel re-derives the cache offset from the runtime `next_layer_size`.
template <typename E>
DEVICE_FORCEINLINE void flat_round2_resolve_ext_compact(const flat_round2_unified_desc_compact &desc, const gkr_source_record record,
                                                         const E *&prev, E *&cache, bool &first_access, const unsigned next_layer_size) {
  first_access = (record.src & 0x8000u) != 0;
  const u32 ptr_idx = (record.src >> 11) & 0xFu;
  const u32 poly_idx = record.src & 0x07FFu;
  const u8 *base_u8 = desc.tables.bases[ptr_idx];
  const u32 log2_stride = desc.tables.log2_stride[ptr_idx];
  const E *poly_slot = reinterpret_cast<const E *>(base_u8) + (static_cast<size_t>(poly_idx) << log2_stride);
  prev = first_access ? poly_slot : nullptr;
  // cache_offset = size_after_one_fold = 4 * next_layer_size (round-2
  // sumcheck step 2 invariant).
  cache = const_cast<E *>(poly_slot) + (static_cast<size_t>(next_layer_size) << 2);
}

template <typename E>
DEVICE_FORCEINLINE E flat_round2_ext_fold_and_load_compact(const flat_round2_unified_desc_compact &desc, const gkr_source_record record,
                                                            const E &folding_challenge, const unsigned fold_stride, const unsigned next_layer_size,
                                                            const unsigned index) {
  const E *prev;
  E *cache;
  bool first_access;
  flat_round2_resolve_ext_compact<E>(desc, record, prev, cache, first_access, next_layer_size);
  if (!first_access)
    return load<E, ld_modifier::ca>(cache, index);
  const E f0 = load<E, ld_modifier::cs>(prev, index);
  const E f1 = load<E, ld_modifier::cs>(prev, fold_stride + index);
  const E folded = E::fma(folding_challenge, E::sub(f1, f0), f0);
  store<E, st_modifier::wb>(cache, folded, index);
  return folded;
}

template <typename E, unsigned NUM_WARPS>
DEVICE_FORCEINLINE void flat_round2_tile_fold_compact(const flat_round2_unified_desc_compact &desc, const unsigned fold_start, const unsigned fold_end,
                                                       const unsigned fold_stride, const unsigned next_layer_size, const unsigned gid, const unsigned warp_id) {
  if (fold_start == fold_end)
    return;
  for (unsigned s = fold_start + warp_id; s < fold_end; s += NUM_WARPS) {
    const u16 src_idx = desc.fold_sources[s];
    if (src_idx & FLAT_CONT_EXT_SOURCE_BIT) {
      const gkr_source_record ext_record = desc.ext_sources[src_idx & ~FLAT_CONT_EXT_SOURCE_BIT];
      flat_round2_ext_fold_and_load_compact<E>(desc, ext_record, ::ab_gkr_round2_challenges[1], fold_stride, next_layer_size, gid);
      flat_round2_ext_fold_and_load_compact<E>(desc, ext_record, ::ab_gkr_round2_challenges[1], fold_stride, next_layer_size, next_layer_size + gid);
    } else {
      flat_round2_get_base_value_compact<E>(desc, src_idx, gid);
      flat_round2_get_base_value_compact<E>(desc, src_idx, next_layer_size + gid);
    }
  }
  __syncthreads();
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void flat_round2_load_pair_cached_compact(const flat_round2_unified_desc_compact &desc, const u16 source_idx,
                                                              const unsigned next_layer_size, const unsigned gid, E &f0, E &f1_or_delta) {
  const E *cache;
  if (source_idx & FLAT_CONT_EXT_SOURCE_BIT) {
    const gkr_source_record ext_record = desc.ext_sources[source_idx & ~FLAT_CONT_EXT_SOURCE_BIT];
    const u32 ptr_idx = (ext_record.cache >> 11) & 0xFu;
    const u32 poly_idx = ext_record.cache & 0x07FFu;
    const u8 *base_u8 = desc.tables.bases[ptr_idx];
    const u32 log2_stride = desc.tables.log2_stride[ptr_idx];
    const E *poly_slot = reinterpret_cast<const E *>(base_u8) + (static_cast<size_t>(poly_idx) << log2_stride);
    // Round 2 ext cache lives at sub_offset = size_after_one_fold within the
    // poly slot; cache_offset = 4 * next_layer_size, matching
    // `flat_round2_resolve_ext_compact`.
    cache = poly_slot + (static_cast<size_t>(next_layer_size) << 2);
  } else {
    gkr_base_source_kind source_kind;
    bool first_access;
    const bf *base_input_start;
    E *cache_mut;
    flat_round2_resolve_base_compact<E>(desc, source_idx, source_kind, first_access, base_input_start, cache_mut);
    cache = cache_mut;
  }
  f0 = load<E, ld_modifier::ca>(cache, gid);
  const E f1 = load<E, ld_modifier::ca>(cache, next_layer_size + gid);
  if constexpr (EXPLICIT_FORM) {
    f1_or_delta = f1;
  } else {
    f1_or_delta = E::sub(f1, f0);
  }
}

template <typename E, bool EXPLICIT_FORM, unsigned NUM_WARPS>
DEVICE_FORCEINLINE void flat_round2_compute_unified_compact(const flat_round2_unified_desc_compact &desc, const unsigned term_start, const unsigned term_end,
                                                             const unsigned next_layer_size, const unsigned gid, const unsigned warp_id, E &c0, E &c1) {
  coeff_loader_constant_indexed coeff{};

  for (unsigned i = term_start + warp_id; i < term_end; i += NUM_WARPS) {
    const flat_unified_term t = desc.terms[i];
    const E k = coeff(t.coeff_idx);

    switch (t.term_type) {
    case TERM_TYPE_CONSTANT:
      c0 = E::add(c0, k);
      if constexpr (EXPLICIT_FORM)
        c1 = E::add(c1, k);
      break;
    case TERM_TYPE_C0_ONLY_LINEAR: {
      E f0, f1;
      flat_round2_load_pair_cached_compact<E, EXPLICIT_FORM>(desc, t.source_a, next_layer_size, gid, f0, f1);
      c0 = E::fma(k, f0, c0);
      if constexpr (EXPLICIT_FORM)
        c1 = E::fma(k, f1, c1);
      break;
    }
    case TERM_TYPE_UNIFIED_QUADRATIC: {
      E a0, a1;
      flat_round2_load_pair_cached_compact<E, EXPLICIT_FORM>(desc, t.source_a, next_layer_size, gid, a0, a1);
      E b0, b1;
      flat_round2_load_pair_cached_compact<E, EXPLICIT_FORM>(desc, t.source_b, next_layer_size, gid, b0, b1);
      c0 = E::fma(k, E::mul(a0, b0), c0);
      c1 = E::fma(k, E::mul(a1, b1), c1);
      break;
    }
    case TERM_TYPE_UNIFIED_LINEAR: {
      E f0, f1;
      flat_round2_load_pair_cached_compact<E, EXPLICIT_FORM>(desc, t.source_a, next_layer_size, gid, f0, f1);
      c0 = E::fma(k, f0, c0);
      c1 = E::fma(k, f1, c1);
      break;
    }
    }
  }
}

} // namespace airbender::prover::gkr
