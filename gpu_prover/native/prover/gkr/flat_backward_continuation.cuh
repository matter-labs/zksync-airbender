#pragma once

#include "common.cuh"
#include "flat_backward.cuh" // flat_c0_ref, flat_c1_pair, coeff_loader_ptr

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
  const E folded = E::add(f0, E::mul(folding_challenge, E::sub(f1, f0)));
  store<E, st_modifier::wb>(entry.this_layer_cache_start, folded, index);
  return folded;
}

// Load both evaluation points (f0 at gid, f1 at gid + next_layer_size).
// In explicit form: returns (f0, f1).
// In compact form: returns (f0, delta = f1 - f0).
template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void flat_cont_load_pair(const flat_continuing_source_entry<E> &entry, const E &folding_challenge, const unsigned fold_stride,
                                            const unsigned next_layer_size, const unsigned gid, E &f0, E &f1_or_delta) {
  f0 = flat_cont_fold_and_load(entry, folding_challenge, fold_stride, gid);
  const E f1 = flat_cont_fold_and_load(entry, folding_challenge, fold_stride, next_layer_size + gid);
  if constexpr (EXPLICIT_FORM) {
    f1_or_delta = f1;
  } else {
    f1_or_delta = E::sub(f1, f0);
  }
}

// --- Flat continuation kernel ---

template <typename E, bool EXPLICIT_FORM, typename CoeffLoader>
DEVICE_FORCEINLINE void flat_continuation_compute_impl(const flat_continuation_static_desc<E> &desc, CoeffLoader coeff_loader, const E &folding_challenge,
                                                       const unsigned fold_stride, const unsigned next_layer_size, const E *__restrict__ eq_values,
                                                       E *__restrict__ contributions, const unsigned acc_size, const unsigned gid) {
  E c0 = E::ZERO();
  E c1 = E::ZERO();

  // Constants (no source reference)
  for (unsigned i = 0; i < desc.num_constants; i++) {
    const E k = coeff_loader();
    c0 = E::add(c0, k);
    if constexpr (EXPLICIT_FORM)
      c1 = E::add(c1, k);
  }

  // c0-only linear terms (copy gates, linear constraint terms)
  // Compact: c0 only. Explicit: c0 + c1.
  for (unsigned i = 0; i < desc.num_c0_only_linear; i++) {
    const auto &entry = desc.sources[desc.c0_only_linear[i].source_idx];
    E f0, f1;
    flat_cont_load_pair<E, EXPLICIT_FORM>(entry, folding_challenge, fold_stride, next_layer_size, gid, f0, f1);
    const E k = coeff_loader();
    c0 = E::add(c0, E::mul(k, f0));
    if constexpr (EXPLICIT_FORM)
      c1 = E::add(c1, E::mul(k, f1));
  }

  // Unified quadratic terms (product, lookup, mask, constraint quadratic, cross-products)
  // Always contribute to both c0 and c1.
  for (unsigned i = 0; i < desc.num_unified_quadratic; i++) {
    const auto &t = desc.unified_quadratic[i];
    E a0, a1;
    flat_cont_load_pair<E, EXPLICIT_FORM>(desc.sources[t.source_a], folding_challenge, fold_stride, next_layer_size, gid, a0, a1);
    E b0, b1;
    flat_cont_load_pair<E, EXPLICIT_FORM>(desc.sources[t.source_b], folding_challenge, fold_stride, next_layer_size, gid, b0, b1);
    const E k = coeff_loader();
    c0 = E::add(c0, E::mul(k, E::mul(a0, b0)));
    c1 = E::add(c1, E::mul(k, E::mul(a1, b1)));
  }

  // Unified linear terms (materialize linear form)
  // Always contribute to both c0 and c1.
  for (unsigned i = 0; i < desc.num_unified_linear; i++) {
    const auto &entry = desc.sources[desc.unified_linear[i].source_idx];
    E f0, f1;
    flat_cont_load_pair<E, EXPLICIT_FORM>(entry, folding_challenge, fold_stride, next_layer_size, gid, f0, f1);
    const E k = coeff_loader();
    c0 = E::add(c0, E::mul(k, f0));
    c1 = E::add(c1, E::mul(k, f1));
  }

  // eq_values: cs (streaming, read once, large) — don't pollute L1 or L2.
  const E eq = load<E, ld_modifier::cs>(eq_values, gid);
  store<E, st_modifier::cs>(contributions, E::mul(c0, eq), gid);
  store<E, st_modifier::cs>(contributions + acc_size, E::mul(c1, eq), gid);
}

// Public API: pointer-based (non-constant path).
template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void flat_continuation_compute(const flat_continuation_static_desc<E> &desc, const E *__restrict__ coefficients, const E &folding_challenge,
                                                  const unsigned fold_stride, const unsigned next_layer_size, const E *__restrict__ eq_values,
                                                  E *__restrict__ contributions, const unsigned acc_size, const unsigned gid) {
  coeff_loader_ptr<E> loader{coefficients};
  flat_continuation_compute_impl<E, EXPLICIT_FORM>(desc, loader, folding_challenge, fold_stride, next_layer_size, eq_values, contributions, acc_size, gid);
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
constexpr unsigned FLAT_CONT_UNIFIED_MAX_GRID_DIM =
    (FLAT_CONT_MAX_BASE_SOURCES + FLAT_CONT_MAX_EXT_SOURCES) / FLAT_CONT_UNIFIED_SOURCE_GROUP_SIZE;
constexpr unsigned FLAT_CONT_UNIFIED_MAX_TERMS = 1024;
constexpr unsigned FLAT_CONT_UNIFIED_MAX_TILES = FLAT_CONT_UNIFIED_MAX_TERMS;
constexpr unsigned FLAT_CONT_UNIFIED_MAX_FOLD_SOURCES =
    FLAT_CONT_MAX_BASE_SOURCES + FLAT_CONT_MAX_EXT_SOURCES;

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

// Combined descriptor for the unified round 2 kernel: base_after_two + ext
// sources + mixed terms with per-tile fold/compute metadata.
template <typename B, typename E> struct flat_round2_unified_desc {
  gkr_base_after_two_source<B, E> base_sources[FLAT_CONT_MAX_BASE_SOURCES];
  u32 num_base_sources;

  flat_continuing_source_entry<E> ext_sources[FLAT_CONT_MAX_EXT_SOURCES];
  u32 num_ext_sources;

  flat_unified_term terms[FLAT_CONT_UNIFIED_MAX_TERMS];
  u32 num_terms;

  u32 num_constant_terms;
  u32 num_tiles;
  u16 tile_term_offsets[FLAT_CONT_UNIFIED_MAX_TILES + 1];
  u16 tile_fold_offsets[FLAT_CONT_UNIFIED_MAX_TILES + 1];
  u16 fold_sources[FLAT_CONT_UNIFIED_MAX_FOLD_SOURCES];
};

// Round 1 load pair: dispatches on source type bit.
template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void flat_round1_load_pair(const flat_round1_static_desc<bf, E> &desc, const u16 source_idx, const E &folding_challenge,
                                              const unsigned fold_stride, const unsigned next_layer_size, const unsigned gid, E &f0, E &f1_or_delta) {
  if (source_idx & FLAT_CONT_EXT_SOURCE_BIT) {
    flat_cont_load_pair<E, EXPLICIT_FORM>(desc.ext_sources[source_idx & ~FLAT_CONT_EXT_SOURCE_BIT], folding_challenge, fold_stride, next_layer_size, gid, f0,
                                          f1_or_delta);
  } else {
    gkr_get_base_after_one_points<E, EXPLICIT_FORM>(desc.base_sources[source_idx], folding_challenge, gid, f0, f1_or_delta);
  }
}

// Round 1 flat compute kernel (templatized on CoeffLoader).
template <typename E, bool EXPLICIT_FORM, typename CoeffLoader>
DEVICE_FORCEINLINE void flat_round1_compute_impl(const flat_round1_static_desc<bf, E> &desc, CoeffLoader coeff_loader, const E &folding_challenge,
                                                 const unsigned fold_stride, const unsigned next_layer_size, const E *__restrict__ eq_values,
                                                 E *__restrict__ contributions, const unsigned acc_size, const unsigned gid) {
  E c0 = E::ZERO();
  E c1 = E::ZERO();

  for (unsigned i = 0; i < desc.num_constants; i++) {
    const E k = coeff_loader();
    c0 = E::add(c0, k);
    if constexpr (EXPLICIT_FORM)
      c1 = E::add(c1, k);
  }
  for (unsigned i = 0; i < desc.num_c0_only_linear; i++) {
    E f0, f1;
    flat_round1_load_pair<E, EXPLICIT_FORM>(desc, desc.c0_only_linear[i].source_idx, folding_challenge, fold_stride, next_layer_size, gid, f0, f1);
    const E k = coeff_loader();
    c0 = E::add(c0, E::mul(k, f0));
    if constexpr (EXPLICIT_FORM)
      c1 = E::add(c1, E::mul(k, f1));
  }
  for (unsigned i = 0; i < desc.num_unified_quadratic; i++) {
    const auto &t = desc.unified_quadratic[i];
    E a0, a1;
    flat_round1_load_pair<E, EXPLICIT_FORM>(desc, t.source_a, folding_challenge, fold_stride, next_layer_size, gid, a0, a1);
    E b0, b1;
    flat_round1_load_pair<E, EXPLICIT_FORM>(desc, t.source_b, folding_challenge, fold_stride, next_layer_size, gid, b0, b1);
    const E k = coeff_loader();
    c0 = E::add(c0, E::mul(k, E::mul(a0, b0)));
    c1 = E::add(c1, E::mul(k, E::mul(a1, b1)));
  }
  for (unsigned i = 0; i < desc.num_unified_linear; i++) {
    E f0, f1;
    flat_round1_load_pair<E, EXPLICIT_FORM>(desc, desc.unified_linear[i].source_idx, folding_challenge, fold_stride, next_layer_size, gid, f0, f1);
    const E k = coeff_loader();
    c0 = E::add(c0, E::mul(k, f0));
    c1 = E::add(c1, E::mul(k, f1));
  }

  const E eq = load<E, ld_modifier::cs>(eq_values, gid);
  store<E, st_modifier::cs>(contributions, E::mul(c0, eq), gid);
  store<E, st_modifier::cs>(contributions + acc_size, E::mul(c1, eq), gid);
}

// Public API: pointer-based (non-constant path).
template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void flat_round1_compute(const flat_round1_static_desc<bf, E> &desc, const E *__restrict__ coefficients, const E &folding_challenge,
                                            const unsigned fold_stride, const unsigned next_layer_size, const E *__restrict__ eq_values,
                                            E *__restrict__ contributions, const unsigned acc_size, const unsigned gid) {
  coeff_loader_ptr<E> loader{coefficients};
  flat_round1_compute_impl<E, EXPLICIT_FORM>(desc, loader, folding_challenge, fold_stride, next_layer_size, eq_values, contributions, acc_size, gid);
}

// --- Round 2 static description ---
// Base sources: gkr_base_after_two_source (self-contained, includes fold params).

template <typename B, typename E> struct flat_round2_static_desc {
  gkr_base_after_two_source<B, E> base_sources[FLAT_CONT_MAX_BASE_SOURCES];
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

// Round 2 load pair: dispatches on source type bit.
// Needs both folding challenges (first and second).
template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void flat_round2_load_pair(const flat_round2_static_desc<bf, E> &desc, const u16 source_idx, const E &first_folding_challenge,
                                              const E &second_folding_challenge, const unsigned fold_stride, const unsigned next_layer_size, const unsigned gid,
                                              E &f0, E &f1_or_delta) {
  if (source_idx & FLAT_CONT_EXT_SOURCE_BIT) {
    // Ext continuing sources fold with the second challenge only (the first was consumed in round 1).
    flat_cont_load_pair<E, EXPLICIT_FORM>(desc.ext_sources[source_idx & ~FLAT_CONT_EXT_SOURCE_BIT], second_folding_challenge, fold_stride, next_layer_size, gid,
                                          f0, f1_or_delta);
  } else {
    gkr_get_base_after_two_points<E, EXPLICIT_FORM>(desc.base_sources[source_idx], first_folding_challenge, second_folding_challenge, gid, f0, f1_or_delta);
  }
}

// Round 2 flat compute kernel (templatized on CoeffLoader).
template <typename E, bool EXPLICIT_FORM, typename CoeffLoader>
DEVICE_FORCEINLINE void flat_round2_compute_impl(const flat_round2_static_desc<bf, E> &desc, CoeffLoader coeff_loader, const E &first_folding_challenge,
                                                 const E &second_folding_challenge, const unsigned fold_stride, const unsigned next_layer_size,
                                                 const E *__restrict__ eq_values, E *__restrict__ contributions, const unsigned acc_size, const unsigned gid) {
  E c0 = E::ZERO();
  E c1 = E::ZERO();

  for (unsigned i = 0; i < desc.num_constants; i++) {
    const E k = coeff_loader();
    c0 = E::add(c0, k);
    if constexpr (EXPLICIT_FORM)
      c1 = E::add(c1, k);
  }
  for (unsigned i = 0; i < desc.num_c0_only_linear; i++) {
    E f0, f1;
    flat_round2_load_pair<E, EXPLICIT_FORM>(desc, desc.c0_only_linear[i].source_idx, first_folding_challenge, second_folding_challenge, fold_stride,
                                            next_layer_size, gid, f0, f1);
    const E k = coeff_loader();
    c0 = E::add(c0, E::mul(k, f0));
    if constexpr (EXPLICIT_FORM)
      c1 = E::add(c1, E::mul(k, f1));
  }
  for (unsigned i = 0; i < desc.num_unified_quadratic; i++) {
    const auto &t = desc.unified_quadratic[i];
    E a0, a1;
    flat_round2_load_pair<E, EXPLICIT_FORM>(desc, t.source_a, first_folding_challenge, second_folding_challenge, fold_stride, next_layer_size, gid, a0, a1);
    E b0, b1;
    flat_round2_load_pair<E, EXPLICIT_FORM>(desc, t.source_b, first_folding_challenge, second_folding_challenge, fold_stride, next_layer_size, gid, b0, b1);
    const E k = coeff_loader();
    c0 = E::add(c0, E::mul(k, E::mul(a0, b0)));
    c1 = E::add(c1, E::mul(k, E::mul(a1, b1)));
  }
  for (unsigned i = 0; i < desc.num_unified_linear; i++) {
    E f0, f1;
    flat_round2_load_pair<E, EXPLICIT_FORM>(desc, desc.unified_linear[i].source_idx, first_folding_challenge, second_folding_challenge, fold_stride,
                                            next_layer_size, gid, f0, f1);
    const E k = coeff_loader();
    c0 = E::add(c0, E::mul(k, f0));
    c1 = E::add(c1, E::mul(k, f1));
  }

  const E eq = load<E, ld_modifier::cs>(eq_values, gid);
  store<E, st_modifier::cs>(contributions, E::mul(c0, eq), gid);
  store<E, st_modifier::cs>(contributions + acc_size, E::mul(c1, eq), gid);
}

// Public API: pointer-based (non-constant path).
template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void flat_round2_compute(const flat_round2_static_desc<bf, E> &desc, const E *__restrict__ coefficients, const E &first_folding_challenge,
                                            const E &second_folding_challenge, const unsigned fold_stride, const unsigned next_layer_size,
                                            const E *__restrict__ eq_values, E *__restrict__ contributions, const unsigned acc_size, const unsigned gid) {
  coeff_loader_ptr<E> loader{coefficients};
  flat_round2_compute_impl<E, EXPLICIT_FORM>(desc, loader, first_folding_challenge, second_folding_challenge, fold_stride, next_layer_size, eq_values,
                                             contributions, acc_size, gid);
}

} // namespace airbender::prover::gkr

// __constant__ coefficient symbol for continuation rounds.
// Separate from round 0's symbol to avoid coupling.
// Defined in main_backward_round3_compute_coeff.cu.
EXTERN __device__ __constant__ e4 ab_gkr_flat_continuation_coefficients[airbender::prover::gkr::FLAT_CONT_CONST_MAX];

namespace airbender::prover::gkr {

// Constant-symbol loader for continuation rounds: accesses the symbol by index → LDC.
// Not templated: the __constant__ symbol is e4, direct access is required for LDC.
struct coeff_loader_continuation_constant {
  unsigned idx = 0;
  DEVICE_FORCEINLINE e4 operator()() { return ::ab_gkr_flat_continuation_coefficients[idx++]; }
};

// Constant-path variants: read coefficients from __constant__ symbol via LDC.

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void flat_continuation_compute_constant(const flat_continuation_static_desc<E> &desc, const E &folding_challenge, const unsigned fold_stride,
                                                           const unsigned next_layer_size, const E *__restrict__ eq_values, E *__restrict__ contributions,
                                                           const unsigned acc_size, const unsigned gid) {
  coeff_loader_continuation_constant loader{};
  flat_continuation_compute_impl<E, EXPLICIT_FORM>(desc, loader, folding_challenge, fold_stride, next_layer_size, eq_values, contributions, acc_size, gid);
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void flat_round1_compute_constant(const flat_round1_static_desc<bf, E> &desc, const E &folding_challenge, const unsigned fold_stride,
                                                     const unsigned next_layer_size, const E *__restrict__ eq_values, E *__restrict__ contributions,
                                                     const unsigned acc_size, const unsigned gid) {
  coeff_loader_continuation_constant loader{};
  flat_round1_compute_impl<E, EXPLICIT_FORM>(desc, loader, folding_challenge, fold_stride, next_layer_size, eq_values, contributions, acc_size, gid);
}

template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void flat_round2_compute_constant(const flat_round2_static_desc<bf, E> &desc, const E &first_folding_challenge,
                                                     const E &second_folding_challenge, const unsigned fold_stride, const unsigned next_layer_size,
                                                     const E *__restrict__ eq_values, E *__restrict__ contributions, const unsigned acc_size,
                                                     const unsigned gid) {
  coeff_loader_continuation_constant loader{};
  flat_round2_compute_impl<E, EXPLICIT_FORM>(desc, loader, first_folding_challenge, second_folding_challenge, fold_stride, next_layer_size, eq_values,
                                             contributions, acc_size, gid);
}

// ===========================================================================
// Warp-split variants: multiple warps share gids, interleave terms.
// Reduces per-source L1 footprint by ~4x compared to the default kernels.
// ===========================================================================

// Indexed __constant__ coefficient loader: reads by explicit index (not idx++).
struct coeff_loader_constant_indexed {
  DEVICE_FORCEINLINE e4 operator()(unsigned idx) const { return ::ab_gkr_flat_continuation_coefficients[idx]; }
};

// Round 1 warp-split compute: each warp processes every NUM_WARPS-th term.
// Accumulates partial c0/c1 (caller reduces across warps).
template <typename E, bool EXPLICIT_FORM, unsigned NUM_WARPS>
DEVICE_FORCEINLINE void flat_round1_compute_warp_split(const flat_round1_static_desc<bf, E> &desc, const E &folding_challenge, const unsigned fold_stride,
                                                       const unsigned next_layer_size, const unsigned gid, const unsigned warp_id, E &c0, E &c1) {
  unsigned coeff_base = 0;
  coeff_loader_constant_indexed coeff{};

  for (unsigned i = warp_id; i < desc.num_constants; i += NUM_WARPS) {
    const E k = coeff(coeff_base + i);
    c0 = E::add(c0, k);
    if constexpr (EXPLICIT_FORM)
      c1 = E::add(c1, k);
  }
  coeff_base += desc.num_constants;

  for (unsigned i = warp_id; i < desc.num_c0_only_linear; i += NUM_WARPS) {
    E f0, f1;
    flat_round1_load_pair<E, EXPLICIT_FORM>(desc, desc.c0_only_linear[i].source_idx, folding_challenge, fold_stride, next_layer_size, gid, f0, f1);
    const E k = coeff(coeff_base + i);
    c0 = E::add(c0, E::mul(k, f0));
    if constexpr (EXPLICIT_FORM)
      c1 = E::add(c1, E::mul(k, f1));
  }
  coeff_base += desc.num_c0_only_linear;

  for (unsigned i = warp_id; i < desc.num_unified_quadratic; i += NUM_WARPS) {
    const auto &t = desc.unified_quadratic[i];
    E a0, a1;
    flat_round1_load_pair<E, EXPLICIT_FORM>(desc, t.source_a, folding_challenge, fold_stride, next_layer_size, gid, a0, a1);
    E b0, b1;
    flat_round1_load_pair<E, EXPLICIT_FORM>(desc, t.source_b, folding_challenge, fold_stride, next_layer_size, gid, b0, b1);
    const E k = coeff(coeff_base + i);
    c0 = E::add(c0, E::mul(k, E::mul(a0, b0)));
    c1 = E::add(c1, E::mul(k, E::mul(a1, b1)));
  }
  coeff_base += desc.num_unified_quadratic;

  for (unsigned i = warp_id; i < desc.num_unified_linear; i += NUM_WARPS) {
    E f0, f1;
    flat_round1_load_pair<E, EXPLICIT_FORM>(desc, desc.unified_linear[i].source_idx, folding_challenge, fold_stride, next_layer_size, gid, f0, f1);
    const E k = coeff(coeff_base + i);
    c0 = E::add(c0, E::mul(k, f0));
    c1 = E::add(c1, E::mul(k, f1));
  }
}

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
      c0 = E::add(c0, E::mul(k, f0));
      if constexpr (EXPLICIT_FORM)
        c1 = E::add(c1, E::mul(k, f1));
      break;
    }
    case TERM_TYPE_UNIFIED_QUADRATIC: {
      E a0, a1;
      flat_round1_load_pair_cached<E, EXPLICIT_FORM>(desc, t.source_a, next_layer_size, gid, a0, a1);
      E b0, b1;
      flat_round1_load_pair_cached<E, EXPLICIT_FORM>(desc, t.source_b, next_layer_size, gid, b0, b1);
      c0 = E::add(c0, E::mul(k, E::mul(a0, b0)));
      c1 = E::add(c1, E::mul(k, E::mul(a1, b1)));
      break;
    }
    case TERM_TYPE_UNIFIED_LINEAR: {
      E f0, f1;
      flat_round1_load_pair_cached<E, EXPLICIT_FORM>(desc, t.source_a, next_layer_size, gid, f0, f1);
      c0 = E::add(c0, E::mul(k, f0));
      c1 = E::add(c1, E::mul(k, f1));
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
      c0 = E::add(c0, E::mul(k, f0));
      if constexpr (EXPLICIT_FORM)
        c1 = E::add(c1, E::mul(k, f1));
      break;
    }
    case TERM_TYPE_UNIFIED_QUADRATIC: {
      E a0, a1;
      flat_cont_load_pair_cached<E, EXPLICIT_FORM>(desc, t.source_a, next_layer_size, gid, a0, a1);
      E b0, b1;
      flat_cont_load_pair_cached<E, EXPLICIT_FORM>(desc, t.source_b, next_layer_size, gid, b0, b1);
      c0 = E::add(c0, E::mul(k, E::mul(a0, b0)));
      c1 = E::add(c1, E::mul(k, E::mul(a1, b1)));
      break;
    }
    case TERM_TYPE_UNIFIED_LINEAR: {
      E f0, f1;
      flat_cont_load_pair_cached<E, EXPLICIT_FORM>(desc, t.source_a, next_layer_size, gid, f0, f1);
      c0 = E::add(c0, E::mul(k, f0));
      c1 = E::add(c1, E::mul(k, f1));
      break;
    }
    }
  }
}

// ===========================================================================
// Unified tiled helpers for round 2: base_after_two + ext sources.
// ===========================================================================

// Per-tile fold for round 2: dispatches on source type bit.
// Base sources use two-fold, ext sources fold with second challenge only.
template <typename E, unsigned NUM_WARPS>
DEVICE_FORCEINLINE void flat_round2_tile_fold(const flat_round2_unified_desc<bf, E> &desc, const unsigned fold_start, const unsigned fold_end,
                                              const E &first_challenge, const E &second_challenge, const unsigned fold_stride, const unsigned next_layer_size,
                                              const unsigned gid, const unsigned warp_id) {
  if (fold_start == fold_end)
    return;
  for (unsigned s = fold_start + warp_id; s < fold_end; s += NUM_WARPS) {
    const u16 src_idx = desc.fold_sources[s];
    if (src_idx & FLAT_CONT_EXT_SOURCE_BIT) {
      const auto &entry = desc.ext_sources[src_idx & ~FLAT_CONT_EXT_SOURCE_BIT];
      flat_cont_fold_and_load(entry, second_challenge, fold_stride, gid);
      flat_cont_fold_and_load(entry, second_challenge, fold_stride, next_layer_size + gid);
    } else {
      const auto &source = desc.base_sources[src_idx];
      gkr_get_base_after_two_value(source, first_challenge, second_challenge, gid);
      gkr_get_base_after_two_value(source, first_challenge, second_challenge, next_layer_size + gid);
    }
  }
  __syncthreads();
}

// Load pair from cache only for round 2 unified desc.
template <typename E, bool EXPLICIT_FORM>
DEVICE_FORCEINLINE void flat_round2_load_pair_cached(const flat_round2_unified_desc<bf, E> &desc, const u16 source_idx, const unsigned next_layer_size,
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

// Process a range of unified terms from cache for round 2. Warp-split with interleaving.
template <typename E, bool EXPLICIT_FORM, unsigned NUM_WARPS>
DEVICE_FORCEINLINE void flat_round2_compute_unified(const flat_round2_unified_desc<bf, E> &desc, const unsigned term_start, const unsigned term_end,
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
      flat_round2_load_pair_cached<E, EXPLICIT_FORM>(desc, t.source_a, next_layer_size, gid, f0, f1);
      c0 = E::add(c0, E::mul(k, f0));
      if constexpr (EXPLICIT_FORM)
        c1 = E::add(c1, E::mul(k, f1));
      break;
    }
    case TERM_TYPE_UNIFIED_QUADRATIC: {
      E a0, a1;
      flat_round2_load_pair_cached<E, EXPLICIT_FORM>(desc, t.source_a, next_layer_size, gid, a0, a1);
      E b0, b1;
      flat_round2_load_pair_cached<E, EXPLICIT_FORM>(desc, t.source_b, next_layer_size, gid, b0, b1);
      c0 = E::add(c0, E::mul(k, E::mul(a0, b0)));
      c1 = E::add(c1, E::mul(k, E::mul(a1, b1)));
      break;
    }
    case TERM_TYPE_UNIFIED_LINEAR: {
      E f0, f1;
      flat_round2_load_pair_cached<E, EXPLICIT_FORM>(desc, t.source_a, next_layer_size, gid, f0, f1);
      c0 = E::add(c0, E::mul(k, f0));
      c1 = E::add(c1, E::mul(k, f1));
      break;
    }
    }
  }
}

} // namespace airbender::prover::gkr
