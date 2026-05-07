#pragma once

#include "common.cuh"

EXTERN __device__ __constant__ e4 ab_gkr_lookup_gamma_consts[3];

// Flat forward layer kernel.
//
// Instead of a switch on gate kind, this compiles every gate in the layer
// into per-category flat arrays. Each category has its own tight loop in the
// kernel body, avoiding branch-heavy code and allowing the compiler to emit
// dense, predictable instruction streams.
//
// Sources are encoded as raw pointers in a single table:
//   * real device pointers (always >= 8-byte aligned, so bit 0..2 are zero);
//   * virtual base sources (range checks, inits/teardowns) use a null pointer
//     with the `gkr_base_source_kind` packed into bits 0..2.
//
// Output pointers live inline on each category entry: every gate produces its
// output(s) exactly once, so there is no need for an output indirection table.
//
// Only the "direct-source" gate variants are supported. Mapping-based gates
// (LOOKUP_*_FROM_VECTOR_INPUTS, LOOKUP_PAIR_FROM_BASE_INPUTS,
// LOOKUP_WITH_DENS_AND_SETUP_EXPRESSIONS, etc.) only appear in uncached GKR
// layouts (`*_no_caches_gkr.json`); gpu_prover exclusively consumes cached
// layouts, where mapping-based relations are pre-materialized upstream into
// the direct-source categories below.

namespace airbender::prover::gkr {

DEVICE_FORCEINLINE e4 lookup_gamma() { return ::ab_gkr_lookup_gamma_consts[0]; }

DEVICE_FORCEINLINE e4 lookup_gamma_sq() { return ::ab_gkr_lookup_gamma_consts[1]; }

DEVICE_FORCEINLINE e4 lookup_two_gamma() { return ::ab_gkr_lookup_gamma_consts[2]; }

// ---------------------------------------------------------------------------
// Sizing
// ---------------------------------------------------------------------------

// Max number of distinct source pointers referenced by any single layer.
// Observed layers emit <= 63 gates; each gate touches at most 4 sources, so
// 256 is a conservative cap (keeps the descriptor under the 32764-byte
// `__grid_constant__` limit).
constexpr unsigned FLAT_FWD_MAX_SOURCES = 256;

// Max gates per descriptor in any single category. Rust chunks layers across
// multiple descriptors when a category reaches this cap, keeping the
// grid-constant argument comfortably under the 32764-byte limit even with the
// direct no-cache categories below.
constexpr unsigned FLAT_FWD_MAX_PER_CATEGORY = 16;

// ---------------------------------------------------------------------------
// Per-category entries
// ---------------------------------------------------------------------------

// PRODUCT: ext * ext -> ext.
template <typename E> struct flat_fwd_product_entry {
  u16 src_a;
  u16 src_b;
  E *dst;
};

// MASK_IDENTITY: bf mask, ext input -> ext.
template <typename E> struct flat_fwd_mask_entry {
  u16 src_mask;
  u16 src_input;
  E *dst;
};

// LOOKUP_PAIR: 4 ext sources -> (num, den).
template <typename E> struct flat_fwd_lookup4_entry {
  u16 src_a;
  u16 src_b;
  u16 src_c;
  u16 src_d;
  E *num;
  E *den;
};

// LOOKUP_BASE_PAIR: bf b, bf d -> (num, den) with gamma.
template <typename E> struct flat_fwd_bf_pair_entry {
  u16 src_b;
  u16 src_d;
  E *num;
  E *den;
};

// LOOKUP_EXT_PAIR: ext b, ext d -> (num, den) with gamma.
template <typename E> struct flat_fwd_e4_pair_entry {
  u16 src_b;
  u16 src_d;
  E *num;
  E *den;
};

// LOOKUP_WITH_CACHED_DENS_AND_SETUP: bf a, ext b, bf c, ext d -> (num, den).
template <typename E> struct flat_fwd_cached_dens_entry {
  u16 src_a;
  u16 src_b;
  u16 src_c;
  u16 src_d;
  E *num;
  E *den;
};

// LOOKUP_BASE_MINUS_MULTIPLICITY_BY_BASE: bf b, bf c, bf d -> (num, den).
// d may be a virtual source (range check / inits+teardowns); the kind is
// encoded in the low bits of the source pointer.
template <typename E> struct flat_fwd_bf_minus_mult_entry {
  u16 src_b;
  u16 src_c;
  u16 src_d;
  u16 _pad;
  E *num;
  E *den;
};

// LOOKUP_EXT_MINUS_MULTIPLICITY_BY_EXT: ext b, bf c, ext d -> (num, den).
template <typename E> struct flat_fwd_e4_minus_mult_entry {
  u16 src_b;
  u16 src_c;
  u16 src_d;
  u16 _pad;
  E *num;
  E *den;
};

// LOOKUP_UNBALANCED_BASE: ext a, ext b, bf d(remainder) -> (num, den).
template <typename E> struct flat_fwd_bf_unbalanced_entry {
  u16 src_a;
  u16 src_b;
  u16 src_d;
  u16 _pad;
  E *num;
  E *den;
};

// LOOKUP_UNBALANCED_EXTENSION: ext a, ext b, ext d(remainder) -> (num, den).
template <typename E> struct flat_fwd_e4_unbalanced_entry {
  u16 src_a;
  u16 src_b;
  u16 src_d;
  u16 _pad;
  E *num;
  E *den;
};

// Direct no-cache lookup categories consume Stage-1 mapping arrays directly.
template <typename E> struct flat_fwd_mapped_bf_pair_entry {
  const u32 *mapping_b;
  const u32 *mapping_d;
  E *num;
  E *den;
};

template <typename E> struct flat_fwd_mapped_e4_pair_entry {
  const u32 *mapping_b;
  const u32 *mapping_d;
  const E *generic_lookup;
  E *num;
  E *den;
};

template <typename E> struct flat_fwd_mapped_cached_dens_entry {
  const u32 *mapping_b;
  const E *generic_lookup;
  const bf *decoder_mask;
  const E *decoder_fill_value;
  u16 src_a;
  u16 src_c;
  u32 generic_lookup_len;
  u32 _pad;
  E *num;
  E *den;
};

template <typename E> struct flat_fwd_mapped_e4_minus_mult_entry {
  const u32 *mapping_b;
  const E *generic_lookup;
  u16 src_c;
  u16 _pad;
  u32 generic_lookup_len;
  E *num;
  E *den;
};

template <typename E> struct flat_fwd_mapped_e4_unbalanced_entry {
  u16 src_a;
  u16 src_b;
  u32 _pad;
  const u32 *mapping_d;
  const E *generic_lookup;
  E *num;
  E *den;
};

template <typename E> struct flat_fwd_memory_expr {
  gkr_forward_cache_address_space_kind address_space_kind;
  const bf *address_space_ptr;
  bf address_space_constant;
  E constant_term;
  const bf *linear_inputs[GKR_FORWARD_CACHE_MEMORY_LINEAR_TERMS];
  E linear_challenges[GKR_FORWARD_CACHE_MEMORY_LINEAR_TERMS];
};

template <typename E> struct flat_fwd_memory_product_entry {
  flat_fwd_memory_expr<E> lhs;
  flat_fwd_memory_expr<E> rhs;
  E *dst;
};

template <typename E> struct flat_fwd_memory_materialize_entry {
  flat_fwd_memory_expr<E> expr;
  E *dst;
};

// ---------------------------------------------------------------------------
// Static description
// ---------------------------------------------------------------------------

// Passed as `__grid_constant__`. Total size is well under the 32KB limit.
template <typename E> struct flat_forward_static_desc {
  const void *sources[FLAT_FWD_MAX_SOURCES];
  u32 num_sources;

  flat_fwd_product_entry<E> products[FLAT_FWD_MAX_PER_CATEGORY];
  u32 num_products;

  flat_fwd_mask_entry<E> masks[FLAT_FWD_MAX_PER_CATEGORY];
  u32 num_masks;

  flat_fwd_lookup4_entry<E> lookup4s[FLAT_FWD_MAX_PER_CATEGORY];
  u32 num_lookup4s;

  flat_fwd_bf_pair_entry<E> bf_pairs[FLAT_FWD_MAX_PER_CATEGORY];
  u32 num_bf_pairs;

  flat_fwd_e4_pair_entry<E> e4_pairs[FLAT_FWD_MAX_PER_CATEGORY];
  u32 num_e4_pairs;

  flat_fwd_cached_dens_entry<E> cached_denses[FLAT_FWD_MAX_PER_CATEGORY];
  u32 num_cached_denses;

  flat_fwd_bf_minus_mult_entry<E> bf_minus_mults[FLAT_FWD_MAX_PER_CATEGORY];
  u32 num_bf_minus_mults;

  flat_fwd_e4_minus_mult_entry<E> e4_minus_mults[FLAT_FWD_MAX_PER_CATEGORY];
  u32 num_e4_minus_mults;

  flat_fwd_bf_unbalanced_entry<E> bf_unbalanceds[FLAT_FWD_MAX_PER_CATEGORY];
  u32 num_bf_unbalanceds;

  flat_fwd_e4_unbalanced_entry<E> e4_unbalanceds[FLAT_FWD_MAX_PER_CATEGORY];
  u32 num_e4_unbalanceds;

  flat_fwd_mapped_bf_pair_entry<E> mapped_bf_pairs[FLAT_FWD_MAX_PER_CATEGORY];
  u32 num_mapped_bf_pairs;

  flat_fwd_mapped_e4_pair_entry<E> mapped_e4_pairs[FLAT_FWD_MAX_PER_CATEGORY];
  u32 num_mapped_e4_pairs;

  flat_fwd_mapped_cached_dens_entry<E> mapped_cached_denses[FLAT_FWD_MAX_PER_CATEGORY];
  u32 num_mapped_cached_denses;

  flat_fwd_mapped_e4_minus_mult_entry<E> mapped_e4_minus_mults[FLAT_FWD_MAX_PER_CATEGORY];
  u32 num_mapped_e4_minus_mults;

  flat_fwd_mapped_e4_unbalanced_entry<E> mapped_e4_unbalanceds[FLAT_FWD_MAX_PER_CATEGORY];
  u32 num_mapped_e4_unbalanceds;

  flat_fwd_memory_product_entry<E> memory_products[FLAT_FWD_MAX_PER_CATEGORY];
  u32 num_memory_products;

  flat_fwd_memory_materialize_entry<E> memory_materializes[FLAT_FWD_MAX_PER_CATEGORY];
  u32 num_memory_materializes;
};

// ---------------------------------------------------------------------------
// Source load helpers
// ---------------------------------------------------------------------------

// `ca` (cache-all) hint: sources are reused across gates, so L1 caching pays
// off here. Virtual base sources are materialized on the fly.
DEVICE_FORCEINLINE bf flat_fwd_load_bf(const void *src, const unsigned gid) {
  const uintptr_t p = reinterpret_cast<uintptr_t>(src);
  if (p >= 8)
    return load<bf, ld_modifier::ca>(reinterpret_cast<const bf *>(src), gid);
  return gkr_virtual_base_value(static_cast<gkr_base_source_kind>(p), gid);
}

template <typename E> DEVICE_FORCEINLINE E flat_fwd_load_ext(const void *src, const unsigned gid) {
  return load<E, ld_modifier::ca>(reinterpret_cast<const E *>(src), gid);
}

template <typename E> DEVICE_FORCEINLINE E flat_fwd_load_generic_lookup(const E *generic_lookup, const u32 mapping) {
  return load<E, ld_modifier::ca>(generic_lookup, mapping);
}

template <typename E> DEVICE_FORCEINLINE E flat_fwd_load_generic_lookup_setup(const E *generic_lookup, const u32 generic_lookup_len, const unsigned gid) {
  return gid < generic_lookup_len ? load<E, ld_modifier::ca>(generic_lookup, gid) : E::ZERO();
}

template <typename E> DEVICE_FORCEINLINE E flat_fwd_load_mapped_lookup(const u32 *mapping, const E *generic_lookup, const unsigned gid) {
  return flat_fwd_load_generic_lookup(generic_lookup, load<u32, ld_modifier::ca>(mapping, gid));
}

template <typename E> DEVICE_FORCEINLINE E flat_fwd_load_decoder_mapped_lookup(const flat_fwd_mapped_cached_dens_entry<E> &t, const unsigned gid) {
  E value = flat_fwd_load_mapped_lookup(t.mapping_b, t.generic_lookup, gid);
  if (t.decoder_mask != nullptr) {
    const bf enabled = load<bf, ld_modifier::ca>(t.decoder_mask, gid);
    if (enabled.limb == 0)
      value = load<E, ld_modifier::ca>(t.decoder_fill_value, 0);
  }
  return value;
}

template <typename E> DEVICE_FORCEINLINE E flat_fwd_eval_memory_expr(const flat_fwd_memory_expr<E> &expr, const unsigned gid) {
  E value = expr.constant_term;
  switch (expr.address_space_kind) {
  case GKR_FORWARD_CACHE_ADDRESS_SPACE_CONSTANT:
    value = E::add(value, expr.address_space_constant);
    break;
  case GKR_FORWARD_CACHE_ADDRESS_SPACE_IS:
    value = E::add(value, load<bf, ld_modifier::ca>(expr.address_space_ptr, gid));
    break;
  case GKR_FORWARD_CACHE_ADDRESS_SPACE_NOT:
    value = E::add(value, E::sub(E::ONE(), load<bf, ld_modifier::ca>(expr.address_space_ptr, gid)));
    break;
  case GKR_FORWARD_CACHE_ADDRESS_SPACE_EMPTY:
    break;
  }

#pragma unroll
  for (unsigned term = 0; term < GKR_FORWARD_CACHE_MEMORY_LINEAR_TERMS; ++term) {
    if (expr.linear_inputs[term] == nullptr)
      continue;
    const bf input = load<bf, ld_modifier::ca>(expr.linear_inputs[term], gid);
    value = E::fma(expr.linear_challenges[term], input, value);
  }
  return value;
}

// ---------------------------------------------------------------------------
// Kernel body
// ---------------------------------------------------------------------------

template <typename E> DEVICE_FORCEINLINE void flat_forward_compute(const flat_forward_static_desc<E> &desc, const unsigned gid) {
  // PRODUCT: ext * ext -> ext.
  for (unsigned i = 0; i < desc.num_products; i++) {
    const auto &t = desc.products[i];
    const E a = flat_fwd_load_ext<E>(desc.sources[t.src_a], gid);
    const E b = flat_fwd_load_ext<E>(desc.sources[t.src_b], gid);
    E value;
    gkr_eval_product(a, b, value);
    store<E, st_modifier::cs>(t.dst, value, gid);
  }

  // MASK_IDENTITY: bf mask, ext input -> ext.
  for (unsigned i = 0; i < desc.num_masks; i++) {
    const auto &t = desc.masks[i];
    const bf mask = flat_fwd_load_bf(desc.sources[t.src_mask], gid);
    const E input = flat_fwd_load_ext<E>(desc.sources[t.src_input], gid);
    E value;
    gkr_eval_mask_identity(mask, input, value);
    store<E, st_modifier::cs>(t.dst, value, gid);
  }

  // LOOKUP_PAIR: 4 ext sources -> (num, den). No gamma.
  for (unsigned i = 0; i < desc.num_lookup4s; i++) {
    const auto &t = desc.lookup4s[i];
    const E a = flat_fwd_load_ext<E>(desc.sources[t.src_a], gid);
    const E b = flat_fwd_load_ext<E>(desc.sources[t.src_b], gid);
    const E c = flat_fwd_load_ext<E>(desc.sources[t.src_c], gid);
    const E d = flat_fwd_load_ext<E>(desc.sources[t.src_d], gid);
    E num, den;
    gkr_eval_lookup_pair(a, b, c, d, num, den);
    store<E, st_modifier::cs>(t.num, num, gid);
    store<E, st_modifier::cs>(t.den, den, gid);
  }

  // Gamma is used by every remaining category. All threads branch the same
  // way on grid-constant counts, so this compiles to a uniform predicate.
  const bool has_lookup_with_gamma = desc.num_bf_pairs || desc.num_e4_pairs || desc.num_cached_denses || desc.num_bf_minus_mults || desc.num_e4_minus_mults ||
                                     desc.num_bf_unbalanceds || desc.num_e4_unbalanceds || desc.num_mapped_bf_pairs || desc.num_mapped_e4_pairs ||
                                     desc.num_mapped_cached_denses || desc.num_mapped_e4_minus_mults || desc.num_mapped_e4_unbalanceds;
  E gamma = E::ZERO();
  E gamma_sq = E::ZERO();
  E two_gamma = E::ZERO();
  if (has_lookup_with_gamma) {
    gamma = lookup_gamma();
    gamma_sq = lookup_gamma_sq();
    two_gamma = lookup_two_gamma();
  }

  // LOOKUP_BASE_PAIR: bf b, bf d -> (num, den).
  for (unsigned i = 0; i < desc.num_bf_pairs; i++) {
    const auto &t = desc.bf_pairs[i];
    const bf b = flat_fwd_load_bf(desc.sources[t.src_b], gid);
    const bf d = flat_fwd_load_bf(desc.sources[t.src_d], gid);
    E num, den;
    gkr_eval_lookup_base_pair_v2(b, d, gamma, gamma_sq, two_gamma, num, den);
    store<E, st_modifier::cs>(t.num, num, gid);
    store<E, st_modifier::cs>(t.den, den, gid);
  }

  // LOOKUP_EXT_PAIR: ext b, ext d -> (num, den).
  for (unsigned i = 0; i < desc.num_e4_pairs; i++) {
    const auto &t = desc.e4_pairs[i];
    const E b = flat_fwd_load_ext<E>(desc.sources[t.src_b], gid);
    const E d = flat_fwd_load_ext<E>(desc.sources[t.src_d], gid);
    E num, den;
    gkr_eval_lookup_ext_pair(b, d, gamma, num, den);
    store<E, st_modifier::cs>(t.num, num, gid);
    store<E, st_modifier::cs>(t.den, den, gid);
  }

  // LOOKUP_WITH_CACHED_DENS_AND_SETUP: bf a, ext b, bf c, ext d.
  for (unsigned i = 0; i < desc.num_cached_denses; i++) {
    const auto &t = desc.cached_denses[i];
    const bf a = flat_fwd_load_bf(desc.sources[t.src_a], gid);
    const E b = flat_fwd_load_ext<E>(desc.sources[t.src_b], gid);
    const bf c = flat_fwd_load_bf(desc.sources[t.src_c], gid);
    const E d = flat_fwd_load_ext<E>(desc.sources[t.src_d], gid);
    E num, den;
    gkr_eval_lookup_cached_dens_and_setup(a, b, c, d, gamma, num, den);
    store<E, st_modifier::cs>(t.num, num, gid);
    store<E, st_modifier::cs>(t.den, den, gid);
  }

  // LOOKUP_BASE_MINUS_MULTIPLICITY_BY_BASE: bf b, bf c, bf d (d may be virtual).
  for (unsigned i = 0; i < desc.num_bf_minus_mults; i++) {
    const auto &t = desc.bf_minus_mults[i];
    const bf b = flat_fwd_load_bf(desc.sources[t.src_b], gid);
    const bf c = flat_fwd_load_bf(desc.sources[t.src_c], gid);
    const bf d = flat_fwd_load_bf(desc.sources[t.src_d], gid);
    E num, den;
    gkr_eval_lookup_base_minus_multiplicity_v2(b, c, d, gamma, gamma_sq, num, den);
    store<E, st_modifier::cs>(t.num, num, gid);
    store<E, st_modifier::cs>(t.den, den, gid);
  }

  // LOOKUP_EXT_MINUS_MULTIPLICITY_BY_EXT: ext b, bf c, ext d.
  for (unsigned i = 0; i < desc.num_e4_minus_mults; i++) {
    const auto &t = desc.e4_minus_mults[i];
    const E b = flat_fwd_load_ext<E>(desc.sources[t.src_b], gid);
    const bf c = flat_fwd_load_bf(desc.sources[t.src_c], gid);
    const E d = flat_fwd_load_ext<E>(desc.sources[t.src_d], gid);
    E num, den;
    gkr_eval_lookup_base_minus_multiplicity(b, c, d, gamma, num, den);
    store<E, st_modifier::cs>(t.num, num, gid);
    store<E, st_modifier::cs>(t.den, den, gid);
  }

  // LOOKUP_UNBALANCED_BASE: ext a, ext b, bf remainder(d).
  for (unsigned i = 0; i < desc.num_bf_unbalanceds; i++) {
    const auto &t = desc.bf_unbalanceds[i];
    const E a = flat_fwd_load_ext<E>(desc.sources[t.src_a], gid);
    const E b = flat_fwd_load_ext<E>(desc.sources[t.src_b], gid);
    const bf d = flat_fwd_load_bf(desc.sources[t.src_d], gid);
    E num, den;
    gkr_eval_lookup_unbalanced(d, a, b, gamma, num, den);
    store<E, st_modifier::cs>(t.num, num, gid);
    store<E, st_modifier::cs>(t.den, den, gid);
  }

  // LOOKUP_UNBALANCED_EXTENSION: ext a, ext b, ext remainder(d).
  for (unsigned i = 0; i < desc.num_e4_unbalanceds; i++) {
    const auto &t = desc.e4_unbalanceds[i];
    const E a = flat_fwd_load_ext<E>(desc.sources[t.src_a], gid);
    const E b = flat_fwd_load_ext<E>(desc.sources[t.src_b], gid);
    const E d = flat_fwd_load_ext<E>(desc.sources[t.src_d], gid);
    E num, den;
    gkr_eval_lookup_unbalanced(d, a, b, gamma, num, den);
    store<E, st_modifier::cs>(t.num, num, gid);
    store<E, st_modifier::cs>(t.den, den, gid);
  }

  // Direct no-cache LOOKUP_PAIR_FROM_BASE_INPUTS: mapping indices are the base values.
  for (unsigned i = 0; i < desc.num_mapped_bf_pairs; i++) {
    const auto &t = desc.mapped_bf_pairs[i];
    const bf b = bf::from_u32_unchecked(load<u32, ld_modifier::ca>(t.mapping_b, gid));
    const bf d = bf::from_u32_unchecked(load<u32, ld_modifier::ca>(t.mapping_d, gid));
    E num, den;
    gkr_eval_lookup_base_pair_v2(b, d, gamma, gamma_sq, two_gamma, num, den);
    store<E, st_modifier::cs>(t.num, num, gid);
    store<E, st_modifier::cs>(t.den, den, gid);
  }

  // Direct no-cache LOOKUP_PAIR_FROM_VECTOR_INPUTS.
  for (unsigned i = 0; i < desc.num_mapped_e4_pairs; i++) {
    const auto &t = desc.mapped_e4_pairs[i];
    const E b = flat_fwd_load_mapped_lookup(t.mapping_b, t.generic_lookup, gid);
    const E d = flat_fwd_load_mapped_lookup(t.mapping_d, t.generic_lookup, gid);
    E num, den;
    gkr_eval_lookup_ext_pair(b, d, gamma, num, den);
    store<E, st_modifier::cs>(t.num, num, gid);
    store<E, st_modifier::cs>(t.den, den, gid);
  }

  // Direct no-cache LOOKUP_WITH_DENS_AND_SETUP_EXPRESSIONS.
  for (unsigned i = 0; i < desc.num_mapped_cached_denses; i++) {
    const auto &t = desc.mapped_cached_denses[i];
    const bf a = flat_fwd_load_bf(desc.sources[t.src_a], gid);
    const E b = flat_fwd_load_decoder_mapped_lookup(t, gid);
    const bf c = flat_fwd_load_bf(desc.sources[t.src_c], gid);
    const E d = flat_fwd_load_generic_lookup_setup(t.generic_lookup, t.generic_lookup_len, gid);
    E num, den;
    gkr_eval_lookup_cached_dens_and_setup(a, b, c, d, gamma, num, den);
    store<E, st_modifier::cs>(t.num, num, gid);
    store<E, st_modifier::cs>(t.den, den, gid);
  }

  // Direct no-cache LOOKUP_FROM_VECTOR_INPUT_WITH_SETUP.
  for (unsigned i = 0; i < desc.num_mapped_e4_minus_mults; i++) {
    const auto &t = desc.mapped_e4_minus_mults[i];
    const E b = flat_fwd_load_mapped_lookup(t.mapping_b, t.generic_lookup, gid);
    const bf c = flat_fwd_load_bf(desc.sources[t.src_c], gid);
    const E d = flat_fwd_load_generic_lookup_setup(t.generic_lookup, t.generic_lookup_len, gid);
    E num, den;
    gkr_eval_lookup_base_minus_multiplicity(b, c, d, gamma, num, den);
    store<E, st_modifier::cs>(t.num, num, gid);
    store<E, st_modifier::cs>(t.den, den, gid);
  }

  // Direct no-cache LOOKUP_UNBALANCED_PAIR_WITH_VECTOR_INPUTS.
  for (unsigned i = 0; i < desc.num_mapped_e4_unbalanceds; i++) {
    const auto &t = desc.mapped_e4_unbalanceds[i];
    const E a = flat_fwd_load_ext<E>(desc.sources[t.src_a], gid);
    const E b = flat_fwd_load_ext<E>(desc.sources[t.src_b], gid);
    const E d = flat_fwd_load_mapped_lookup(t.mapping_d, t.generic_lookup, gid);
    E num, den;
    gkr_eval_lookup_unbalanced(d, a, b, gamma, num, den);
    store<E, st_modifier::cs>(t.num, num, gid);
    store<E, st_modifier::cs>(t.den, den, gid);
  }

  // Direct no-cache INITIAL_GRAND_PRODUCT_WITHOUT_CACHES.
  for (unsigned i = 0; i < desc.num_memory_products; i++) {
    const auto &t = desc.memory_products[i];
    const E lhs = flat_fwd_eval_memory_expr(t.lhs, gid);
    const E rhs = flat_fwd_eval_memory_expr(t.rhs, gid);
    E value;
    gkr_eval_product(lhs, rhs, value);
    store<E, st_modifier::cs>(t.dst, value, gid);
  }

  // Direct no-cache MATERIALIZE_GRAND_PRODUCT_TERM_EXPRESSION.
  for (unsigned i = 0; i < desc.num_memory_materializes; i++) {
    const auto &t = desc.memory_materializes[i];
    store<E, st_modifier::cs>(t.dst, flat_fwd_eval_memory_expr(t.expr, gid), gid);
  }
}

} // namespace airbender::prover::gkr
