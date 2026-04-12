#pragma once

#include "common.cuh"

namespace airbender::prover::gkr {

// Maximum array sizes for the flat round 0 static description.
// The entire struct is passed as __grid_constant__.
constexpr unsigned FLAT_ROUND0_CONST_MAX = 512; // 8KB — fits all non-delegation L1 and all L2+

constexpr unsigned FLAT_ROUND0_MAX_SOURCES = 1280;
constexpr unsigned FLAT_ROUND0_MAX_C0_BF = 128;
constexpr unsigned FLAT_ROUND0_MAX_C0_EXT = 512;
constexpr unsigned FLAT_ROUND0_MAX_C1_BF_BF = 4096;
constexpr unsigned FLAT_ROUND0_MAX_C1_E4_E4 = 512;
constexpr unsigned FLAT_ROUND0_MAX_C1_BF_E4 = 512;
constexpr unsigned FLAT_ROUND0_MAX_C1_LINEAR = 128;

// Term structure references (no coefficients — those live in a separate device buffer).
// u16 indices: supports up to 65535 sources per layer.
struct flat_c0_ref {
  u16 source_idx;
};

struct flat_c1_pair {
  u16 source_a;
  u16 source_b;
};

// Static description for GKR backward round 0.
// Sources are encoded as raw pointers. Virtual sources (range checks, etc.)
// use the low 3 bits of a null pointer to encode the gkr_base_source_kind.
// Real device pointers are always >= 256-byte aligned, so no collision.
struct flat_round0_static_desc {
  const void *sources[FLAT_ROUND0_MAX_SOURCES];
  u32 num_sources;

  flat_c0_ref c0_bf[FLAT_ROUND0_MAX_C0_BF];
  u32 num_c0_bf;
  flat_c0_ref c0_ext[FLAT_ROUND0_MAX_C0_EXT];
  u32 num_c0_ext;

  flat_c1_pair c1_bf_bf[FLAT_ROUND0_MAX_C1_BF_BF];
  u32 num_c1_bf_bf;
  flat_c1_pair c1_e4_e4[FLAT_ROUND0_MAX_C1_E4_E4];
  u32 num_c1_e4_e4;
  flat_c1_pair c1_bf_e4[FLAT_ROUND0_MAX_C1_BF_E4];
  u32 num_c1_bf_e4;

  flat_c0_ref c1_linear[FLAT_ROUND0_MAX_C1_LINEAR];
  u32 num_c1_linear;
};

// --- Load helpers ---

// Source loads use ca (cache in L1 and L2) — sources are reused across terms
// and L1 caching provides significant hit rate (~40%) from this reuse.
DEVICE_FORCEINLINE bf flat_load_bf_value(const void *src, const unsigned gid) {
  const uintptr_t p = reinterpret_cast<uintptr_t>(src);
  if (p >= 8)
    return load<bf, ld_modifier::ca>(reinterpret_cast<const bf *>(src), gid);
  return gkr_virtual_base_value(static_cast<gkr_base_source_kind>(p), gid);
}

DEVICE_FORCEINLINE bf flat_load_bf_delta(const void *src, const unsigned gid, const unsigned acc_size) {
  return bf::sub(flat_load_bf_value(src, gid + acc_size), flat_load_bf_value(src, gid));
}

template <typename E> DEVICE_FORCEINLINE E flat_load_ext_value(const void *src, const unsigned gid) {
  return load<E, ld_modifier::ca>(reinterpret_cast<const E *>(src), gid);
}

template <typename E> DEVICE_FORCEINLINE E flat_load_ext_delta(const void *src, const unsigned gid, const unsigned acc_size) {
  const E f0 = flat_load_ext_value<E>(src, gid);
  const E f1 = flat_load_ext_value<E>(src, gid + acc_size);
  return E::sub(f1, f0);
}

// --- Flat round 0 kernel ---

// Coefficient load helper: ca (cache in L1) — small buffer, all threads read
// the same coeff[i] per iteration (broadcast), sequential access.
template <typename E> DEVICE_FORCEINLINE E flat_load_coeff(const E *&coeff) {
  const E val = load<E, ld_modifier::ca>(coeff, 0);
  ++coeff;
  return val;
}

template <typename E>
DEVICE_FORCEINLINE void flat_round0_compute(const flat_round0_static_desc &desc, const E *__restrict__ coefficients, const E *__restrict__ eq_values,
                                            E *__restrict__ contributions, const unsigned acc_size, const unsigned gid) {
  const E *coeff = coefficients;
  E c0 = E::ZERO();

  // c0: base field output terms
  for (unsigned i = 0; i < desc.num_c0_bf; i++) {
    const bf val = flat_load_bf_value(desc.sources[desc.c0_bf[i].source_idx], gid);
    c0 = E::add(c0, E::mul(flat_load_coeff(coeff), val));
  }

  // c0: extension field output terms
  for (unsigned i = 0; i < desc.num_c0_ext; i++) {
    const E val = flat_load_ext_value<E>(desc.sources[desc.c0_ext[i].source_idx], gid);
    c0 = E::add(c0, E::mul(flat_load_coeff(coeff), val));
  }

  E c1 = E::ZERO();

  // c1: bf*bf quadratic terms
  for (unsigned i = 0; i < desc.num_c1_bf_bf; i++) {
    const auto &t = desc.c1_bf_bf[i];
    const bf a = flat_load_bf_delta(desc.sources[t.source_a], gid, acc_size);
    const bf b = flat_load_bf_delta(desc.sources[t.source_b], gid, acc_size);
    c1 = E::add(c1, E::mul(flat_load_coeff(coeff), bf::mul(a, b)));
  }

  // c1: E4*E4 quadratic terms
  for (unsigned i = 0; i < desc.num_c1_e4_e4; i++) {
    const auto &t = desc.c1_e4_e4[i];
    const E a = flat_load_ext_delta<E>(desc.sources[t.source_a], gid, acc_size);
    const E b = flat_load_ext_delta<E>(desc.sources[t.source_b], gid, acc_size);
    c1 = E::add(c1, E::mul(flat_load_coeff(coeff), E::mul(a, b)));
  }

  // c1: bf*E4 mixed quadratic terms
  for (unsigned i = 0; i < desc.num_c1_bf_e4; i++) {
    const auto &t = desc.c1_bf_e4[i];
    const bf a = flat_load_bf_delta(desc.sources[t.source_a], gid, acc_size);
    const E b = flat_load_ext_delta<E>(desc.sources[t.source_b], gid, acc_size);
    c1 = E::add(c1, E::mul(flat_load_coeff(coeff), E::mul(b, a)));
  }

  // c1: linear-in-delta terms
  for (unsigned i = 0; i < desc.num_c1_linear; i++) {
    const bf d = flat_load_bf_delta(desc.sources[desc.c1_linear[i].source_idx], gid, acc_size);
    c1 = E::add(c1, E::mul(flat_load_coeff(coeff), d));
  }

  // eq_values: cs (streaming, read once, large) — don't pollute L1 or L2.
  const E eq = load<E, ld_modifier::cs>(eq_values, gid);
  store<E, st_modifier::cs>(contributions, E::mul(c0, eq), gid);
  store<E, st_modifier::cs>(contributions + acc_size, E::mul(c1, eq), gid);
}

} // namespace airbender::prover::gkr

// __constant__ coefficient symbol — declared at global scope (NTT pattern).
// Defined in main_backward_round0_flat.cu.
EXTERN __device__ __constant__ e4 ab_gkr_flat_round0_coefficients[airbender::prover::gkr::FLAT_ROUND0_CONST_MAX];

namespace airbender::prover::gkr {

// --- Constant-path round 0 kernel ---
// Same as flat_round0_compute but reads coefficients from __constant__ symbol.

template <typename E>
DEVICE_FORCEINLINE void flat_round0_compute_constant(const flat_round0_static_desc &desc, const E *__restrict__ eq_values, E *__restrict__ contributions,
                                                     const unsigned acc_size, const unsigned gid) {
  flat_round0_compute(desc, reinterpret_cast<const E *>(::ab_gkr_flat_round0_coefficients), eq_values, contributions, acc_size, gid);
}

} // namespace airbender::prover::gkr
