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

// Phase C compact mirror of `flat_round0_static_desc`. Source pointers
// collapse to u16 packed references (`is_virtual<<15 | ptr_idx<<11 | poly_idx`,
// 4-bit ptr_idx, 11-bit poly_idx),
// resolved via the per-launch `tables` block (`bases` / `log2_stride`).
// Term tables (`c0_bf`, `c1_bf_bf`, ...) are unchanged — they already use u16
// indices into `sources[]`. Mirror of
// `gpu_prover::prover::gkr::backward_flat_compact::GpuFlatRound0StaticDescCompact`.
struct flat_round0_static_desc_compact {
  gkr_dim_reducing_tables tables;

  gkr_source_record sources[FLAT_ROUND0_MAX_SOURCES];
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

static_assert(sizeof(flat_round0_static_desc_compact) <= 32 * 1024, "flat_round0_static_desc_compact exceeds the 32 KB cudaLaunchKernelExC inline ceiling");

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

// --- Compact load helpers (Phase C u16 source encoding) ---
//
// Each `packed` u16 is one entry of `desc.sources[]`. Layout:
//   bit 15      : is_virtual (1 = virtual base-field source)
//   bits 14..11 : ptr_idx (4 bits, 16 slots) into `tables.bases` / `tables.log2_stride`
//   bits 10..0  : poly_idx (11 bits, max 2048) (real path) OR low 3 bits = `gkr_base_source_kind`
// `log2_stride` is in element units (matches the Rust storage layout's
// per-poly element stride; see Phase B notes in `common.cuh`).

DEVICE_FORCEINLINE bf flat_load_bf_value_compact(const gkr_dim_reducing_tables &tables, const gkr_source_record record, const unsigned gid) {
  if ((record.src & 0x8000u) != 0) {
    const auto kind = static_cast<gkr_base_source_kind>(record.src & 0x7u);
    return gkr_virtual_base_value(kind, gid);
  }
  const u16 packed = record.src;
  const u32 ptr_idx = (packed >> 11) & 0xFu;
  const u32 poly_idx = packed & 0x07FFu;
  const u8 *base_u8 = tables.bases[ptr_idx];
  const u32 log2_stride = tables.log2_stride[ptr_idx];
  const bf *poly = reinterpret_cast<const bf *>(base_u8) + (static_cast<size_t>(poly_idx) << log2_stride);
  return load<bf, ld_modifier::ca>(poly, gid);
}

DEVICE_FORCEINLINE bf flat_load_bf_delta_compact(const gkr_dim_reducing_tables &tables, const gkr_source_record record, const unsigned gid,
                                                 const unsigned acc_size) {
  return bf::sub(flat_load_bf_value_compact(tables, record, gid + acc_size), flat_load_bf_value_compact(tables, record, gid));
}

template <typename E>
DEVICE_FORCEINLINE E flat_load_ext_value_compact(const gkr_dim_reducing_tables &tables, const gkr_source_record record, const unsigned gid) {
  // Extension-field sources never use the virtual encoding (only base-field
  // sources can be virtual). The encoder emits the real path for ext sources.
  const u16 packed = record.src;
  const u32 ptr_idx = (packed >> 11) & 0xFu;
  const u32 poly_idx = packed & 0x07FFu;
  const u8 *base_u8 = tables.bases[ptr_idx];
  const u32 log2_stride = tables.log2_stride[ptr_idx];
  const E *poly = reinterpret_cast<const E *>(base_u8) + (static_cast<size_t>(poly_idx) << log2_stride);
  return load<E, ld_modifier::ca>(poly, gid);
}

template <typename E>
DEVICE_FORCEINLINE E flat_load_ext_delta_compact(const gkr_dim_reducing_tables &tables, const gkr_source_record record, const unsigned gid,
                                                 const unsigned acc_size) {
  const E f0 = flat_load_ext_value_compact<E>(tables, record, gid);
  const E f1 = flat_load_ext_value_compact<E>(tables, record, gid + acc_size);
  return E::sub(f1, f0);
}

// --- Flat round 0 kernel ---

// --- Coefficient loaders ---
// CoeffLoader is a lightweight callable: operator() returns the next coefficient.
// Two flavors: pointer-based (LDG) and constant-symbol (LDC).

// Pointer-based: walks a device pointer with ca (cache-all) hint.
template <typename E> struct coeff_loader_ptr {
  const E *ptr;
  DEVICE_FORCEINLINE E operator()() {
    const E val = load<E, ld_modifier::ca>(ptr, 0);
    ++ptr;
    return val;
  }
};

// Constant-symbol loaders are defined after each __constant__ declaration
// so that they can name the symbol directly (required for LDC emission).

template <typename E, typename CoeffLoader>
DEVICE_FORCEINLINE void flat_round0_compute_impl(const flat_round0_static_desc &desc, CoeffLoader coeff_loader, const E *__restrict__ eq_values,
                                                 E *__restrict__ contributions, const unsigned acc_size, const unsigned gid) {
  E c0 = E::ZERO();

  // c0: base field output terms
  for (unsigned i = 0; i < desc.num_c0_bf; i++) {
    const bf val = flat_load_bf_value(desc.sources[desc.c0_bf[i].source_idx], gid);
    c0 = E::fma(coeff_loader(), val, c0);
  }

  // c0: extension field output terms
  for (unsigned i = 0; i < desc.num_c0_ext; i++) {
    const E val = flat_load_ext_value<E>(desc.sources[desc.c0_ext[i].source_idx], gid);
    c0 = E::fma(coeff_loader(), val, c0);
  }

  E c1 = E::ZERO();

  // c1: bf*bf quadratic terms
  for (unsigned i = 0; i < desc.num_c1_bf_bf; i++) {
    const auto &t = desc.c1_bf_bf[i];
    const bf a = flat_load_bf_delta(desc.sources[t.source_a], gid, acc_size);
    const bf b = flat_load_bf_delta(desc.sources[t.source_b], gid, acc_size);
    c1 = E::fma(coeff_loader(), bf::mul(a, b), c1);
  }

  // c1: E4*E4 quadratic terms
  for (unsigned i = 0; i < desc.num_c1_e4_e4; i++) {
    const auto &t = desc.c1_e4_e4[i];
    const E a = flat_load_ext_delta<E>(desc.sources[t.source_a], gid, acc_size);
    const E b = flat_load_ext_delta<E>(desc.sources[t.source_b], gid, acc_size);
    c1 = E::fma(coeff_loader(), E::mul(a, b), c1);
  }

  // c1: bf*E4 mixed quadratic terms
  for (unsigned i = 0; i < desc.num_c1_bf_e4; i++) {
    const auto &t = desc.c1_bf_e4[i];
    const bf a = flat_load_bf_delta(desc.sources[t.source_a], gid, acc_size);
    const E b = flat_load_ext_delta<E>(desc.sources[t.source_b], gid, acc_size);
    c1 = E::fma(coeff_loader(), E::mul(b, a), c1);
  }

  // c1: linear-in-delta terms
  for (unsigned i = 0; i < desc.num_c1_linear; i++) {
    const bf d = flat_load_bf_delta(desc.sources[desc.c1_linear[i].source_idx], gid, acc_size);
    c1 = E::fma(coeff_loader(), d, c1);
  }

  // eq_values: cs (streaming, read once, large) — don't pollute L1 or L2.
  const E eq = load<E, ld_modifier::cs>(eq_values, gid);
  store<E, st_modifier::cs>(contributions, E::mul(c0, eq), gid);
  store<E, st_modifier::cs>(contributions + acc_size, E::mul(c1, eq), gid);
}

// Public API: pointer-based (non-constant path).
template <typename E>
DEVICE_FORCEINLINE void flat_round0_compute(const flat_round0_static_desc &desc, const E *__restrict__ coefficients, const E *__restrict__ eq_values,
                                            E *__restrict__ contributions, const unsigned acc_size, const unsigned gid) {
  coeff_loader_ptr<E> loader{coefficients};
  flat_round0_compute_impl(desc, loader, eq_values, contributions, acc_size, gid);
}

} // namespace airbender::prover::gkr

// __constant__ coefficient symbol — declared at global scope (NTT pattern).
// Defined in main_backward_round0_flat.cu.
EXTERN __device__ __constant__ e4 ab_gkr_flat_round0_coefficients[airbender::prover::gkr::FLAT_ROUND0_CONST_MAX];

namespace airbender::prover::gkr {

// Constant-symbol loader for round 0: accesses the symbol by index → LDC.
// Not templated: the __constant__ symbol is e4, direct access is required for LDC.
struct coeff_loader_round0_constant {
  unsigned idx = 0;
  DEVICE_FORCEINLINE e4 operator()() { return ::ab_gkr_flat_round0_coefficients[idx++]; }
};

// --- Constant-path round 0 kernel ---
// Same as flat_round0_compute but reads coefficients from __constant__ symbol via LDC.

template <typename E>
DEVICE_FORCEINLINE void flat_round0_compute_constant(const flat_round0_static_desc &desc, const E *__restrict__ eq_values, E *__restrict__ contributions,
                                                     const unsigned acc_size, const unsigned gid) {
  coeff_loader_round0_constant loader{};
  flat_round0_compute_impl<E>(desc, loader, eq_values, contributions, acc_size, gid);
}

// --- Phase C compact compute path ---
//
// Same algebra as `flat_round0_compute_impl`, but every `desc.sources[idx]`
// dereference goes through `desc.tables` via `flat_load_*_compact` instead
// of directly dereferencing a raw pointer.

template <typename E, typename CoeffLoader>
DEVICE_FORCEINLINE void flat_round0_compute_compact_impl(const flat_round0_static_desc_compact &desc, CoeffLoader coeff_loader, const E *__restrict__ eq_values,
                                                         E *__restrict__ contributions, const unsigned acc_size, const unsigned gid) {
  E c0 = E::ZERO();

  for (unsigned i = 0; i < desc.num_c0_bf; i++) {
    const bf val = flat_load_bf_value_compact(desc.tables, desc.sources[desc.c0_bf[i].source_idx], gid);
    c0 = E::fma(coeff_loader(), val, c0);
  }

  for (unsigned i = 0; i < desc.num_c0_ext; i++) {
    const E val = flat_load_ext_value_compact<E>(desc.tables, desc.sources[desc.c0_ext[i].source_idx], gid);
    c0 = E::fma(coeff_loader(), val, c0);
  }

  E c1 = E::ZERO();

  for (unsigned i = 0; i < desc.num_c1_bf_bf; i++) {
    const auto &t = desc.c1_bf_bf[i];
    const bf a = flat_load_bf_delta_compact(desc.tables, desc.sources[t.source_a], gid, acc_size);
    const bf b = flat_load_bf_delta_compact(desc.tables, desc.sources[t.source_b], gid, acc_size);
    c1 = E::fma(coeff_loader(), bf::mul(a, b), c1);
  }

  for (unsigned i = 0; i < desc.num_c1_e4_e4; i++) {
    const auto &t = desc.c1_e4_e4[i];
    const E a = flat_load_ext_delta_compact<E>(desc.tables, desc.sources[t.source_a], gid, acc_size);
    const E b = flat_load_ext_delta_compact<E>(desc.tables, desc.sources[t.source_b], gid, acc_size);
    c1 = E::fma(coeff_loader(), E::mul(a, b), c1);
  }

  for (unsigned i = 0; i < desc.num_c1_bf_e4; i++) {
    const auto &t = desc.c1_bf_e4[i];
    const bf a = flat_load_bf_delta_compact(desc.tables, desc.sources[t.source_a], gid, acc_size);
    const E b = flat_load_ext_delta_compact<E>(desc.tables, desc.sources[t.source_b], gid, acc_size);
    c1 = E::fma(coeff_loader(), E::mul(b, a), c1);
  }

  for (unsigned i = 0; i < desc.num_c1_linear; i++) {
    const bf d = flat_load_bf_delta_compact(desc.tables, desc.sources[desc.c1_linear[i].source_idx], gid, acc_size);
    c1 = E::fma(coeff_loader(), d, c1);
  }

  const E eq = load<E, ld_modifier::cs>(eq_values, gid);
  store<E, st_modifier::cs>(contributions, E::mul(c0, eq), gid);
  store<E, st_modifier::cs>(contributions + acc_size, E::mul(c1, eq), gid);
}

template <typename E>
DEVICE_FORCEINLINE void flat_round0_compute_compact(const flat_round0_static_desc_compact &desc, const E *__restrict__ coefficients,
                                                    const E *__restrict__ eq_values, E *__restrict__ contributions, const unsigned acc_size,
                                                    const unsigned gid) {
  coeff_loader_ptr<E> loader{coefficients};
  flat_round0_compute_compact_impl(desc, loader, eq_values, contributions, acc_size, gid);
}

template <typename E>
DEVICE_FORCEINLINE void flat_round0_compute_constant_compact(const flat_round0_static_desc_compact &desc, const E *__restrict__ eq_values,
                                                             E *__restrict__ contributions, const unsigned acc_size, const unsigned gid) {
  coeff_loader_round0_constant loader{};
  flat_round0_compute_compact_impl<E>(desc, loader, eq_values, contributions, acc_size, gid);
}

} // namespace airbender::prover::gkr
