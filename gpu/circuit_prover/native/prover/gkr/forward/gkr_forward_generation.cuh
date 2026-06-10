#pragma once

#include "../support/lookup_helpers.cuh"

// ===========================================================================
// GKR forward-pass code-generation macro header.
//
// Consumes the macro-DSL body emitted by the `gpu_gkr_fwd_generator` crate
// (one `FWD_FN_BEGIN(L) ... FWD_FN_END` per layer) and expands it into a
// straight-line, per-row CUDA kernel: one thread per trace row `gid`, each
// distinct column loaded once, each shared value computed once (the generator
// performs the CSE; these macros are the thin typed expansion).
//
// This deliberately replaces the runtime category-loop of `flat.cuh` with
// generated straight-line code, but REUSES that path's field ops and the
// `gkr_eval_*_v2` helpers (same num/den/product math, base-staying domains).
//
// Challenge-derived constants split by where they come from:
//   * gamma powers (`ab_gkr_lookup_gamma_consts`) and alpha powers
//     (`ab_gkr_lookup_alpha_powers`) are SHARED with the flat path and populated
//     by the setup/forward preludes — still read from `__constant__` here.
//   * the permutation linearization challenges, the additive seed, and the
//     decoder fill value are forward-generation-specific. They are now carried
//     in the kernel proxy (by value for the host-known challenges, by pointer
//     for the device-resident fill value) instead of `__constant__`, so the A/B
//     path needs no per-launch H2D upload or D2D copy for them.
// ===========================================================================

// Shared with the flat forward path (defined in flat_layer.cu / setup/kernels.cu);
// `ab_gkr_lookup_alpha_powers` is already EXTERN-declared via descriptors.cuh.
EXTERN __device__ __constant__ e4 ab_gkr_lookup_gamma_consts[3]; // [gamma, gamma^2, 2*gamma]

namespace airbender::prover::gkr::forward::generation {

// Per-row forward proxy. Column-major data buffers: element (column `c`, row
// `gid`) lives at `base[c * trace_len + gid]`. Forward-generation-specific
// challenge data is carried here (was `__constant__`): the permutation
// linearization challenges and additive seed are host-known at schedule time so
// they ride along by value; the decoder fill value is device-computed in setup
// so a pointer to it is read directly. The shared gamma/alpha powers still come
// from `__constant__`.
template <typename E> struct GkrFwdProxy {
  const bf *memory;        // base-layer memory columns
  const bf *witness;       // base-layer witness columns
  const bf *setup;         // setup columns
  const E *generic_lookup; // vectorized-lookup setup polynomial (row-indexed)
  u32 generic_lookup_len;  // valid length of generic_lookup (zero-pad beyond)
  bf *cache_base;          // base-field cache outputs   [off * trace_len + gid]
  E *cache_ext;            // ext-field cache outputs    [off * trace_len + gid]
  bf *out_base;            // base-field gate outputs    [off * trace_len + gid]
  E *out_ext;              // ext-field gate outputs     [off * trace_len + gid]
  unsigned trace_len;      // number of rows (also the column stride)
  // Permutation linearization challenges indexed by role (ADDR_LOW=0,
  // ADDR_HIGH=1, TS_LOW=2, TS_HIGH=3, VAL_LOW=4, VAL_HIGH=5 — see cs
  // constants.rs); sized to the memory-tuple linear-term capacity.
  E perm_challenges[airbender::prover::gkr::GKR_FORWARD_CACHE_MEMORY_LINEAR_TERMS];
  E perm_additive;             // additive linearization challenge
  const E *decoder_fill_value; // -> alpha^(width-1) * (Decoder table id); read on padding rows
};

DEVICE_FORCEINLINE e4 fwd_gamma() { return ::ab_gkr_lookup_gamma_consts[0]; }
DEVICE_FORCEINLINE e4 fwd_gamma_sq() { return ::ab_gkr_lookup_gamma_consts[1]; }
DEVICE_FORCEINLINE e4 fwd_two_gamma() { return ::ab_gkr_lookup_gamma_consts[2]; }

// ---------------------------------------------------------------------------
// Function / kernel scaffold. Each generated layer is a templated device-inline
// fn over the proxy (so the data-pointer types stay generic); the macros below
// reference `p` (the proxy) and `gid` (the row), both bound by FWD_FN_BEGIN.
// ---------------------------------------------------------------------------
#define FWD_FN_BEGIN(L) template <class P> DEVICE_FORCEINLINE void fwd_layer_##L(const P p, const unsigned gid) {
#define FWD_FN_END }

// ---------------------------------------------------------------------------
// Base-column loads (column-major; the generator emits one per physical column).
// Virtual setup polys are computed on the fly per row. Use the `cs`
// (cache-streaming / evict-first) hint: each column element is read exactly once
// (one thread per row, one load per column via CSE) so there is no reuse to keep
// in L1 — matches the store side and avoids polluting L1 with use-once lines.
// ---------------------------------------------------------------------------
#define LOAD_MEM(var, col) const bf var = load<bf, ld_modifier::cs>(p.memory + (size_t)(col) * p.trace_len, gid);
#define LOAD_WIT(var, col) const bf var = load<bf, ld_modifier::cs>(p.witness + (size_t)(col) * p.trace_len, gid);
#define LOAD_SETUP(var, col) const bf var = load<bf, ld_modifier::cs>(p.setup + (size_t)(col) * p.trace_len, gid);
#define LOAD_RC16(var) const bf var = gkr_virtual_base_value(GKR_BASE_SOURCE_VIRTUAL_RANGE_CHECK_16_BITS, gid);
#define LOAD_RCTS(var) const bf var = gkr_virtual_base_value(GKR_BASE_SOURCE_VIRTUAL_RANGE_CHECK_TIMESTAMP, gid);

// ---------------------------------------------------------------------------
// Base-field arithmetic. IR constants are canonical u32 field elements; the
// generator special-cases 0/1/-1 so no ×0/×1 multiply is ever emitted.
// ---------------------------------------------------------------------------
#define BF_CONST(dst, c) const bf dst = bf::from_u32_unchecked(c);
#define BF_ADD(dst, a, b) const bf dst = bf::add(a, b);
#define BF_SUB(dst, a, b) const bf dst = bf::sub(a, b);
#define BF_NEG(dst, a) const bf dst = bf::neg(a);
#define BF_MULC(dst, c, a) const bf dst = bf::mul(bf::from_u32_unchecked(c), a);
#define BF_FMAC(dst, c, a, acc) const bf dst = bf::fma(bf::from_u32_unchecked(c), a, acc);

// ---------------------------------------------------------------------------
// Vectorized-lookup folding: base->ext lift then alpha-power accumulation. The
// alpha^k weights live in the shared `ab_gkr_lookup_alpha_powers` constant table
// (k is the column index); the lift carries alpha^0 = 1 with no multiply.
// ---------------------------------------------------------------------------
#define E_FROM_BASE(dst, b) const e4 dst = e4::from_scalar(b);
#define E_FMA_ALPHA(dst, k, b, acc) const e4 dst = e4::fma(::ab_gkr_lookup_alpha_powers[k], b, acc);
// Decoder lookup: padding rows (execute predicate limb == 0) take the fill,
// read directly from the device-resident setup value via the proxy pointer.
#define SELECT_DECODER_FILL(dst, pred, v) const e4 dst = ((pred).limb != 0) ? (v) : (*p.decoder_fill_value);

// ---------------------------------------------------------------------------
// Permutation (memory-tuple) accumulation. `role` indexes the linearization
// challenges; the additive seed and a base constant fold cheaply into ext.
// Challenges ride in the proxy by value (host-known at schedule time).
// ---------------------------------------------------------------------------
#define E_FROM_PERM_ADD(dst) const e4 dst = p.perm_additive;
#define E_ADD_BFC(dst, acc, c) const e4 dst = e4::add(acc, bf::from_u32_unchecked(c));
#define E_ADD_PERM(dst, role, acc) const e4 dst = e4::add(acc, p.perm_challenges[role]);
#define E_SUB_PERM(dst, role, acc) const e4 dst = e4::sub(acc, p.perm_challenges[role]);
#define E_FMA_PERM(dst, role, b, acc) const e4 dst = e4::fma(p.perm_challenges[role], b, acc);
#define E_FMA_PERMC(dst, role, c, acc) const e4 dst = e4::fma(p.perm_challenges[role], bf::from_u32_unchecked(c), acc);

// ---------------------------------------------------------------------------
// Vectorized-lookup setup gather (zero-padded beyond generic_lookup_len).
// ---------------------------------------------------------------------------
#define LOOKUP_SETUP(dst) const e4 dst = gkr_forward_lookup_setup_value<e4>(p.generic_lookup, p.generic_lookup_len, gid);

// ---------------------------------------------------------------------------
// Output gates. PRODUCT is the grand product; the LOOKUP_* gates emit a
// (num, den) pair via the base-staying `_v2` helpers (gamma from constants).
// ---------------------------------------------------------------------------
#define PRODUCT(dst, a, b)                                                                                                                                     \
  e4 dst;                                                                                                                                                      \
  gkr_eval_product<e4>(a, b, dst);
#define LOOKUP_BASE_PAIR(num, den, b, d)                                                                                                                       \
  e4 num;                                                                                                                                                      \
  e4 den;                                                                                                                                                      \
  gkr_eval_lookup_base_pair_v2(b, d, fwd_gamma(), fwd_gamma_sq(), fwd_two_gamma(), num, den);
#define LOOKUP_BASE_MINUS_MULT(num, den, b, c, d)                                                                                                              \
  e4 num;                                                                                                                                                      \
  e4 den;                                                                                                                                                      \
  gkr_eval_lookup_base_minus_multiplicity_v2(b, c, d, fwd_gamma(), fwd_gamma_sq(), num, den);
#define LOOKUP_CACHED_DENS(num, den, a, b, c, d)                                                                                                               \
  e4 num;                                                                                                                                                      \
  e4 den;                                                                                                                                                      \
  gkr_eval_lookup_cached_dens_and_setup(a, b, c, d, fwd_gamma(), num, den);
// Ext-operand lookup pair (both inputs are already-materialized ext vector
// tuples). Algebraically identical to LOOKUP_BASE_PAIR; `_v2` is a base-only
// optimization, so the ext path uses the shifted-form helper directly.
#define LOOKUP_EXT_PAIR(num, den, a, b)                                                                                                                        \
  e4 num;                                                                                                                                                      \
  e4 den;                                                                                                                                                      \
  gkr_eval_lookup_ext_pair<e4>(a, b, fwd_gamma(), num, den);
// Ext-operand lookup-with-setup (ext input, base multiplicity, ext denom). The
// generic minus-multiplicity helper deduces the mixed operand domains.
#define LOOKUP_EXT_MINUS_MULT(num, den, b, c, d)                                                                                                               \
  e4 num;                                                                                                                                                      \
  e4 den;                                                                                                                                                      \
  gkr_eval_lookup_base_minus_multiplicity(b, c, d, fwd_gamma(), num, den);

// ---------------------------------------------------------------------------
// Stores (cache values re-read same-layer via the SSA temp; the store feeds
// downstream layers). Column-major by offset.
// ---------------------------------------------------------------------------
#define STORE_CACHE_BASE(off, var) store<bf, st_modifier::cs>(p.cache_base + (size_t)(off) * p.trace_len, var, gid);
#define STORE_CACHE_EXT(off, var) store<e4, st_modifier::cs>(p.cache_ext + (size_t)(off) * p.trace_len, var, gid);
#define STORE_INNER_BASE(off, var) store<bf, st_modifier::cs>(p.out_base + (size_t)(off) * p.trace_len, var, gid);
#define STORE_INNER_EXT(off, var) store<e4, st_modifier::cs>(p.out_ext + (size_t)(off) * p.trace_len, var, gid);

// ---------------------------------------------------------------------------
// Kernel entry. extern "C" symbol = the ABI (the C++ namespace is organizational).
// Layer 0 only for now; multi-layer dispatch is added when later layers land.
// ---------------------------------------------------------------------------
// Launch bounds are overridable at compile time for the ptxas register/occupancy
// sweep (`-DFWD_LB_MAX_THREADS=… -DFWD_LB_MIN_BLOCKS=…`); the defaults reproduce
// the production launch geometry (128 threads/block, ≥4 blocks/SM) exactly.
#ifndef FWD_LB_MAX_THREADS
#define FWD_LB_MAX_THREADS 128
#endif
#ifndef FWD_LB_MIN_BLOCKS
#define FWD_LB_MIN_BLOCKS 4
#endif

// NB: the NVIDIA shared-memory register-spilling pragma
// (`.pragma "enable_smem_spilling"`) is NOT usable here. It requires whole-program
// ptxas mode (`-rdc=false`), but this archive is built with `-rdc=true` (separate
// compilation) — which this kernel needs, since it reads `__constant__` tables
// (`ab_gkr_lookup_gamma_consts`, `ab_gkr_lookup_alpha_powers`) defined in sibling
// TUs. Under `-rdc=true` the pragma is a hard `ptxas fatal`, not a no-op. Reducing
// register pressure here is the only occupancy lever (see FWD_LB_MIN_BLOCKS).
#define FWD_KERNEL_NAME(NAME) ab_gkr_forward_##NAME##_layer0_kernel
#define FWD_KERNEL(NAME)                                                                                                                                       \
  EXTERN __launch_bounds__(FWD_LB_MAX_THREADS, FWD_LB_MIN_BLOCKS)                                                                                              \
  __global__ void FWD_KERNEL_NAME(NAME)(const __grid_constant__ GkrFwdProxy<e4> proxy, const unsigned count) {                                                 \
    const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;                                                                                                \
    if (gid >= count)                                                                                                                                          \
      return;                                                                                                                                                  \
    fwd_layer_0(proxy, gid);                                                                                                                                   \
  }

} // namespace airbender::prover::gkr::forward::generation
