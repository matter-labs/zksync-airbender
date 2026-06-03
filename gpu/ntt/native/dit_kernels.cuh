// Ported from ntt-experiments include/ntt/kernels.cuh (rr/v8-logn13-two-pass-ntt).
// Unified NTT kernels: ntt_single (one engine call, no smem hop) + ntt_two_pass.
#pragma once
#include "dit_memory.cuh" // StoreMode, load_vec_vpt, store_vec_vpt,
#include <primitives/field.cuh>
// stage_combined, load_combined
#include "dit_core.cuh"
#include "dit_coset.cuh"
#include "dit_geometry.cuh"
#include "dit_swizzle.cuh"
#include "dit_twiddles.cuh"
using namespace ::airbender::primitives::field;
namespace airbender {
namespace ntt {

// smem for ntt_single: just the clean N-1 triangle (shared across the block).
template <unsigned LOG_N, unsigned LOG_VPT> constexpr unsigned ntt_single_smem() { return clean_triangle_count<LOG_N, LOG_VPT>() * sizeof(bf); }

// Multi-warp single-pass NTT. The clean twiddle triangle is staged to smem
// (V4) once per block; each NTT in the warp's LANES-lane subgroup runs one
// dit_phase (no smem hop). K cosets/slot via the in-register delta walk.
// __device__ impl invoked by the EXTERN __global__ wrappers in dit_kernels_extern.cu
// (wrapped by the Rust launcher `monomials_to_evals_dit`). MIN_BLOCKS_PER_SM is now unused
// but kept so the wrapper's 6-arg instantiation still matches.
template <unsigned LOG_N, unsigned LOG_VPT, unsigned NUM_WARPS, unsigned K_PER_NTT_SLOT = 8u, StoreMode STORE_MODE = StoreMode::CS,
          unsigned MIN_BLOCKS_PER_SM = 0u>
DEVICE_FORCEINLINE void ntt_single(const bf *__restrict__ monomials_bitrev,
                                   const bf *__restrict__ tw_clean, // host-built clean triangle (N-1)
                                   bf *__restrict__ out_natural, u32 cfp_0, u32 coset_step,
                                   u32 coset_out_stride) { // per-coset OUTPUT stride in bf elements (== N for contiguous)
  using G = NttSingleGeom<LOG_N, LOG_VPT>;
  constexpr unsigned VPT = G::VPT;
  constexpr unsigned LANES = G::LANES;
  constexpr unsigned NTTS_PER_WARP = G::NTTS_PER_WARP;
  constexpr unsigned BLOCK_THREADS = NUM_WARPS * 32u;
  constexpr unsigned TRI = clean_triangle_count<LOG_N, LOG_VPT>();

  extern __shared__ bf smem[];
  bf *const tw = smem;

  const unsigned tid = threadIdx.x;
  const unsigned warp_id = tid >> 5;
  const unsigned warp_lane = tid & 31u;
  const unsigned ntt_idx_in_warp = warp_lane / LANES;
  const unsigned lane_in_ntt = warp_lane & (LANES - 1u);

  stage_triangle_v4(tw, tw_clean, TRI, tid, BLOCK_THREADS);
  __syncthreads();

  constexpr unsigned SLOTS_PER_BLOCK = NUM_WARPS * NTTS_PER_WARP;
  const unsigned ntt_slot_global = blockIdx.x * SLOTS_PER_BLOCK + warp_id * NTTS_PER_WARP + ntt_idx_in_warp;
  const u32 cfp_first = cfp_0 + ntt_slot_global * K_PER_NTT_SLOT * coset_step;

  bf mono[VPT], d[VPT];
  load_vec_vpt<LOG_VPT>(monomials_bitrev + VPT * lane_in_ntt, mono);
  coset_twist<LOG_N, VPT>(mono, VPT * lane_in_ntt, cfp_first);
  if constexpr (K_PER_NTT_SLOT > 1)
    coset_delta<LOG_N, VPT>(d, VPT * lane_in_ntt, coset_step);

  bf w[VPT];
  for (unsigned c = 0; c < K_PER_NTT_SLOT; ++c) {
#pragma unroll
    for (unsigned r = 0; r < VPT; ++r)
      w[r] = mono[r];
    // clean triangle: LOG_TBL=LOG_N, tw_row=lane_in_ntt, tw_base=lane*VPT.
    dit_phase<LOG_N, LANES, /*LOG_TBL=*/LOG_N, LOG_VPT, /*SKIP_LAST_TW=*/true>(tw, VPT * lane_in_ntt, lane_in_ntt, lane_in_ntt, w);
    const unsigned coset_idx = ntt_slot_global * K_PER_NTT_SLOT + c;
    store_vec_vpt<LOG_VPT, STORE_MODE>(out_natural + (size_t)coset_idx * coset_out_stride + VPT * lane_in_ntt, w);
    if constexpr (K_PER_NTT_SLOT > 1) {
      if (c + 1u < K_PER_NTT_SLOT) {
#pragma unroll
        for (unsigned r = 0; r < VPT; ++r)
          mono[r] = bf::mul(mono[r], d[r]);
      }
    }
  }
}

// Bench-only: streaming single-pass. Each of the block's SLOTS_PER_BLOCK NTT
// slots grid-strides cosets by gridDim.x*SLOTS_PER_BLOCK with a guard
// (coset_idx < num_cosets), so the grid is free (any size). Uses the in-register
// DELTA WALK (like ntt_single): twist once for the slot's first coset, then a
// single bf::mul per coset advances the coset factor by slot_stride cosets
// (delta = w^(bitrev*slot_stride*coset_step)). Avoids the per-coset coset_twist
// table lookup. Parity-identical: the running product reconstructs
// w^(bitrev*coset_idx*coset_step).
template <unsigned LOG_N, unsigned LOG_VPT, unsigned NUM_WARPS, StoreMode STORE_MODE = StoreMode::CS>
DEVICE_FORCEINLINE void ntt_single_stream(const bf *__restrict__ monomials_bitrev, const bf *__restrict__ tw_clean, bf *__restrict__ out_natural, u32 cfp_0,
                                          u32 coset_step, u32 num_cosets, u32 coset_out_stride) {
  using G = NttSingleGeom<LOG_N, LOG_VPT>;
  constexpr unsigned VPT = G::VPT;
  constexpr unsigned LANES = G::LANES;
  constexpr unsigned NTTS_PER_WARP = G::NTTS_PER_WARP;
  constexpr unsigned BLOCK_THREADS = NUM_WARPS * 32u;
  constexpr unsigned TRI = clean_triangle_count<LOG_N, LOG_VPT>();
  constexpr unsigned SLOTS_PER_BLOCK = NUM_WARPS * NTTS_PER_WARP;
  extern __shared__ bf smem[];
  bf *const tw = smem;
  const unsigned tid = threadIdx.x;
  const unsigned warp_id = tid >> 5;
  const unsigned warp_lane = tid & 31u;
  const unsigned ntt_idx_in_warp = warp_lane / LANES;
  const unsigned lane_in_ntt = warp_lane & (LANES - 1u);
  stage_triangle_v4(tw, tw_clean, TRI, tid, BLOCK_THREADS);
  __syncthreads();
  const unsigned slot = warp_id * NTTS_PER_WARP + ntt_idx_in_warp;   // 0..SLOTS_PER_BLOCK
  const unsigned slot_global0 = blockIdx.x * SLOTS_PER_BLOCK + slot; // first coset for this slot
  const unsigned slot_stride = gridDim.x * SLOTS_PER_BLOCK;          // grid-stride in coset index

  bf mono[VPT], d[VPT];
  load_vec_vpt<LOG_VPT>(monomials_bitrev + VPT * lane_in_ntt, mono);
  // Twist once for this slot's FIRST coset, then walk by a constant delta.
  coset_twist<LOG_N, VPT>(mono, VPT * lane_in_ntt, cfp_0 + slot_global0 * coset_step);
  coset_delta<LOG_N, VPT>(d, VPT * lane_in_ntt, slot_stride * coset_step);

  for (unsigned coset_idx = slot_global0; coset_idx < num_cosets; coset_idx += slot_stride) {
    bf w[VPT];
#pragma unroll
    for (unsigned r = 0; r < VPT; ++r)
      w[r] = mono[r];
    dit_phase<LOG_N, LANES, /*LOG_TBL=*/LOG_N, LOG_VPT, /*SKIP_LAST_TW=*/true>(tw, VPT * lane_in_ntt, lane_in_ntt, lane_in_ntt, w);
    store_vec_vpt<LOG_VPT, STORE_MODE>(out_natural + (size_t)coset_idx * coset_out_stride + VPT * lane_in_ntt, w);
    // Advance the coset factor to the next coset (harmless wasted mul on the
    // final iteration; the loop guard handles termination).
#pragma unroll
    for (unsigned r = 0; r < VPT; ++r)
      mono[r] = bf::mul(mono[r], d[r]);
  }
}

// --- two-pass --------------------------------------------------------------
// smem (bf): coupled pass-1 triangle + clean pass-2 triangle + d (N) + slab (N).
// The clean pass-2 triangle has 2^LOG_N2-1 entries (always == 3 mod 4), so it is
// padded up to a 4-multiple (P2C_PAD) before the regions that follow it, keeping
// d_smem and slab 16-byte aligned for their V4 (st/ld.shared.v4) accesses.
template <unsigned LOG_N, unsigned LOG_VPT> constexpr unsigned ntt_two_pass_smem() {
  using G = NttTwoPassGeom<LOG_N, LOG_VPT>;
  constexpr unsigned P2C_PAD = (clean_triangle_count<G::LOG_N2, LOG_VPT>() + 3u) & ~3u;
  unsigned w = coupled_triangle_count<LOG_N, LOG_VPT, G::LOG_N1>() + P2C_PAD + G::N // slab
               + G::N;                                                              // staged d-table
  return w * sizeof(bf);
}

// __device__ impl invoked by the EXTERN __global__ wrappers in dit_kernels_extern.cu
// (wrapped by the Rust launcher `monomials_to_evals_dit`). MIN_BLOCKS_PER_SM is now unused
// but kept so the wrapper's 4-arg instantiation still matches.
template <unsigned LOG_N, unsigned LOG_VPT, StoreMode SM, unsigned MIN_BLOCKS_PER_SM = 1u>
DEVICE_FORCEINLINE void ntt_two_pass(const bf *__restrict__ monomials_bitrev,
                                     const bf *__restrict__ tw_p1_coupled, // host build_coupled_triangle
                                     const bf *__restrict__ tw_p2_clean,   // host build_clean_triangle<LOG_N2>
                                     const bf *__restrict__ d_table, bf *__restrict__ out_natural, u32 cfp_0, u32 coset_step, u32 num_cosets,
                                     u32 coset_out_stride) { // per-coset OUTPUT stride in bf elements (== N for contiguous)
  using G = NttTwoPassGeom<LOG_N, LOG_VPT>;
  constexpr unsigned VPT = G::VPT;
  constexpr unsigned P1C = coupled_triangle_count<LOG_N, LOG_VPT, G::LOG_N1>();
  constexpr unsigned P2C = clean_triangle_count<G::LOG_N2, LOG_VPT>();
  constexpr unsigned P2C_PAD = (P2C + 3u) & ~3u; // keep d_smem/slab 16B-aligned
  extern __shared__ bf smem[];

  bf *const couple = smem;            // P1C (mult of 4)
  bf *const tw_p2 = couple + P1C;     // P2C entries, P2C_PAD reserved
  bf *const d_smem = tw_p2 + P2C_PAD; // N (staged d-table)
  bf *const slab = d_smem + G::N;

  const unsigned tid = threadIdx.x;
  const unsigned base = tid * VPT;
  const unsigned bx = blockIdx.x;
  const unsigned gd = gridDim.x;

  stage_triangle_v4(couple, tw_p1_coupled, P1C, tid, blockDim.x);
  stage_triangle_v4(tw_p2, tw_p2_clean, P2C, tid, blockDim.x);
  stage_combined<LOG_N, LOG_VPT>(d_smem, d_table, tid);

  bf mono[VPT];
  load_vec_vpt<G::LOG_VPT>(monomials_bitrev + base, mono);
  coset_twist<G::LOG_N, VPT>(mono, base, cfp_0 + bx * coset_step);
  __syncthreads();

  // Guarded grid-stride: each block walks cosets bx, bx+gd, bx+2*gd, … < num_cosets;
  // the loop condition is the guard, so the grid is free (any size). mono is
  // twisted once for coset=bx, then advanced by the d-table each iteration (which
  // steps the coset factor by gd*coset_step, matching the stride).
  for (unsigned coset = bx; coset < num_cosets; coset += gd) {
    bf v[VPT];
    const unsigned p1_n2 = tid >> (G::LOG_N1 - LOG_VPT);
    const unsigned p1_lane = tid & (G::LANES_P1 - 1u);
    { // Pass 1: coupled triangle (LOG_TBL=LOG_N, tw_row=tid, base=p1_n2*N1),
      // last stage applied (SKIP_LAST_TW=false), non-restoring + restore.
#pragma unroll
      for (unsigned r = 0; r < VPT; ++r)
        v[r] = mono[r];
      dit_phase<G::LOG_N1, G::LANES_P1, /*LOG_TBL=*/G::LOG_N, LOG_VPT, /*SKIP_LAST_TW=*/false>(couple, p1_n2 * G::N1, tid, p1_lane, v);
    }
    { // Transition store (mirror): VPT/4 x st.shared.v4 at v4sg_dit_addr.
#pragma unroll
      for (unsigned g4 = 0; g4 < VPT / 4u; ++g4) {
        const unsigned a = v4sg_dit_addr<LOG_N, LOG_VPT>(base + 4u * g4);
        st_shared_v4(slab + a, v[4u * g4 + 0], v[4u * g4 + 1], v[4u * g4 + 2], v[4u * g4 + 3]);
      }
    }
    __syncthreads();
    { // Pass 2: clean triangle (LOG_TBL=LOG_N2, tw_row=p2_lane, base=p2_lane*VPT),
      // last stage skipped; mirror write-back (intra-thread WAR, no barrier).
      const unsigned p2_n1 = tid >> (G::LOG_N2 - LOG_VPT);
      const unsigned p2_lane = tid & (G::LANES_P2 - 1u);
      bf w[VPT];
#pragma unroll
      for (unsigned r = 0; r < VPT; ++r) {
        const unsigned L = (p2_lane * VPT + r) * G::N1 + p2_n1;
        w[r] = slab[v4sg_dit_addr<LOG_N, LOG_VPT>(L)];
      }
      dit_phase<G::LOG_N2, G::LANES_P2, /*LOG_TBL=*/G::LOG_N2, LOG_VPT, /*SKIP_LAST_TW=*/true>(tw_p2, p2_lane * VPT, p2_lane, p2_lane, w);
#pragma unroll
      for (unsigned r = 0; r < VPT; ++r) {
        const unsigned L = (p2_lane * VPT + r) * G::N1 + p2_n1;
        slab[v4sg_dit_addr<LOG_N, LOG_VPT>(L)] = w[r];
      }
    }
    __syncthreads();
    { // Output gather: V4 load at v4sg_dit_addr, coalesced store.
      bf *const out_c = out_natural + (size_t)coset * coset_out_stride;
      bf out[VPT];
#pragma unroll
      for (unsigned g4 = 0; g4 < VPT / 4u; ++g4) {
        const unsigned a = v4sg_dit_addr<LOG_N, LOG_VPT>(base + 4u * g4);
        ld_shared_v4(slab + a, out[4u * g4 + 0], out[4u * g4 + 1], out[4u * g4 + 2], out[4u * g4 + 3]);
      }
      store_vec_vpt<G::LOG_VPT, SM>(out_c + base, out);
    }
    if (coset + gd < num_cosets) {
      bf dv[VPT];
      load_combined<LOG_N, LOG_VPT, /*STAGED=*/true>(dv, d_smem, tid);
#pragma unroll
      for (unsigned r = 0; r < VPT; ++r)
        mono[r] = bf::mul(mono[r], dv[r]);
    }
  }
}

// Bench-only: identical to ntt_two_pass but with a COMPILE-TIME coset loop count
// K (fully unrolled), no runtime cosets_per_block. Launch grid = num_cosets / K.
template <unsigned LOG_N, unsigned LOG_VPT, unsigned K, StoreMode SM, unsigned MIN_BLOCKS_PER_SM = 1u>
DEVICE_FORCEINLINE void ntt_two_pass_fixed(const bf *__restrict__ monomials_bitrev,
                                           const bf *__restrict__ tw_p1_coupled, // host build_coupled_triangle
                                           const bf *__restrict__ tw_p2_clean,   // host build_clean_triangle<LOG_N2>
                                           const bf *__restrict__ d_table, bf *__restrict__ out_natural, u32 cfp_0, u32 coset_step,
                                           u32 coset_out_stride) { // per-coset OUTPUT stride in bf elements (== N for contiguous)
  using G = NttTwoPassGeom<LOG_N, LOG_VPT>;
  constexpr unsigned VPT = G::VPT;
  constexpr unsigned P1C = coupled_triangle_count<LOG_N, LOG_VPT, G::LOG_N1>();
  constexpr unsigned P2C = clean_triangle_count<G::LOG_N2, LOG_VPT>();
  constexpr unsigned P2C_PAD = (P2C + 3u) & ~3u; // keep d_smem/slab 16B-aligned
  extern __shared__ bf smem[];

  bf *const couple = smem;            // P1C (mult of 4)
  bf *const tw_p2 = couple + P1C;     // P2C entries, P2C_PAD reserved
  bf *const d_smem = tw_p2 + P2C_PAD; // N (staged d-table)
  bf *const slab = d_smem + G::N;

  const unsigned tid = threadIdx.x;
  const unsigned base = tid * VPT;
  const unsigned bx = blockIdx.x;
  const unsigned gd = gridDim.x;

  stage_triangle_v4(couple, tw_p1_coupled, P1C, tid, blockDim.x);
  stage_triangle_v4(tw_p2, tw_p2_clean, P2C, tid, blockDim.x);
  stage_combined<LOG_N, LOG_VPT>(d_smem, d_table, tid);

  bf mono[VPT];
  load_vec_vpt<G::LOG_VPT>(monomials_bitrev + base, mono);
  coset_twist<G::LOG_N, VPT>(mono, base, cfp_0 + bx * coset_step);
  __syncthreads();

  // grid (gd) is a power-of-two divisor of num_cosets, so every block does
  // EXACTLY cosets_per_block = num_cosets / gd cosets (no ragged tail, no guard).
  constexpr unsigned k_local = K;
  for (unsigned c = 0; c < k_local; ++c) {
    bf v[VPT];
    const unsigned p1_n2 = tid >> (G::LOG_N1 - LOG_VPT);
    const unsigned p1_lane = tid & (G::LANES_P1 - 1u);
    { // Pass 1: coupled triangle (LOG_TBL=LOG_N, tw_row=tid, base=p1_n2*N1),
      // last stage applied (SKIP_LAST_TW=false), non-restoring + restore.
#pragma unroll
      for (unsigned r = 0; r < VPT; ++r)
        v[r] = mono[r];
      dit_phase<G::LOG_N1, G::LANES_P1, /*LOG_TBL=*/G::LOG_N, LOG_VPT, /*SKIP_LAST_TW=*/false>(couple, p1_n2 * G::N1, tid, p1_lane, v);
    }
    { // Transition store (mirror): VPT/4 x st.shared.v4 at v4sg_dit_addr.
#pragma unroll
      for (unsigned g4 = 0; g4 < VPT / 4u; ++g4) {
        const unsigned a = v4sg_dit_addr<LOG_N, LOG_VPT>(base + 4u * g4);
        st_shared_v4(slab + a, v[4u * g4 + 0], v[4u * g4 + 1], v[4u * g4 + 2], v[4u * g4 + 3]);
      }
    }
    __syncthreads();
    { // Pass 2: clean triangle (LOG_TBL=LOG_N2, tw_row=p2_lane, base=p2_lane*VPT),
      // last stage skipped; mirror write-back (intra-thread WAR, no barrier).
      const unsigned p2_n1 = tid >> (G::LOG_N2 - LOG_VPT);
      const unsigned p2_lane = tid & (G::LANES_P2 - 1u);
      bf w[VPT];
#pragma unroll
      for (unsigned r = 0; r < VPT; ++r) {
        const unsigned L = (p2_lane * VPT + r) * G::N1 + p2_n1;
        w[r] = slab[v4sg_dit_addr<LOG_N, LOG_VPT>(L)];
      }
      dit_phase<G::LOG_N2, G::LANES_P2, /*LOG_TBL=*/G::LOG_N2, LOG_VPT, /*SKIP_LAST_TW=*/true>(tw_p2, p2_lane * VPT, p2_lane, p2_lane, w);
#pragma unroll
      for (unsigned r = 0; r < VPT; ++r) {
        const unsigned L = (p2_lane * VPT + r) * G::N1 + p2_n1;
        slab[v4sg_dit_addr<LOG_N, LOG_VPT>(L)] = w[r];
      }
    }
    __syncthreads();
    { // Output gather: V4 load at v4sg_dit_addr, coalesced store.
      bf *const out_c = out_natural + (size_t)(bx + c * gd) * coset_out_stride;
      bf out[VPT];
#pragma unroll
      for (unsigned g4 = 0; g4 < VPT / 4u; ++g4) {
        const unsigned a = v4sg_dit_addr<LOG_N, LOG_VPT>(base + 4u * g4);
        ld_shared_v4(slab + a, out[4u * g4 + 0], out[4u * g4 + 1], out[4u * g4 + 2], out[4u * g4 + 3]);
      }
      store_vec_vpt<G::LOG_VPT, SM>(out_c + base, out);
    }
    if (c + 1u < k_local) {
      bf dv[VPT];
      load_combined<LOG_N, LOG_VPT, /*STAGED=*/true>(dv, d_smem, tid);
#pragma unroll
      for (unsigned r = 0; r < VPT; ++r)
        mono[r] = bf::mul(mono[r], dv[r]);
    }
  }
}

} // namespace ntt
} // namespace airbender
