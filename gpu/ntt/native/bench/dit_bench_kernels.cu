// Bench-only DIT kernel variants (fixed-loop + streaming), compiled into
// gpu_ntt_native ONLY when -DGPU_NTT_BUILD_BENCH=ON (the gpu_ntt `bench` feature).
#include "../dit_kernels.cuh"
namespace airbender {
namespace ntt {

// Bench-only: identical to ntt_two_pass (dit_kernels.cuh) but with a COMPILE-TIME
// coset loop count K (fully unrolled), no runtime cosets_per_block; launch grid =
// num_cosets / K. Instantiated solely by the DIT_2P_FIXED bench kernels below, so it
// lives in this bench translation unit rather than the production DIT header.
template <unsigned LOG_N, unsigned LOG_VPT, unsigned K, StoreMode SM>
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
  extern __shared__ __align__(16) bf smem[];

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

#define DIT_2P_FIXED(LOGN, LOGVPT, K)                                                                                                                          \
  EXTERN __launch_bounds__(NttTwoPassGeom<LOGN, LOGVPT>::THREADS, 1u) __global__ void ab_dit_two_pass_fixed_##LOGN##_##LOGVPT##_##K(                           \
      const bf *mono, const bf *tw_p1, const bf *tw_p2, const bf *d_tab, bf *out, u32 cfp0, u32 step, u32 cstride) {                                           \
    ntt_two_pass_fixed<LOGN, LOGVPT, K, StoreMode::CS>(mono, tw_p1, tw_p2, d_tab, out, cfp0, step, cstride);                                                   \
  }
DIT_2P_FIXED(9, 3, 1)
DIT_2P_FIXED(9, 3, 2)
DIT_2P_FIXED(9, 3, 4)
DIT_2P_FIXED(9, 3, 8)
DIT_2P_FIXED(9, 3, 16)
DIT_2P_FIXED(10, 3, 1)
DIT_2P_FIXED(10, 3, 2)
DIT_2P_FIXED(10, 3, 4)
DIT_2P_FIXED(10, 3, 8)
DIT_2P_FIXED(10, 3, 16)
DIT_2P_FIXED(11, 3, 1)
DIT_2P_FIXED(11, 3, 2)
DIT_2P_FIXED(11, 3, 4)
DIT_2P_FIXED(11, 3, 8)
DIT_2P_FIXED(11, 3, 16)
DIT_2P_FIXED(12, 3, 1)
DIT_2P_FIXED(12, 3, 2)
DIT_2P_FIXED(12, 3, 4)
DIT_2P_FIXED(12, 3, 8)
DIT_2P_FIXED(12, 3, 16)
DIT_2P_FIXED(13, 3, 1)
DIT_2P_FIXED(13, 3, 2)
DIT_2P_FIXED(13, 3, 4)
DIT_2P_FIXED(13, 3, 8)
DIT_2P_FIXED(13, 3, 16)
DIT_2P_FIXED(8, 2, 1)
DIT_2P_FIXED(8, 2, 2)
DIT_2P_FIXED(8, 2, 4)
DIT_2P_FIXED(8, 2, 8)
DIT_2P_FIXED(8, 2, 16)
DIT_2P_FIXED(9, 2, 1)
DIT_2P_FIXED(9, 2, 2)
DIT_2P_FIXED(9, 2, 4)
DIT_2P_FIXED(9, 2, 8)
DIT_2P_FIXED(9, 2, 16)
DIT_2P_FIXED(10, 2, 1)
DIT_2P_FIXED(10, 2, 2)
DIT_2P_FIXED(10, 2, 4)
DIT_2P_FIXED(10, 2, 8)
DIT_2P_FIXED(10, 2, 16)
DIT_2P_FIXED(11, 2, 1)
DIT_2P_FIXED(11, 2, 2)
DIT_2P_FIXED(11, 2, 4)
DIT_2P_FIXED(11, 2, 8)
DIT_2P_FIXED(11, 2, 16)
DIT_2P_FIXED(12, 2, 1)
DIT_2P_FIXED(12, 2, 2)
DIT_2P_FIXED(12, 2, 4)
DIT_2P_FIXED(12, 2, 8)
DIT_2P_FIXED(12, 2, 16)
#undef DIT_2P_FIXED
// The bench's Bench1pStream bindings link the ab_dit_single_stream_* symbols,
// which are the production single-pass launch path defined in dit_kernels_extern.cu.
#define DIT_1P_FIXED(LOGN, LOGVPT, K)                                                                                                                          \
  EXTERN __launch_bounds__(4u * 32u)                                                                                                                           \
      __global__ void ab_dit_single_fixed_##LOGN##_##LOGVPT##_##K(const bf *mono, const bf *tw_clean, bf *out, u32 cfp0, u32 step, u32 cstride) {              \
    ntt_single<LOGN, LOGVPT, 4u, K, StoreMode::CS>(mono, tw_clean, out, cfp0, step, cstride);                                                                  \
  }
DIT_1P_FIXED(3, 3, 1)
DIT_1P_FIXED(3, 3, 2)
DIT_1P_FIXED(3, 3, 4)
DIT_1P_FIXED(3, 3, 8)
DIT_1P_FIXED(3, 3, 16)
DIT_1P_FIXED(4, 3, 1)
DIT_1P_FIXED(4, 3, 2)
DIT_1P_FIXED(4, 3, 4)
DIT_1P_FIXED(4, 3, 8)
DIT_1P_FIXED(4, 3, 16)
DIT_1P_FIXED(5, 3, 1)
DIT_1P_FIXED(5, 3, 2)
DIT_1P_FIXED(5, 3, 4)
DIT_1P_FIXED(5, 3, 8)
DIT_1P_FIXED(5, 3, 16)
DIT_1P_FIXED(6, 3, 1)
DIT_1P_FIXED(6, 3, 2)
DIT_1P_FIXED(6, 3, 4)
DIT_1P_FIXED(6, 3, 8)
DIT_1P_FIXED(6, 3, 16)
DIT_1P_FIXED(7, 3, 1)
DIT_1P_FIXED(7, 3, 2)
DIT_1P_FIXED(7, 3, 4)
DIT_1P_FIXED(7, 3, 8)
DIT_1P_FIXED(7, 3, 16)
DIT_1P_FIXED(8, 3, 1)
DIT_1P_FIXED(8, 3, 2)
DIT_1P_FIXED(8, 3, 4)
DIT_1P_FIXED(8, 3, 8)
DIT_1P_FIXED(8, 3, 16)
DIT_1P_FIXED(2, 2, 1)
DIT_1P_FIXED(2, 2, 2)
DIT_1P_FIXED(2, 2, 4)
DIT_1P_FIXED(2, 2, 8)
DIT_1P_FIXED(2, 2, 16)
DIT_1P_FIXED(3, 2, 1)
DIT_1P_FIXED(3, 2, 2)
DIT_1P_FIXED(3, 2, 4)
DIT_1P_FIXED(3, 2, 8)
DIT_1P_FIXED(3, 2, 16)
DIT_1P_FIXED(4, 2, 1)
DIT_1P_FIXED(4, 2, 2)
DIT_1P_FIXED(4, 2, 4)
DIT_1P_FIXED(4, 2, 8)
DIT_1P_FIXED(4, 2, 16)
DIT_1P_FIXED(5, 2, 1)
DIT_1P_FIXED(5, 2, 2)
DIT_1P_FIXED(5, 2, 4)
DIT_1P_FIXED(5, 2, 8)
DIT_1P_FIXED(5, 2, 16)
DIT_1P_FIXED(6, 2, 1)
DIT_1P_FIXED(6, 2, 2)
DIT_1P_FIXED(6, 2, 4)
DIT_1P_FIXED(6, 2, 8)
DIT_1P_FIXED(6, 2, 16)
DIT_1P_FIXED(7, 2, 1)
DIT_1P_FIXED(7, 2, 2)
DIT_1P_FIXED(7, 2, 4)
DIT_1P_FIXED(7, 2, 8)
DIT_1P_FIXED(7, 2, 16)
#undef DIT_1P_FIXED
} // namespace ntt
} // namespace airbender
