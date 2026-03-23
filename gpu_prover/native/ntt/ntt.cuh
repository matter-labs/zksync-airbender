#include "../primitives/field.cuh"
#include "../primitives/memory.cuh"
#include "context.cuh"
#include <cuda_pipeline.h>

namespace airbender::ntt {

using bf = base_field;

// bank-conflict-free swizzling pattern from https://www.nvidia.com/en-us/on-demand/session/gtc24-s62400/ slide 92
DEVICE_FORCEINLINE int xy_to_swizzled(const int x, const int y) {
  constexpr int BANKS = 32;
  constexpr int BANK_MASK = BANKS - 1;
  return y * BANKS + ((y & BANK_MASK) ^ x);
}

DEVICE_FORCEINLINE int linear_to_swizzled(const int i) {
  constexpr int LOG_BANKS = 5;
  constexpr int BANKS = 1 << LOG_BANKS;
  constexpr int BANK_MASK = BANKS - 1;
  return xy_to_swizzled(i & BANK_MASK, i >> LOG_BANKS);
}

// helper for dealing with intermediate transposed monomials
DEVICE_FORCEINLINE int transposed_row_to_effective_row(const int row) {
  constexpr int ROW_SIZE = 32;
  constexpr int ROW_MASK = ROW_SIZE - 1;
  constexpr int CHUNK_MASK = 1023;
  const int x_in_chunk = row & ROW_MASK;
  const int y_in_chunk = (row & CHUNK_MASK) >> 5;
  const int effective_row = (row & (~CHUNK_MASK)) + ROW_SIZE * x_in_chunk + y_in_chunk;
  return effective_row;
}

// This is a little tricky:
// it assumes "i" NEEDS to be bitreved and accounts for that by assuming "fine" and "coarse"
// arrays are already bitreved.
template <const bf *coarse_powers, const bf *fine_powers> DEVICE_FORCEINLINE bf get_cmem_twiddle(const int i) {
  int fine_idx = (i >> CMEM_COARSE_LOG_COUNT) & CMEM_FINE_MASK;
  int coarse_idx = i & CMEM_COARSE_MASK;
  const bf coarse = *(coarse_powers + coarse_idx);
  if (fine_idx == 0)
    return coarse;
  const bf fine = *(fine_powers + fine_idx);
  return bf::mul(fine, coarse);
}

struct TenStages {
  static constexpr int COARSE_LOG_COUNT = 13;
  static constexpr int COARSE_MASK = MASK_13;
  static constexpr int FINE_LOG_COUNT = 10;
  static constexpr int FINE_MASK = MASK_10;
};

struct EightStages {
  static constexpr int COARSE_LOG_COUNT = 12;
  static constexpr int COARSE_MASK = MASK_12;
  static constexpr int FINE_LOG_COUNT = 11;
  static constexpr int FINE_MASK = MASK_11;
};

template <typename T, const bf *fine_powers> DEVICE_FORCEINLINE bf get_cmem_smem_twiddle(const int i, const bf *coarse_powers) {
  int fine_idx = (i >> T::COARSE_LOG_COUNT) & T::FINE_MASK;
  int coarse_idx = i & T::COARSE_MASK;
  const bf coarse = *(coarse_powers + linear_to_swizzled(coarse_idx));
  if (fine_idx == 0)
    return coarse;
  const bf fine = *(fine_powers + fine_idx);
  // const bf fine = *(fine_powers + fine_idx);
  return bf::mul(fine, coarse);
}

DEVICE_FORCEINLINE void exchg_dit_0(bf &a, bf &b) {
  const auto a_tmp = a;
  a = bf::add(a_tmp, b);
  b = bf::sub(a_tmp, b);
}

DEVICE_FORCEINLINE void exchg_dit(bf &a, bf &b, const bf &twiddle) {
  b = bf::mul(b, twiddle);
  const auto a_tmp = a;
  a = bf::add(a_tmp, b);
  b = bf::sub(a_tmp, b);
}

DEVICE_FORCEINLINE void exchg_dif_0(bf &a, bf &b) {
  const auto a_tmp = a;
  a = bf::add(a_tmp, b);
  b = bf::sub(a_tmp, b);
}

DEVICE_FORCEINLINE void exchg_dif(bf &a, bf &b, const bf &twiddle) {
  const auto a_tmp = a;
  a = bf::add(a_tmp, b);
  b = bf::sub(a_tmp, b);
  b = bf::mul(b, twiddle);
}

template <typename T, int STRIDE, int REGION_SIZE, int NUM_REGIONS, const bf *cmem_twiddles>
DEVICE_FORCEINLINE void reg_exchg_cmem_smem_twiddles_inv(bf *vals, const int exchg_region_offset, const bf *smem_twiddles) {
#pragma unroll
  for (int region{0}; region < NUM_REGIONS; region++) {
    const bf twiddle = get_cmem_smem_twiddle<T, cmem_twiddles>(exchg_region_offset + region, smem_twiddles);
    const int region_offset = region * REGION_SIZE;
#pragma unroll
    for (int lane_in_region{0}; lane_in_region < STRIDE; lane_in_region++) {
      const int i = region_offset + lane_in_region;
      exchg_dit(vals[i], vals[i + STRIDE], twiddle);
    }
  }
}

template <int STRIDE, int REGION_SIZE, int NUM_REGIONS> DEVICE_FORCEINLINE void reg_exchg_cmem_twiddles_inv(bf *vals, const int exchg_region_offset) {
#pragma unroll
  for (int region{0}; region < NUM_REGIONS; region++) {
    const bf twiddle = get_cmem_twiddle<ab_inv_cmem_twiddles_coarse, ab_inv_cmem_twiddles_fine>(exchg_region_offset + region);
    const int region_offset = region * REGION_SIZE;
#pragma unroll
    for (int lane_in_region{0}; lane_in_region < STRIDE; lane_in_region++) {
      const int i = region_offset + lane_in_region;
      exchg_dit(vals[i], vals[i + STRIDE], twiddle);
    }
  }
}

template <int STRIDE, int REGION_SIZE, int NUM_REGIONS> DEVICE_FORCEINLINE void reg_exchg_inv(bf *vals, const int exchg_region_offset) {
#pragma unroll
  for (int region{0}; region < NUM_REGIONS; region++) {
    const bf twiddle = ab_inv_cmem_twiddles_coarse[exchg_region_offset + region];
    const int region_offset = region * REGION_SIZE;
#pragma unroll
    for (int lane_in_region{0}; lane_in_region < STRIDE; lane_in_region++) {
      const int i = region_offset + lane_in_region;
      exchg_dit(vals[i], vals[i + STRIDE], twiddle);
    }
  }
}

template <int STRIDE, int REGION_SIZE, int NUM_REGIONS> DEVICE_FORCEINLINE void reg_exchg_hypercube_inv(bf *vals) {
#pragma unroll
  for (int region{0}; region < NUM_REGIONS; region++) {
    const int region_offset = region * REGION_SIZE;
#pragma unroll
    for (int lane_in_region{0}; lane_in_region < STRIDE; lane_in_region++) {
      const int i = region_offset + lane_in_region;
      vals[i + STRIDE] = bf::sub(vals[i + STRIDE], vals[i]);
    }
  }
}

template <typename T, int STRIDE, int REGION_SIZE, int NUM_REGIONS, const bf *cmem_twiddles>
DEVICE_FORCEINLINE void reg_exchg_cmem_smem_twiddles_fwd(bf *vals, const int exchg_region_offset, const bf *smem_twiddles) {
#pragma unroll
  for (int region{0}; region < NUM_REGIONS; region++) {
    const bf twiddle = get_cmem_smem_twiddle<T, cmem_twiddles>(exchg_region_offset + region, smem_twiddles);
    const int region_offset = region * REGION_SIZE;
#pragma unroll
    for (int lane_in_region{0}; lane_in_region < STRIDE; lane_in_region++) {
      const int i = region_offset + lane_in_region;
      exchg_dif(vals[i], vals[i + STRIDE], twiddle);
    }
  }
}

template <int STRIDE, int REGION_SIZE, int NUM_REGIONS> DEVICE_FORCEINLINE void reg_exchg_cmem_twiddles_fwd(bf *vals, const int exchg_region_offset) {
#pragma unroll
  for (int region{0}; region < NUM_REGIONS; region++) {
    const bf twiddle = get_cmem_twiddle<ab_fwd_cmem_twiddles_coarse, ab_fwd_cmem_twiddles_fine>(exchg_region_offset + region);
    const int region_offset = region * REGION_SIZE;
#pragma unroll
    for (int lane_in_region{0}; lane_in_region < STRIDE; lane_in_region++) {
      const int i = region_offset + lane_in_region;
      exchg_dif(vals[i], vals[i + STRIDE], twiddle);
    }
  }
}

template <int STRIDE, int REGION_SIZE, int NUM_REGIONS> DEVICE_FORCEINLINE void reg_exchg_fwd(bf *vals, const int exchg_region_offset) {
#pragma unroll
  for (int region{0}; region < NUM_REGIONS; region++) {
    const bf twiddle = ab_fwd_cmem_twiddles_coarse[exchg_region_offset + region];
    const int region_offset = region * REGION_SIZE;
#pragma unroll
    for (int lane_in_region{0}; lane_in_region < STRIDE; lane_in_region++) {
      const int i = region_offset + lane_in_region;
      exchg_dif(vals[i], vals[i + STRIDE], twiddle);
    }
  }
}

template <int STRIDE, int REGION_SIZE, int NUM_REGIONS> DEVICE_FORCEINLINE void reg_exchg_fwd(bf *vals) {
#pragma unroll
  for (int region{0}; region < NUM_REGIONS; region++) {
    const bf twiddle = ab_fwd_cmem_twiddles_coarse[region];
    const int region_offset = region * REGION_SIZE;
#pragma unroll
    for (int lane_in_region{0}; lane_in_region < STRIDE; lane_in_region++) {
      const int i = region_offset + lane_in_region;
      exchg_dif(vals[i], vals[i + STRIDE], twiddle);
    }
  }
}

template <int STRIDE> DEVICE_FORCEINLINE void reg_exchg_final_fwd(bf *vals) {
#pragma unroll
  for (int i{0}; i < STRIDE; i++)
    exchg_dif_0(vals[i], vals[i + STRIDE]);
}

template <int GROUP> DEVICE_FORCEINLINE void exchg_pipeline_group(bf *vals, const bf twiddle) {
  exchg_dit_0(vals[GROUP], vals[GROUP + 16]);
  exchg_dit_0(vals[GROUP + 8], vals[GROUP + 24]);
  exchg_dit_0(vals[GROUP], vals[GROUP + 8]);
  exchg_dit(vals[GROUP + 16], vals[GROUP + 24], twiddle);
}

template <int GROUP> DEVICE_FORCEINLINE void exchg_pipeline_group_hypercube(bf *vals) {
  vals[GROUP + 16] = bf::sub(vals[GROUP + 16], vals[GROUP]);
  vals[GROUP + 24] = bf::sub(vals[GROUP + 24], vals[GROUP + 8]);
  vals[GROUP + 8] = bf::sub(vals[GROUP + 8], vals[GROUP]);
  vals[GROUP + 24] = bf::sub(vals[GROUP + 24], vals[GROUP + 16]);
}

template <int GROUP, int IL_GMEM_STRIDE, int PL_GROUP_SIZE, int PL_STRIDE>
DEVICE_FORCEINLINE void prefetch_pipeline_group(bf *vals, const bf_matrix_getter<ld_modifier::cg> &gmem_in, const int thread_il_gmem_start) {
#pragma unroll
  for (int i{0}, row{thread_il_gmem_start + GROUP * IL_GMEM_STRIDE}; i < PL_GROUP_SIZE; i++, row += IL_GMEM_STRIDE * PL_STRIDE)
    vals[GROUP + i * PL_STRIDE] = gmem_in.get_at_row(row);
}

} // namespace airbender::ntt
