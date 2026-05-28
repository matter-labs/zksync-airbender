#include "../../common.cuh"
#include "../../ntt/context.cuh"
#include "../../primitives/field.cuh"
#include "../../primitives/memory.cuh"
#include "../../primitives/vectorized.cuh"

using namespace ::airbender::ntt;
using namespace ::airbender::primitives::field;
using namespace ::airbender::primitives::memory;
using namespace ::airbender::primitives::vectorized;

namespace airbender::prover::whir {

DEVICE_FORCEINLINE unsigned bitreverse_low_bits(const unsigned value, const unsigned num_bits) { return __brev(value) >> (32 - num_bits); }

EXTERN __launch_bounds__(512, 2)
__global__ void ab_pack_rows_for_whir_leaves_bf_kernel(vectorized_e4_matrix_getter<ld_modifier::cs> src,
                                                       vectorized_e4_matrix_setter<st_modifier::cs> dst,
                                                       const unsigned log_trace_len,
                                                       const unsigned log_lde_factor,
                                                       const unsigned log_values_per_leaf) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  const unsigned log_dst_rows_per_coset = log_trace_len - log_values_per_leaf;
  const unsigned coset = gid >> log_dst_rows_per_coset;
  const unsigned lane_in_coset_mask = (1 << log_dst_rows_per_coset) - 1;
  const unsigned dst_row = gid & lane_in_coset_mask;

  src.add_row(coset << log_trace_len);
  dst.add_row(gid);

  extern __shared__ uint8_t smem[];

  const unsigned dst_rows_per_coset = 1 << log_dst_rows_per_coset;
  const unsigned slot_in_leaf = 2 * threadIdx.y;
  const unsigned src_row_a = dst_row + bitreverse_low_bits(slot_in_leaf, log_values_per_leaf) * dst_rows_per_coset;
  const unsigned src_row_b = src_row_a + (dst_rows_per_coset << (log_values_per_leaf - 1));

  const e4 a = src.get_at_row(src_row_a);
  const e4 b = src.get_at_row(src_row_b);

  const unsigned coset_offset = bitreverse_low_bits(coset, log_lde_factor) << (OMEGA_LOG_ORDER - log_trace_len - log_lde_factor);
  bf x_inv = get_inverse_twiddle_power((src_row_a << (OMEGA_LOG_ORDER - log_trace_len)) + coset_offset);

  const bf two_inv_power = ab_inv_sizes[log_values_per_leaf];

  if (log_values_per_leaf == 1) {
    // We need to multiply by two_inv_power at some point. Might as well be here.
    const e4 c = e4::mul(two_inv_power, e4::add(a, b));
    const e4 d = e4::mul(bf::mul(x_inv, two_inv_power), e4::sub(a, b));

    dst.set_at_col(slot_in_leaf, c);
    dst.set_at_col(slot_in_leaf + 1, d);
  } else {
    e4* smem_thread = reinterpret_cast<e4 *>(smem) + threadIdx.x;
    bf* x_invs = reinterpret_cast<bf *>(smem + 2 * blockDim.x * blockDim.y * sizeof(e4)) + threadIdx.x;

    // We need to multiply by two_inv_power at some point. Might as well be here.
    smem_thread[blockDim.x * slot_in_leaf] = e4::mul(two_inv_power, e4::add(a, b));
    smem_thread[blockDim.x * (slot_in_leaf + 1)] = e4::mul(bf::mul(x_inv, two_inv_power), e4::sub(a, b));

    // Middle stages (stage enumeration runs from 0 to log_values_per_leaf - 1)
    for (unsigned stage = 1; stage < log_values_per_leaf - 1; stage++) {
      const unsigned exchg_stride = 1 << stage;
      const unsigned exchg_region = threadIdx.y >> stage;
      const unsigned exchg_lane = threadIdx.y & (exchg_stride - 1);
      const unsigned slot_in_leaf = 2 * exchg_stride * exchg_region + exchg_lane;

      // Exchange region leaders publish squared x_invs
      if (exchg_lane == 0) {
        x_inv = bf::sqr(x_inv);
        x_invs[blockDim.x * exchg_region] = x_inv;
      }
      // TODO: Evaluate performance impact of full syncthreads().
      // If it's bad, remap threads so exchanges happen within warps, with a swizzled access pattern to avoid bank conflicts.
      __syncthreads();
      const e4 a = smem_thread[blockDim.x * slot_in_leaf];
      const e4 b = smem_thread[blockDim.x * (slot_in_leaf + exchg_stride)];
      if (exchg_lane != 0)
        x_inv = x_invs[blockDim.x * exchg_region];
      __syncthreads();

      const e4 c = e4::add(a, b);
      const e4 d = e4::mul(x_inv, e4::sub(a, b));
      smem_thread[blockDim.x * slot_in_leaf] = c;
      smem_thread[blockDim.x * (slot_in_leaf + exchg_stride)] = d;
    }

    // Last stage (special cased to elide a bit of work)
    const unsigned stage = log_values_per_leaf - 1;
    const unsigned exchg_stride = 1 << stage;
    const unsigned slot_in_leaf = threadIdx.y;

    // Exchange region leader publishes squared x_inv
    if (threadIdx.y == 0) {
      x_inv = bf::sqr(x_inv);
      x_invs[0] = x_inv;
    }
    __syncthreads();
    if (threadIdx.y != 0)
      x_inv = x_invs[0];
    const e4 a = smem_thread[blockDim.x * slot_in_leaf];
    const e4 b = smem_thread[blockDim.x * (slot_in_leaf + exchg_stride)];

    const e4 c = e4::add(a, b);
    const e4 d = e4::mul(x_inv, e4::sub(a, b));
    dst.set_at_col(slot_in_leaf, c);
    dst.set_at_col(slot_in_leaf + exchg_stride, d);
  }
}

static constexpr unsigned MAX_VALS_PER_LEAF = 32;

template <unsigned LOG_VALUES_PER_LEAF>
DEVICE_FORCEINLINE void pack_rows_for_whir_leaves_impl(bf_matrix_getter<ld_modifier::cs> src,
                                                       bf_matrix_setter<st_modifier::cs> dst,
                                                       const bf high_power_offset,
                                                       const unsigned log_trace_len,
                                                       const unsigned log_lde_factor) {
  constexpr unsigned VALUES_PER_LEAF = 1 << LOG_VALUES_PER_LEAF;

  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  const unsigned log_dst_rows_per_coset = log_trace_len - LOG_VALUES_PER_LEAF;
  const unsigned coset = gid >> log_dst_rows_per_coset;
  const unsigned lane_in_coset_mask = (1 << log_dst_rows_per_coset) - 1;
  const unsigned dst_row = gid & lane_in_coset_mask;

  src.add_row(coset << log_trace_len);
  dst.add_row(gid);

  extern __shared__ bf x_invs_block[];
  bf *x_invs = x_invs_block + threadIdx.x;

  // Populate twiddles (x_invs) for reuse
  const unsigned coset_offset = bitreverse_low_bits(coset, log_lde_factor) << (OMEGA_LOG_ORDER - log_trace_len - log_lde_factor);
  bf x_inv =  get_inverse_twiddle_power((dst_row << (OMEGA_LOG_ORDER - log_trace_len)) + coset_offset);
  x_invs[0] = x_inv;
#pragma unroll
  for (unsigned src_slot_in_leaf = 1; src_slot_in_leaf < (VALUES_PER_LEAF >> 1); src_slot_in_leaf++) {
    const unsigned slot_in_leaf = bitreverse_low_bits(src_slot_in_leaf, LOG_VALUES_PER_LEAF - 1);
    x_inv = bf::mul(high_power_offset, x_inv);
    x_invs[blockDim.x * slot_in_leaf] = x_inv;
  }
  bf *x_invs_prev = x_invs;
#pragma unroll
  for (unsigned twiddles_prev_stage = VALUES_PER_LEAF >> 1; twiddles_prev_stage > 1; twiddles_prev_stage >>= 1) {
    bf *x_invs_current = x_invs_prev + blockDim.x * twiddles_prev_stage;
#pragma unroll
    for (unsigned i = 0; i < twiddles_prev_stage >> 1; i++) {
      x_invs_current[blockDim.x * i] = bf::sqr(x_invs_prev[blockDim.x * (2 * i)]);
    }
    x_invs_prev = x_invs_current;
  }

  bf vals[MAX_VALS_PER_LEAF];

  const unsigned dst_rows_per_coset = 1 << log_dst_rows_per_coset;
#pragma unroll 1
  for (unsigned c = 0; c < 4; c++) {
#pragma unroll
    for (unsigned slot_in_leaf = 0; slot_in_leaf < (1 << LOG_VALUES_PER_LEAF); slot_in_leaf += 2) {
      const unsigned src_row_a = dst_row + bitreverse_low_bits(slot_in_leaf, LOG_VALUES_PER_LEAF) * dst_rows_per_coset;
      const unsigned src_row_b = src_row_a + (dst_rows_per_coset << (LOG_VALUES_PER_LEAF - 1));

      vals[slot_in_leaf] = src.get(src_row_a, c);
      vals[slot_in_leaf + 1] = src.get(src_row_b, c);

      // We need to multiply by two_inv_power at some point. Might as well be here.
      vals[slot_in_leaf] = bf::mul(ab_inv_sizes[LOG_VALUES_PER_LEAF], vals[slot_in_leaf]);
      vals[slot_in_leaf + 1] = bf::mul(ab_inv_sizes[LOG_VALUES_PER_LEAF], vals[slot_in_leaf + 1]);
    }

    bf *x_invs_current = x_invs;
#pragma unroll
    for (unsigned stage = 0; stage < LOG_VALUES_PER_LEAF; stage++) {
      const unsigned exchg_stride = 1 << stage;
      const unsigned num_exchg_regions = VALUES_PER_LEAF >> (stage + 1);
      for (unsigned i = 0; i < num_exchg_regions; i++) {
        const bf x_inv = x_invs_current[blockDim.x * i];
        const unsigned region_start = 2 * i * exchg_stride;
        for (unsigned j = 0; j < exchg_stride; j++) {
          const bf a = vals[region_start + j];
          const bf b = vals[region_start + j + exchg_stride];
          vals[region_start + j] = bf::add(a, b);
          vals[region_start + j + exchg_stride] = bf::mul(x_inv, bf::sub(a, b));
        }
      }
      x_invs_current += blockDim.x * num_exchg_regions;
    }

#pragma unroll
    for (unsigned slot_in_leaf = 0; slot_in_leaf < VALUES_PER_LEAF; slot_in_leaf++)
      dst.set_at_col(4 * slot_in_leaf + c, vals[slot_in_leaf]);
  }
}


EXTERN __launch_bounds__(128, 6)
__global__ void ab_pack_rows_for_whir_leaves_1(bf_matrix_getter<ld_modifier::cs> src,
                                               bf_matrix_setter<st_modifier::cs> dst,
                                               const bf high_power_offset,
                                               const unsigned log_trace_len,
                                               const unsigned log_lde_factor) {
  pack_rows_for_whir_leaves_impl<1>(src, dst, high_power_offset, log_trace_len, log_lde_factor);
}

EXTERN __launch_bounds__(128, 6)
__global__ void ab_pack_rows_for_whir_leaves_2(bf_matrix_getter<ld_modifier::cs> src,
                                               bf_matrix_setter<st_modifier::cs> dst,
                                               const bf high_power_offset,
                                               const unsigned log_trace_len,
                                               const unsigned log_lde_factor) {
  pack_rows_for_whir_leaves_impl<2>(src, dst, high_power_offset, log_trace_len, log_lde_factor);
}

EXTERN __launch_bounds__(128, 6)
__global__ void ab_pack_rows_for_whir_leaves_3(bf_matrix_getter<ld_modifier::cs> src,
                                               bf_matrix_setter<st_modifier::cs> dst,
                                               const bf high_power_offset,
                                               const unsigned log_trace_len,
                                               const unsigned log_lde_factor) {
  pack_rows_for_whir_leaves_impl<3>(src, dst, high_power_offset, log_trace_len, log_lde_factor);
}

EXTERN __launch_bounds__(128, 6)
__global__ void ab_pack_rows_for_whir_leaves_4(bf_matrix_getter<ld_modifier::cs> src,
                                               bf_matrix_setter<st_modifier::cs> dst,
                                               const bf high_power_offset,
                                               const unsigned log_trace_len,
                                               const unsigned log_lde_factor) {
  pack_rows_for_whir_leaves_impl<4>(src, dst, high_power_offset, log_trace_len, log_lde_factor);
}

EXTERN __launch_bounds__(128, 6)
__global__ void ab_pack_rows_for_whir_leaves_5(bf_matrix_getter<ld_modifier::cs> src,
                                               bf_matrix_setter<st_modifier::cs> dst,
                                               const bf high_power_offset,
                                               const unsigned log_trace_len,
                                               const unsigned log_lde_factor) {
  pack_rows_for_whir_leaves_impl<5>(src, dst, high_power_offset, log_trace_len, log_lde_factor);
}

} // namespace airbender::prover::whir
