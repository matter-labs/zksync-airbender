#include "../context.cuh"
#include "../field.cuh"
#include "../memory.cuh"
#include "../vectorized.cuh"

using namespace ::airbender::field;
using namespace ::airbender::memory;
using namespace ::airbender::vectorized;

namespace airbender::ntt {

using bf = base_field;
using e2f = ext2_field;
using e4f = ext2_field;

DEVICE_FORCEINLINE unsigned bitrev(const unsigned idx, const unsigned log_n) { return __brev(idx) >> (32 - log_n); }

// Load-store helpers convenient when working with ALGO: TWO-FOR-ONE FFT ALGORITHM
// Specifically, these come in handy for
// Loading real x[n], y[n] cols to a single complex z[n]
// Storing output x[n], y[n] real evals from a single complex z[n]
DEVICE_FORCEINLINE e2f load_one_maybe_vectorized(const bf *gmem_in, const unsigned stride, bool is_odd_tail) {
  const auto c0 = memory::load_cg(gmem_in);
  const auto c1 = is_odd_tail ? bf{0} : memory::load_cg(gmem_in + stride);
  return e2f{c0, c1};
}

DEVICE_FORCEINLINE e2f load_one_maybe_vectorized(const e2f *gmem_in, const unsigned stride, bool is_odd_tail) { return memory::load_cg(gmem_in); }

DEVICE_FORCEINLINE void load_two_vectorized_complex(const bf *gmem_in, e2f &val0, e2f &val1, const unsigned stride, bool is_odd_tail) {
  const auto c0s = memory::load_cg(reinterpret_cast<const uint2 *>(gmem_in));
  uint2 c1s{0, 0};
  if (!is_odd_tail) {
    c1s = memory::load_cg(reinterpret_cast<const uint2 *>(gmem_in + stride));
  }
  val0 = e2f{bf{c0s.x}, bf{c1s.x}};
  val1 = e2f{bf{c0s.y}, bf{c1s.y}};
}

DEVICE_FORCEINLINE void store_one_maybe_vectorized(bf *gmem_out, const e2f val, const unsigned stride, bool is_odd_tail) {
  memory::store_cg(gmem_out, val[0]);
  if (!is_odd_tail)
    memory::store_cg(gmem_out + stride, val[1]);
}

DEVICE_FORCEINLINE void store_one_maybe_vectorized(e2f *gmem_out, const e2f val, const unsigned stride, bool is_odd_tail) { memory::store_cg(gmem_out, val); }

DEVICE_FORCEINLINE void store_two_vectorized_complex(bf *gmem_out, const e2f val0, const e2f val1, const unsigned stride, bool is_odd_tail) {
  const uint2 c0s{val0[0].limb, val1[0].limb};
  memory::store_cg(reinterpret_cast<uint2 *>(gmem_out), c0s);
  if (!is_odd_tail) {
    const uint2 c1s{val0[1].limb, val1[1].limb};
    memory::store_cg(reinterpret_cast<uint2 *>(gmem_out + stride), c1s);
  }
}

DEVICE_FORCEINLINE void exchg_dit(e2f &a, e2f &b, const e2f &twiddle) {
  b = e2f::mul(b, twiddle);
  const auto a_tmp = a;
  a = e2f::add(a_tmp, b);
  b = e2f::sub(a_tmp, b);
}

DEVICE_FORCEINLINE void exchg_dif(e2f &a, e2f &b, const e2f &twiddle) {
  const auto a_tmp = a;
  a = e2f::add(a_tmp, b);
  b = e2f::sub(a_tmp, b);
  b = e2f::mul(b, twiddle);
}

// This is a little tricky:
// it assumes "i" NEEDS to be bitreved and accounts for that by assuming "fine" and "coarse"
// arrays are already bitreved.
template <bool inverse> DEVICE_FORCEINLINE e2f get_twiddle(const unsigned i) {
  const powers_data_2_layer &data = inverse ? ab_powers_data_w_inv_bitrev_for_ntt : ab_powers_data_w_bitrev_for_ntt;
  unsigned fine_idx = (i >> data.coarse.log_count) & data.fine.mask;
  unsigned coarse_idx = i & data.coarse.mask;
  auto coarse = memory::load_ca(data.coarse.values + coarse_idx);
  if (fine_idx == 0)
    return coarse;
  auto fine = memory::load_ca(data.fine.values + fine_idx);
  return e2f::mul(fine, coarse);
}

DEVICE_FORCEINLINE void shfl_xor_e2f(e2f *vals, const unsigned i, const unsigned lane_id, const unsigned lane_mask) {
  // Some threads need to post vals[2 * i], others need to post vals[2 * i + 1].
  // We use a temporary to avoid calling shfls divergently, which is unsafe on pre-Volta.
  e2f tmp{};
  if (lane_id & lane_mask)
    tmp = vals[2 * i];
  else
    tmp = vals[2 * i + 1];
  tmp[0].limb = __shfl_xor_sync(0xffffffff, tmp[0].limb, lane_mask);
  tmp[1].limb = __shfl_xor_sync(0xffffffff, tmp[1].limb, lane_mask);
  if (lane_id & lane_mask)
    vals[2 * i] = tmp;
  else
    vals[2 * i + 1] = tmp;
}

template <unsigned VALS_PER_WARP, unsigned LOG_VALS_PER_THREAD, bool inverse>
DEVICE_FORCEINLINE void load_initial_twiddles_warp(e2f *twiddle_cache, const unsigned lane_id, const unsigned gmem_offset) {
  // cooperatively loads all the twiddles this warp needs for intrawarp stages
  e2f *twiddles_this_stage = twiddle_cache;
  unsigned num_twiddles_this_stage = VALS_PER_WARP >> 1;
  unsigned exchg_region_offset = gmem_offset >> 1;
#pragma unroll
  for (unsigned stage = 0; stage < LOG_VALS_PER_THREAD; stage++) {
#pragma unroll
    for (unsigned i = lane_id; i < num_twiddles_this_stage; i += 32) {
      twiddles_this_stage[i] = get_twiddle<inverse>(i + exchg_region_offset);
    }
    twiddles_this_stage += num_twiddles_this_stage;
    num_twiddles_this_stage >>= 1;
    exchg_region_offset >>= 1;
  }

  // loads final 31 twiddles with minimal divergence. pain.
  const unsigned lz = __clz(lane_id);
  const unsigned stage_offset = 5 - (32 - lz);
  const unsigned mask = (1u << (32 - lz)) - 1;
  if (lane_id > 0) {
    exchg_region_offset >>= stage_offset;
    twiddles_this_stage[lane_id ^ 31] = get_twiddle<inverse>((lane_id ^ mask) + exchg_region_offset);
  }

  __syncwarp();
}

template <unsigned LOG_VALS_PER_THREAD, bool inverse>
DEVICE_FORCEINLINE void load_noninitial_twiddles_warp(e2f *twiddle_cache, const unsigned lane_id, const unsigned warp_id,
                                                      const unsigned block_exchg_region_offset) {
  // cooperatively loads all the twiddles this warp needs for intrawarp stages
  static_assert(LOG_VALS_PER_THREAD <= 4);
  constexpr unsigned NUM_INTRAWARP_STAGES = LOG_VALS_PER_THREAD + 1;

  // tile size 16: num twiddles = vals per warp / 2 / 16 == vals per thread
  unsigned num_twiddles_first_stage = 1u << LOG_VALS_PER_THREAD;
  unsigned exchg_region_offset = block_exchg_region_offset + warp_id * num_twiddles_first_stage;

  // loads 2 * num_twiddles_first_stage - 1 twiddles with minimal divergence. pain.
  if (lane_id > 0 && lane_id < 2 * num_twiddles_first_stage) {
    const unsigned lz = __clz(lane_id);
    const unsigned stage_offset = NUM_INTRAWARP_STAGES - (32 - lz);
    const unsigned mask = (1u << (32 - lz)) - 1;
    exchg_region_offset >>= stage_offset;
    twiddle_cache[lane_id ^ (2 * num_twiddles_first_stage - 1)] = get_twiddle<inverse>((lane_id ^ mask) + exchg_region_offset);
  }

  __syncwarp();
}

// Assumes coset_idx > 0
DEVICE_FORCEINLINE e2f get_lde_scale_and_shift_factor(const unsigned k, const unsigned log_extension_degree, const unsigned coset_idx, const unsigned log_n) {
  // following the notation of https://eprint.iacr.org/2023/824.pdf Section 4
  const unsigned tau_power_of_w = coset_idx << (CIRCLE_GROUP_LOG_ORDER - log_n - log_extension_degree);
  const unsigned H_over_two = 1u << (log_n - 1);
  const unsigned power_of_w = k >= H_over_two ? tau_power_of_w * (k - H_over_two) : (1u << CIRCLE_GROUP_LOG_ORDER) - tau_power_of_w * (H_over_two - k);
  return get_power_of_w(power_of_w, false);
}

DEVICE_FORCEINLINE e2f lde_scale_and_shift(const e2f Zk, const unsigned k, const unsigned log_extension_degree, const unsigned coset_idx,
                                           const unsigned log_n) {
  // Assumes the 0th coset is the main domain, as in zksync_airbender
  if (coset_idx == 0)
    return Zk;
  const auto gauged_shift_factor = get_lde_scale_and_shift_factor(k, log_extension_degree, coset_idx, log_n);
  return e2f::mul(Zk, gauged_shift_factor);
}

template <bool inverse = false>
DEVICE_FORCEINLINE e2f lde_scale(const e2f Zk, const unsigned k, const unsigned log_extension_degree, const unsigned coset_idx, const unsigned log_n) {
  // Assumes the 0th coset is the main domain, as in zksync_airbender
  if (coset_idx == 0)
    return Zk;
  const unsigned tau_power_of_w = coset_idx << (CIRCLE_GROUP_LOG_ORDER - log_n - log_extension_degree);
  const auto scale_factor = get_power_of_w(k * tau_power_of_w, inverse);
  return e2f::mul(Zk, scale_factor);
}

template <typename T> struct COLS_PER_BLOCK {};
template <> struct COLS_PER_BLOCK<bf> {
  static constexpr unsigned VAL = 8;
};
template <> struct COLS_PER_BLOCK<e2f> {
  static constexpr unsigned VAL = 4;
};

template <typename T> struct COLS_INC {};
template <> struct COLS_INC<bf> {
  static constexpr unsigned VAL = 2;
};
template <> struct COLS_INC<e2f> {
  static constexpr unsigned VAL = 1;
};

} // namespace airbender::ntt
