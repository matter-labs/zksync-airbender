// Adapted from PR #493 (gpu/ntt/native/natural_monomials_to_bitrev_evals_proth120.cu).
#pragma once
#include "context.cuh"

namespace airbender::ntt {

struct dit_policy {
  proth120_twiddle_descriptor descriptor;
  static constexpr bool USES_TWIDDLES = true;
  DEVICE_FORCEINLINE void exchg(pr &a, pr &b, const pr twiddle) const {
    b = pr::mul(b, twiddle);
    const pr t = a;
    a = pr::add(t, b);
    b = pr::sub(t, b);
  }
  DEVICE_FORCEINLINE void exchg_0(pr &a, pr &b) const {
    const pr t = a;
    a = pr::add(t, b);
    b = pr::sub(t, b);
  }
};

struct mobius_policy {
  static constexpr bool USES_TWIDDLES = false;
  DEVICE_FORCEINLINE void exchg(pr &a, pr &b, const pr) const { b = pr::sub(b, a); }
  DEVICE_FORCEINLINE void exchg_0(pr &a, pr &b) const { b = pr::sub(b, a); }
};

struct chunk_map {
  u32 strip_base;
  u32 strip_blocks;
  u32 strip_domain_bits;
};

static_assert(sizeof(chunk_map) == 12);

struct coset_scale {
  const u32 *coset;
  u32 k0;
  u32 batched;
  u32 log_domain;
  u32 reserved;
};

static_assert(sizeof(coset_scale) == 24);

DEVICE_FORCEINLINE u32 coset_scale_index(const coset_scale &s) { return (s.coset ? *s.coset : s.k0) + (s.batched ? blockIdx.z : 0); }

// offset_k^row with offset_k = w_D^k = w_L^(k << (L - D)), natural coefficient index `row`.
DEVICE_FORCEINLINE pr coset_scale_power(const proth120_twiddle_descriptor &d, const coset_scale &s, const u32 k, const u32 row) {
  const u64 mask = (u64{1} << d.log_max_domain) - 1;
  return pr_root_power(d, ((static_cast<u64>(k) * row) << (d.log_max_domain - s.log_domain)) & mask);
}

DEVICE_FORCEINLINE u32 chunk_block_y(const chunk_map &m) {
  return ((blockIdx.y / m.strip_blocks) << m.strip_domain_bits) | (m.strip_base + blockIdx.y % m.strip_blocks);
}

template <class P> DEVICE_FORCEINLINE void exchange(const P &policy, pr &a, pr &b, const u32 region) {
  if constexpr (P::USES_TWIDDLES)
    policy.exchg(a, b, get_forward_pr_twiddle(policy.descriptor, region));
  else
    policy.exchg_0(a, b);
}

template <class P> DEVICE_FORCEINLINE void exchange_two(const P &policy, pr &a, pr &b, pr &c, pr &d, const u32 region) {
  if constexpr (P::USES_TWIDDLES) {
    const pr twiddle = get_forward_pr_twiddle(policy.descriptor, region);
    policy.exchg(a, b, twiddle);
    policy.exchg(c, d, twiddle);
  } else {
    policy.exchg_0(a, b);
    policy.exchg_0(c, d);
  }
}

template <int VALS_PER_THREAD, int STAGES_SO_FAR_THIS_LAUNCH, int VALS_PER_BLOCK, int LOG_THREADS_PER_BLOCK, bool SKIP_LAST = false, class P>
DEVICE_FORCEINLINE void do_2_smem_stages(pr *smem_block, const P &policy) {
  constexpr int LOG_SMEM_REGIONS_PER_BLOCK = STAGES_SO_FAR_THIS_LAUNCH;
  constexpr int SMEM_REGION_SIZE = VALS_PER_BLOCK >> LOG_SMEM_REGIONS_PER_BLOCK;
  constexpr int LOG_THREADS_PER_SMEM_REGION = LOG_THREADS_PER_BLOCK - STAGES_SO_FAR_THIS_LAUNCH;
  constexpr int THREADS_PER_SMEM_REGION = 1 << LOG_THREADS_PER_SMEM_REGION;
  const int smem_region = threadIdx.x >> LOG_THREADS_PER_SMEM_REGION;
  const int lane_in_smem_region = threadIdx.x & (THREADS_PER_SMEM_REGION - 1);
  pr *smem = smem_block + smem_region * SMEM_REGION_SIZE;
  pr vals[VALS_PER_THREAD];
#pragma unroll
  for (int i{0}, addr{lane_in_smem_region}; i < VALS_PER_THREAD; i++, addr += THREADS_PER_SMEM_REGION)
    vals[i] = smem[addr];
  int exchg_region = smem_region + (blockIdx.x << LOG_SMEM_REGIONS_PER_BLOCK);
  exchange_two(policy, vals[0], vals[2], vals[1], vals[3], exchg_region);
  if constexpr (!SKIP_LAST) {
    exchg_region <<= 1;
    exchange(policy, vals[0], vals[1], exchg_region);
    exchange(policy, vals[2], vals[3], exchg_region + 1);
  }
#pragma unroll
  for (int i{0}, addr{lane_in_smem_region}; i < VALS_PER_THREAD; i++, addr += THREADS_PER_SMEM_REGION)
    smem[addr] = vals[i];
  if (THREADS_PER_SMEM_REGION > 32)
    __syncthreads();
  else
    __syncwarp();
}

template <int STAGES, bool NARROW, class P, bool SCALE = false>
DEVICE_FORCEINLINE void nonfinal(pr_matrix_getter<ld_modifier::cg> gmem_in, pr_matrix_setter<st_modifier::cg> gmem_out, const P &policy, const u32 log_n,
                                 const u32 start_stage, const chunk_map map, const coset_scale scale = {}) {
  static_assert(!NARROW || (STAGES >= 5 && STAGES <= 7));
  constexpr int LOG_TILE_SIZE = 3;
  constexpr int TILE_SIZE = 1 << LOG_TILE_SIZE;
  constexpr int LOG_VALS_PER_THREAD = 2;
  constexpr int VALS_PER_THREAD = 1 << LOG_VALS_PER_THREAD;
  constexpr int LOG_TILES_PER_BLOCK = NARROW ? STAGES : 8;
  constexpr int LOG_VALS_PER_BLOCK = LOG_TILES_PER_BLOCK + LOG_TILE_SIZE;
  constexpr int LOG_THREADS_PER_BLOCK = LOG_VALS_PER_BLOCK - LOG_VALS_PER_THREAD;
  constexpr int VALS_PER_BLOCK = 1 << LOG_VALS_PER_BLOCK;
  const int exchg_region_size = 1 << (log_n - start_stage);
  const int tile_gmem_stride = exchg_region_size >> LOG_TILES_PER_BLOCK;
  const int tile_in_block = threadIdx.x >> LOG_TILE_SIZE;
  const int lane_in_tile = threadIdx.x & (TILE_SIZE - 1);
  __shared__ pr smem_block[VALS_PER_BLOCK];
  pr vals[VALS_PER_THREAD];
  gmem_in.add_col(blockIdx.z);
  gmem_out.add_col(blockIdx.z);
  int exchg_region = blockIdx.x;
  const int block_start_in_exchg_region = TILE_SIZE * chunk_block_y(map);
  const int block_start = exchg_region_size * exchg_region + block_start_in_exchg_region;
  gmem_in.add_row(block_start);
  gmem_out.add_row(block_start);
#pragma unroll
  for (int i{0}, addr{lane_in_tile + tile_in_block * tile_gmem_stride}; i < VALS_PER_THREAD; i++, addr += exchg_region_size >> LOG_VALS_PER_THREAD)
    vals[i] = gmem_in.get_at_row(addr);
  if constexpr (SCALE) {
    const u32 k = coset_scale_index(scale);
    if (k != 0) {
#pragma unroll
      for (int i{0}, addr{lane_in_tile + tile_in_block * tile_gmem_stride}; i < VALS_PER_THREAD; i++, addr += exchg_region_size >> LOG_VALS_PER_THREAD)
        vals[i] = pr::mul(vals[i], coset_scale_power(policy.descriptor, scale, k, block_start + addr));
    }
  }
  if (start_stage == 0) {
    policy.exchg_0(vals[0], vals[2]);
    policy.exchg_0(vals[1], vals[3]);
  } else {
    exchange_two(policy, vals[0], vals[2], vals[1], vals[3], exchg_region);
  }
  exchg_region <<= 1;
  exchange(policy, vals[0], vals[1], exchg_region);
  exchange(policy, vals[2], vals[3], exchg_region + 1);
#pragma unroll
  for (unsigned i{0}, addr{threadIdx.x}; i < VALS_PER_THREAD; i++, addr += blockDim.x)
    smem_block[addr] = vals[i];
  __syncthreads();
  do_2_smem_stages<4, 2, VALS_PER_BLOCK, LOG_THREADS_PER_BLOCK, false, P>(smem_block, policy);
  do_2_smem_stages<4, 4, VALS_PER_BLOCK, LOG_THREADS_PER_BLOCK, (STAGES == 5), P>(smem_block, policy);
  if constexpr (STAGES >= 7)
    do_2_smem_stages<4, 6, VALS_PER_BLOCK, LOG_THREADS_PER_BLOCK, (STAGES == 7), P>(smem_block, policy);
  const int warp_id = threadIdx.x >> 5;
  const int lane_id = threadIdx.x & 31;
  pr *smem_warp = smem_block + 32 * VALS_PER_THREAD * warp_id;
  constexpr int TILES_PER_STORE = 32 >> LOG_TILE_SIZE;
  constexpr int TILES_PER_WARP = (32 * VALS_PER_THREAD) >> LOG_TILE_SIZE;
  const int tile_in_store = lane_id >> LOG_TILE_SIZE;
  gmem_out.add_row(tile_gmem_stride * (tile_in_store + TILES_PER_WARP * warp_id) + lane_in_tile);
#pragma unroll
  for (int i{0}, addr_smem{lane_id}, addr_gmem{0}; i < VALS_PER_THREAD; i++, addr_smem += 32, addr_gmem += TILES_PER_STORE * tile_gmem_stride)
    gmem_out.set_at_row(addr_gmem, smem_warp[addr_smem]);
}

template <int LOG_THREADS_PER_BLOCK, int STAGES, class P>
DEVICE_FORCEINLINE void final(pr_matrix_getter<ld_modifier::cg> gmem_in, pr_matrix_setter<st_modifier::cg> gmem_out, const P &policy, const u32 log_n,
                              const u32 start_stage) {
  constexpr int LOG_VALS_PER_THREAD = 2;
  constexpr int VALS_PER_THREAD = 1 << LOG_VALS_PER_THREAD;
  constexpr int LOG_VALS_PER_BLOCK = LOG_THREADS_PER_BLOCK + LOG_VALS_PER_THREAD;
  constexpr int VALS_PER_BLOCK = 1 << LOG_VALS_PER_BLOCK;
  extern __shared__ pr smem_block[];
  pr vals[VALS_PER_THREAD];
  gmem_in.add_col(blockIdx.y);
  gmem_out.add_col(blockIdx.y);
  const int gmem_block_start = blockIdx.x * VALS_PER_BLOCK;
  gmem_in.add_row(gmem_block_start);
  gmem_out.add_row(gmem_block_start);
#pragma unroll
  for (unsigned i{0}, addr{threadIdx.x}; i < VALS_PER_THREAD; i++, addr += blockDim.x)
    vals[i] = gmem_in.get_at_row(addr);
  int exchg_region = blockIdx.x;
  exchange_two(policy, vals[0], vals[2], vals[1], vals[3], exchg_region);
  exchg_region <<= 1;
  exchange(policy, vals[0], vals[1], exchg_region);
  exchange(policy, vals[2], vals[3], exchg_region + 1);
#pragma unroll
  for (unsigned i{0}, addr{threadIdx.x}; i < VALS_PER_THREAD; i++, addr += blockDim.x)
    smem_block[addr] = vals[i];
  __syncthreads();
  do_2_smem_stages<4, 2, VALS_PER_BLOCK, LOG_THREADS_PER_BLOCK, false, P>(smem_block, policy);
  do_2_smem_stages<4, 4, VALS_PER_BLOCK, LOG_THREADS_PER_BLOCK, false, P>(smem_block, policy);
  do_2_smem_stages<4, 6, VALS_PER_BLOCK, LOG_THREADS_PER_BLOCK, false, P>(smem_block, policy);
  if constexpr (STAGES > 8)
    do_2_smem_stages<4, 8, VALS_PER_BLOCK, LOG_THREADS_PER_BLOCK, false, P>(smem_block, policy);
  if constexpr (STAGES > 10)
    do_2_smem_stages<4, 10, VALS_PER_BLOCK, LOG_THREADS_PER_BLOCK, false, P>(smem_block, policy);
  const int warp_id = threadIdx.x >> 5;
  const int lane_id = threadIdx.x & 31;
  pr *smem_warp = smem_block + 32 * VALS_PER_THREAD * warp_id;
  gmem_out.add_row(32 * VALS_PER_THREAD * warp_id);
#pragma unroll
  for (int i{0}, addr{lane_id}; i < VALS_PER_THREAD; i++, addr += 32)
    gmem_out.set_at_row(addr, smem_warp[addr]);
}

template <class P>
DEVICE_FORCEINLINE void small(pr_matrix_getter<ld_modifier::cg> gmem_in, pr_matrix_setter<st_modifier::cg> gmem_out, const P &policy, const u32 log_n,
                              const u32 start_stage) {
  extern __shared__ pr smem_block[];
  const u32 n = 1u << log_n;
  const u32 t = threadIdx.x;
  gmem_in.add_col(blockIdx.y);
  gmem_out.add_col(blockIdx.y);
  for (u32 row = t; row < n; row += blockDim.x)
    smem_block[row] = gmem_in.get_at_row(row);
  __syncthreads();
  for (u32 stage = 0; stage < log_n; stage++) {
    const u32 half = n >> (stage + 1);
    for (u32 pair = t; pair < n / 2; pair += blockDim.x) {
      const u32 region = pair / half;
      const u32 j = pair & (half - 1);
      const u32 a = 2 * half * region + j;
      const u32 b = a + half;
      pr va = smem_block[a];
      pr vb = smem_block[b];
      exchange(policy, va, vb, (blockIdx.x << stage) + region);
      smem_block[a] = va;
      smem_block[b] = vb;
    }
    __syncthreads();
  }
  for (u32 row = t; row < n; row += blockDim.x)
    gmem_out.set_at_row(row, smem_block[row]);
}

} // namespace airbender::ntt
