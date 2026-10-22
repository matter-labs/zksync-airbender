// Adapted from PR #493 (gpu/ntt/native/natural_monomials_to_bitrev_evals_proth120.cu).
#pragma once
#include "context.cuh"

namespace airbender::ntt {

struct dit_policy {
  proth120_twiddle_descriptor descriptor;
  static constexpr bool USES_TWIDDLES = true;
  static constexpr bool LAZY = false;
  DEVICE_FORCEINLINE pr twiddle(const u32 region, const int) const { return get_forward_pr_twiddle(descriptor, region); }
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

// Unreduced butterflies inside one nonfinal pass: starting below 2p, a pass of s <= 8 stages keeps
// every value below (2 + 2s) p <= 18p < R / 2 (R = 2^128, p < R / 36), so `montmul_raw` of a value and
// a canonical twiddle stays below 2p and no limb sum wraps; the pass stores `proth_canonical` values.
struct lazy_dit_policy : dit_policy {
  static constexpr bool LAZY = true;
  static constexpr DEVICE_FORCEINLINE pr TWO_P() { return proth120_detail::MODULUS<2>(); }
  DEVICE_FORCEINLINE void exchg(pr &a, pr &b, const pr twiddle) const {
    pr product{};
    proth120_detail::montmul_raw(b, twiddle, product);
    exchg_0(a, product);
    b = product;
  }
  DEVICE_FORCEINLINE void exchg_0(pr &a, pr &b) const {
    pr sum{};
    pr shifted{};
    proth120_detail::add_limbs<false>(a, b, sum);
    proth120_detail::add_limbs<false>(a, TWO_P(), shifted);
    proth120_detail::sub_limbs<false>(shifted, b, b);
    a = sum;
  }
};

// x mod p for x < 2^128 - p, p = 7 * 2^120 + 1: with x = h * 2^120 + l, h = 7q + t (t < 7),
// x + p - q * p = p + t * 2^120 + l - q lies in [p - q, 2p).
DEVICE_FORCEINLINE pr proth_canonical(const pr x) {
  const u32 q = (x.limbs[3] >> 24) / 7;
  pr shifted{};
  proth120_detail::add_limbs<false>(x, proth120_detail::MODULUS<1>(), shifted);
  pr r{};
  proth120_detail::sub_limbs<false>(shifted, pr{{q, 0, 0, (7 * q) << 24}}, r);
  return proth120_detail::reduce<1>(r);
}

// Twiddles of the block's relative stages >= 2 come from a shared-memory table in heap order:
// relative stage t, region (blockIdx.x << t) + j at index 2^t - 1 + j.
template <class BASE> struct staged_policy : BASE {
  const pr *staged;
  DEVICE_FORCEINLINE pr twiddle(const u32 region, const int stage) const {
    return stage < 2 ? get_forward_pr_twiddle(this->descriptor, region) : staged[(1u << stage) - 1 + region - (blockIdx.x << stage)];
  }
};

struct mobius_policy {
  static constexpr bool USES_TWIDDLES = false;
  static constexpr bool LAZY = false;
  DEVICE_FORCEINLINE void exchg(pr &a, pr &b, const pr) const { b = pr::sub(b, a); }
  DEVICE_FORCEINLINE void exchg_0(pr &a, pr &b) const { b = pr::sub(b, a); }
};

// `gate` (null: always on) points to a slot's active flag; a gated-off launch returns at entry.
struct chunk_map {
  const u32 *gate;
  u32 strip_base;
  u32 strip_blocks;
  u32 strip_domain_bits;
  u32 reserved;
};

static_assert(sizeof(chunk_map) == 24);

DEVICE_FORCEINLINE bool gated_off(const u32 *gate) { return gate && !*gate; }

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

template <class P> DEVICE_FORCEINLINE void exchange(const P &policy, pr &a, pr &b, const u32 region, const int stage = -1) {
  if constexpr (P::USES_TWIDDLES)
    policy.exchg(a, b, policy.twiddle(region, stage));
  else
    policy.exchg_0(a, b);
}

template <class P> DEVICE_FORCEINLINE void exchange_two(const P &policy, pr &a, pr &b, pr &c, pr &d, const u32 region, const int stage = -1) {
  if constexpr (P::USES_TWIDDLES) {
    const pr twiddle = policy.twiddle(region, stage);
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
  exchange_two(policy, vals[0], vals[2], vals[1], vals[3], exchg_region, STAGES_SO_FAR_THIS_LAUNCH);
  if constexpr (!SKIP_LAST) {
    exchg_region <<= 1;
    exchange(policy, vals[0], vals[1], exchg_region, STAGES_SO_FAR_THIS_LAUNCH + 1);
    exchange(policy, vals[2], vals[3], exchg_region + 1, STAGES_SO_FAR_THIS_LAUNCH + 1);
  }
#pragma unroll
  for (int i{0}, addr{lane_in_smem_region}; i < VALS_PER_THREAD; i++, addr += THREADS_PER_SMEM_REGION)
    smem[addr] = vals[i];
  if (THREADS_PER_SMEM_REGION > 32)
    __syncthreads();
  else
    __syncwarp();
}

template <int STAGES, int LOG_TILES_PER_BLOCK, class P>
DEVICE_FORCEINLINE void nonfinal_rest(pr (&vals)[4], pr *smem_block, pr_matrix_setter<st_modifier::cg> &gmem_out, const P &policy, const u32 start_stage,
                                      int exchg_region, const int tile_gmem_stride, const int lane_in_tile) {
  constexpr int LOG_TILE_SIZE = 3;
  constexpr int VALS_PER_THREAD = 4;
  constexpr int LOG_VALS_PER_BLOCK = LOG_TILES_PER_BLOCK + LOG_TILE_SIZE;
  constexpr int LOG_THREADS_PER_BLOCK = LOG_VALS_PER_BLOCK - 2;
  constexpr int VALS_PER_BLOCK = 1 << LOG_VALS_PER_BLOCK;
  if (start_stage == 0) {
    policy.exchg_0(vals[0], vals[2]);
    policy.exchg_0(vals[1], vals[3]);
  } else {
    exchange_two(policy, vals[0], vals[2], vals[1], vals[3], exchg_region, 0);
  }
  exchg_region <<= 1;
  exchange(policy, vals[0], vals[1], exchg_region, 1);
  exchange(policy, vals[2], vals[3], exchg_region + 1, 1);
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
    gmem_out.set_at_row(addr_gmem, P::LAZY ? proth_canonical(smem_warp[addr_smem]) : smem_warp[addr_smem]);
}

template <int STAGES, bool NARROW, class P, bool SCALE = false, bool STAGED = false>
DEVICE_FORCEINLINE void nonfinal(pr_matrix_getter<ld_modifier::cg> gmem_in, pr_matrix_setter<st_modifier::cg> gmem_out, const P &policy, const u32 log_n,
                                 const u32 start_stage, const chunk_map map, const coset_scale scale = {}) {
  static_assert(!NARROW || (STAGES >= 5 && STAGES <= 7));
  if (gated_off(map.gate))
    return;
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
        if constexpr (P::LAZY) {
          pr scaled{};
          proth120_detail::montmul_raw(vals[i], coset_scale_power(policy.descriptor, scale, k, block_start + addr), scaled);
          vals[i] = scaled;
        } else
          vals[i] = pr::mul(vals[i], coset_scale_power(policy.descriptor, scale, k, block_start + addr));
    }
  }
  if constexpr (STAGED) {
    static_assert(P::USES_TWIDDLES);
    __shared__ pr staged[(1 << STAGES) - 1];
    for (u32 m = 3 + threadIdx.x; m + 1 < (1u << STAGES); m += blockDim.x) {
      const u32 t = 31 - __clz(m + 1);
      staged[m] = get_forward_pr_twiddle(policy.descriptor, (blockIdx.x << t) + m + 1 - (1u << t));
    }
    const staged_policy<P> staged_policy{policy, staged};
    nonfinal_rest<STAGES, LOG_TILES_PER_BLOCK>(vals, smem_block, gmem_out, staged_policy, start_stage, exchg_region, tile_gmem_stride, lane_in_tile);
  } else {
    nonfinal_rest<STAGES, LOG_TILES_PER_BLOCK>(vals, smem_block, gmem_out, policy, start_stage, exchg_region, tile_gmem_stride, lane_in_tile);
  }
}

// One suffix tile of a coset prefix: components g = G * 2^sb + w (tiles G = first_tile..), each the
// contiguous 2^R-value run at prefix block bitrev_a(g) of every column. A 256-thread block owns
// 2^(10 - R) components of one column; it runs their first R - V suffix stages (local stage t,
// region (bitrev_a(g) << t) + z) and stores the 2^V-value leaf groups to the tile as
// [tile][column][f_lo][w][2^V], f_lo = bitrev_{R - V}(group). grid = (tiles x 2^sb / components per block,
// columns, cosets); cosets advance the prefix by prefix_coset_stride and the tile by tile_coset_stride.
struct suffix_tile_args {
  const pr *prefix;
  pr *tile;
  const u32 *gate;
  u64 prefix_column_stride;
  u64 prefix_coset_stride;
  u64 tile_coset_stride;
  u32 log_a;
  u32 skip_bottom;
  u32 first_tile;
  u32 columns;
};

template <int R, int V, class P> DEVICE_FORCEINLINE void suffix_micro(const P &policy, const suffix_tile_args args) {
  static_assert(R >= 6 && R <= 8 && V >= 1 && V < R);
  if (gated_off(args.gate))
    return;
  constexpr int STAGES_DONE = R - V;
  constexpr int LOG_THREADS_PER_COMPONENT = R - 2;
  constexpr int THREADS_PER_COMPONENT = 1 << LOG_THREADS_PER_COMPONENT;
  constexpr int LOG_COMPONENTS = 10 - R;
  constexpr int TWIDDLES = (1 << STAGES_DONE) - 1;
  __shared__ pr runs[1 << 10];
  __shared__ pr twiddles[TWIDDLES << LOG_COMPONENTS];
  const u32 blocks_per_tile = (1u << args.skip_bottom) >> LOG_COMPONENTS;
  const u32 tile_in_batch = blockIdx.x / blocks_per_tile;
  const u32 component = threadIdx.x >> LOG_THREADS_PER_COMPONENT;
  const u32 lane = threadIdx.x & (THREADS_PER_COMPONENT - 1);
  const u32 w = ((blockIdx.x % blocks_per_tile) << LOG_COMPONENTS) + component;
  const u32 g = ((args.first_tile + tile_in_batch) << args.skip_bottom) + w;
  const u32 b = bitreverse_low_bits(g, args.log_a);
  const u32 column = blockIdx.y;
  const pr *run = args.prefix + blockIdx.z * args.prefix_coset_stride + column * args.prefix_column_stride + (static_cast<u64>(b) << R);
  pr *smem = runs + (component << R);
  pr *table = twiddles + component * TWIDDLES;
#pragma unroll
  for (int j = 0; j < 4; j++)
    smem[lane + j * THREADS_PER_COMPONENT] = load_cg(run + lane + j * THREADS_PER_COMPONENT);
  if constexpr (P::USES_TWIDDLES) {
    for (u32 i = lane; i < TWIDDLES; i += THREADS_PER_COMPONENT) {
      const u32 t = 31 - __clz(i + 1);
      table[i] = policy.twiddle((b << t) + i + 1 - (1u << t), -1);
    }
  }
  __syncthreads();
#pragma unroll
  for (int t = 0; t < STAGES_DONE; t++) {
    const int log_half = R - t - 1;
#pragma unroll
    for (int j = 0; j < 2; j++) {
      const u32 pair = lane + j * THREADS_PER_COMPONENT;
      const u32 z = pair >> log_half;
      const u32 i0 = (z << (log_half + 1)) + (pair & ((1u << log_half) - 1));
      const u32 i1 = i0 + (1u << log_half);
      pr x = smem[i0];
      pr y = smem[i1];
      if constexpr (P::USES_TWIDDLES)
        policy.exchg(x, y, table[(1u << t) - 1 + z]);
      else
        policy.exchg_0(x, y);
      smem[i0] = x;
      smem[i1] = y;
    }
    __syncthreads();
  }
  pr *tile = args.tile + blockIdx.z * args.tile_coset_stride +
             (static_cast<u64>(tile_in_batch) * args.columns + column) * (static_cast<u64>(1) << (args.skip_bottom + R));
#pragma unroll
  for (int j = 0; j < 4; j++) {
    const u32 i = lane + j * THREADS_PER_COMPONENT;
    const u32 f_lo = bitreverse_low_bits(i >> V, STAGES_DONE);
    const pr value = smem[i];
    tile[((static_cast<u64>(f_lo) << args.skip_bottom) + w) * (1u << V) + (i & ((1u << V) - 1))] = P::LAZY ? proth_canonical(value) : value;
  }
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
