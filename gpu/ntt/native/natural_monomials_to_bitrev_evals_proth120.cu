#include <cuda.h>

#include "dit_memory.cuh"
#include "ntt.cuh"
#include "pass_config.cuh"

namespace airbender::ntt {

// Covers 2^15 to 2^24 with the following stages per kernel breakdown:
// 15: 7 nonfinal + 8 final
// 16: 8 nonfinal + 8 final
// 17: 7 nonfinal + 10 final
// 18: 8 nonfinal + 10 final
// 19: 7 nonfinal + 12 final
// 20: 8 nonfinal + 12 final
// 21:
// 22: 7 nonfinal + 7 nonfinal + 8 final
// 23: 8 nonfinal + 7 nonfinal + 8 final
// 24: 8 nonfinal + 8 nonfinal + 8 final

using pr = proth120_field;

template <int VALS_PER_THREAD, int STAGES_SO_FAR_THIS_LAUNCH, int VALS_PER_BLOCK, int LOG_THREADS_PER_BLOCK, bool SKIP_LAST=false>
DEVICE_FORCEINLINE void do_2_smem_stages(pr *smem_block) {
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
  const pr twiddle = get_forward_pr_twiddle(exchg_region);
  exchg_dit(vals[0], vals[2], twiddle);
  exchg_dit(vals[1], vals[3], twiddle);

  if (!SKIP_LAST) {
    exchg_region <<= 1; 
    // TODO: Check if "twiddle" above is equal to twiddle0^2 for all threads.
    const pr twiddle0 = get_forward_pr_twiddle(exchg_region);
    const pr twiddle1 = get_forward_pr_twiddle(exchg_region + 1);
    exchg_dit(vals[0], vals[1], twiddle0);
    exchg_dit(vals[2], vals[3], twiddle1);
  }

#pragma unroll
  for (int i{0}, addr{lane_in_smem_region}; i < VALS_PER_THREAD; i++, addr += THREADS_PER_SMEM_REGION)
    smem[addr] = vals[i];

  if (THREADS_PER_SMEM_REGION > 32)
    __syncthreads();
  else
    __syncwarp();
}

template <bool SKIP_LAST>
DEVICE_FORCEINLINE void pr_natural_monomials_to_bitrev_evals_nonfinal_7_or_8_stages(pr_matrix_getter<ld_modifier::cg> gmem_in,
                                                                                    pr_matrix_setter<st_modifier::cg> gmem_out,
                                                                                    const int log_n,
                                                                                    const int start_stage) {
  constexpr int LOG_TILE_SIZE = 3; // 8 16-byte elems = 128B = 1 cache line
  constexpr int TILE_SIZE = 1 << LOG_TILE_SIZE; 
  constexpr int LOG_VALS_PER_THREAD = 2;
  constexpr int VALS_PER_THREAD = 1 << LOG_VALS_PER_THREAD;
  constexpr int LOG_THREADS_PER_BLOCK = 9;
  // constexpr int THREADS_PER_BLOCK = 1 << LOG_THREADS_PER_BLOCK; // 512
  constexpr int LOG_VALS_PER_BLOCK = LOG_THREADS_PER_BLOCK + LOG_VALS_PER_THREAD;
  constexpr int VALS_PER_BLOCK = 1 << LOG_VALS_PER_BLOCK; // 2048
  constexpr int LOG_TILES_PER_BLOCK = LOG_VALS_PER_BLOCK - LOG_TILE_SIZE;

  const int exchg_region_size = 1 << (log_n - start_stage);
  const int tile_gmem_stride = exchg_region_size >> LOG_TILES_PER_BLOCK;

  const int tile_in_block = threadIdx.x >> LOG_TILE_SIZE;
  const int lane_in_tile = threadIdx.x & (TILE_SIZE - 1);

  __shared__ pr smem_block[VALS_PER_BLOCK];

  pr vals[VALS_PER_THREAD];

  gmem_in.add_col(blockIdx.z);
  gmem_out.add_col(blockIdx.z);

  int exchg_region = blockIdx.x;
  const int block_start_in_exchg_region = TILE_SIZE * blockIdx.y;
  const int block_start = exchg_region_size * exchg_region + block_start_in_exchg_region;
  gmem_in.add_row(block_start);
  gmem_out.add_row(block_start);

#pragma unroll
  for (int i{0}, addr{lane_in_tile + tile_in_block * tile_gmem_stride}; i < VALS_PER_THREAD; i++, addr += exchg_region_size >> LOG_VALS_PER_THREAD)
    vals[i] = gmem_in.get_at_row(addr);

  // 2 stages
  if (start_stage == 0) { 
    exchg_dit_0(vals[0], vals[2]);
    exchg_dit_0(vals[1], vals[3]);
  } else {
    // No need for explicit bitrevs.
    // exchg_region is the bitreved region, but the getter and power tables expect it to be.
    const pr twiddle = get_forward_pr_twiddle(exchg_region);
    exchg_dit(vals[0], vals[2], twiddle);
    exchg_dit(vals[1], vals[3], twiddle);
  }
  exchg_region <<= 1;
  const pr twiddle0 = get_forward_pr_twiddle(exchg_region);
  const pr twiddle1 = get_forward_pr_twiddle(exchg_region + 1);
  exchg_dit(vals[0], vals[1], twiddle0);
  exchg_dit(vals[2], vals[3], twiddle1);

#pragma unroll
  for (unsigned i{0}, addr{threadIdx.x}; i < VALS_PER_THREAD; i++, addr += blockDim.x)
    smem_block[addr] = vals[i];

  __syncthreads();

  // Smem exchange region size is now 512, with 128 threads per region
  do_2_smem_stages<4, 2, VALS_PER_BLOCK, LOG_THREADS_PER_BLOCK>(smem_block);
  // Smem exchange region size is now 128, with 32 threads per region
  do_2_smem_stages<4, 4, VALS_PER_BLOCK, LOG_THREADS_PER_BLOCK>(smem_block);
  // Smem exchange region size is now 32, with 8 threads per region
  // I don't think this causes needless bank conflicts,
  // because each tile of 8 elements is 128B = 1 full row of banks.
  do_2_smem_stages<4, 6, VALS_PER_BLOCK, LOG_THREADS_PER_BLOCK, SKIP_LAST>(smem_block);

  const int warp_id = threadIdx.x >> 5;
  const int lane_id = threadIdx.x & 31;
  pr *smem_warp = smem_block + 32 * VALS_PER_THREAD * warp_id;
  constexpr int TILES_PER_STORE = 32 >> LOG_TILE_SIZE;                    // 4: one warp-wide store covers 4 tiles
  constexpr int TILES_PER_WARP = (32 * VALS_PER_THREAD) >> LOG_TILE_SIZE; // 16: a warp's 128 smem values
  const int tile_in_store = lane_id >> LOG_TILE_SIZE;
  gmem_out.add_row(tile_gmem_stride * (tile_in_store + TILES_PER_WARP * warp_id) + lane_in_tile);
#pragma unroll
  for (int i{0}, addr_smem{lane_id}, addr_gmem{0}; i < VALS_PER_THREAD; i++, addr_smem += 32, addr_gmem += TILES_PER_STORE * tile_gmem_stride)
    gmem_out.set_at_row(addr_gmem, smem_warp[addr_smem]);
}

EXTERN __launch_bounds__(512, 2)
__global__ void ab_pr_natural_monomials_to_bitrev_evals_nonfinal_7_stages(pr_matrix_getter<ld_modifier::cg> gmem_in,
                                                                          pr_matrix_setter<st_modifier::cg> gmem_out,
                                                                          const int log_n,
                                                                          const int start_stage) {
  pr_natural_monomials_to_bitrev_evals_nonfinal_7_or_8_stages<true>(gmem_in, gmem_out, log_n, start_stage);
};

EXTERN __launch_bounds__(512, 2)
__global__ void ab_pr_natural_monomials_to_bitrev_evals_nonfinal_8_stages(pr_matrix_getter<ld_modifier::cg> gmem_in,
                                                                          pr_matrix_setter<st_modifier::cg> gmem_out,
                                                                          const int log_n,
                                                                          const int start_stage) {
  pr_natural_monomials_to_bitrev_evals_nonfinal_7_or_8_stages<false>(gmem_in, gmem_out, log_n, start_stage);
};

// Shim that allows the compiler to instantiate do_2_smem_stages for cases where STAGES and STAGES_SO_FAR would trigger
// ...natural_monomials_to_bitrev_evals_proth120.cu(28): note #62-D: shift count is negative
// In those cases do_2_smem_stages is instantiated (triggering the error) but not actually used,
// so we work around by substituting a dummy value for STAGES_SO_FAR.
template <int STAGES, int STAGES_SO_FAR> struct MaybeDummyMap {
  static constexpr int STAGES_SO_FAR_MAYBE_DUMMY = STAGES_SO_FAR;
};

template<> struct MaybeDummyMap<8, 8> {
  static constexpr int STAGES_SO_FAR_MAYBE_DUMMY = 0; // dummy value
};

template<> struct MaybeDummyMap<8, 10> {
  static constexpr int STAGES_SO_FAR_MAYBE_DUMMY = 0; // dummy value
};

template<> struct MaybeDummyMap<10, 10> {
  static constexpr int STAGES_SO_FAR_MAYBE_DUMMY = 0; // dummy value
};

template <int LOG_THREADS_PER_BLOCK, int STAGES>
DEVICE_FORCEINLINE void pr_natural_monomials_to_bitrev_evals_final_8_10_or_12_stages(pr_matrix_getter<ld_modifier::cg> gmem_in,
                                                                                     pr_matrix_setter<st_modifier::cg> gmem_out,
                                                                                     const int log_n,
                                                                                     const int start_stage) {
  constexpr int LOG_VALS_PER_THREAD = 2;
  constexpr int VALS_PER_THREAD = 1 << LOG_VALS_PER_THREAD;
  // constexpr int THREADS_PER_BLOCK = 1 << LOG_THREADS_PER_BLOCK; // 64, 256, or 1024
  constexpr int LOG_VALS_PER_BLOCK = LOG_THREADS_PER_BLOCK + LOG_VALS_PER_THREAD;
  constexpr int VALS_PER_BLOCK = 1 << LOG_VALS_PER_BLOCK; // 256, 1024, or 4096

  extern __shared__ pr smem_block[]; // 4096, 16384, or 65536 bytes

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
  const pr twiddle = get_forward_pr_twiddle(exchg_region);
  exchg_dit(vals[0], vals[2], twiddle);
  exchg_dit(vals[1], vals[3], twiddle);
  exchg_region <<= 1;
  // TODO: check if twiddle above always equals twiddle0^2
  const pr twiddle0 = get_forward_pr_twiddle(exchg_region);
  const pr twiddle1 = get_forward_pr_twiddle(exchg_region + 1);
  exchg_dit(vals[0], vals[1], twiddle0);
  exchg_dit(vals[2], vals[3], twiddle1);

#pragma unroll
  for (unsigned i{0}, addr{threadIdx.x}; i < VALS_PER_THREAD; i++, addr += blockDim.x)
    smem_block[addr] = vals[i];

  __syncthreads();

  // Exchange region size is now 64, 256, or 1024, with 16, 64, or 256 threads per region
  do_2_smem_stages<4, 2, VALS_PER_BLOCK, LOG_THREADS_PER_BLOCK>(smem_block);
  // Exchange region size is now 16,  64, or  256, with  4, 16, or  64 threads per region
  do_2_smem_stages<4, 4, VALS_PER_BLOCK, LOG_THREADS_PER_BLOCK>(smem_block);
  // Some of the following incur up to 4-way bank conflicts. TODO: check impact.
  // Exchange region size is now  4,  16, or   64, with  1,  4, or  16 threads per region
  do_2_smem_stages<4, 6, VALS_PER_BLOCK, LOG_THREADS_PER_BLOCK>(smem_block);
  // Exchange region size is now  _,   4, or   16, with  _,  1, or   4 threads per region
  if (STAGES > 8)
    do_2_smem_stages<4, MaybeDummyMap<STAGES, 8>::STAGES_SO_FAR_MAYBE_DUMMY, VALS_PER_BLOCK, LOG_THREADS_PER_BLOCK>(smem_block);
  // Exchange region size is now  _,   _, or    4, with  _, _, or    1 threads per region
  if (STAGES > 10)
    do_2_smem_stages<4, MaybeDummyMap<STAGES, 10>::STAGES_SO_FAR_MAYBE_DUMMY, VALS_PER_BLOCK, LOG_THREADS_PER_BLOCK>(smem_block);

  const int warp_id = threadIdx.x >> 5;
  const int lane_id = threadIdx.x & 31;
  pr *smem_warp = smem_block + 32 * VALS_PER_THREAD * warp_id;
  gmem_out.add_row(32 * VALS_PER_THREAD * warp_id);
#pragma unroll
  for (int i{0}, addr{lane_id}; i < VALS_PER_THREAD; i++, addr += 32)
    gmem_out.set_at_row(addr, smem_warp[addr]);
}

EXTERN __launch_bounds__(64, 16)
__global__ void ab_pr_natural_monomials_to_bitrev_evals_final_8_stages(pr_matrix_getter<ld_modifier::cg> gmem_in,
                                                                       pr_matrix_setter<st_modifier::cg> gmem_out,
                                                                       const int log_n,
                                                                       const int start_stage) {
  pr_natural_monomials_to_bitrev_evals_final_8_10_or_12_stages<6, 8>(gmem_in, gmem_out, log_n, start_stage);
}

EXTERN __launch_bounds__(256, 4)
__global__ void ab_pr_natural_monomials_to_bitrev_evals_final_10_stages(pr_matrix_getter<ld_modifier::cg> gmem_in,
                                                                        pr_matrix_setter<st_modifier::cg> gmem_out,
                                                                        const int log_n,
                                                                        const int start_stage) {
  pr_natural_monomials_to_bitrev_evals_final_8_10_or_12_stages<8, 10>(gmem_in, gmem_out, log_n, start_stage);
}

EXTERN __launch_bounds__(1024, 1)
__global__ void ab_pr_natural_monomials_to_bitrev_evals_final_12_stages(pr_matrix_getter<ld_modifier::cg> gmem_in,
                                                                        pr_matrix_setter<st_modifier::cg> gmem_out,
                                                                        const int log_n,
                                                                        const int start_stage) {
  pr_natural_monomials_to_bitrev_evals_final_8_10_or_12_stages<10, 12>(gmem_in, gmem_out, log_n, start_stage);
}

} // namespace airbender::ntt
