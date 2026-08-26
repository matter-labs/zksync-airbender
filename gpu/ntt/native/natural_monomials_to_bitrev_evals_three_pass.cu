#include <cuda.h>

#include "dit_memory.cuh"
#include "ntt.cuh"
#include "pass_config.cuh"

namespace airbender::ntt {

// Encode the rank-2 view used by the non-cross terminal TMA egress. The
// global buffer is viewed as N/32 consecutive rows of 32 bf values, and each
// warp writes one 32x32 box. Resolve the driver entry point through cudart so
// the Rust final link does not acquire a direct libcuda dependency.
EXTERN cudaError_t ab_encode_natural_final_output_tensor_map(CUtensorMap *tensor_map, bf *output, const unsigned long long n) {
  struct Encoder {
    decltype(&cuTensorMapEncodeTiled) function;
    cudaError_t status;
  };
  static const Encoder encoder = [] {
    void *raw_function = nullptr;
    cudaDriverEntryPointQueryResult query_result{};
    cudaError_t status = cudaGetDriverEntryPointByVersion("cuTensorMapEncodeTiled", &raw_function, 12000, cudaEnableDefault, &query_result);
    if (status == cudaSuccess && (raw_function == nullptr || query_result != cudaDriverEntryPointSuccess))
      status = cudaErrorNotSupported;
    return Encoder{reinterpret_cast<decltype(&cuTensorMapEncodeTiled)>(raw_function), status};
  }();
  if (encoder.status != cudaSuccess)
    return encoder.status;
  if ((reinterpret_cast<uintptr_t>(tensor_map) & 127u) != 0 || (reinterpret_cast<uintptr_t>(output) & 127u) != 0 || n < 1024 || (n & 1023u) != 0)
    return cudaErrorInvalidValue;

  constexpr unsigned RANK = 2;
  const cuuint64_t global_dims[RANK] = {32, static_cast<cuuint64_t>(n / 32)};
  const cuuint64_t global_strides[RANK - 1] = {32 * sizeof(bf)};
  const cuuint32_t box_dims[RANK] = {32, 32};
  const cuuint32_t element_strides[RANK] = {1, 1};
  const CUresult result =
      encoder.function(tensor_map, CU_TENSOR_MAP_DATA_TYPE_UINT32, RANK, output, global_dims, global_strides, box_dims, element_strides,
                       CU_TENSOR_MAP_INTERLEAVE_NONE, CU_TENSOR_MAP_SWIZZLE_128B, CU_TENSOR_MAP_L2_PROMOTION_NONE, CU_TENSOR_MAP_FLOAT_OOB_FILL_NONE);
  return result == CUDA_SUCCESS ? cudaSuccess : cudaErrorInvalidValue;
}

// Natural-order monomials -> bitreversed-order evaluations, three-pass regime
// (log_n in [21, 24]): out_k[p] = f(g_k * omega^rev_n(p)). Descending-stride
// DIT network (pass structure cloned from evals_to_monomials_three_pass.cu)
// over FORWARD twiddles, with no 1/N normalization. Pass 1 also carries the
// multi-coset shape: one shared input column feeds every coset's output slab,
// with the coset pre-scale g_k^row fused into the load.

template <bool HYPERCUBE_FINAL4>
DEVICE_FORCEINLINE void natural_monomials_to_bitrev_evals_initial_8_stages(bf_matrix_getter<ld_modifier::cg> gmem_in,
                                                                           bf_matrix_setter<st_modifier::cg> gmem_out, const bool transposed_monomials,
                                                                           const int log_n, const int coset_index_base, const int coset_factor_shift,
                                                                           const int num_cols_per_coset, const int log_cosets_in_tile) {
  using namespace pass_config::three_pass_phase_a;
  constexpr int ROLES = 2;
  constexpr int ROLE_TILE_STRIDE = THREAD_TILES_PER_BLOCK / ROLES;

  const int lane_in_tile = threadIdx.x & 31;

  const int exchg_region_size = 1 << log_n; // start_stage == 0
  const int tile_gmem_stride = exchg_region_size >> LOG_DATA_TILES_PER_BLOCK;
  const int interleaved_gmem_stride = tile_gmem_stride * THREAD_TILES_PER_BLOCK;

  // Flat-blockIdx.x layout: log_blocks_x = log_n - 13 blocks per (single)
  // exchange region, no intra-NTT y axis, then cosets, then columns. Inputs
  // are shared across cosets; outputs are coset-major with per-coset stride
  // `num_cols_per_coset`.
  const unsigned log_blocks_x = static_cast<unsigned>(log_n - 13);
  const FlatBlockIndex fi = decompose_flat_2d(log_blocks_x, 0u, static_cast<unsigned>(log_cosets_in_tile));
  gmem_in.add_col(static_cast<int>(fi.col));
  gmem_out.add_col(static_cast<int>(fi.coset) * num_cols_per_coset + static_cast<int>(fi.col));
  const unsigned coset_factor_power = static_cast<unsigned>((coset_index_base + static_cast<int>(fi.coset)) << coset_factor_shift);

  // Full global physical row = block offset + tile/lane/iteration offsets, so
  // the coset exponent and the transposed-layout mapping see absolute rows.
  const int gmem_block_offset = static_cast<int>(fi.intra_x) << LOG_DATA_TILE_SIZE;

  __shared__ bf smem_block[8192];

#pragma unroll
  for (int role = 0; role < ROLES; role++) {
    int tile_id = (threadIdx.x >> LOG_DATA_TILE_SIZE) + role * ROLE_TILE_STRIDE;
    asm volatile("mov.u32 %0, %0;" : "+r"(tile_id));
    const int thread_il_gmem_start = gmem_block_offset + lane_in_tile + tile_id * tile_gmem_stride;
    const int thread_il_smem_start = lane_in_tile + tile_id * TILE_SIZE;

    bf vals[VALS_PER_THREAD];

#pragma unroll
    for (int i{0}, row{thread_il_gmem_start}; i < VALS_PER_THREAD; i++, row += interleaved_gmem_stride)
      vals[i] = gmem_in.get_at_row(row);

    // The log_n=20 hypercube pre-tail has exactly bits 3..0 left. In this
    // load layout, threads in a warp hold consecutive physical rows for each
    // fixed register index, so those four Mobius stages are XOR-lane
    // exchanges. Every lane executes every shuffle; only the upper endpoint
    // of each pair applies y -= x. The input stays read-only, allowing all
    // cosets to share it in the existing flat tiled launch.
    if (HYPERCUBE_FINAL4) {
      constexpr unsigned WARP_MASK = 0xffffffff;
#pragma unroll
      for (int i{0}; i < VALS_PER_THREAD; i++) {
#pragma unroll
        for (int partner_mask = 8; partner_mask > 0; partner_mask >>= 1) {
          const unsigned partner_bits = __shfl_xor_sync(WARP_MASK, bf::into_raw_u32(vals[i]), partner_mask);
          if (lane_in_tile & partner_mask)
            vals[i] = bf::sub(vals[i], bf::from_reduced_raw_repr(partner_bits));
        }
      }
    }

    // A separate coset adjustment loop performs better than interleaving
    // adjustments with loads. The natural labeling IS the exponent, so no
    // bitrev here; `transposed_row_to_effective_row` resolves the physical
    // row of the transposed-monomial layout to its logical row.
    // Branch (grid-uniform) instead of a per-element ternary: the ternary
    // makes the compiler compute the transposed-layout row math and discard
    // it on the natural path.
    if (coset_factor_power != 0) {
      if (transposed_monomials) {
#pragma unroll
        for (int i{0}, row{thread_il_gmem_start}; i < VALS_PER_THREAD; i++, row += interleaved_gmem_stride)
          vals[i] = bf::mul(vals[i], get_forward_twiddle_power(static_cast<unsigned>(transposed_row_to_effective_row(row)) * coset_factor_power));
      } else {
        if constexpr (HYPERCUBE_FINAL4) {
          // The log_n=20 fused boundary reads natural rows in an arithmetic
          // progression. Seed its geometric power progression once per role
          // instead of reconstructing all 16 powers independently.
          const bf power_delta = get_forward_twiddle_power(static_cast<unsigned>(interleaved_gmem_stride) * coset_factor_power);
          bf power = get_forward_twiddle_power(static_cast<unsigned>(thread_il_gmem_start) * coset_factor_power);
#pragma unroll
          for (int i = 0; i < VALS_PER_THREAD - 1; i++) {
            vals[i] = bf::mul(vals[i], power);
            power = bf::mul(power, power_delta);
          }
          vals[VALS_PER_THREAD - 1] = bf::mul(vals[VALS_PER_THREAD - 1], power);
        } else {
#pragma unroll
          for (int i{0}, row{thread_il_gmem_start}; i < VALS_PER_THREAD; i++, row += interleaved_gmem_stride)
            vals[i] = bf::mul(vals[i], get_forward_twiddle_power(static_cast<unsigned>(row) * coset_factor_power));
        }
      }
    }

    // This half always starts at exchange-region zero. Region zero's twiddle
    // is the identity at every stage, so skip its 15 field multiplications.
    reg_exchg_fwd_dit_offset_0<8, 16, 1>(vals);
    reg_exchg_fwd_dit_offset_0<4, 8, 2>(vals);
    reg_exchg_fwd_dit_offset_0<2, 4, 4>(vals);
    reg_exchg_fwd_dit_offset_0<1, 2, 8>(vals);

#pragma unroll
    for (int i{0}, addr{thread_il_smem_start}; i < VALS_PER_THREAD; i++, addr += TILE_SIZE * THREAD_TILES_PER_BLOCK)
      smem_block[addr] = vals[i]; // write interleaved smem tiles
  }

  __syncthreads();

#pragma unroll
  for (int role = 0; role < ROLES; role++) {
    int tile_id = (threadIdx.x >> LOG_DATA_TILE_SIZE) + role * ROLE_TILE_STRIDE;
    // Keep the second role's address/twiddle seed local to its unrolled body.
    // Otherwise ptxas hoists it across the first role and spills one word.
    asm volatile("mov.u32 %0, %0;" : "+r"(tile_id));
    const int thread_ct_gmem_start = gmem_block_offset + lane_in_tile + tile_id * interleaved_gmem_stride;
    const int thread_ct_smem_start = lane_in_tile + tile_id * TILE_SIZE * THREAD_TILES_PER_BLOCK;

    bf vals[VALS_PER_THREAD];

#pragma unroll
    for (int i{0}, addr{thread_ct_smem_start}; i < VALS_PER_THREAD; i++, addr += TILE_SIZE)
      vals[i] = smem_block[addr]; // read consecutive smem tiles

    int tile_exchg_region_offset = tile_id;
    reg_exchg_fwd_dit<8, 16, 1>(vals, tile_exchg_region_offset);
    tile_exchg_region_offset <<= 1;
    reg_exchg_fwd_dit<4, 8, 2>(vals, tile_exchg_region_offset);
    tile_exchg_region_offset <<= 1;
    reg_exchg_fwd_dit<2, 4, 4>(vals, tile_exchg_region_offset);
    tile_exchg_region_offset <<= 1;
    reg_exchg_fwd_dit<1, 2, 8>(vals, tile_exchg_region_offset);

    // Un-transpose on the way out: pass 1's strides are all multiples of the
    // 1024-row transposition chunk (so the layout does not disturb its
    // butterflies or twiddle groups), but passes 2 and 3 exchange rows WITHIN
    // a chunk and require natural row order.
    if (transposed_monomials) {
#pragma unroll
      for (int i{0}, row{thread_ct_gmem_start}; i < VALS_PER_THREAD; i++, row += tile_gmem_stride)
        gmem_out.set_at_row(transposed_row_to_effective_row(row), vals[i]);
    } else {
#pragma unroll
      for (int i{0}, row{thread_ct_gmem_start}; i < VALS_PER_THREAD; i++, row += tile_gmem_stride)
        gmem_out.set_at_row(row, vals[i]);
    }
  }
}

// Pass 1: stages 0..7 (exchange region = the whole NTT).
EXTERN __launch_bounds__(256, 3) __global__
    void ab_natural_monomials_to_bitrev_evals_initial_8_stages_kernel(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out,
                                                                      const bool transposed_monomials, const int log_n, const int coset_index_base,
                                                                      const int coset_factor_shift, const int num_cols_per_coset,
                                                                      const int log_cosets_in_tile) {
  natural_monomials_to_bitrev_evals_initial_8_stages<false>(gmem_in, gmem_out, transposed_monomials, log_n, coset_index_base, coset_factor_shift,
                                                            num_cols_per_coset, log_cosets_in_tile);
}

// Commitment-only log_n=20 boundary: hypercube final4 plus the unchanged
// natural-to-bitrev initial8. The pre-tail scratch is deliberately read-only.
EXTERN __launch_bounds__(256, 1) __global__ void ab_natural_monomials_to_bitrev_evals_initial_8_stages_from_hypercube_final_4_kernel(
    bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out, const bool transposed_monomials, const int log_n,
    const int coset_index_base, const int coset_factor_shift, const int num_cols_per_coset, const int log_cosets_in_tile) {
  natural_monomials_to_bitrev_evals_initial_8_stages<true>(gmem_in, gmem_out, transposed_monomials, log_n, coset_index_base, coset_factor_shift,
                                                           num_cols_per_coset, log_cosets_in_tile);
}

template <int STRIDE, int REGION_SIZE, int NUM_REGIONS>
DEVICE_FORCEINLINE void reg_exchg_precomputed_twiddles_fwd_dit(bf *vals, const int exchg_region_offset) {
#pragma unroll
  for (int region = 0; region < NUM_REGIONS; region++) {
    const bf twiddle = mem::load_ca(ab_fully_precomputed_bitrev_twiddles + exchg_region_offset + region);
    const int region_offset = region * REGION_SIZE;
#pragma unroll
    for (int lane_in_region = 0; lane_in_region < STRIDE; lane_in_region++) {
      const int i = region_offset + lane_in_region;
      exchg_dit(vals[i], vals[i + STRIDE], twiddle);
    }
  }
}

template <int STRIDE, int REGION_SIZE, int NUM_REGIONS>
DEVICE_FORCEINLINE void reg_exchg_packed_precomputed_twiddles_fwd_dit(bf *vals, const int exchg_region_offset) {
  static_assert(NUM_REGIONS == 1 || NUM_REGIONS == 2 || NUM_REGIONS == 4 || NUM_REGIONS == 8);

  // Every caller doubles the exchange-region offset before doubling the
  // region count, so the table run is naturally aligned to its packed width.
  // All lanes in a warp use the same address: unlike strided value egress,
  // these vector loads remain one coalesced/broadcast global transaction.
  const bf *src = ab_fully_precomputed_bitrev_twiddles + exchg_region_offset;
  bf twiddles[NUM_REGIONS];
  if constexpr (NUM_REGIONS == 1) {
    twiddles[0] = mem::load_ca(src);
  } else if constexpr (NUM_REGIONS == 2) {
    const bf2_wide packed = mem::load_ca(reinterpret_cast<const bf2_wide *>(src));
    twiddles[0] = packed.v[0];
    twiddles[1] = packed.v[1];
  } else if constexpr (NUM_REGIONS == 4) {
    const bf4_wide packed = mem::load_ca(reinterpret_cast<const bf4_wide *>(src));
#pragma unroll
    for (int i = 0; i < NUM_REGIONS; i++)
      twiddles[i] = packed.v[i];
  } else {
    const bf8_wide packed = mem::load_ca(reinterpret_cast<const bf8_wide *>(src));
#pragma unroll
    for (int i = 0; i < NUM_REGIONS; i++)
      twiddles[i] = packed.v[i];
  }

#pragma unroll
  for (int region = 0; region < NUM_REGIONS; region++) {
    const int region_offset = region * REGION_SIZE;
#pragma unroll
    for (int lane_in_region = 0; lane_in_region < STRIDE; lane_in_region++) {
      const int i = region_offset + lane_in_region;
      exchg_dit(vals[i], vals[i + STRIDE], twiddles[region]);
    }
  }
}

// Pass 2: 8 in-place stages per coset starting at `start_stage` (8 in the
// three-pass plan). Its largest twiddle index is below 2^15, so the existing
// fully-precomputed order-2^18 table contains this order-2^16 prefix exactly.
EXTERN __launch_bounds__(256, 3) __global__
    void ab_natural_monomials_to_bitrev_evals_middle_8_stages_kernel(bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out,
                                                                     const int log_n, const int start_stage, const int num_cols_per_coset,
                                                                     const int log_cosets_in_tile) {
  using namespace pass_config::three_pass_phase_a;
  constexpr int ROLES = 2;
  constexpr int ROLE_TILE_STRIDE = THREAD_TILES_PER_BLOCK / ROLES;
  constexpr int START_STAGE = 8;

  const int lane_in_tile = threadIdx.x & 31;

  const int exchg_region_size = 1 << (log_n - START_STAGE);
  const int tile_gmem_stride = exchg_region_size >> LOG_DATA_TILES_PER_BLOCK;
  const int interleaved_gmem_stride = tile_gmem_stride * THREAD_TILES_PER_BLOCK;

  //   log_blocks_x = log_n - start_stage - 13 (blocks per exchg region)
  //   log_blocks_y = start_stage              (num exchg regions)
  const unsigned log_blocks_x = static_cast<unsigned>(log_n - START_STAGE - 13);
  constexpr unsigned log_blocks_y = START_STAGE;
  const FlatBlockIndex fi = decompose_flat_2d(log_blocks_x, log_blocks_y, static_cast<unsigned>(log_cosets_in_tile));
  apply_flat_col_offset(fi, num_cols_per_coset, gmem_in, gmem_out);
  const unsigned blocks_per_exchg_region = 1u << log_blocks_x;
  const unsigned num_exchg_regions = 1u << log_blocks_y;

  // Reversed block indexing, to help L2 hits.
  const int alternating_block_idx_x = static_cast<int>(blocks_per_exchg_region) - 1 - static_cast<int>(fi.intra_x);
  const int alternating_block_idx_y = static_cast<int>(num_exchg_regions) - 1 - static_cast<int>(fi.intra_y);
  const int gmem_block_offset = alternating_block_idx_y * exchg_region_size + (alternating_block_idx_x << LOG_DATA_TILE_SIZE);
  gmem_in.add_row(gmem_block_offset);
  gmem_out.add_row(gmem_block_offset);

  __shared__ bf smem_block[8192];

#pragma unroll
  for (int role = 0; role < ROLES; role++) {
    const int tile_id = (threadIdx.x >> LOG_DATA_TILE_SIZE) + role * ROLE_TILE_STRIDE;
    const int thread_il_gmem_start = lane_in_tile + tile_id * tile_gmem_stride;
    const int thread_il_smem_start = lane_in_tile + tile_id * TILE_SIZE;

    bf vals[VALS_PER_THREAD];

#pragma unroll
    for (int i{0}, addr{thread_il_gmem_start}; i < VALS_PER_THREAD; i++, addr += interleaved_gmem_stride)
      vals[i] = gmem_in.get_at_row(addr);

    int block_exchg_region_offset = alternating_block_idx_y;
    reg_exchg_precomputed_twiddles_fwd_dit<8, 16, 1>(vals, block_exchg_region_offset);
    block_exchg_region_offset <<= 1;
    reg_exchg_precomputed_twiddles_fwd_dit<4, 8, 2>(vals, block_exchg_region_offset);
    block_exchg_region_offset <<= 1;
    reg_exchg_precomputed_twiddles_fwd_dit<2, 4, 4>(vals, block_exchg_region_offset);
    block_exchg_region_offset <<= 1;
    reg_exchg_precomputed_twiddles_fwd_dit<1, 2, 8>(vals, block_exchg_region_offset);

#pragma unroll
    for (int i{0}, addr{thread_il_smem_start}; i < VALS_PER_THREAD; i++, addr += TILE_SIZE * THREAD_TILES_PER_BLOCK)
      smem_block[addr] = vals[i]; // write interleaved smem tiles
  }

  __syncthreads();

#pragma unroll
  for (int role = 0; role < ROLES; role++) {
    const int tile_id = (threadIdx.x >> LOG_DATA_TILE_SIZE) + role * ROLE_TILE_STRIDE;
    const int thread_ct_gmem_start = lane_in_tile + tile_id * interleaved_gmem_stride;
    const int thread_ct_smem_start = lane_in_tile + tile_id * TILE_SIZE * THREAD_TILES_PER_BLOCK;

    bf vals[VALS_PER_THREAD];

#pragma unroll
    for (int i{0}, addr{thread_ct_smem_start}; i < VALS_PER_THREAD; i++, addr += TILE_SIZE)
      vals[i] = smem_block[addr]; // read consecutive smem tiles

    int tile_exchg_region_offset = (alternating_block_idx_y << 4) + tile_id;
    reg_exchg_precomputed_twiddles_fwd_dit<8, 16, 1>(vals, tile_exchg_region_offset);
    tile_exchg_region_offset <<= 1;
    reg_exchg_precomputed_twiddles_fwd_dit<4, 8, 2>(vals, tile_exchg_region_offset);
    tile_exchg_region_offset <<= 1;
    reg_exchg_precomputed_twiddles_fwd_dit<2, 4, 4>(vals, tile_exchg_region_offset);
    tile_exchg_region_offset <<= 1;
    reg_exchg_precomputed_twiddles_fwd_dit<1, 2, 8>(vals, tile_exchg_region_offset);

#pragma unroll
    for (int i{0}, row{thread_ct_gmem_start}; i < VALS_PER_THREAD; i++, row += tile_gmem_stride)
      gmem_out.set_at_row(row, vals[i]); // write consecutive gmem tiles
  }
}

// Fixed one-NTT, one-coset production shape.
template <int LOG_N>
DEVICE_FORCEINLINE void natural_monomials_to_bitrev_evals_middle_8_stages_fixed_packed(bf_matrix_getter<ld_modifier::cg> gmem_in,
                                                                                       bf_matrix_setter<st_modifier::cg> gmem_out, bf *smem_block) {
  using namespace pass_config::three_pass_phase_a;
  static_assert(LOG_N >= 22 && LOG_N <= 24);
  constexpr int ROLES = 2;
  constexpr int ROLE_TILE_STRIDE = THREAD_TILES_PER_BLOCK / ROLES;
  constexpr int EXCHG_REGION_SIZE = 1 << (LOG_N - 8);
  constexpr int TILE_GMEM_STRIDE = EXCHG_REGION_SIZE >> LOG_DATA_TILES_PER_BLOCK;
  constexpr int INTERLEAVED_GMEM_STRIDE = TILE_GMEM_STRIDE * THREAD_TILES_PER_BLOCK;
  constexpr int LOG_BLOCKS_PER_EXCHG_REGION = LOG_N - 21;
  constexpr int BLOCKS_PER_EXCHG_REGION = 1 << LOG_BLOCKS_PER_EXCHG_REGION;
  constexpr int NUM_EXCHG_REGIONS = 256;

  const int lane_in_tile = threadIdx.x & 31;
  const unsigned intra_x = blockIdx.x & (BLOCKS_PER_EXCHG_REGION - 1);
  const unsigned intra_y = blockIdx.x >> LOG_BLOCKS_PER_EXCHG_REGION;

  const int alternating_block_idx_x = BLOCKS_PER_EXCHG_REGION - 1 - static_cast<int>(intra_x);
  const int alternating_block_idx_y = NUM_EXCHG_REGIONS - 1 - static_cast<int>(intra_y);
  const int gmem_block_offset = alternating_block_idx_y * EXCHG_REGION_SIZE + (alternating_block_idx_x << LOG_DATA_TILE_SIZE);
  gmem_in.add_row(gmem_block_offset);
  gmem_out.add_row(gmem_block_offset);

#pragma unroll
  for (int role = 0; role < ROLES; role++) {
    const int tile_id = (threadIdx.x >> LOG_DATA_TILE_SIZE) + role * ROLE_TILE_STRIDE;
    const int thread_il_gmem_start = lane_in_tile + tile_id * TILE_GMEM_STRIDE;
    const int thread_il_smem_start = lane_in_tile + tile_id * TILE_SIZE;

    bf vals[VALS_PER_THREAD];

#pragma unroll
    for (int i{0}, addr{thread_il_gmem_start}; i < VALS_PER_THREAD; i++, addr += INTERLEAVED_GMEM_STRIDE)
      vals[i] = gmem_in.get_at_row(addr);

    int block_exchg_region_offset = alternating_block_idx_y;
    reg_exchg_packed_precomputed_twiddles_fwd_dit<8, 16, 1>(vals, block_exchg_region_offset);
    block_exchg_region_offset <<= 1;
    reg_exchg_packed_precomputed_twiddles_fwd_dit<4, 8, 2>(vals, block_exchg_region_offset);
    block_exchg_region_offset <<= 1;
    reg_exchg_packed_precomputed_twiddles_fwd_dit<2, 4, 4>(vals, block_exchg_region_offset);
    block_exchg_region_offset <<= 1;
    reg_exchg_packed_precomputed_twiddles_fwd_dit<1, 2, 8>(vals, block_exchg_region_offset);

#pragma unroll
    for (int i{0}, addr{thread_il_smem_start}; i < VALS_PER_THREAD; i++, addr += TILE_SIZE * THREAD_TILES_PER_BLOCK)
      smem_block[addr] = vals[i];
  }

  __syncthreads();

#pragma unroll
  for (int role = 0; role < ROLES; role++) {
    const int tile_id = (threadIdx.x >> LOG_DATA_TILE_SIZE) + role * ROLE_TILE_STRIDE;
    const int thread_ct_gmem_start = lane_in_tile + tile_id * INTERLEAVED_GMEM_STRIDE;
    const int thread_ct_smem_start = lane_in_tile + tile_id * TILE_SIZE * THREAD_TILES_PER_BLOCK;

    bf vals[VALS_PER_THREAD];

#pragma unroll
    for (int i{0}, addr{thread_ct_smem_start}; i < VALS_PER_THREAD; i++, addr += TILE_SIZE)
      vals[i] = smem_block[addr];

    int tile_exchg_region_offset = (alternating_block_idx_y << 4) + tile_id;
    reg_exchg_packed_precomputed_twiddles_fwd_dit<8, 16, 1>(vals, tile_exchg_region_offset);
    tile_exchg_region_offset <<= 1;
    reg_exchg_packed_precomputed_twiddles_fwd_dit<4, 8, 2>(vals, tile_exchg_region_offset);
    tile_exchg_region_offset <<= 1;
    reg_exchg_packed_precomputed_twiddles_fwd_dit<2, 4, 4>(vals, tile_exchg_region_offset);
    tile_exchg_region_offset <<= 1;
    reg_exchg_packed_precomputed_twiddles_fwd_dit<1, 2, 8>(vals, tile_exchg_region_offset);

#pragma unroll
    for (int i{0}, row{thread_ct_gmem_start}; i < VALS_PER_THREAD; i++, row += TILE_GMEM_STRIDE)
      gmem_out.set_at_row(row, vals[i]);
  }
}

#define DEFINE_NATURAL_MIDDLE_FIXED_PACKED(LOG_N)                                                                                                              \
  EXTERN __launch_bounds__(256, 3) __global__ void ab_natural_monomials_to_bitrev_evals_middle_8_stages_log_n_##LOG_N##_packed_twiddles_kernel(                \
      bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out) {                                                                 \
    __shared__ bf smem_block[8192];                                                                                                                            \
    natural_monomials_to_bitrev_evals_middle_8_stages_fixed_packed<LOG_N>(gmem_in, gmem_out, smem_block);                                                      \
  }

DEFINE_NATURAL_MIDDLE_FIXED_PACKED(22)
DEFINE_NATURAL_MIDDLE_FIXED_PACKED(23)
DEFINE_NATURAL_MIDDLE_FIXED_PACKED(24)

#undef DEFINE_NATURAL_MIDDLE_FIXED_PACKED

// At log_n=21 the 128 MiB L2 strategy keeps both LDE cosets in one launch and
// may also batch several columns. Specialize the fixed block/coset geometry
// while retaining the runtime column stride needed by that batching.
EXTERN __launch_bounds__(256, 3) __global__
    void ab_natural_monomials_to_bitrev_evals_middle_8_stages_log_n_21_two_cosets_packed_twiddles_kernel(bf_matrix_getter<ld_modifier::cg> gmem_in,
                                                                                                         bf_matrix_setter<st_modifier::cg> gmem_out,
                                                                                                         const int num_cols_per_coset) {
  using namespace pass_config::three_pass_phase_a;
  constexpr int ROLES = 2;
  constexpr int ROLE_TILE_STRIDE = THREAD_TILES_PER_BLOCK / ROLES;
  constexpr int EXCHG_REGION_SIZE = 1 << 13;
  constexpr int TILE_GMEM_STRIDE = EXCHG_REGION_SIZE >> LOG_DATA_TILES_PER_BLOCK;
  constexpr int INTERLEAVED_GMEM_STRIDE = TILE_GMEM_STRIDE * THREAD_TILES_PER_BLOCK;
  constexpr int NUM_EXCHG_REGIONS = 256;

  const int lane_in_tile = threadIdx.x & 31;
  const unsigned intra_y = blockIdx.x & (NUM_EXCHG_REGIONS - 1);
  const unsigned ntt_idx = blockIdx.x >> 8;
  const unsigned coset = ntt_idx & 1;
  const unsigned col = ntt_idx >> 1;
  const int col_offset = static_cast<int>(coset) * num_cols_per_coset + static_cast<int>(col);
  gmem_in.add_col(col_offset);
  gmem_out.add_col(col_offset);

  const int alternating_block_idx_y = NUM_EXCHG_REGIONS - 1 - static_cast<int>(intra_y);
  const int gmem_block_offset = alternating_block_idx_y * EXCHG_REGION_SIZE;
  gmem_in.add_row(gmem_block_offset);
  gmem_out.add_row(gmem_block_offset);

  __shared__ bf smem_block[8192];

#pragma unroll
  for (int role = 0; role < ROLES; role++) {
    const int tile_id = (threadIdx.x >> LOG_DATA_TILE_SIZE) + role * ROLE_TILE_STRIDE;
    const int thread_il_gmem_start = lane_in_tile + tile_id * TILE_GMEM_STRIDE;
    const int thread_il_smem_start = lane_in_tile + tile_id * TILE_SIZE;

    bf vals[VALS_PER_THREAD];

#pragma unroll
    for (int i{0}, addr{thread_il_gmem_start}; i < VALS_PER_THREAD; i++, addr += INTERLEAVED_GMEM_STRIDE)
      vals[i] = gmem_in.get_at_row(addr);

    int block_exchg_region_offset = alternating_block_idx_y;
    reg_exchg_packed_precomputed_twiddles_fwd_dit<8, 16, 1>(vals, block_exchg_region_offset);
    block_exchg_region_offset <<= 1;
    reg_exchg_packed_precomputed_twiddles_fwd_dit<4, 8, 2>(vals, block_exchg_region_offset);
    block_exchg_region_offset <<= 1;
    reg_exchg_packed_precomputed_twiddles_fwd_dit<2, 4, 4>(vals, block_exchg_region_offset);
    block_exchg_region_offset <<= 1;
    reg_exchg_packed_precomputed_twiddles_fwd_dit<1, 2, 8>(vals, block_exchg_region_offset);

#pragma unroll
    for (int i{0}, addr{thread_il_smem_start}; i < VALS_PER_THREAD; i++, addr += TILE_SIZE * THREAD_TILES_PER_BLOCK)
      smem_block[addr] = vals[i];
  }

  __syncthreads();

#pragma unroll
  for (int role = 0; role < ROLES; role++) {
    const int tile_id = (threadIdx.x >> LOG_DATA_TILE_SIZE) + role * ROLE_TILE_STRIDE;
    const int thread_ct_gmem_start = lane_in_tile + tile_id * INTERLEAVED_GMEM_STRIDE;
    const int thread_ct_smem_start = lane_in_tile + tile_id * TILE_SIZE * THREAD_TILES_PER_BLOCK;

    bf vals[VALS_PER_THREAD];

#pragma unroll
    for (int i{0}, addr{thread_ct_smem_start}; i < VALS_PER_THREAD; i++, addr += TILE_SIZE)
      vals[i] = smem_block[addr];

    int tile_exchg_region_offset = (alternating_block_idx_y << 4) + tile_id;
    reg_exchg_packed_precomputed_twiddles_fwd_dit<8, 16, 1>(vals, tile_exchg_region_offset);
    tile_exchg_region_offset <<= 1;
    reg_exchg_packed_precomputed_twiddles_fwd_dit<4, 8, 2>(vals, tile_exchg_region_offset);
    tile_exchg_region_offset <<= 1;
    reg_exchg_packed_precomputed_twiddles_fwd_dit<2, 4, 4>(vals, tile_exchg_region_offset);
    tile_exchg_region_offset <<= 1;
    reg_exchg_packed_precomputed_twiddles_fwd_dit<1, 2, 8>(vals, tile_exchg_region_offset);

#pragma unroll
    for (int i{0}, row{thread_ct_gmem_start}; i < VALS_PER_THREAD; i++, row += TILE_GMEM_STRIDE)
      gmem_out.set_at_row(row, vals[i]);
  }
}

// Pass 3: the final STAGES (= log_n - 16) finest stages, in place per coset.
// Outputs are always written in plain (non-transposed) row order: the
// bitreversed codeword is what the tree layer consumes.
template <int STRIDE, int REGION_SIZE, int NUM_REGIONS>
DEVICE_FORCEINLINE void reg_exchg_aligned_cmem_smem_twiddles_fwd_dit(bf *vals, const int exchg_region_offset, const bf *smem_twiddles) {
  static_assert(NUM_REGIONS > 0 && NUM_REGIONS <= 16);
  static_assert((NUM_REGIONS & (NUM_REGIONS - 1)) == 0);
  static_assert((32 % NUM_REGIONS) == 0);

  // Every terminal call aligns the exchange-region offset to NUM_REGIONS.
  // Since NUM_REGIONS divides both a 32-entry swizzle row and the 4096-entry
  // coarse table, the unrolled run crosses neither boundary. Swizzling the
  // aligned base once and XORing the region is therefore identical to
  // swizzling every coarse index independently.
  const int fine_idx = (exchg_region_offset >> EightStages::COARSE_LOG_COUNT) & EightStages::FINE_MASK;
  const int coarse_base = exchg_region_offset & EightStages::COARSE_MASK;
  const int swizzled_coarse_base = linear_to_swizzled(coarse_base);
  // Entry zero is BF::ONE by construction in generate_fwd_inv_arrays. The
  // zero-fine regions are rare here, so exact identity multiplications are
  // cheaper than duplicating the fully unrolled butterfly body around a branch.
  const bf fine = ab_fwd_cmem_twiddles_finest_11[fine_idx];
#pragma unroll
  for (int region = 0; region < NUM_REGIONS; region++) {
    const bf coarse = smem_twiddles[swizzled_coarse_base ^ region];
    const bf twiddle = bf::mul(fine, coarse);
    const int region_offset = region * REGION_SIZE;
#pragma unroll
    for (int lane_in_region = 0; lane_in_region < STRIDE; lane_in_region++) {
      const int i = region_offset + lane_in_region;
      exchg_dit(vals[i], vals[i + STRIDE], twiddle);
    }
  }
}

// A 16-byte-chunk XOR swizzle for the packed half of a 32x32 warp
// transpose. Four consecutive logical x coordinates stay physically
// consecutive and aligned, while the chunk index retains the bank-rotation
// property of xy_to_swizzled.
DEVICE_FORCEINLINE int xy_to_swizzled_v4(const int x, const int y) { return y * 32 + 4 * ((y & 7) ^ (x >> 2)) + (x & 3); }

template <unsigned N> DEVICE_FORCEINLINE void warp_transpose_swizzled_v4(bf *smem_warp, bf *vals, const int lane) {
  static_assert(N == 32, "warp_transpose_swizzled_v4 assumes a 32-wide warp tile");
#pragma unroll
  for (int y = 0; y < static_cast<int>(N); y++)
    smem_warp[xy_to_swizzled_v4(lane, y)] = vals[y];
  __syncwarp();
#pragma unroll
  for (int chunk = 0; chunk < static_cast<int>(N) / 4; chunk++) {
    const int x = 4 * chunk;
    ld_shared_v4(smem_warp + xy_to_swizzled_v4(x, lane), vals[x], vals[x + 1], vals[x + 2], vals[x + 3]);
  }
}

template <unsigned N> DEVICE_FORCEINLINE void warp_transpose_swizzled_v4_mirror(bf *smem_warp, bf *vals, const int lane) {
  static_assert(N == 32, "warp_transpose_swizzled_v4_mirror assumes a 32-wide warp tile");
#pragma unroll
  for (int chunk = 0; chunk < static_cast<int>(N) / 4; chunk++) {
    const int x = 4 * chunk;
    st_shared_v4(smem_warp + xy_to_swizzled_v4(x, lane), vals[x], vals[x + 1], vals[x + 2], vals[x + 3]);
  }
  __syncwarp();
#pragma unroll
  for (int y = 0; y < static_cast<int>(N); y++)
    vals[y] = smem_warp[xy_to_swizzled_v4(lane, y)];
}

template <int STAGES, ld_modifier LD, st_modifier ST, bool HOIST_FINE, bool BULK_TWIDDLES, bool TMA_EGRESS = false, bool DELAYED_NEXT_PREFETCH = false,
          bool PACKED_SMEM_TRANSPOSE = false, bool PACKED_PRECOMPUTED_NUM2 = false>
DEVICE_FORCEINLINE void natural_monomials_to_bitrev_evals_final_up_to_8_stages_with_smem(
    bf_matrix_getter<LD> gmem_in, bf_matrix_setter<ST> gmem_out, const int log_n, const int num_cols_per_coset, const int log_cosets_in_tile, bf *smem_block,
    unsigned long long *twiddle_copy_barrier, const CUtensorMap *output_tensor_map = nullptr, const bf *delayed_prefetch_src = nullptr) {
  using namespace pass_config::three_pass_phase_b;
  constexpr int INITIAL_EXCHG_REGIONS_PER_WARP = 1 << (10 - STAGES);

  const unsigned log_blocks_per_ntt = static_cast<unsigned>(log_n) - 13u;
  const FlatBlockIndex fi = decompose_flat_1d(log_blocks_per_ntt, static_cast<unsigned>(log_cosets_in_tile));
  // apply_flat_col_offset is pinned to cg accessors; inline it for the
  // modifier-templated body.
  const int col_offset = static_cast<int>(fi.coset) * num_cols_per_coset + static_cast<int>(fi.col);
  gmem_in.add_col(col_offset);
  gmem_out.add_col(col_offset);

  const int lane_id = threadIdx.x & 31;
  const int warp_id = threadIdx.x >> 5;
  const int gmem_block_offset = static_cast<int>(fi.intra_x) * VALS_PER_BLOCK;
  gmem_in.add_row(gmem_block_offset + warp_id * VALS_PER_WARP);
  gmem_out.add_row(gmem_block_offset + warp_id * VALS_PER_WARP);

  bf *smem_warp = smem_block + (warp_id & 3) * VALS_PER_WARP;
  bf *smem_twiddles = smem_block + (VALS_PER_BLOCK >> 1);

  bf vals[VALS_PER_THREAD];

  if constexpr (BULK_TWIDDLES) {
#if __CUDA_ARCH__ >= 900
    // One CTA-owned bulk transaction stages the 16 KiB coarse table while the
    // block loads its values and executes the cmem-only stages. Thread 0 is the
    // sole barrier participant; after it observes transaction completion, the
    // existing CTA barrier below publishes the table to every thread.
    if (threadIdx.x == 0) {
      const unsigned mbar_s = static_cast<unsigned>(__cvta_generic_to_shared(twiddle_copy_barrier));
      const unsigned dst_s = static_cast<unsigned>(__cvta_generic_to_shared(smem_twiddles));
      constexpr unsigned COPY_BYTES = 4096 * sizeof(bf);
      asm volatile("mbarrier.init.shared::cta.b64 [%0], 1;" : : "r"(mbar_s));
      asm volatile("fence.mbarrier_init.release.cluster;" : : : "memory");
      asm volatile("mbarrier.arrive.expect_tx.release.cta.shared::cta.b64 _, [%0], %1;" : : "r"(mbar_s), "r"(COPY_BYTES));
      asm volatile("cp.async.bulk.shared::cta.global.mbarrier::complete_tx::bytes [%0], [%1], %2, [%3];"
                   :
                   : "r"(dst_s), "l"(ab_fwd_gmem_twiddles_coarse), "r"(COPY_BYTES), "r"(mbar_s)
                   : "memory");
    }
#else
    const int pipeline_memcpy_start = 4 * threadIdx.x;
    const int pipeline_memcpy_stride = 4 * blockDim.x;
    const bf *twiddle_src = ab_fwd_gmem_twiddles_coarse;
#pragma unroll
    for (int i{0}, addr{pipeline_memcpy_start}; i < 4; i++, addr += pipeline_memcpy_stride)
      __pipeline_memcpy_async(smem_twiddles + addr, twiddle_src + addr, 4 * sizeof(bf));
    __pipeline_commit();
#endif
  } else {
    // Keep the cross body under its 128-register budget.
    const int pipeline_memcpy_start = 4 * threadIdx.x;
    const int pipeline_memcpy_stride = 4 * blockDim.x;
    const bf *twiddle_src = ab_fwd_gmem_twiddles_coarse;
#pragma unroll
    for (int i{0}, addr{pipeline_memcpy_start}; i < 4; i++, addr += pipeline_memcpy_stride)
      __pipeline_memcpy_async(smem_twiddles + addr, twiddle_src + addr, 4 * sizeof(bf));
    __pipeline_commit();
  }

#pragma unroll
  for (int i{0}, row{lane_id}; i < VALS_PER_THREAD; i++, row += WARP_SIZE)
    vals[i] = gmem_in.get_at_row(row);

  if constexpr (DELAYED_NEXT_PREFETCH) {
    // The cross kernel consumes this exact line set in its second phase. Issue
    // after the current terminal's global-load queue instead of at kernel
    // entry, leaving the rest of the terminal as overlap distance without
    // parking B values in registers.
    const size_t global_thread = static_cast<size_t>(blockIdx.x) * blockDim.x + threadIdx.x;
    ::airbender::primitives::ptx::prefetch_l2(delayed_prefetch_src + global_thread * WARP_SIZE);
  }

  // Use pure cmem for warp-uniform twiddles
  if (STAGES >= 5) {
    int warp_exchg_region_offset = INITIAL_EXCHG_REGIONS_PER_WARP * (static_cast<int>(fi.intra_x) * WARPS_PER_BLOCK + warp_id);
#pragma unroll
    for (int i{0}; i < INITIAL_EXCHG_REGIONS_PER_WARP; i++) {
      int exchg_region_offset = warp_exchg_region_offset + i;
      if (STAGES == 8) {
        bf *vals_this_region = vals + 8 * i;
        reg_exchg_precomputed_twiddles_fwd_dit<4, 8, 1>(vals_this_region, exchg_region_offset);
        exchg_region_offset <<= 1;
        if constexpr (PACKED_PRECOMPUTED_NUM2)
          reg_exchg_packed_precomputed_twiddles_fwd_dit<2, 4, 2>(vals_this_region, exchg_region_offset);
        else
          reg_exchg_precomputed_twiddles_fwd_dit<2, 4, 2>(vals_this_region, exchg_region_offset);
        exchg_region_offset <<= 1;
        reg_exchg_cmem_twiddles_fwd_dit<1, 2, 4>(vals_this_region, exchg_region_offset);
      }
      if (STAGES == 7) {
        bf *vals_this_region = vals + 4 * i;
        reg_exchg_cmem_twiddles_fwd_dit<2, 4, 1>(vals_this_region, exchg_region_offset);
        exchg_region_offset <<= 1;
        reg_exchg_cmem_twiddles_fwd_dit<1, 2, 2>(vals_this_region, exchg_region_offset);
      }
      if (STAGES == 6) {
        bf *vals_this_region = vals + 2 * i;
        reg_exchg_cmem_twiddles_fwd_dit<1, 2, 1>(vals_this_region, exchg_region_offset);
      }
    }
  }

  if (warp_id & 4) {
    if constexpr (PACKED_SMEM_TRANSPOSE)
      warp_transpose_swizzled_v4<VALS_PER_THREAD>(smem_warp, vals, lane_id);
    else
      warp_transpose_swizzled<VALS_PER_THREAD>(smem_warp, vals, lane_id);
  }

  if constexpr (BULK_TWIDDLES) {
#if __CUDA_ARCH__ >= 900
    if (threadIdx.x == 0)
      asm volatile("{\n\t"
                   ".reg .pred p;\n"
                   "WAIT:\n\t"
                   "mbarrier.try_wait.parity.shared::cta.b64 p, [%0], 0;\n\t"
                   "@!p bra WAIT;\n\t"
                   "}"
                   :
                   : "r"(static_cast<unsigned>(__cvta_generic_to_shared(twiddle_copy_barrier)))
                   : "memory");
#else
    __pipeline_wait_prior(0);
#endif
  } else {
    __pipeline_wait_prior(0);
  }

  __syncthreads();

  if (!(warp_id & 4)) {
    if constexpr (PACKED_SMEM_TRANSPOSE)
      warp_transpose_swizzled_v4<VALS_PER_THREAD>(smem_warp, vals, lane_id);
    else
      warp_transpose_swizzled<VALS_PER_THREAD>(smem_warp, vals, lane_id);
  }

  int thread_exchg_region_offset = threadIdx.x + static_cast<int>(fi.intra_x) * blockDim.x;
  if constexpr (HOIST_FINE) {
    reg_exchg_aligned_cmem_smem_twiddles_fwd_dit<16, 32, 1>(vals, thread_exchg_region_offset, smem_twiddles);
    thread_exchg_region_offset <<= 1;
    reg_exchg_aligned_cmem_smem_twiddles_fwd_dit<8, 16, 2>(vals, thread_exchg_region_offset, smem_twiddles);
    thread_exchg_region_offset <<= 1;
    reg_exchg_aligned_cmem_smem_twiddles_fwd_dit<4, 8, 4>(vals, thread_exchg_region_offset, smem_twiddles);
    thread_exchg_region_offset <<= 1;
    reg_exchg_aligned_cmem_smem_twiddles_fwd_dit<2, 4, 8>(vals, thread_exchg_region_offset, smem_twiddles);
    thread_exchg_region_offset <<= 1;
    reg_exchg_aligned_cmem_smem_twiddles_fwd_dit<1, 2, 16>(vals, thread_exchg_region_offset, smem_twiddles);
  } else {
    constexpr bf *cmem_twiddles = ab_fwd_cmem_twiddles_finest_11;
    reg_exchg_cmem_smem_twiddles_fwd_dit<EightStages, 16, 32, 1, cmem_twiddles>(vals, thread_exchg_region_offset, smem_twiddles);
    thread_exchg_region_offset <<= 1;
    reg_exchg_cmem_smem_twiddles_fwd_dit<EightStages, 8, 16, 2, cmem_twiddles>(vals, thread_exchg_region_offset, smem_twiddles);
    thread_exchg_region_offset <<= 1;
    reg_exchg_cmem_smem_twiddles_fwd_dit<EightStages, 4, 8, 4, cmem_twiddles>(vals, thread_exchg_region_offset, smem_twiddles);
    thread_exchg_region_offset <<= 1;
    reg_exchg_cmem_smem_twiddles_fwd_dit<EightStages, 2, 4, 8, cmem_twiddles>(vals, thread_exchg_region_offset, smem_twiddles);
    thread_exchg_region_offset <<= 1;
    reg_exchg_cmem_smem_twiddles_fwd_dit<EightStages, 1, 2, 16, cmem_twiddles>(vals, thread_exchg_region_offset, smem_twiddles);
  }

  // Un-swizzle and store with coalescing, or publish each warp's canonical
  // 32x32 tile in the 128-byte TMA swizzle and let one tensor store write it.
  __syncthreads();

  smem_warp = smem_block + warp_id * VALS_PER_WARP;
  if constexpr (TMA_EGRESS) {
    // CU_TENSOR_MAP_SWIZZLE_128B XORs 16-byte chunks, not individual bf
    // values. A lane owns one logical 128-byte row. Its eight STS.128
    // operations therefore incur four shared wavefronts apiece (32 total),
    // while the TMA engine unswizzles the tile into canonical global order.
#pragma unroll
    for (int chunk = 0; chunk < VALS_PER_THREAD / 4; chunk++) {
      const int swizzled_chunk = chunk ^ (lane_id & 7);
      bf *dst = smem_warp + lane_id * VALS_PER_THREAD + 4 * swizzled_chunk;
      st_shared_v4(dst, vals[4 * chunk], vals[4 * chunk + 1], vals[4 * chunk + 2], vals[4 * chunk + 3]);
    }

    // Every producer orders its shared writes into the async proxy. The warp
    // barrier then makes those fences precede lane 0's TMA read of this warp's
    // disjoint 4 KiB slab.
    asm volatile("fence.proxy.async.shared::cta;" : : : "memory");
    __syncwarp();
    if (lane_id == 0) {
      const int tensor_coords_0 = 0;
      const int tensor_coords_1 = (gmem_block_offset + warp_id * VALS_PER_WARP) / VALS_PER_THREAD;
      const unsigned src_s = static_cast<unsigned>(__cvta_generic_to_shared(smem_warp));
      unsigned long long cache_policy;
      asm volatile("createpolicy.fractional.L2::evict_first.b64 %0, 1.0;" : "=l"(cache_policy));
      asm volatile("cp.async.bulk.tensor.2d.global.shared::cta.tile.bulk_group.L2::cache_hint [%0, {%1, %2}], [%3], %4;"
                   :
                   : "l"(output_tensor_map), "r"(tensor_coords_0), "r"(tensor_coords_1), "r"(src_s), "l"(cache_policy)
                   : "memory");
      asm volatile("cp.async.bulk.commit_group;" : : : "memory");
      asm volatile("cp.async.bulk.wait_group.read 0;" : : : "memory");
    }
  } else {
    if constexpr (PACKED_SMEM_TRANSPOSE)
      warp_transpose_swizzled_v4<VALS_PER_THREAD>(smem_warp, vals, lane_id);
    else
      warp_transpose_swizzled<VALS_PER_THREAD>(smem_warp, vals, lane_id);

#pragma unroll
    for (int i{0}, row{lane_id}; i < VALS_PER_THREAD; i++, row += WARP_SIZE)
      gmem_out.set_at_row(row, vals[i]);
  }
}

template <int STAGES, ld_modifier LD, st_modifier ST>
DEVICE_FORCEINLINE void natural_monomials_to_bitrev_evals_final_up_to_8_stages(bf_matrix_getter<LD> gmem_in, bf_matrix_setter<ST> gmem_out, const int log_n,
                                                                               const int num_cols_per_coset, const int log_cosets_in_tile) {
  __shared__ __align__(16) bf smem_block[8192]; // 4096 vals, 4096 coarse twiddles
  __shared__ __align__(8) unsigned long long twiddle_copy_barrier;
  natural_monomials_to_bitrev_evals_final_up_to_8_stages_with_smem<STAGES, LD, ST, true, true>(gmem_in, gmem_out, log_n, num_cols_per_coset, log_cosets_in_tile,
                                                                                               smem_block, &twiddle_copy_barrier);
}

template <int STAGES, bool PACKED_SMEM_TRANSPOSE = false, bool PACKED_PRECOMPUTED_NUM2 = false>
DEVICE_FORCEINLINE void natural_monomials_to_bitrev_evals_final_up_to_8_stages_tma(bf_matrix_getter<ld_modifier::cs> gmem_in,
                                                                                   bf_matrix_setter<st_modifier::cs> gmem_out, const int log_n,
                                                                                   const CUtensorMap *output_tensor_map) {
  // The 128-byte TMA swizzle repeats after 1024 bytes. Every warp slab starts
  // at a 4096-byte multiple of this base.
  __shared__ __align__(1024) bf smem_block[8192];
  __shared__ __align__(8) unsigned long long twiddle_copy_barrier;
  natural_monomials_to_bitrev_evals_final_up_to_8_stages_with_smem<STAGES, ld_modifier::cs, st_modifier::cs, true, true, true, false, PACKED_SMEM_TRANSPOSE,
                                                                   PACKED_PRECOMPUTED_NUM2>(gmem_in, gmem_out, log_n, 1, 0, smem_block, &twiddle_copy_barrier,
                                                                                            output_tensor_map);
}

#define DEFINE_FINAL_KERNEL(STAGES)                                                                                                                            \
  EXTERN __launch_bounds__(256, 3) __global__ void ab_natural_monomials_to_bitrev_evals_final_##STAGES##_stages_kernel(                                        \
      bf_matrix_getter<ld_modifier::cg> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out, const int log_n, const int num_cols_per_coset,                    \
      const int log_cosets_in_tile) {                                                                                                                          \
    natural_monomials_to_bitrev_evals_final_up_to_8_stages<STAGES, ld_modifier::cg, st_modifier::cg>(gmem_in, gmem_out, log_n, num_cols_per_coset,             \
                                                                                                     log_cosets_in_tile);                                      \
  }

DEFINE_FINAL_KERNEL(5)
DEFINE_FINAL_KERNEL(6)
DEFINE_FINAL_KERNEL(7)
DEFINE_FINAL_KERNEL(8)

#undef DEFINE_FINAL_KERNEL

// Evict variant for the LDE's terminal pass: its input lines are dead after
// this read and its output (the committed codeword) is not re-read within the
// LDE phase (next consumer is the Merkle leaf hash), so evict-first keeps
// these dead lines from evicting the monomials that later cosets' initials
// still need.
#define DEFINE_FINAL_EVICT_KERNEL(STAGES)                                                                                                                      \
  EXTERN __launch_bounds__(256, 3) __global__ void ab_natural_monomials_to_bitrev_evals_final_##STAGES##_stages_evict_kernel(                                  \
      bf_matrix_getter<ld_modifier::cs> gmem_in, bf_matrix_setter<st_modifier::cs> gmem_out, const int log_n, const int num_cols_per_coset,                    \
      const int log_cosets_in_tile) {                                                                                                                          \
    natural_monomials_to_bitrev_evals_final_up_to_8_stages<STAGES, ld_modifier::cs, st_modifier::cs>(gmem_in, gmem_out, log_n, num_cols_per_coset,             \
                                                                                                     log_cosets_in_tile);                                      \
  }

DEFINE_FINAL_EVICT_KERNEL(5)
DEFINE_FINAL_EVICT_KERNEL(6)
DEFINE_FINAL_EVICT_KERNEL(7)
DEFINE_FINAL_EVICT_KERNEL(8)

#undef DEFINE_FINAL_EVICT_KERNEL

#define DEFINE_FINAL_EVICT_TMA_KERNEL(STAGES)                                                                                                                  \
  EXTERN __launch_bounds__(256, 3) __global__ void ab_natural_monomials_to_bitrev_evals_final_##STAGES##_stages_evict_tma_kernel(                              \
      bf_matrix_getter<ld_modifier::cs> gmem_in, bf_matrix_setter<st_modifier::cs> gmem_out, const int log_n,                                                  \
      const __grid_constant__ CUtensorMap output_tensor_map) {                                                                                                 \
    natural_monomials_to_bitrev_evals_final_up_to_8_stages_tma<STAGES>(gmem_in, gmem_out, log_n, &output_tensor_map);                                          \
  }

DEFINE_FINAL_EVICT_TMA_KERNEL(5)
DEFINE_FINAL_EVICT_TMA_KERNEL(6)
DEFINE_FINAL_EVICT_TMA_KERNEL(7)
DEFINE_FINAL_EVICT_TMA_KERNEL(8)

#undef DEFINE_FINAL_EVICT_TMA_KERNEL

// Evict + L2-prefetch variant of the terminal pass: while this codeword
// streams out, prefetch the next NTT slab (the launch has exactly n/32
// threads and the source is exactly n/32 128-byte lines:
// one prefetch per thread, issued at each block's tail so the DRAM fetches
// stagger through this kernel's drain). Single-column launches only: the
// prefetch indexing assumes gridDim.x covers one NTT.
#define DEFINE_FINAL_EVICT_PREFETCH_KERNEL(STAGES)                                                                                                             \
  EXTERN __launch_bounds__(256, 3) __global__ void ab_natural_monomials_to_bitrev_evals_final_##STAGES##_stages_evict_prefetch_kernel(                         \
      bf_matrix_getter<ld_modifier::cs> gmem_in, bf_matrix_setter<st_modifier::cs> gmem_out, const int log_n, const int num_cols_per_coset,                    \
      const int log_cosets_in_tile, const bf *prefetch_src) {                                                                                                  \
    natural_monomials_to_bitrev_evals_final_up_to_8_stages<STAGES, ld_modifier::cs, st_modifier::cs>(gmem_in, gmem_out, log_n, num_cols_per_coset,             \
                                                                                                     log_cosets_in_tile);                                      \
    /* Last instruction per block: the grid drains over several waves, so                                                                                      \
       the fetches stagger into the tail of this launch, trailing its own                                                                                      \
       traffic with minimal eviction lead before the next consumer. */                                                                                         \
    if (prefetch_src != nullptr)                                                                                                                               \
      ::airbender::primitives::ptx::prefetch_l2(prefetch_src + (static_cast<size_t>(blockIdx.x) * blockDim.x + threadIdx.x) * 32u);                            \
  }

DEFINE_FINAL_EVICT_PREFETCH_KERNEL(5)
DEFINE_FINAL_EVICT_PREFETCH_KERNEL(6)
DEFINE_FINAL_EVICT_PREFETCH_KERNEL(7)
DEFINE_FINAL_EVICT_PREFETCH_KERNEL(8)

#undef DEFINE_FINAL_EVICT_PREFETCH_KERNEL

#define DEFINE_FINAL_EVICT_PREFETCH_PACKED_TMA_KERNEL(STAGES)                                                                                                  \
  EXTERN __launch_bounds__(256, 3) __global__ void ab_natural_monomials_to_bitrev_evals_final_##STAGES##_stages_evict_prefetch_packed_smem_tma_kernel(         \
      bf_matrix_getter<ld_modifier::cs> gmem_in, bf_matrix_setter<st_modifier::cs> gmem_out, const int log_n, const bf *prefetch_src,                          \
      const __grid_constant__ CUtensorMap output_tensor_map) {                                                                                                 \
    natural_monomials_to_bitrev_evals_final_up_to_8_stages_tma<STAGES, true>(gmem_in, gmem_out, log_n, &output_tensor_map);                                    \
    if (prefetch_src != nullptr)                                                                                                                               \
      ::airbender::primitives::ptx::prefetch_l2(prefetch_src + (static_cast<size_t>(blockIdx.x) * blockDim.x + threadIdx.x) * 32u);                            \
  }

DEFINE_FINAL_EVICT_PREFETCH_PACKED_TMA_KERNEL(5)
DEFINE_FINAL_EVICT_PREFETCH_PACKED_TMA_KERNEL(6)
DEFINE_FINAL_EVICT_PREFETCH_PACKED_TMA_KERNEL(7)

#undef DEFINE_FINAL_EVICT_PREFETCH_PACKED_TMA_KERNEL

EXTERN __launch_bounds__(256, 3) __global__ void ab_natural_monomials_to_bitrev_evals_final_8_stages_evict_prefetch_packed_smem_packed_num2_tma_kernel(
    bf_matrix_getter<ld_modifier::cs> gmem_in, bf_matrix_setter<st_modifier::cs> gmem_out, const int log_n, const bf *prefetch_src,
    const __grid_constant__ CUtensorMap output_tensor_map) {
  natural_monomials_to_bitrev_evals_final_up_to_8_stages_tma<8, true, true>(gmem_in, gmem_out, log_n, &output_tensor_map);
  if (prefetch_src != nullptr)
    ::airbender::primitives::ptx::prefetch_l2(prefetch_src + (static_cast<size_t>(blockIdx.x) * blockDim.x + threadIdx.x) * 32u);
}

// Finish the next column's fine-first hypercube pass in the same block/window
// as the current column's last-coset terminal pass. Both phase-B bodies use
// identical 8192-row ownership, and the natural terminal's shared state is
// dead before this body starts, so they can reuse one shared slab.
template <int STAGES>
DEVICE_FORCEINLINE void cross_column_hypercube_finest(bf_matrix_getter<ld_modifier::cs> gmem_in, bf_matrix_setter<st_modifier::cg> gmem_out, bf *smem_block) {
  using namespace pass_config::three_pass_phase_b;
  constexpr int INITIAL_EXCHG_REGIONS_PER_WARP = 1 << (10 - STAGES);

  const int lane_id = threadIdx.x & 31;
  const int warp_id = threadIdx.x >> 5;
  const int gmem_block_offset = blockIdx.x * VALS_PER_BLOCK;
  gmem_in.add_row(gmem_block_offset + warp_id * VALS_PER_WARP);
  gmem_out.add_row(gmem_block_offset + warp_id * VALS_PER_WARP);

  bf *smem_warp = smem_block + warp_id * VALS_PER_WARP;
  bf vals[VALS_PER_THREAD];

#pragma unroll
  for (int i{0}, row{lane_id}; i < VALS_PER_THREAD; i++, row += WARP_SIZE)
    vals[i] = gmem_in.get_at_row(row);

  if (STAGES >= 5) {
#pragma unroll
    for (int i{0}; i < INITIAL_EXCHG_REGIONS_PER_WARP; i++) {
      if (STAGES == 8) {
        bf *vals_this_region = vals + 8 * i;
        reg_exchg_hypercube_inv<4, 8, 1>(vals_this_region);
        reg_exchg_hypercube_inv<2, 4, 2>(vals_this_region);
        reg_exchg_hypercube_inv<1, 2, 4>(vals_this_region);
      }
      if (STAGES == 7) {
        bf *vals_this_region = vals + 4 * i;
        reg_exchg_hypercube_inv<2, 4, 1>(vals_this_region);
        reg_exchg_hypercube_inv<1, 2, 2>(vals_this_region);
      }
      if (STAGES == 6) {
        bf *vals_this_region = vals + 2 * i;
        reg_exchg_hypercube_inv<1, 2, 1>(vals_this_region);
      }
    }
  }

  warp_transpose_swizzled_v4<VALS_PER_THREAD>(smem_warp, vals, lane_id);

  reg_exchg_hypercube_inv<16, 32, 1>(vals);
  reg_exchg_hypercube_inv<8, 16, 2>(vals);
  reg_exchg_hypercube_inv<4, 8, 4>(vals);
  reg_exchg_hypercube_inv<2, 4, 8>(vals);
  reg_exchg_hypercube_inv<1, 2, 16>(vals);

  warp_transpose_swizzled_v4_mirror<VALS_PER_THREAD>(smem_warp, vals, lane_id);

#pragma unroll
  for (int i{0}, row{lane_id}; i < VALS_PER_THREAD; i++, row += WARP_SIZE)
    gmem_out.set_at_row(row, vals[i]);
}

template <int STAGES, bool PDL>
DEVICE_FORCEINLINE void natural_final_cross_column(bf_matrix_getter<ld_modifier::cs> gmem_in, bf_matrix_setter<st_modifier::cs> gmem_out,
                                                   bf_matrix_getter<ld_modifier::cs> next_hypercube_in, bf_matrix_setter<st_modifier::cg> next_pre_tail_out,
                                                   const int log_n) {
  __shared__ __align__(16) bf smem_block[8192];
  natural_monomials_to_bitrev_evals_final_up_to_8_stages_with_smem<STAGES, ld_modifier::cs, st_modifier::cs, false, false, false, true, true>(
      gmem_in, gmem_out, log_n, 1, 0, smem_block, nullptr, nullptr, next_hypercube_in.ptr);
  __syncthreads();
  if constexpr (PDL) {
    if (threadIdx.x == 0)
      cudaTriggerProgrammaticLaunchCompletion();
  }
  cross_column_hypercube_finest<STAGES>(next_hypercube_in, next_pre_tail_out, smem_block);
}

#define DEFINE_RETAINED_CROSS_COLUMN_FINAL_KERNEL(STAGES, SUFFIX, PDL)                                                                                         \
  EXTERN __launch_bounds__(256, 2) __global__ void ab_natural_monomials_to_bitrev_evals_final_##STAGES##_stages_evict_##SUFFIX##_kernel(                       \
      bf_matrix_getter<ld_modifier::cs> gmem_in, bf_matrix_setter<st_modifier::cs> gmem_out, bf_matrix_getter<ld_modifier::cs> next_hypercube_in,              \
      bf_matrix_setter<st_modifier::cg> next_pre_tail_out, const int log_n) {                                                                                  \
    natural_final_cross_column<STAGES, PDL>(gmem_in, gmem_out, next_hypercube_in, next_pre_tail_out, log_n);                                                   \
  }

DEFINE_RETAINED_CROSS_COLUMN_FINAL_KERNEL(5, delayed_prefetch_packed_smem_cross_column, false)
DEFINE_RETAINED_CROSS_COLUMN_FINAL_KERNEL(6, delayed_prefetch_packed_smem_cross_column_pdl, true)
DEFINE_RETAINED_CROSS_COLUMN_FINAL_KERNEL(7, delayed_prefetch_packed_smem_cross_column_pdl, true)
DEFINE_RETAINED_CROSS_COLUMN_FINAL_KERNEL(8, delayed_prefetch_packed_smem_cross_column_pdl, true)

#undef DEFINE_RETAINED_CROSS_COLUMN_FINAL_KERNEL

} // namespace airbender::ntt
