// Backward coefficient-term ISA executor (design section 11).
//
// SCOPE OF THIS FILE AT THIS POINT IN THE PLAN. Task 9 established the ABI, the
// launch geometry and the specialization set. The typed source resolvers
// (Task 10) and the u16 decode/arithmetic loop (Task 11) are NOT here yet:
// `coefficient_body` sets up the private cell file, initializes the two
// accumulators exactly as section 11 specifies, and writes the contribution
// pair. `desc.program` is not decoded, so the kernels currently publish the
// `c_init`-only value of `acc_c0`. They are launchable and correct for a
// zero-word program; they are not yet the executor.
//
// What is deliberately absent, and must stay absent (section 11): a T0/T2
// split, warp shuffles, a general accumulator, an accumulator stash, a
// batch-accumulate destination, an `AccInit` operand, validation work in a
// release kernel, and any extra launch.

#include "../support/eq_inline.cuh"
#include "coefficient_vm.cuh"

__device__ __constant__ e4 ab_gkr_bwd_coeff_fold_factors[airbender::prover::gkr::BWD_COEFF_FOLD_FACTOR_CAP];

namespace airbender::prover::gkr {

// Coefficient banks (section 9.3). The bank is selected launch-wide; no term or
// value operand carries an address-space tag.
//
// Index 0 is `+1` and index 1 is `-1` — reserved literals that let the executor
// use add/FMA or subtract/FMS with no E4 coefficient multiplication at all. A
// bank entry `i` is index `BWD_COEFF_INDEX_RESERVED + i`.

// Reads the incumbent stream-ordered `__constant__` bank. Direct symbol access
// is required for LDC emission, so this loader is not templated.
struct coeff_bank_constant {
  DEVICE_FORCEINLINE e4 operator[](const u16 index) const { return ::ab_gkr_flat_coefficients[index - BWD_COEFF_INDEX_RESERVED]; }
};

// Reads the descriptor's single coefficient pointer. The constant
// specialization ignores that pointer entirely.
struct coeff_bank_pointer {
  const e4 *base;
  DEVICE_FORCEINLINE e4 operator[](const u16 index) const { return load<e4, ld_modifier::ca>(base, index - BWD_COEFF_INDEX_RESERVED); }
};

// The one place a coefficient index becomes a value: the two reserved literals
// never touch a bank.
template <typename Bank> DEVICE_FORCEINLINE e4 coefficient_value(const Bank &bank, const u16 index) {
  if (index == BWD_COEFF_INDEX_ONE)
    return e4::ONE();
  if (index == BWD_COEFF_INDEX_NEG_ONE) {
    constexpr e4 minus_one = e4::from_scalar(bf::neg(bf::ONE()));
    return minus_one;
  }
  return bank[index];
}

// Each thread owns a private cell file of `cell_budget` E4 cells. Within a warp
// the file is transposed so a typed access is one stride-32 index in the typed
// array: `thread_bf[bf_lane << 5]` and `thread_e4[e4_bucket << 5]`. An E4 cell
// is four consecutive BF lanes, so `e4_bucket = bf_lane >> 2` and an E4 lane
// must be four-aligned.
struct cell_file {
  bf *bf_lanes;
  e4 *e4_cells;
};

DEVICE_FORCEINLINE cell_file thread_cell_file(e4 *dynamic_cells, const u32 cell_budget) {
  const u32 lane = threadIdx.x & BWD_COEFF_LANE_INDEX_MASK;
  const u32 warp = threadIdx.x >> BWD_COEFF_WARP_SHIFT;
  e4 *warp_base = dynamic_cells + static_cast<size_t>(warp) * cell_budget * BWD_COEFF_WARP_LANES;
  return cell_file{reinterpret_cast<bf *>(warp_base) + lane, warp_base + lane};
}

// REGIME_IS_R0 and FOLD_DEPTH are the section 11 specialization axes; the cell
// budget is runtime launch metadata, so one instantiation covers c2..c16.
template <bool REGIME_IS_R0, u32 FOLD_DEPTH, typename Bank> DEVICE_FORCEINLINE void coefficient_body(const bwd_coeff_desc &desc, const Bank &bank) {
  static_assert(FOLD_DEPTH <= BWD_COEFF_MAX_FOLD_DEPTH, "fold depth outside D0..D3");
  static_assert(!REGIME_IS_R0 || FOLD_DEPTH == 0, "R0 never folds: FoldDepth is a continuation-only axis");

  extern __shared__ e4 bwd_coeff_cells_dyn[];
  const cell_file cells = thread_cell_file(bwd_coeff_cells_dyn, desc.cell_budget);

  // One thread per logical row; BWD_COEFF_ROWS_PER_BLOCK rows per block.
  const size_t logical_row = static_cast<size_t>(blockIdx.x) * blockDim.x + threadIdx.x;
  if (logical_row >= desc.logical_rows)
    return;

  e4 acc_c0 = desc.c_init == BWD_COEFF_C_INIT_NONE ? e4::ZERO() : coefficient_value(bank, desc.c_init);
  e4 acc_c2 = e4::ZERO();

  // TASK 10 inserts the typed R0/D0..D3 source resolvers here and TASK 11 the
  // sequential u16 decode loop over `desc.program[0 .. desc.num_words)`, which
  // is warp-uniform and never randomly accessed. `cells` is its private file.
  (void)cells;

  // `lower_bwd_coeff` rejects a null `contributions` or `eq_low`
  // (BwdCoeffLowerError::NullRuntimePointer), so this is defence in depth
  // against a hand-built descriptor, NOT a supported "evaluate but do not
  // store" mode. Silently producing nothing is the safest response a release
  // kernel can give: it has no error channel.
  if (desc.contributions == nullptr || desc.eq_low == nullptr)
    return;
  const e4 eq = gkr_compute_eq_inline<e4>(desc.eq_low, desc.eq_sizes, static_cast<u32>(logical_row));
  store<e4, st_modifier::cs>(desc.contributions, e4::mul(eq, acc_c0), logical_row);
  store<e4, st_modifier::cs>(desc.contributions + desc.logical_rows, e4::mul(eq, acc_c2), logical_row);
}

template <bool REGIME_IS_R0, u32 FOLD_DEPTH> DEVICE_FORCEINLINE void coefficient_body_constant(const bwd_coeff_desc &desc) {
  coefficient_body<REGIME_IS_R0, FOLD_DEPTH>(desc, coeff_bank_constant{});
}

template <bool REGIME_IS_R0, u32 FOLD_DEPTH> DEVICE_FORCEINLINE void coefficient_body_pointer(const bwd_coeff_desc &desc) {
  coefficient_body<REGIME_IS_R0, FOLD_DEPTH>(desc, coeff_bank_pointer{desc.coefficients});
}

} // namespace airbender::prover::gkr

EXTERN __global__ void ab_gkr_bwd_coeff_build_fold_factors_kernel(const e4 *round_challenges, const u32 target_depth, const u32 fold_depth, e4 *fold_factors) {
  using namespace airbender::primitives::field;
  const u32 slot = threadIdx.x;
  u32 delta;
  u32 leaf;
  if (slot < 2) {
    delta = 1;
    leaf = slot;
  } else {
    if (fold_depth < 2 || slot >= 2 + (1u << fold_depth))
      return;
    delta = fold_depth;
    leaf = slot - 2;
  }
  if (target_depth < delta)
    return;

  const u32 backing_depth = target_depth - delta;
  const e4 first_challenge = round_challenges[backing_depth];
  e4 factor = (leaf & 1u) != 0 ? first_challenge : e4::sub(e4::ONE(), first_challenge);
  for (u32 round = 1; round < delta; round++) {
    const e4 challenge = round_challenges[backing_depth + round];
    const e4 term = ((leaf >> round) & 1u) != 0 ? challenge : e4::sub(e4::ONE(), challenge);
    factor = e4::mul(factor, term);
  }
  fold_factors[slot] = factor;
}

#define AB_GKR_BWD_COEFF_KERNEL(symbol, regime_is_r0, fold_depth, body)                                                                                        \
  EXTERN __launch_bounds__(airbender::prover::gkr::BWD_COEFF_THREADS_PER_BLOCK)                                                                                \
      __global__ void symbol(const __grid_constant__ airbender::prover::gkr::bwd_coeff_desc desc) {                                                            \
    airbender::prover::gkr::body<regime_is_r0, fold_depth>(desc);                                                                                              \
  }

AB_GKR_BWD_COEFF_KERNEL(ab_gkr_bwd_coeff_r0_const_kernel, true, 0, coefficient_body_constant)
AB_GKR_BWD_COEFF_KERNEL(ab_gkr_bwd_coeff_r0_ptr_kernel, true, 0, coefficient_body_pointer)
AB_GKR_BWD_COEFF_KERNEL(ab_gkr_bwd_coeff_ext_d0_const_kernel, false, 0, coefficient_body_constant)
AB_GKR_BWD_COEFF_KERNEL(ab_gkr_bwd_coeff_ext_d0_ptr_kernel, false, 0, coefficient_body_pointer)
AB_GKR_BWD_COEFF_KERNEL(ab_gkr_bwd_coeff_ext_d1_const_kernel, false, 1, coefficient_body_constant)
AB_GKR_BWD_COEFF_KERNEL(ab_gkr_bwd_coeff_ext_d1_ptr_kernel, false, 1, coefficient_body_pointer)
AB_GKR_BWD_COEFF_KERNEL(ab_gkr_bwd_coeff_ext_d2_const_kernel, false, 2, coefficient_body_constant)
AB_GKR_BWD_COEFF_KERNEL(ab_gkr_bwd_coeff_ext_d2_ptr_kernel, false, 2, coefficient_body_pointer)
AB_GKR_BWD_COEFF_KERNEL(ab_gkr_bwd_coeff_ext_d3_const_kernel, false, 3, coefficient_body_constant)
AB_GKR_BWD_COEFF_KERNEL(ab_gkr_bwd_coeff_ext_d3_ptr_kernel, false, 3, coefficient_body_pointer)

#undef AB_GKR_BWD_COEFF_KERNEL
