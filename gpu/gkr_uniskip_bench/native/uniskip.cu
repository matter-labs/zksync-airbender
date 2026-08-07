#include "uniskip_abi.cuh"

#include <nvtx3/nvToolsExt.h>

// Storage for the `__constant__` symbols declared by uniskip_abi.cuh.
__device__ __constant__ e4 ab_gkr_uniskip_coeff_bank[airbender::gkr_uniskip_bench::UNISKIP_COEFF_BANK];
__device__ __constant__ e4 ab_gkr_uniskip_eq_high[2 * airbender::gkr_uniskip_bench::UNISKIP_EQ_HIGH];
__device__ __constant__ bf ab_gkr_uniskip_lde_matrix[airbender::gkr_uniskip_bench::UNISKIP_TAPS * airbender::gkr_uniskip_bench::UNISKIP_TAPS];
__device__ __constant__ e4 ab_gkr_uniskip_fold_weights[airbender::gkr_uniskip_bench::UNISKIP_TAPS];

namespace airbender::gkr_uniskip_bench {

// Type-check the source accessor for both field classes until the eval kernel
// instantiates it (the LDE kernels below address the taps directly).
template __device__ bf uniskip_source_value<bf>(const uniskip_vm_desc &, u16, u32, u32);
template __device__ e4 uniskip_source_value<e4>(const uniskip_vm_desc &, u16, u32, u32);

// Deterministic data generator, reproduced bit-for-bit by `src/reference.rs`.
// `index` is the ABSOLUTE index of the field element inside its backing
// allocation; `component` tags the bf limbs of an e4 (0 for a bf element).
// The result is canonical in [1, ORDER - 1] and never zero.
DEVICE_FORCEINLINE u32 uniskip_init_canonical(const u32 seed, const u64 index, const u32 component) {
  constexpr u64 ORDER_MINUS_ONE = bf::ORDER - 1;
  return static_cast<u32>((u64{seed} + index * 17 + u64{component} * 0x101) % ORDER_MINUS_ONE + 1);
}

EXTERN __global__ void ab_gkr_uniskip_init_bf_kernel(bf *dst, const u64 count, const u32 seed) {
  for (u64 i = blockIdx.x * u64{blockDim.x} + threadIdx.x; i < count; i += u64{blockDim.x} * gridDim.x)
    dst[i] = bf::from_u32_unchecked(uniskip_init_canonical(seed, i, 0));
}

EXTERN __global__ void ab_gkr_uniskip_init_e4_kernel(e4 *dst, const u64 count, const u32 seed) {
  for (u64 i = blockIdx.x * u64{blockDim.x} + threadIdx.x; i < count; i += u64{blockDim.x} * gridDim.x) {
    bf components[4];
#pragma unroll
    for (u32 c = 0; c < 4; ++c)
      components[c] = bf::from_u32_unchecked(uniskip_init_canonical(seed, i, c));
    dst[i] = e4(components);
  }
}

// The lowered source table IS the used-column map: `jobs` lists the source-record
// indices of one field class, so there are no dense window spans and the processed
// count is exact by construction — one output per (job, coset cell, row).
EXTERN __global__ void ab_gkr_uniskip_lde_bf_kernel(const __grid_constant__ uniskip_vm_desc desc, const u16 *jobs, const u32 num_jobs) {
  const u64 rows = u64{1} << desc.log_rows;
  const u64 total = rows * u64{num_jobs} * UNISKIP_TAPS;
  for (u64 i = blockIdx.x * u64{blockDim.x} + threadIdx.x; i < total; i += u64{blockDim.x} * gridDim.x) {
    const u32 job = static_cast<u32>(i >> desc.log_rows) / UNISKIP_TAPS;
    const u32 cell = static_cast<u32>(i >> desc.log_rows) % UNISKIP_TAPS;
    const u64 row = i & (rows - 1);
    const uniskip_source_record rec = desc.source[jobs[job]];
    const u32 window = rec.addr >> 7;
    const size_t col = rec.addr & 0x7f;
    const bf *taps = reinterpret_cast<const bf *>(desc.tap_bases[window].base);
    bf *coset = reinterpret_cast<bf *>(const_cast<u8 *>(desc.coset_bases[window].base));
    bf acc = bf::ZERO();
#pragma unroll
    for (u32 t = 0; t < UNISKIP_TAPS; ++t)
      acc = bf::add(
          acc, bf::mul(ab_gkr_uniskip_lde_matrix[cell * UNISKIP_TAPS + t], load<bf, ld_modifier::ca>(taps, ((col * UNISKIP_TAPS + t) << desc.log_rows) + row)));
    coset[((col * UNISKIP_TAPS + cell) << desc.log_rows) + row] = acc;
  }
}

EXTERN __global__ void ab_gkr_uniskip_lde_e4_kernel(const __grid_constant__ uniskip_vm_desc desc, const u16 *jobs, const u32 num_jobs) {
  const u64 rows = u64{1} << desc.log_rows;
  const u64 total = rows * u64{num_jobs} * UNISKIP_TAPS;
  for (u64 i = blockIdx.x * u64{blockDim.x} + threadIdx.x; i < total; i += u64{blockDim.x} * gridDim.x) {
    const u32 job = static_cast<u32>(i >> desc.log_rows) / UNISKIP_TAPS;
    const u32 cell = static_cast<u32>(i >> desc.log_rows) % UNISKIP_TAPS;
    const u64 row = i & (rows - 1);
    const uniskip_source_record rec = desc.source[jobs[job]];
    const u32 window = rec.addr >> 7;
    const size_t col = rec.addr & 0x7f;
    const e4 *taps = reinterpret_cast<const e4 *>(desc.tap_bases[window].base);
    e4 *coset = reinterpret_cast<e4 *>(const_cast<u8 *>(desc.coset_bases[window].base));
    e4 acc = e4::ZERO();
#pragma unroll
    for (u32 t = 0; t < UNISKIP_TAPS; ++t)
      acc = e4::add(
          acc, e4::mul(load<e4, ld_modifier::ca>(taps, ((col * UNISKIP_TAPS + t) << desc.log_rows) + row), ab_gkr_uniskip_lde_matrix[cell * UNISKIP_TAPS + t]));
    coset[((col * UNISKIP_TAPS + cell) << desc.log_rows) + row] = acc;
  }
}

// ROW SHAPE. One thread owns (job, row) and emits all 16 coset cells from ONE tap
// load, so the 16 threads that shared a row's taps in the cell-shape kernel above are
// now a single THREAD — the reuse is register-local and the 16x tap re-read is gone by
// construction. Lanes are consecutive rows, so each tap-plane load and each coset-plane
// store is warp-coalesced exactly as before. Bytes written are identical to the
// cell-shape kernel's.
EXTERN __global__ void ab_gkr_uniskip_lde_bf_v2_kernel(const __grid_constant__ uniskip_vm_desc desc, const u16 *jobs, const u32 num_jobs) {
  const u64 rows = u64{1} << desc.log_rows;
  const u64 total = rows * u64{num_jobs};
  for (u64 i = blockIdx.x * u64{blockDim.x} + threadIdx.x; i < total; i += u64{blockDim.x} * gridDim.x) {
    const u32 job = static_cast<u32>(i >> desc.log_rows);
    const u64 row = i & (rows - 1);
    const uniskip_source_record rec = desc.source[jobs[job]];
    const u32 window = rec.addr >> 7;
    const size_t col = rec.addr & 0x7f;
    const bf *taps = reinterpret_cast<const bf *>(desc.tap_bases[window].base);
    bf *coset = reinterpret_cast<bf *>(const_cast<u8 *>(desc.coset_bases[window].base));
    bf tap[UNISKIP_TAPS];
#pragma unroll
    for (u32 t = 0; t < UNISKIP_TAPS; ++t)
      tap[t] = load<bf, ld_modifier::cs>(taps, ((col * UNISKIP_TAPS + t) << desc.log_rows) + row);
#pragma unroll
    for (u32 cell = 0; cell < UNISKIP_TAPS; ++cell) {
      bf acc = bf::ZERO();
#pragma unroll
      for (u32 t = 0; t < UNISKIP_TAPS; ++t)
        acc = bf::add(acc, bf::mul(ab_gkr_uniskip_lde_matrix[cell * UNISKIP_TAPS + t], tap[t]));
      coset[((col * UNISKIP_TAPS + cell) << desc.log_rows) + row] = acc;
    }
  }
}

// LIMB-LANE ROW SHAPE. One thread owns (job, row, limb): limb = lane & 3 and the row
// advances with lane >> 2, so a warp covers 8 rows x 4 limbs = 128 B contiguous of every
// plane it touches. The coset LDE is BF-linear per limb, so a lane needs only its own
// limb of the 16 taps to produce its limb of all 16 cells — the cell-sharers of the
// cell-shape kernel collapse into ONE thread here too, and its 4 limb-sharers are
// adjacent lanes. Bytes written are identical to the cell-shape kernel's.
EXTERN __global__ void ab_gkr_uniskip_lde_e4_v2_kernel(const __grid_constant__ uniskip_vm_desc desc, const u16 *jobs, const u32 num_jobs) {
  constexpr u32 LIMBS = 4;
  const u64 rows = u64{1} << desc.log_rows;
  const u64 total = rows * u64{num_jobs} * LIMBS;
  for (u64 i = blockIdx.x * u64{blockDim.x} + threadIdx.x; i < total; i += u64{blockDim.x} * gridDim.x) {
    const u32 job = static_cast<u32>(i >> (desc.log_rows + 2));
    const u64 row = (i >> 2) & (rows - 1);
    const u32 limb = static_cast<u32>(i) & (LIMBS - 1);
    const uniskip_source_record rec = desc.source[jobs[job]];
    const u32 window = rec.addr >> 7;
    const size_t col = rec.addr & 0x7f;
    // e4 planes viewed as bf words: limb `l` of element `e` is word `4e + l`. The lane
    // base is 64-bit; the plane-to-plane offsets below fit 32 bits (15 * 4 << 21).
    const size_t lane = (((col * UNISKIP_TAPS) << desc.log_rows) + row) * LIMBS + limb;
    const bf *taps = reinterpret_cast<const bf *>(desc.tap_bases[window].base) + lane;
    bf *coset = reinterpret_cast<bf *>(const_cast<u8 *>(desc.coset_bases[window].base)) + lane;
    const u32 plane = LIMBS << desc.log_rows;
    bf tap[UNISKIP_TAPS];
#pragma unroll
    for (u32 t = 0; t < UNISKIP_TAPS; ++t)
      tap[t] = load<bf, ld_modifier::cs>(taps, t * plane);
#pragma unroll
    for (u32 cell = 0; cell < UNISKIP_TAPS; ++cell) {
      bf acc = bf::ZERO();
#pragma unroll
      for (u32 t = 0; t < UNISKIP_TAPS; ++t)
        acc = bf::add(acc, bf::mul(tap[t], ab_gkr_uniskip_lde_matrix[cell * UNISKIP_TAPS + t]));
      coset[cell * plane] = acc;
    }
  }
}

// FOLD. Collapses the 16 taps on H into the evaluation at the round challenge r:
// folded[source * rows + row] = sum_t L_t(r) * tap_t(row), an e4 for both input
// classes. Output is indexed by SOURCE id, not by job: the two class job lists
// partition the source ids, so both kernels share one buffer and each column's
// folded values stay contiguous. The taps are read exactly once here, hence `cs`
// rather than the LDE's reuse-friendly `ca`.
EXTERN __global__ void ab_gkr_uniskip_fold_bf_kernel(const __grid_constant__ uniskip_vm_desc desc, const u16 *jobs, const u32 num_jobs, e4 *folded) {
  const u64 rows = u64{1} << desc.log_rows;
  const u64 total = rows * u64{num_jobs};
  for (u64 i = blockIdx.x * u64{blockDim.x} + threadIdx.x; i < total; i += u64{blockDim.x} * gridDim.x) {
    const u32 job = static_cast<u32>(i >> desc.log_rows);
    const u64 row = i & (rows - 1);
    const u16 source = jobs[job];
    const uniskip_source_record rec = desc.source[source];
    const u32 window = rec.addr >> 7;
    const size_t col = rec.addr & 0x7f;
    const bf *taps = reinterpret_cast<const bf *>(desc.tap_bases[window].base);
    e4 acc = e4::ZERO();
#pragma unroll
    for (u32 t = 0; t < UNISKIP_TAPS; ++t)
      acc = e4::fma(ab_gkr_uniskip_fold_weights[t], load<bf, ld_modifier::cs>(taps, ((col * UNISKIP_TAPS + t) << desc.log_rows) + row), acc);
    folded[u64{source} * rows + row] = acc;
  }
}

EXTERN __global__ void ab_gkr_uniskip_fold_e4_kernel(const __grid_constant__ uniskip_vm_desc desc, const u16 *jobs, const u32 num_jobs, e4 *folded) {
  const u64 rows = u64{1} << desc.log_rows;
  const u64 total = rows * u64{num_jobs};
  for (u64 i = blockIdx.x * u64{blockDim.x} + threadIdx.x; i < total; i += u64{blockDim.x} * gridDim.x) {
    const u32 job = static_cast<u32>(i >> desc.log_rows);
    const u64 row = i & (rows - 1);
    const u16 source = jobs[job];
    const uniskip_source_record rec = desc.source[source];
    const u32 window = rec.addr >> 7;
    const size_t col = rec.addr & 0x7f;
    const e4 *taps = reinterpret_cast<const e4 *>(desc.tap_bases[window].base);
    e4 acc = e4::ZERO();
#pragma unroll
    for (u32 t = 0; t < UNISKIP_TAPS; ++t)
      acc = e4::fma(ab_gkr_uniskip_fold_weights[t], load<e4, ld_modifier::cs>(taps, ((col * UNISKIP_TAPS + t) << desc.log_rows) + row), acc);
    folded[u64{source} * rows + row] = acc;
  }
}

DEVICE_FORCEINLINE e4 uniskip_shfl_xor_e4(const e4 value, const int lane_mask) {
  static_assert(sizeof(e4) == sizeof(uint4));
  e4 result;
  *reinterpret_cast<uint4 *>(&result) = shfl_xor(0xffffffffu, *reinterpret_cast<const uint4 *>(&value), lane_mask, UNISKIP_ROWS_PER_BLOCK);
  return result;
}

// Sum one e4 across a full warp; every lane ends with the total.
DEVICE_FORCEINLINE e4 uniskip_warp_sum(e4 value) {
#pragma unroll
  for (int lane_mask = UNISKIP_ROWS_PER_BLOCK >> 1; lane_mask > 0; lane_mask >>= 1)
    value = e4::add(value, uniskip_shfl_xor_e4(value, lane_mask));
  return value;
}

// T(row) of the factored eq: the low `low` bits of the row index eq_low, the next
// `high[1]` bits high table 1, the top bits high table 0 (the split
// `geometry::Geometry::split_row` mirrors). Every shift is < log_rows <= 21.
DEVICE_FORCEINLINE e4 uniskip_eq_at(const uniskip_vm_desc &desc, const u32 row) {
  const u32 low_bits = desc.eq_sizes.low;
  const u32 high1_bits = desc.eq_sizes.high[1];
  const u32 low = row & ((1u << low_bits) - 1);
  const u32 high1 = (row >> low_bits) & ((1u << high1_bits) - 1);
  const u32 high0 = row >> (low_bits + high1_bits);
  const e4 high = e4::mul(ab_gkr_uniskip_eq_high[high0], ab_gkr_uniskip_eq_high[UNISKIP_EQ_HIGH + high1]);
  return e4::mul(high, load<e4, ld_modifier::ca>(desc.eq_low, low));
}

// CELL-SLAB WARPS. blockDim = 256; lane = row inside a 32-row tile, so the whole
// block works one tile and warp w owns cells 4w..4w+3 (warps 0-3 tap cells, warps
// 4-7 coset cells — the H-vs-coset choice is warp-uniform inside the accessor).
// The 4 accumulators are indexed ONLY by fully unrolled loops: a dynamic index
// would put them in local memory and spill.
// `Geometry` guarantees rows == gridDim.x * UNISKIP_ROWS_PER_BLOCK (log_rows >= 5),
// so no row is out of range.
EXTERN __global__ void ab_gkr_uniskip_eval_kernel(const __grid_constant__ uniskip_vm_desc desc) {
  const u32 lane = threadIdx.x % UNISKIP_ROWS_PER_BLOCK;
  const u32 warp = threadIdx.x / UNISKIP_ROWS_PER_BLOCK;
  const u32 row = blockIdx.x * UNISKIP_ROWS_PER_BLOCK + lane;
  const u32 first_cell = warp * UNISKIP_CELLS_PER_WARP;

  e4 acc[UNISKIP_CELLS_PER_WARP];
#pragma unroll
  for (u32 i = 0; i < UNISKIP_CELLS_PER_WARP; ++i)
    acc[i] = e4::ZERO();

  for (u32 pc = 0; pc < desc.record_count;) {
    const uniskip_term term = desc.program[pc];
    const e4 coeff = ab_gkr_uniskip_coeff_bank[term.coeff];
    if (term.term_class == UNISKIP_CLASS_GROUP_BF) {
      // Header: coeff = core bank id, source_a = arity. The members sum in bf,
      // scaled by their IMMEDIATE id, and the whole group costs one e4 coeff FMA.
      const u32 arity = term.source_a;
      bf sum[UNISKIP_CELLS_PER_WARP];
#pragma unroll
      for (u32 i = 0; i < UNISKIP_CELLS_PER_WARP; ++i)
        sum[i] = bf::ZERO();
      for (u32 m = 1; m <= arity; ++m) {
        const uniskip_term member = desc.program[pc + m];
        const bool product = member.term_class == UNISKIP_CLASS_PRODUCT_BF_BF;
#pragma unroll
        for (u32 i = 0; i < UNISKIP_CELLS_PER_WARP; ++i) {
          const u32 cell = first_cell + i;
          bf value = uniskip_source_value<bf>(desc, member.source_a, cell, row);
          if (product)
            value = bf::mul(value, uniskip_source_value<bf>(desc, member.source_b, cell, row));
          if (member.coeff == UNISKIP_IMMEDIATE_ONE)
            sum[i] = bf::add(sum[i], value);
          else if (member.coeff == UNISKIP_IMMEDIATE_NEG_ONE)
            sum[i] = bf::sub(sum[i], value);
          else
            sum[i] = bf::fma(desc.immediates[member.coeff - UNISKIP_IMMEDIATE_RESERVED], value, sum[i]);
        }
      }
#pragma unroll
      for (u32 i = 0; i < UNISKIP_CELLS_PER_WARP; ++i)
        acc[i] = e4::fma(coeff, sum[i], acc[i]);
      pc += arity + 1;
      continue;
    }
    switch (term.term_class) {
    case UNISKIP_CLASS_LINEAR_BF:
#pragma unroll
      for (u32 i = 0; i < UNISKIP_CELLS_PER_WARP; ++i)
        acc[i] = e4::fma(coeff, uniskip_source_value<bf>(desc, term.source_a, first_cell + i, row), acc[i]);
      break;
    case UNISKIP_CLASS_LINEAR_E4:
#pragma unroll
      for (u32 i = 0; i < UNISKIP_CELLS_PER_WARP; ++i)
        acc[i] = e4::fma(coeff, uniskip_source_value<e4>(desc, term.source_a, first_cell + i, row), acc[i]);
      break;
    case UNISKIP_CLASS_PRODUCT_BF_BF:
#pragma unroll
      for (u32 i = 0; i < UNISKIP_CELLS_PER_WARP; ++i) {
        const u32 cell = first_cell + i;
        const bf a = uniskip_source_value<bf>(desc, term.source_a, cell, row);
        const bf b = uniskip_source_value<bf>(desc, term.source_b, cell, row);
        acc[i] = e4::fma(coeff, bf::mul(a, b), acc[i]);
      }
      break;
    case UNISKIP_CLASS_PRODUCT_BF_E4:
#pragma unroll
      for (u32 i = 0; i < UNISKIP_CELLS_PER_WARP; ++i) {
        const u32 cell = first_cell + i;
        const bf a = uniskip_source_value<bf>(desc, term.source_a, cell, row);
        const e4 b = uniskip_source_value<e4>(desc, term.source_b, cell, row);
        acc[i] = e4::fma(coeff, e4::mul(b, a), acc[i]);
      }
      break;
    case UNISKIP_CLASS_PRODUCT_E4_E4:
#pragma unroll
      for (u32 i = 0; i < UNISKIP_CELLS_PER_WARP; ++i) {
        const u32 cell = first_cell + i;
        const e4 a = uniskip_source_value<e4>(desc, term.source_a, cell, row);
        const e4 b = uniskip_source_value<e4>(desc, term.source_b, cell, row);
        acc[i] = e4::fma(coeff, e4::mul(a, b), acc[i]);
      }
      break;
    }
    ++pc;
  }

  const e4 eq = uniskip_eq_at(desc, row);
#pragma unroll
  for (u32 i = 0; i < UNISKIP_CELLS_PER_WARP; ++i) {
    const e4 total = uniskip_warp_sum(e4::mul(acc[i], eq));
    if (lane == 0)
      desc.partials[blockIdx.x * UNISKIP_CELLS + first_cell + i] = total;
  }
}

// One block per cell; each sums its column of the partials matrix.
EXTERN __global__ void ab_gkr_uniskip_finalize_kernel(const e4 *partials, const u32 blocks, e4 *q) {
  __shared__ e4 warp_sums[UNISKIP_WARPS_PER_BLOCK];
  const u32 cell = blockIdx.x;
  const u32 lane = threadIdx.x % UNISKIP_ROWS_PER_BLOCK;
  const u32 warp = threadIdx.x / UNISKIP_ROWS_PER_BLOCK;

  e4 sum = e4::ZERO();
  for (u32 block = threadIdx.x; block < blocks; block += UNISKIP_THREADS_PER_BLOCK)
    sum = e4::add(sum, load<e4, ld_modifier::cs>(partials, block * UNISKIP_CELLS + cell));
  sum = uniskip_warp_sum(sum);
  if (lane == 0)
    warp_sums[warp] = sum;
  __syncthreads();
  if (warp != 0)
    return;
  sum = uniskip_warp_sum(lane < UNISKIP_WARPS_PER_BLOCK ? warp_sums[lane] : e4::ZERO());
  if (lane == 0)
    q[cell] = sum;
}

// NVTX shim. gpu_core owns the cluster's NVTX wrapper, but it is a dev-dependency
// here (crate-root serial guard only), so the two calls the bench needs are
// exported from its own archive. nvtx3 is header-only and inert with no profiler
// attached.
EXTERN void ab_gkr_uniskip_nvtx_range_push(const char *name) { nvtxRangePushA(name); }
EXTERN void ab_gkr_uniskip_nvtx_range_pop() { nvtxRangePop(); }

} // namespace airbender::gkr_uniskip_bench
