#include "uniskip_abi.cuh"

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

} // namespace airbender::gkr_uniskip_bench
