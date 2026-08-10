// v3 R4 rider: does a lane-divergent constant load serialize per unique address on sm_120?
//
// Standalone TU. It shares no header, no descriptor and no symbol with the pass kernels —
// the pair TU's SASS is frozen, so the probe must be unable to move it.
//
// K, the number of distinct constant addresses a warp touches per LDC, is a RUNTIME
// property of the uploaded table plus the (mask, step) pair, never a template argument:
// one instruction stream serves every K, which is the whole point of the measurement.
// The table is a pointer chase — entry at byte offset `o` holds the next byte offset — so
// the address of load n+1 IS the value of load n. That makes the latency loop a true
// loop-carried dependency through the constant cache and costs zero address arithmetic.
#include "common.cuh"

namespace airbender::gkr_uniskip_bench {

// 32 lanes at the widest stride under test (128 B apart) — 4 KB of constant bank 3.
constexpr u32 UNISKIP_LDC_PROBE_WORDS = 1024;
// Independent chases per thread in the throughput kernel: enough in-flight loads that the
// saturated regime measures issue/replay cost rather than the dependent latency above.
constexpr u32 UNISKIP_LDC_PROBE_CHAINS = 8;

} // namespace airbender::gkr_uniskip_bench

// A definition, not the crate's usual `EXTERN` form: `extern "C" T x[N];` is a declaration
// that some other TU has to define, and nothing else in the archive owns this table. Global
// scope keeps the symbol unmangled, so the inline asm below and the Rust upload stub both
// still name it exactly.
__device__ __constant__ u32 ab_gkr_uniskip_ldc_table[airbender::gkr_uniskip_bench::UNISKIP_LDC_PROBE_WORDS];

namespace airbender::gkr_uniskip_bench {

// `volatile` so the load can be neither hoisted out of the loop nor CSE'd across the
// unroll, and hand-written so it is `ld.const` (SASS `LDC c[0x3][Rn]`) and not a generic
// load; the register operand is what keeps it off the uniform datapath (`LDCU`). Naming
// the symbol directly is what buys the bare one-instruction form — reaching it through a
// C++ pointer costs a generic/const round trip inside the dependent chain.
__device__ __forceinline__ u32 ldc_chase(u32 byte_offset) {
  u32 next;
  asm volatile("{\n\t"
               ".reg .u64 base;\n\t"
               ".reg .u64 off;\n\t"
               ".reg .u64 addr;\n\t"
               "mov.u64 base, ab_gkr_uniskip_ldc_table;\n\t"
               "cvt.u64.u32 off, %1;\n\t"
               "add.s64 addr, base, off;\n\t"
               "ld.const.u32 %0, [addr];\n\t"
               "}"
               : "=r"(next)
               : "r"(byte_offset));
  return next;
}

__device__ __forceinline__ u32 chase_start(u32 mask, u32 step, u32 chain) { return (((threadIdx.x & 31u) + chain) * step) & mask; }

__device__ __forceinline__ void publish(u32 sink_value, u64 elapsed, u32 *sink, u64 *cycles) {
  if (threadIdx.x == 0)
    cycles[blockIdx.x] = elapsed;
  sink[blockIdx.x * blockDim.x + threadIdx.x] = sink_value;
}

} // namespace airbender::gkr_uniskip_bench

using namespace airbender::gkr_uniskip_bench;

// The only C++ reference to the table, and it has to exist: nvcc does not count a mention
// inside inline asm as a use, so without this the `.const` array never reaches PTX and
// ptxas rejects the chase's symbol. It doubles as the host's readback of what the device
// actually sees in bank 3.
EXTERN __global__ void ab_gkr_uniskip_ldc_readback_kernel(u32 *out, u32 words) {
  const u32 word = blockIdx.x * blockDim.x + threadIdx.x;
  if (word < words)
    out[word] = ab_gkr_uniskip_ldc_table[word];
}

// Single dependent chase: one LDC per iteration, its address the previous LDC's result.
EXTERN __global__ void ab_gkr_uniskip_ldc_latency_kernel(u32 mask, u32 step, u32 iters, u32 *sink, u64 *cycles) {
  u32 idx = chase_start(mask, step, 0);
  const u64 t0 = clock64();
  for (u32 i = 0; i < iters; ++i)
    idx = ldc_chase(idx);
  publish(idx, clock64() - t0, sink, cycles);
}

// The same loop with the constant load removed: loop control plus one dependent ALU op, so
// the latency arm's floor is measured rather than assumed. A body of `asm volatile("")`
// would not do — nvcc deletes the loop outright.
EXTERN __global__ void ab_gkr_uniskip_ldc_baseline_kernel(u32 mask, u32 step, u32 iters, u32 *sink, u64 *cycles) {
  u32 idx = chase_start(mask, step, 0);
  const u64 t0 = clock64();
  for (u32 i = 0; i < iters; ++i)
    asm volatile("add.u32 %0, %1, %2;" : "=r"(idx) : "r"(idx), "r"(step));
  publish(idx, clock64() - t0, sink, cycles);
}

// UNISKIP_LDC_PROBE_CHAINS independent chases per thread, launched over enough warps to
// saturate the SM: the warp still touches exactly K distinct addresses per LDC.
EXTERN __global__ void ab_gkr_uniskip_ldc_throughput_kernel(u32 mask, u32 step, u32 iters, u32 *sink, u64 *cycles) {
  u32 idx[UNISKIP_LDC_PROBE_CHAINS];
#pragma unroll
  for (u32 chain = 0; chain < UNISKIP_LDC_PROBE_CHAINS; ++chain)
    idx[chain] = chase_start(mask, step, chain);
  const u64 t0 = clock64();
  for (u32 i = 0; i < iters; ++i) {
#pragma unroll
    for (u32 chain = 0; chain < UNISKIP_LDC_PROBE_CHAINS; ++chain)
      idx[chain] = ldc_chase(idx[chain]);
  }
  const u64 elapsed = clock64() - t0;
  u32 acc = 0;
#pragma unroll
  for (u32 chain = 0; chain < UNISKIP_LDC_PROBE_CHAINS; ++chain)
    acc += idx[chain];
  publish(acc, elapsed, sink, cycles);
}
