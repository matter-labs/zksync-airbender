#include "../prover/gkr/forward/flat.cuh"

// LDC-variant program residency: 14336 u16 lanes = 28KB. The module already
// carries ~26KB of production __constant__ symbols in the 64KB budget, so a
// 48KB array would fail device link; 28KB is the spec's program ceiling.
// The host performs a fit check before any upload (bench_interp/mod.rs).
// Definition (no `extern`, mirroring gpu/ntt/native/context.cu); the global
// name is the host-visible symbol the Rust side binds to.
__device__ __constant__ u16 ab_gkr_bench_program[14336];

namespace airbender::prover::gkr::bench {

// 128/4 mirrors the flat kernel's launch bound (flat_layer.cu) and must stay
// >= BENCH_INTERP_THREADS_PER_BLOCK on the Rust side.
// Stub kept from Task 2: proves the build/link/launch path.
EXTERN __launch_bounds__(128, 4) __global__ void ab_gkr_bench_fwd_interp_smoke_kernel(const bf *src, bf *dst, const unsigned count) {
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= count)
    return;
  dst[gid] = src[gid];
}

// ---------------------------------------------------------------------------
// Interpreter core (Task 3): decode loop + SumK arity-1 + smem cell file.
// NativeK instructions DECODE (lane consumption must mirror isa.rs encode
// exactly) but are SKIPPED — payload routines arrive in Task 4. The parity
// test zeroes CPU cache sentinels so the skipped Dst::Slot sentinel write
// equals the zero-initialized cell file by construction.
// ---------------------------------------------------------------------------

// ABI mirrored bit-for-bit by bench_interp/mod.rs `InterpDesc`. Task 4
// EXTENDS this struct with: const u8 *payloads; const u32 *payload_offsets.
struct interp_desc {
  const u16 *program_ldg;     // lane stream (global); ignored by the LDC variant
  u32 program_lanes;          // total lane count — decode must consume exactly this
  u32 n_instr;                // instruction count (not in the lane stream, isa.rs:157-159)
  const void *const *sources; // ONE table: [0..n_sources_bf) bf columns, then e4
                              // columns — Source{id,e4} banks are separate id
                              // spaces (interp.rs:69-71); e4 index = n_sources_bf + id
  u32 n_sources_bf;
  void *const *outputs; // per ORIGINAL output slot j; null = never written
  const u32 *output_e4; // bitset, 1 bit per output slot (buffer width)
  const bf *consts;     // constant table, pre-converted to Montgomery form
                        // by lower.rs (interp.rs:74-76 converts on read)
  u32 budget_cells;     // per-thread bf cells; dynamic smem = budget*4*blockDim
  u32 count;            // rows
  u32 *native_skip;     // debug: one global counter, += per (NativeK, thread)
  u32 *error_flag;      // debug: atomicOr'd INTERP_ERR_* bits; 0 = clean run
};

// Unexpected-program report bits (Task-3 scope traps, no asm("trap;") so the
// test context survives and can read the flag).
constexpr u32 INTERP_ERR_UNSUPPORTED_OP = 1;      // ProdK/DotK or SumK arity != 1
constexpr u32 INTERP_ERR_UNSUPPORTED_OPERAND = 2; // Operand::FixedReg (fwd has n_fixed_cells == 0)
constexpr u32 INTERP_ERR_UNSUPPORTED_DST = 4;     // Dst::FixedReg / Dst::GateIn (never emitted by fwd)
constexpr u32 INTERP_ERR_OUTPUT_WIDTH = 8;        // e4_result vs output_e4 bitset disagree
constexpr u32 INTERP_ERR_NULL_OUTPUT = 16;        // write to a slot the lowering left null
constexpr u32 INTERP_ERR_TRAILING_LANES = 32;     // decode didn't consume program_lanes (isa.rs:216)

template <bool LDC> DEVICE_FORCEINLINE u16 program_lane(const interp_desc &d, const u32 i) {
  // LDG variant: program from global via __ldg (read-only cache); LDC variant:
  // from the __constant__ array (host fit-checked <= 14336 lanes).
  return LDC ? ab_gkr_bench_program[i] : __ldg(d.program_ldg + i);
}

template <bool LDC> DEVICE_FORCEINLINE void interp_body(const interp_desc d) {
  extern __shared__ u32 interp_smem[];
  const unsigned gid = blockIdx.x * blockDim.x + threadIdx.x;
  if (gid >= d.count)
    return;
  // Cell file: bf granularity, column-per-thread layout; e4 = 4 consecutive
  // cell INDICES (quad-aligned by the compiler), i.e. blockDim.x-strided here.
  auto cell = [&](const u32 c) -> bf & { return reinterpret_cast<bf *>(interp_smem)[c * blockDim.x + threadIdx.x]; };
  // CPU zero-initializes the slot file (interp.rs:60); smem is undefined.
  for (u32 c = 0; c < d.budget_cells; c++)
    cell(c) = bf::ZERO();

  u32 i = 0; // lane cursor — warp-uniform: every thread decodes the same lanes
  u32 native_skipped = 0;
  u32 err = 0;
  for (u32 k = 0; k < d.n_instr && err == 0; k++) {
    // Header u16 = op:2 | e4_result:1 | dst_class:2 | arity:5 | dst_lo:6
    // (isa.rs:126-131); dst_lo == 63 spends a sentinel lane (isa.rs:100,133-135).
    const u16 h = program_lane<LDC>(d, i++);
    const u32 op = h & 0b11;                    // isa.rs:127 (ins.op as u16)
    const bool e4_result = ((h >> 2) & 1) != 0; // isa.rs:128
    const u32 dst_class = (h >> 3) & 0b11;      // isa.rs:129
    const u32 arity = (h >> 5) & 0b11111;       // isa.rs:130
    u32 dst_idx = (h >> 10) & 0x3F;             // isa.rs:131
    if (dst_idx == 63)
      dst_idx = program_lane<LDC>(d, i++);

    if (op == 3) { // NativeK: payload lane + operand-count lane + operand lanes (isa.rs:136-139)
      i++;         // payload index — unused until Task 4
      const u32 cnt = program_lane<LDC>(d, i++);
      i += cnt; // skip operand lanes
      // Task 3: skipped ENTIRELY, including the CacheK Dst::Slot sentinel
      // write (interp.rs:93-97) — the parity test zeroes CPU sentinels.
      native_skipped++;
      continue;
    }
    if (op != 0 || arity != 1) {
      // Forward purity contract: SumK arity-1 + NativeK only (fwd.rs:5-9).
      err = INTERP_ERR_UNSUPPORTED_OP;
      break;
    }

    // Single operand lane = kind:3 | e4:1 | idx:12 (isa.rs:140-152).
    const u16 l = program_lane<LDC>(d, i++);
    const u32 kind = l & 0b111;
    const bool op_e4 = ((l >> 3) & 1) != 0;
    const u32 idx = l >> 4;
    e4 v;
    switch (kind) {
    case 0: // Operand::Source (interp.rs:69-71); same ld.global.ca hints as flat (flat.cuh:292-302)
      v = op_e4 ? flat_fwd_load_ext<e4>(d.sources[d.n_sources_bf + idx], gid) : e4::from_scalar(flat_fwd_load_bf(d.sources[idx], gid));
      break;
    case 1: { // Operand::Slot — read_cells (interp.rs:34-43)
      if (op_e4) {
        const bf limbs[4] = {cell(idx), cell(idx + 1), cell(idx + 2), cell(idx + 3)};
        v = e4(limbs);
      } else {
        v = e4::from_scalar(cell(idx));
      }
      break;
    }
    case 3: // Operand::Const (interp.rs:74-76; table is Montgomery-form on device)
      v = e4::from_scalar(load<bf, ld_modifier::ca>(d.consts, idx));
      break;
    case 4: // Operand::Zero
      v = e4::ZERO();
      break;
    case 5: // Operand::One
      v = e4::ONE();
      break;
    case 6: // Operand::NegOne
      v = e4::from_scalar(bf::neg(bf::ONE()));
      break;
    default: // kind 2 = Operand::FixedReg: forward programs have n_fixed_cells == 0 (fwd.rs:746)
      err = INTERP_ERR_UNSUPPORTED_OPERAND;
      break;
    }
    if (err)
      break;

    // SumK arity-1 == identity copy of the operand; dst per interp.rs:131-137.
    switch (dst_class) {
    case 0: // Dst::Slot — write_cells (interp.rs:45-57)
      cell(dst_idx) = v.base_coefficient_from_flat_idx(0);
      if (e4_result) {
        cell(dst_idx + 1) = v.base_coefficient_from_flat_idx(1);
        cell(dst_idx + 2) = v.base_coefficient_from_flat_idx(2);
        cell(dst_idx + 3) = v.base_coefficient_from_flat_idx(3);
      }
      break;
    case 2: { // Dst::Output — store at gid, width per slot (interp.rs:134)
      const bool slot_e4 = ((d.output_e4[dst_idx >> 5] >> (dst_idx & 31)) & 1) != 0;
      if (slot_e4 != e4_result) {
        err = INTERP_ERR_OUTPUT_WIDTH;
        break;
      }
      void *const out = d.outputs[dst_idx];
      if (out == nullptr) {
        err = INTERP_ERR_NULL_OUTPUT;
        break;
      }
      if (e4_result)
        reinterpret_cast<e4 *>(out)[gid] = v;
      else
        reinterpret_cast<bf *>(out)[gid] = v.base_coefficient_from_flat_idx(0);
      break;
    }
    default: // 1 = Dst::FixedReg, 3 = Dst::GateIn — never emitted by the fwd compiler
      err = INTERP_ERR_UNSUPPORTED_DST;
      break;
    }
  }

  if (err == 0 && i != d.program_lanes)
    err = INTERP_ERR_TRAILING_LANES; // mirror of decode's trailing-lanes assert (isa.rs:216)
  if (err != 0)
    atomicOr(d.error_flag, err);
  if (native_skipped != 0)
    atomicAdd(d.native_skip, native_skipped); // test expects n_native_instrs * count total
}

EXTERN __launch_bounds__(128, 4) __global__ void ab_gkr_bench_fwd_interp_ldg_kernel(const interp_desc desc) { interp_body<false>(desc); }

EXTERN __launch_bounds__(128, 4) __global__ void ab_gkr_bench_fwd_interp_ldc_kernel(const interp_desc desc) { interp_body<true>(desc); }

} // namespace airbender::prover::gkr::bench
