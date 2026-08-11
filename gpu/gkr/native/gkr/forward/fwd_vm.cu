// Row-per-thread forward VM. Each warp owns a shared-memory cell partition and
// each thread keeps one E4 accumulator whose first limb is the base-field view.

#include "../eval_vm_exec.cuh"
#include "../support/lookup_helpers.cuh"
#include "fwd_vm.cuh"

// Runtime-produced derived E4 values and the optional decoder fill.
__device__ __constant__ e4 ab_gkr_fwd_vm_const_derived_e4[airbender::gkr::FWD_VM_CONST_DERIVED_E4_CAP];

namespace airbender::gkr {

// --- Ldc sub-source / inline-special payload values ---------------------------
// Mirrors the Rust LdcSub and Special values.
constexpr u32 LDC_CONST = 0;
constexpr u32 LDC_CONST_DERIVED_E4 = 1;
constexpr u32 LDC_ARG_DERIVED_E4 = 2;
constexpr u32 LDC_SPECIAL = 3;
constexpr u32 SPECIAL_ONE = 1;
constexpr u32 SPECIAL_NEG_ONE = 2;

// --- warp-partitioned bucket smem cell file ------------------------------------
// The block's cell file is partitioned into per-warp partitions of contiguous
// shared memory. No
// warp ever touches another warp's partition, so inter-warp races are
// structurally impossible. Within a partition, bucket b owns the contiguous
// 512-B chunk at `b * 512`. The instruction's field bit selects one of two
// views of a chunk (wire encoding unchanged: a bf cell index c is a lane index
// with bucket c >> 2 and sub-index c & 3; an ext cell index IS the bucket
// index):
//   - e4 view: lane t owns bytes [t*16, t*16+16) of the chunk -> a single
//     lds.128/sts.128. The warp accesses 512 contiguous bytes = four 128-B
//     subtransactions, each covering all 32 banks exactly once -> conflict-free.
//   - 4xbf view: the chunk is 4 lines of 32 bf values; bf cell c lives in line
//     c & 3 at word t for lane t -> `chunk + (c & 3)*128 + lane*4`, a regular
//     .32 access. The warp accesses 128 contiguous bytes = all 32 banks
//     exactly once -> conflict-free.
//
// SAFETY INVARIANT (cross-view aliasing): cross-view reuse of a bucket — the
// compiler's allocator time-multiplexes a quad between the two views over
// disjoint lifetimes (the CPU model's `cells` file aliases them) —
// redistributes bytes ACROSS LANES OF THE SAME WARP: lane t's bf words overlap
// OTHER lanes' e4 slices. This is safe because (a) all aliasing is
// warp-contained (the partition), and (b) a converged warp issues instructions
// in program order and the smem/MIO pipeline processes a warp's wavefronts in
// issue order — and the interpreter's control flow is warp-uniform for active
// rows (program lanes are grid-constant broadcasts). Tail lanes skip VM
// execution but participate in the layer barriers. Formally the PTX
// memory model calls unsynchronized cross-lane conflicting access a race; the
// in-order-per-warp hardware argument is load-bearing and holds only under
// warp-uniform control flow.
//
// `cells` is the block's file reinterpreted as bf lanes (u32 words).

constexpr u32 FWD_VM_WARP_LANES = 32;                                    // hardware warp size
constexpr u32 FWD_VM_WARP_SHIFT = 5;                                     // log2(FWD_VM_WARP_LANES)
constexpr u32 FWD_VM_LANE_MASK = FWD_VM_WARP_LANES - 1;                  // threadIdx.x & mask -> lane
constexpr u32 FWD_VM_E4_WORDS = 4;                                       // u32 words per e4 limb vector
constexpr u32 FWD_VM_BUCKET_WORDS = FWD_VM_WARP_LANES * FWD_VM_E4_WORDS; // 128 words = one 512-B chunk
constexpr u32 FWD_VM_BF_PER_BUCKET = FWD_VM_E4_WORDS;                    // bf cells per bucket (4 lines of 32)
constexpr u32 FWD_VM_BF_SUB_MASK = FWD_VM_BF_PER_BUCKET - 1;             // bf cell & mask -> line in bucket
constexpr u32 FWD_VM_BF_BUCKET_SHIFT = 2;                                // log2(FWD_VM_BF_PER_BUCKET); bf cell >> shift -> bucket
constexpr u32 FWD_VM_BUCKETS = 4;
static_assert(1u << FWD_VM_WARP_SHIFT == FWD_VM_WARP_LANES, "warp shift/size drift");
static_assert(1u << FWD_VM_BF_BUCKET_SHIFT == FWD_VM_BF_PER_BUCKET, "bf bucket shift/size drift");

DEVICE_FORCEINLINE u32 smem_warp_base() { return (threadIdx.x >> FWD_VM_WARP_SHIFT) * FWD_VM_BUCKETS * FWD_VM_BUCKET_WORDS; }

DEVICE_FORCEINLINE u32 smem_bf_unit(const u32 cell) {
  return smem_warp_base() + (cell >> FWD_VM_BF_BUCKET_SHIFT) * FWD_VM_BUCKET_WORDS + (cell & FWD_VM_BF_SUB_MASK) * FWD_VM_WARP_LANES +
         (threadIdx.x & FWD_VM_LANE_MASK);
}

DEVICE_FORCEINLINE bf smem_ld_bf(const bf *cells, const u32 cell) { return cells[smem_bf_unit(cell)]; }

DEVICE_FORCEINLINE void smem_st_bf(bf *cells, const u32 cell, const bf v) { cells[smem_bf_unit(cell)] = v; }

// Ext cell = the lane's 16-B slice of the bucket chunk: a single
// lds.128/sts.128 via uint4 (the file base is 16-B aligned and the word offset
// is a multiple of 4, so the vector access is legal).
DEVICE_FORCEINLINE e4 smem_ld_e4(const bf *cells, const u32 bucket) {
  const uint4 v =
      *reinterpret_cast<const uint4 *>(cells + smem_warp_base() + bucket * FWD_VM_BUCKET_WORDS + (threadIdx.x & FWD_VM_LANE_MASK) * FWD_VM_E4_WORDS);
  return *reinterpret_cast<const e4 *>(&v);
}

DEVICE_FORCEINLINE void smem_st_e4(bf *cells, const u32 bucket, const e4 v) {
  *reinterpret_cast<uint4 *>(cells + smem_warp_base() + bucket * FWD_VM_BUCKET_WORDS + (threadIdx.x & FWD_VM_LANE_MASK) * FWD_VM_E4_WORDS) =
      *reinterpret_cast<const uint4 *>(&v);
}

DEVICE_FORCEINLINE const char *source_col(const fwd_vm_desc &d, const u32 window, const u32 col) {
  return d.source_base[window] + static_cast<size_t>(col) * d.source_stride_bytes[window];
}

DEVICE_FORCEINLINE char *dst_col(const fwd_vm_desc &d, const u32 slot, const u32 col) {
  return d.dst_base[slot] + static_cast<size_t>(col) * d.dst_stride_bytes[slot];
}

struct fwd_vm_source_coordinate {
  u32 window;
  u32 column;
};

DEVICE_FORCEINLINE fwd_vm_source_coordinate decode_source(const u16 lane) {
  return {(lane >> FWD_VM_SOURCE_WINDOW_SHIFT) & FWD_VM_SOURCE_WINDOW_MASK, (lane >> FWD_VM_SOURCE_COLUMN_SHIFT) & FWD_VM_SOURCE_COLUMN_MASK};
}

// --- special descriptors ------------------------------------------------------

struct fwd_vm_special {
  u32 kind;
  u32 arena;
  u32 set_index;
  u32 vkind;
};

DEVICE_FORCEINLINE fwd_vm_special unpack_special(const u32 w) {
  fwd_vm_special s;
  s.kind = (w >> FWD_VM_DESC_KIND_SHIFT) & FWD_VM_DESC_KIND_MASK;
  s.arena = (w >> FWD_VM_DESC_ARENA_SHIFT) & FWD_VM_DESC_ARENA_MASK;
  s.set_index = (w >> FWD_VM_DESC_SET_INDEX_SHIFT) & FWD_VM_DESC_SET_INDEX_MASK;
  s.vkind = (w >> FWD_VM_DESC_VKIND_SHIFT) & FWD_VM_DESC_VKIND_MASK;
  return s;
}

// Mapping = one COLUMN of a contiguous u32 arena (column-major, stride = count).
DEVICE_FORCEINLINE const u32 *special_mapping(const fwd_vm_desc &d, const fwd_vm_special &s) {
  return d.mapping_arena[s.arena] + static_cast<size_t>(s.set_index) * d.count;
}

// `vkind` is the native `gkr_base_source_kind` value.
DEVICE_FORCEINLINE e4 read_const_derived_e4(const u32 idx) { return ::ab_gkr_fwd_vm_const_derived_e4[idx]; }

DEVICE_FORCEINLINE e4 read_special_e4(const fwd_vm_desc &d, const u32 desc, const unsigned gid) {
  const fwd_vm_special s = unpack_special(d.descs[desc]);
  switch (s.kind) {
  case SD_SINGLE_COLUMN: {
    // lift(Bf::from_u32_with_reduction(mapping[row])) - the mapping value is a
    // raw index, so it enters the field via the Montgomery conversion.
    const u32 idx = load<u32, ld_modifier::ca>(special_mapping(d, s), gid);
    return e4::from_scalar(bf::from_u32_with_reduction(idx));
  }
  case SD_AGGREGATE: {
    const u32 row = load<u32, ld_modifier::ca>(special_mapping(d, s), gid);
    return load<e4, ld_modifier::ca>(d.table, row);
  }
  case SD_SETUP:
    // Zero-padded tail past the real table length.
    return gid < d.table_len ? load<e4, ld_modifier::ca>(d.table, gid) : e4::ZERO();
  case SD_DECODER: {
    const bf mask = load<bf, ld_modifier::ca>(d.mask, gid);
    if (mask.limb == 0)
      // Challenge-dependent fill from the __constant__ bank: the index is
      // warp-uniform (grid-constant desc), only the mask predicate is
      // per-lane, so this is a constant-cache broadcast.
      return read_const_derived_e4(s.vkind);
    const u32 row = load<u32, ld_modifier::ca>(special_mapping(d, s), gid);
    return load<e4, ld_modifier::ca>(d.table, row);
  }
  case SD_VIRTUAL:
    return e4::from_scalar(gkr_virtual_base_value(static_cast<gkr_base_source_kind>(s.vkind), gid));
  default: // SD_INITS_TOP_BITS: runtime scalar in the descriptor's BF bank
    return e4::from_scalar(d.consts[s.set_index]);
  }
}

// Only base-field intrinsic descriptors appear in this path.
DEVICE_FORCEINLINE bf read_special_bf(const fwd_vm_desc &d, const u32 desc, const unsigned gid) {
  const fwd_vm_special s = unpack_special(d.descs[desc]);
  switch (s.kind) {
  case SD_SINGLE_COLUMN:
    return bf::from_u32_with_reduction(load<u32, ld_modifier::ca>(special_mapping(d, s), gid));
  case SD_VIRTUAL:
    return gkr_virtual_base_value(static_cast<gkr_base_source_kind>(s.vkind), gid);
  case SD_INITS_TOP_BITS:
    return d.consts[s.set_index];
  default:
    return bf::ZERO();
  }
}

// --- Ldc{sub,idx}: consts / derived-e4 banks / inline specials ---------------

DEVICE_FORCEINLINE bf read_ldc_bf(const fwd_vm_desc &d, const u32 sub, const u32 idx) {
  switch (sub) {
  case LDC_CONST:
    return d.consts[idx];
  case LDC_SPECIAL:
    if (idx == SPECIAL_ONE)
      return bf::ONE();
    if (idx == SPECIAL_NEG_ONE)
      return bf::neg(bf::ONE());
    return bf::ZERO();
  default: // derived-e4 banks are e4 by definition - a bf-field read is malformed
    return bf::ZERO();
  }
}

DEVICE_FORCEINLINE e4 read_ldc_e4(const fwd_vm_desc &d, const u32 sub, const u32 idx) {
  switch (sub) {
  case LDC_CONST_DERIVED_E4:
    return read_const_derived_e4(idx);
  case LDC_ARG_DERIVED_E4:
    return d.arg_derived_e4[idx];
  case LDC_SPECIAL:
    if (idx == SPECIAL_ONE)
      return e4::ONE();
    if (idx == SPECIAL_NEG_ONE)
      return e4::from_scalar(bf::neg(bf::ONE()));
    return e4::ZERO();
  default: // consts are bf by definition - an e4-field read is malformed
    return e4::ZERO();
  }
}

// --- typed operand reads ------------------------------------------------------
// The consuming instruction's field bit selects the width (Fma: per side).
// Source loads are single typed loads - a bf column is loaded as bf and lifted
// only when the op's semantics need e4; an e4 column is one vectorized
// load<e4>. Smem: the field bit selects the view (bf lane vs ext bucket).

DEVICE_FORCEINLINE bf read_operand_bf(const fwd_vm_desc &d, const bf *cells, const unsigned gid, const u16 l) {
  switch (l & FWD_VM_OPERAND_TAG_MASK) {
  case FWD_VM_OPERAND_SOURCE: {
    const fwd_vm_source_coordinate source = decode_source(l);
    return load<bf, ld_modifier::ca>(reinterpret_cast<const bf *>(source_col(d, source.window, source.column)), gid);
  }
  case FWD_VM_OPERAND_SMEM: { // Smem { cell }: bf -> 4-B lane index
    const u32 cell = l >> FWD_VM_OPERAND_CELL_SHIFT;
    return smem_ld_bf(cells, cell);
  }
  case FWD_VM_OPERAND_LDC: // Ldc { sub, idx }
    return read_ldc_bf(d, (l >> FWD_VM_LDC_SUB_SHIFT) & FWD_VM_LDC_SUB_MASK, l >> FWD_VM_LDC_IDX_SHIFT);
  default: // FWD_VM_OPERAND_SPECIAL: Special { desc }
    return read_special_bf(d, l >> FWD_VM_OPERAND_DESC_SHIFT, gid);
  }
}

DEVICE_FORCEINLINE e4 read_operand_e4(const fwd_vm_desc &d, const bf *cells, const unsigned gid, const u16 l) {
  switch (l & FWD_VM_OPERAND_TAG_MASK) {
  case FWD_VM_OPERAND_SOURCE: {
    const fwd_vm_source_coordinate source = decode_source(l);
    return load<e4, ld_modifier::ca>(reinterpret_cast<const e4 *>(source_col(d, source.window, source.column)), gid);
  }
  case FWD_VM_OPERAND_SMEM: { // Smem { cell }: ext -> BUCKET index
    const u32 bucket = l >> FWD_VM_OPERAND_CELL_SHIFT;
    return smem_ld_e4(cells, bucket);
  }
  case FWD_VM_OPERAND_LDC: // Ldc { sub, idx }
    return read_ldc_e4(d, (l >> FWD_VM_LDC_SUB_SHIFT) & FWD_VM_LDC_SUB_MASK, l >> FWD_VM_LDC_IDX_SHIFT);
  default: // FWD_VM_OPERAND_SPECIAL: Special { desc }
    return read_special_e4(d, l >> FWD_VM_OPERAND_DESC_SHIFT, gid);
  }
}

// --- typed dst writes ---------------------------------------------------------

DEVICE_FORCEINLINE void write_dst_bf(const fwd_vm_desc &d, bf *cells, const unsigned gid, const u16 dl, const bf v) {
  if ((dl & FWD_VM_DST_TAG_MASK) == FWD_VM_DST_SMEM) { // Smem { cell }: bf lane
    const u32 cell = dl >> FWD_VM_DST_CELL_SHIFT;
    smem_st_bf(cells, cell, v);
  } else { // GlobalMaterialize { slot, col }
    const u32 slot = (dl >> FWD_VM_DST_SLOT_SHIFT) & FWD_VM_DST_SLOT_MASK;
    const u32 col = dl >> FWD_VM_DST_COL_SHIFT;
    store<bf, st_modifier::wb>(reinterpret_cast<bf *>(dst_col(d, slot, col)), v, gid);
  }
}

DEVICE_FORCEINLINE void write_dst_e4(const fwd_vm_desc &d, bf *cells, const unsigned gid, const u16 dl, const e4 v) {
  if ((dl & FWD_VM_DST_TAG_MASK) == FWD_VM_DST_SMEM) { // Smem { cell }: ext bucket
    const u32 bucket = dl >> FWD_VM_DST_CELL_SHIFT;
    smem_st_e4(cells, bucket, v);
  } else { // GlobalMaterialize { slot, col }
    const u32 slot = (dl >> FWD_VM_DST_SLOT_SHIFT) & FWD_VM_DST_SLOT_MASK;
    const u32 col = dl >> FWD_VM_DST_COL_SHIFT;
    store<e4, st_modifier::wb>(reinterpret_cast<e4 *>(dst_col(d, slot, col)), v, gid);
  }
}

// --- forward adapter ----------------------------------------------------------

struct FwdVmAdapter {
  const fwd_vm_desc &desc;
  bf *cells;
  unsigned gid;
  u32 program_offset;

  DEVICE_FORCEINLINE u16 lane(const u32 index) const { return desc.program[program_offset + index]; }

  DEVICE_FORCEINLINE bf read_bf(const u16 lane) { return read_operand_bf(desc, cells, gid, lane); }

  DEVICE_FORCEINLINE e4 read_e4(const u16 lane) { return read_operand_e4(desc, cells, gid, lane); }

  DEVICE_FORCEINLINE void write_bf(const u16 dst, const bf value) { write_dst_bf(desc, cells, gid, dst, value); }

  DEVICE_FORCEINLINE void write_e4(const u16 dst, const e4 value) { write_dst_e4(desc, cells, gid, dst, value); }
};

DEVICE_FORCEINLINE void execute_fwd_vm(const fwd_vm_desc &desc, bf *cells, const unsigned gid, const u32 program_offset, const u32 instruction_count) {
  FwdVmAdapter adapter{desc, cells, gid, program_offset};
  eval_vm_execute(adapter, instruction_count);
}

// Inactive rows must participate in both barriers: the first publishes zeroed
// cells, and the second prevents the next layer's zeroing from racing reads.
// No grid barrier is needed because mutable layer values stay within one gid.
DEVICE_FORCEINLINE void vm_body(const fwd_vm_desc &desc, e4 *cell_file) {
  bf *cells = reinterpret_cast<bf *>(cell_file);
  const u32 gid = blockIdx.x * 128 + threadIdx.x;
  for (u32 layer = 0; layer < desc.layer_count; layer++) {
    for (u32 c = 0; c < FWD_VM_BUCKETS * FWD_VM_BF_PER_BUCKET; c++)
      smem_st_bf(cells, c, bf::ZERO());
    __syncwarp();
    if (gid < desc.count) {
      const fwd_vm_layer &metadata = desc.layers[layer];
      execute_fwd_vm(desc, cells, gid, metadata.program_offset, metadata.instruction_count);
    }
    __syncwarp();
  }
}

DEVICE_FORCEINLINE void fused_reduction_round0(const fwd_vm_reduction_pair &pair, e4 *smem) {
  constexpr u32 round_len = 64;
  const u32 lane = threadIdx.x & FWD_VM_LANE_MASK;
  const u32 block_input = blockIdx.x * 128;
  const u32 block_output = blockIdx.x * round_len;

#pragma unroll
  for (u32 local = lane; local < round_len; local += FWD_VM_WARP_LANES) {
    const u32 even = block_input + 2 * local;
    const u32 odd = even + 1;
    e4 out0;
    e4 out1;
    if (pair.kind == FWD_VM_REDUCTION_PAIR_PAIRWISE2) {
      gkr_eval_product(load<e4, ld_modifier::ca>(pair.input[0], even), load<e4, ld_modifier::ca>(pair.input[0], odd), out0);
      gkr_eval_product(load<e4, ld_modifier::ca>(pair.input[1], even), load<e4, ld_modifier::ca>(pair.input[1], odd), out1);
    } else {
      const e4 a = load<e4, ld_modifier::ca>(pair.input[0], even);
      const e4 b = load<e4, ld_modifier::ca>(pair.input[1], even);
      const e4 c = load<e4, ld_modifier::ca>(pair.input[0], odd);
      const e4 d = load<e4, ld_modifier::ca>(pair.input[1], odd);
      gkr_eval_lookup_pair(a, b, c, d, out0, out1);
    }
    smem[local] = out0;
    smem[round_len + local] = out1;
    store<e4, st_modifier::cs>(pair.round_outputs[0][0], out0, block_output + local);
    store<e4, st_modifier::cs>(pair.round_outputs[0][1], out1, block_output + local);
  }
  // Round 1 reads values written by other lanes.
  __syncwarp();
}

DEVICE_FORCEINLINE void fused_reduction_pair(const fwd_vm_reduction_pair &pair, e4 *smem) {
  fused_reduction_round0(pair, smem);
  const u32 lane = threadIdx.x & FWD_VM_LANE_MASK;

#pragma unroll
  for (u32 round = 1; round < FWD_VM_FUSED_REDUCTION_ROUNDS; round++) {
    const u32 round_len = 64 >> round;
    e4 out0;
    e4 out1;
    if (lane < round_len) {
      if (pair.kind == FWD_VM_REDUCTION_PAIR_PAIRWISE2) {
        gkr_eval_product(smem[2 * lane], smem[2 * lane + 1], out0);
        gkr_eval_product(smem[64 + 2 * lane], smem[64 + 2 * lane + 1], out1);
      } else {
        gkr_eval_lookup_pair(smem[2 * lane], smem[64 + 2 * lane], smem[2 * lane + 1], smem[64 + 2 * lane + 1], out0, out1);
      }
    }
    // Finish all reads before overwriting inputs, then publish writes before the next round.
    __syncwarp();
    if (lane < round_len) {
      smem[lane] = out0;
      smem[64 + lane] = out1;
      const u32 output = blockIdx.x * round_len + lane;
      store<e4, st_modifier::cs>(pair.round_outputs[round][0], out0, output);
      store<e4, st_modifier::cs>(pair.round_outputs[round][1], out1, output);
    }
    __syncwarp();
  }
}

// minBlocks = the occupancy the static smem permits: SM shared capacity
// (~100 KB) / per-block footprint (BUCKETS * 16 B * 128 threads + ~1 KB driver
// overhead), clamped to the 12-block warp limit (4 warps/block). ptxas then
// sizes registers to the smem-permitted occupancy.
EXTERN __launch_bounds__(128, 11) __global__ void ab_gkr_fwd_vm_kernel(const __grid_constant__ fwd_vm_desc desc) {
  __shared__ e4 fwd_vm_cells[FWD_VM_BUCKETS * 128];
  vm_body(desc, fwd_vm_cells);
  // Each reduction warp reloads rows written by the whole CTA.
  __syncthreads();
  const u32 warp = threadIdx.x >> FWD_VM_WARP_SHIFT;
  e4 *smem = fwd_vm_cells + warp * FWD_VM_BUCKETS * FWD_VM_WARP_LANES;
  if (warp < desc.reduction_pair_count)
    fused_reduction_pair(desc.reduction_pairs[warp], smem);
  if (warp + 4 < desc.reduction_pair_count)
    fused_reduction_pair(desc.reduction_pairs[warp + 4], smem);
}

} // namespace airbender::gkr
