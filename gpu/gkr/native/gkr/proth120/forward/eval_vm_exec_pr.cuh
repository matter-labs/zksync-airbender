#pragma once
#include "fwd_vm.cuh"
namespace airbender::gkr::proth120::forward {
constexpr u32 FWD_VM_WARP_LANES = 32;
constexpr u32 FWD_VM_WARP_SHIFT = 5;
constexpr u32 FWD_VM_LANE_MASK = FWD_VM_WARP_LANES - 1;

constexpr u32 LDC_CONST = 0;
constexpr u32 LDC_CONST_DERIVED = 1;
constexpr u32 LDC_ARG_DERIVED = 2;
constexpr u32 LDC_SPECIAL = 3;
constexpr u32 SPECIAL_ONE = 1;
constexpr u32 SPECIAL_NEG_ONE = 2;

template <u32 BUCKETS> DEVICE_FORCEINLINE u32 pr_warp_base() { return (threadIdx.x >> FWD_VM_WARP_SHIFT) * BUCKETS * FWD_VM_WARP_LANES; }

template <u32 BUCKETS> DEVICE_FORCEINLINE pr smem_ld_pr(const pr *cells, const u32 bucket) {
  const uint4 v = *reinterpret_cast<const uint4 *>(cells + pr_warp_base<BUCKETS>() + bucket * FWD_VM_WARP_LANES + (threadIdx.x & FWD_VM_LANE_MASK));
  return *reinterpret_cast<const pr *>(&v);
}

template <u32 BUCKETS> DEVICE_FORCEINLINE void smem_st_pr(pr *cells, const u32 bucket, const pr v) {
  *reinterpret_cast<uint4 *>(cells + pr_warp_base<BUCKETS>() + bucket * FWD_VM_WARP_LANES + (threadIdx.x & FWD_VM_LANE_MASK)) =
      *reinterpret_cast<const uint4 *>(&v);
}

DEVICE_FORCEINLINE const char *source_col(const fwd_vm_desc_pr &d, const u32 window, const u32 col) {
  return d.source_base[window] + static_cast<size_t>(col) * d.source_stride_bytes[window];
}
DEVICE_FORCEINLINE char *dst_col(const fwd_vm_desc_pr &d, const u32 slot, const u32 col) {
  return d.dst_base[slot] + static_cast<size_t>(col) * d.dst_stride_bytes[slot];
}

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
DEVICE_FORCEINLINE const u32 *special_mapping(const fwd_vm_desc_pr &d, const fwd_vm_special &s) {
  return d.mapping_arena[s.arena] + static_cast<size_t>(s.set_index) * d.count;
}

DEVICE_FORCEINLINE pr pr_from_u32(const u32 v) {
  const u32 natural[4] = {v, 0, 0, 0};
  return pr::from_u128_with_reduction(natural);
}

DEVICE_FORCEINLINE u32 virtual_u32(const u32 vkind, const unsigned row) {
  switch (static_cast<gkr_base_source_kind>(vkind)) {
  case GKR_BASE_SOURCE_VIRTUAL_RANGE_CHECK_16_BITS:
    return row < (1u << 16) ? row : 0u;
  case GKR_BASE_SOURCE_VIRTUAL_RANGE_CHECK_TIMESTAMP:
    return row < (1u << GKR_TIMESTAMP_COLUMNS_NUM_BITS) ? row : 0u;
  case GKR_BASE_SOURCE_VIRTUAL_INITS_AND_TEARDOWNS_LOW:
    return (row << 2) & 0xffffu;
  case GKR_BASE_SOURCE_VIRTUAL_INITS_AND_TEARDOWNS_HIGH:
    return row >> 14;
  default:
    return 0u;
  }
}

DEVICE_FORCEINLINE pr read_special_pr(const fwd_vm_desc_pr &d, const u32 desc, const unsigned gid) {
  const fwd_vm_special s = unpack_special(d.descs[desc]);
  switch (s.kind) {
  case SD_SINGLE_COLUMN:
    return pr_from_u32(load<u32, ld_modifier::ca>(special_mapping(d, s), gid));
  case SD_AGGREGATE: {
    const u32 row = load<u32, ld_modifier::ca>(special_mapping(d, s), gid);
    return load<pr, ld_modifier::ca>(d.table, row);
  }
  case SD_SETUP:
    return gid < d.table_len ? load<pr, ld_modifier::ca>(d.table, gid) : pr::ZERO();
  case SD_DECODER: {
    const pr mask = load<pr, ld_modifier::ca>(d.mask, gid);
    if (pr::is_zero(mask))
      return load<pr, ld_modifier::ca>(d.const_derived, s.vkind);
    const u32 row = load<u32, ld_modifier::ca>(d.decoder_mapping, gid);
    return load<pr, ld_modifier::ca>(d.table, row);
  }
  case SD_VIRTUAL:
    return pr_from_u32(virtual_u32(s.vkind, gid));
  default:
    return d.consts[s.set_index];
  }
}

DEVICE_FORCEINLINE pr read_ldc_pr(const fwd_vm_desc_pr &d, const u32 sub, const u32 idx) {
  switch (sub) {
  case LDC_CONST:
    return d.consts[idx];
  case LDC_CONST_DERIVED:
    return load<pr, ld_modifier::ca>(d.const_derived, idx);
  case LDC_ARG_DERIVED:
    return load<pr, ld_modifier::ca>(d.arg_derived, idx);
  default:
    if (idx == SPECIAL_ONE)
      return pr::ONE();
    if (idx == SPECIAL_NEG_ONE)
      return pr::neg(pr::ONE());
    return pr::ZERO();
  }
}

template <u32 BUCKETS, bool STREAMING> DEVICE_FORCEINLINE pr read_operand_pr(const fwd_vm_desc_pr &d, const pr *cells, const unsigned gid, const u16 l) {
  switch (l & FWD_VM_OPERAND_TAG_MASK) {
  case FWD_VM_OPERAND_SOURCE: {
    const u32 window = (l >> FWD_VM_SOURCE_WINDOW_SHIFT) & FWD_VM_SOURCE_WINDOW_MASK;
    const u32 column = (l >> FWD_VM_SOURCE_COLUMN_SHIFT) & FWD_VM_SOURCE_COLUMN_MASK;
    return load<pr, ld_modifier::ca>(reinterpret_cast<const pr *>(source_col(d, window, column)),
                                     STREAMING && (d.temporary_source_mask & (1u << window)) ? blockIdx.x * 128 + threadIdx.x : gid);
  }
  case FWD_VM_OPERAND_SMEM:
    return smem_ld_pr<BUCKETS>(cells, l >> FWD_VM_OPERAND_CELL_SHIFT);
  case FWD_VM_OPERAND_LDC:
    return read_ldc_pr(d, (l >> FWD_VM_LDC_SUB_SHIFT) & FWD_VM_LDC_SUB_MASK, l >> FWD_VM_LDC_IDX_SHIFT);
  default:
    return read_special_pr(d, l >> FWD_VM_OPERAND_DESC_SHIFT, gid);
  }
}

template <u32 BUCKETS, bool STREAMING> DEVICE_FORCEINLINE void write_dst_pr(const fwd_vm_desc_pr &d, pr *cells, const unsigned gid, const u16 dl, const pr v) {
  if ((dl & FWD_VM_DST_TAG_MASK) == FWD_VM_DST_SMEM) {
    smem_st_pr<BUCKETS>(cells, dl >> FWD_VM_DST_CELL_SHIFT, v);
  } else {
    const u32 slot = (dl >> FWD_VM_DST_SLOT_SHIFT) & FWD_VM_DST_SLOT_MASK;
    const u32 col = dl >> FWD_VM_DST_COL_SHIFT;
    store<pr, st_modifier::wb>(reinterpret_cast<pr *>(dst_col(d, slot, col)), v,
                               STREAMING && (d.temporary_dst_mask & (1u << slot)) ? blockIdx.x * 128 + threadIdx.x : gid);
  }
}

template <u32 BUCKETS, bool STREAMING> struct PrFwdVmAdapter {
  const fwd_vm_desc_pr &desc;
  pr *cells;
  unsigned gid;
  u32 program_offset;
  DEVICE_FORCEINLINE u16 lane(const u32 index) const { return desc.program[program_offset + index]; }
  DEVICE_FORCEINLINE pr read(const u16 lane) { return read_operand_pr<BUCKETS, STREAMING>(desc, cells, gid, lane); }
  DEVICE_FORCEINLINE void write(const u16 dst, const pr value) { write_dst_pr<BUCKETS, STREAMING>(desc, cells, gid, dst, value); }
};

template <typename Adapter> DEVICE_FORCEINLINE void eval_vm_execute_pr(Adapter &adapter, const u32 n_instr) {
  u32 i = 0;
  pr acc = pr::ZERO();
  for (u32 k = 0; k < n_instr; k++) {
    const u16 h = adapter.lane(i++);
    const u32 op = h & FWD_VM_OP_MASK;
    if (op == FWD_VM_OP_MOV) {
      const u32 dir = (h >> FWD_VM_MOV_DIR_SHIFT) & FWD_VM_MOV_DIR_MASK;
      switch (dir) {
      case FWD_VM_MOV_ACC_FROM_SRC:
        acc = adapter.read(adapter.lane(i++));
        break;
      case FWD_VM_MOV_DST_FROM_ACC: {
        const u16 dst = adapter.lane(i++);
        adapter.write(dst, acc);
        break;
      }
      default: {
        const u16 dst = adapter.lane(i++);
        adapter.write(dst, adapter.read(adapter.lane(i++)));
        break;
      }
      }
      continue;
    }
    const u32 arity = (h >> FWD_VM_HDR_ARITY_SHIFT) & FWD_VM_HDR_ARITY_MASK;
    const bool minus = ((h >> FWD_VM_HDR_SIGN_SHIFT) & 1) != 0;
    if (op == FWD_VM_OP_ADD) {
      for (u32 t = 0; t < arity; t++) {
        const pr value = adapter.read(adapter.lane(i++));
        acc = minus ? pr::sub(acc, value) : pr::add(acc, value);
      }
    } else if (op == FWD_VM_OP_MUL) {
      if (minus)
        acc = pr::neg(acc);
      for (u32 t = 0; t < arity; t++)
        acc = pr::mul(acc, adapter.read(adapter.lane(i++)));
    } else {
      for (u32 t = 0; t < arity; t++) {
        const pr lhs = adapter.read(adapter.lane(i++));
        const pr rhs = adapter.read(adapter.lane(i++));
        acc = minus ? pr::sub(acc, pr::mul(lhs, rhs)) : pr::fma(lhs, rhs, acc);
      }
    }
  }
}

template <u32 BUCKETS, bool STREAMING> DEVICE_FORCEINLINE void vm_body_pr(const fwd_vm_desc_pr &desc, pr *cells, const u32 tile) {
  const u32 gid = tile * 128 + threadIdx.x;
  for (u32 layer = 0; layer < desc.layer_count; layer++) {
    for (u32 c = 0; c < BUCKETS; c++)
      smem_st_pr<BUCKETS>(cells, c, pr::ZERO());
    __syncwarp();
    if (gid < desc.count) {
      const fwd_vm_layer &metadata = desc.layers[layer];
      PrFwdVmAdapter<BUCKETS, STREAMING> adapter{desc, cells, gid, metadata.program_offset};
      eval_vm_execute_pr(adapter, metadata.instruction_count);
    }
    __syncwarp();
  }
}

DEVICE_FORCEINLINE void fused_reduction_round0_pr(const fwd_vm_reduction_pair_pr &pair, pr *smem, const u32 tile) {
  constexpr u32 round_len = 64;
  const u32 lane = threadIdx.x & FWD_VM_LANE_MASK;
  const u32 block_input = tile * 128;
  const u32 block_output = tile * round_len;
#pragma unroll
  for (u32 local = lane; local < round_len; local += FWD_VM_WARP_LANES) {
    const u32 even = block_input + 2 * local;
    const u32 odd = even + 1;
    pr out0, out1;
    if (pair.kind == FWD_VM_REDUCTION_PAIR_PAIRWISE2) {
      out0 = pr::mul(load<pr, ld_modifier::ca>(pair.input[0], even), load<pr, ld_modifier::ca>(pair.input[0], odd));
      out1 = pr::mul(load<pr, ld_modifier::ca>(pair.input[1], even), load<pr, ld_modifier::ca>(pair.input[1], odd));
    } else {
      const pr a = load<pr, ld_modifier::ca>(pair.input[0], even);
      const pr b = load<pr, ld_modifier::ca>(pair.input[1], even);
      const pr c = load<pr, ld_modifier::ca>(pair.input[0], odd);
      const pr d = load<pr, ld_modifier::ca>(pair.input[1], odd);
      out0 = pr::fma(a, d, pr::mul(c, b));
      out1 = pr::mul(b, d);
    }
    smem[local] = out0;
    smem[round_len + local] = out1;
    store<pr, st_modifier::cs>(pair.round_outputs[0][0], out0, block_output + local);
    store<pr, st_modifier::cs>(pair.round_outputs[0][1], out1, block_output + local);
  }
  __syncwarp();
}

DEVICE_FORCEINLINE void fused_reduction_pair_pr(const fwd_vm_reduction_pair_pr &pair, pr *smem, const u32 tile) {
  fused_reduction_round0_pr(pair, smem, tile);
  const u32 lane = threadIdx.x & FWD_VM_LANE_MASK;
#pragma unroll
  for (u32 round = 1; round < FWD_VM_FUSED_REDUCTION_ROUNDS; round++) {
    const u32 round_len = 64 >> round;
    pr out0, out1;
    if (lane < round_len) {
      if (pair.kind == FWD_VM_REDUCTION_PAIR_PAIRWISE2) {
        out0 = pr::mul(smem[2 * lane], smem[2 * lane + 1]);
        out1 = pr::mul(smem[64 + 2 * lane], smem[64 + 2 * lane + 1]);
      } else {
        const pr a = smem[2 * lane], b = smem[64 + 2 * lane], c = smem[2 * lane + 1], d = smem[64 + 2 * lane + 1];
        out0 = pr::fma(a, d, pr::mul(c, b));
        out1 = pr::mul(b, d);
      }
    }
    __syncwarp();
    if (lane < round_len) {
      smem[lane] = out0;
      smem[64 + lane] = out1;
      const u32 output = tile * round_len + lane;
      store<pr, st_modifier::cs>(pair.round_outputs[round][0], out0, output);
      store<pr, st_modifier::cs>(pair.round_outputs[round][1], out1, output);
    }
    __syncwarp();
  }
}

template <u32 BUCKETS> DEVICE_FORCEINLINE void fwd_vm_pr(const fwd_vm_desc_pr &desc) {
  __shared__ pr cells[BUCKETS * 128];
  vm_body_pr<BUCKETS, false>(desc, cells, blockIdx.x);
  __syncthreads();
  const u32 warp = threadIdx.x >> FWD_VM_WARP_SHIFT;
  static_assert(BUCKETS * FWD_VM_WARP_LANES >= 128, "reduction scratch");
  pr *smem = cells + warp * BUCKETS * FWD_VM_WARP_LANES;
  if (warp < desc.reduction_pair_count)
    fused_reduction_pair_pr(desc.reduction_pairs[warp], smem, blockIdx.x);
  if (warp + 4 < desc.reduction_pair_count)
    fused_reduction_pair_pr(desc.reduction_pairs[warp + 4], smem, blockIdx.x);
}

} // namespace airbender::gkr::proth120::forward
