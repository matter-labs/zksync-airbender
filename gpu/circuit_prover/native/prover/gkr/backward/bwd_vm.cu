#include "../eval_vm_exec.cuh"
#include "../support/eq_inline.cuh"
#include "bwd_vm.cuh"

namespace airbender::prover::gkr {

constexpr u32 LDC_CONST = 0;
constexpr u32 LDC_CONST_DERIVED_E4 = 1;
constexpr u32 LDC_ARG_DERIVED_E4 = 2;
constexpr u32 LDC_SPECIAL = 3;
constexpr u32 SPECIAL_ZERO = 0;
constexpr u32 SPECIAL_ONE = 1;
constexpr u32 SPECIAL_NEG_ONE = 2;

constexpr u32 BWD_VM_WARP_LANES = 32;
constexpr u32 BWD_VM_WARP_SHIFT = 5;
constexpr u32 BWD_VM_LANE_MASK = BWD_VM_WARP_LANES - 1;
constexpr u32 BWD_VM_HALF_WARP_LANES = 16;
constexpr u32 BWD_VM_HALF_WARP_MASK = BWD_VM_HALF_WARP_LANES - 1;
constexpr u32 BWD_VM_E4_WORDS = 4;
constexpr u32 BWD_VM_BUCKET_WORDS = BWD_VM_WARP_LANES * BWD_VM_E4_WORDS;
constexpr u32 BWD_VM_BF_PER_BUCKET = BWD_VM_E4_WORDS;
constexpr u32 BWD_VM_BF_SUB_MASK = BWD_VM_BF_PER_BUCKET - 1;
constexpr u32 BWD_VM_BF_BUCKET_SHIFT = 2;

static_assert(1u << BWD_VM_WARP_SHIFT == BWD_VM_WARP_LANES, "warp layout drift");
static_assert(1u << BWD_VM_BF_BUCKET_SHIFT == BWD_VM_BF_PER_BUCKET, "cell aliasing layout drift");

DEVICE_FORCEINLINE bf bf_minus_one() {
  constexpr bf value = bf::neg(bf::ONE());
  return value;
}

DEVICE_FORCEINLINE e4 e4_minus_one() {
  constexpr e4 value = e4::from_scalar(bf::neg(bf::ONE()));
  return value;
}

DEVICE_FORCEINLINE u32 smem_warp_base(const u32 budget_cells) { return (threadIdx.x >> BWD_VM_WARP_SHIFT) * budget_cells * BWD_VM_BUCKET_WORDS; }

DEVICE_FORCEINLINE u32 smem_bf_unit(const u32 cell, const u32 budget_cells) {
  return smem_warp_base(budget_cells) + (cell >> BWD_VM_BF_BUCKET_SHIFT) * BWD_VM_BUCKET_WORDS + (cell & BWD_VM_BF_SUB_MASK) * BWD_VM_WARP_LANES +
         (threadIdx.x & BWD_VM_LANE_MASK);
}

DEVICE_FORCEINLINE bf smem_ld_bf(const bf *cells, const u32 cell, const u32 budget_cells) { return cells[smem_bf_unit(cell, budget_cells)]; }

DEVICE_FORCEINLINE void smem_st_bf(bf *cells, const u32 cell, const u32 budget_cells, const bf value) { cells[smem_bf_unit(cell, budget_cells)] = value; }

DEVICE_FORCEINLINE e4 smem_ld_e4(const bf *cells, const u32 bucket, const u32 budget_cells) {
  const uint4 value = *reinterpret_cast<const uint4 *>(cells + smem_warp_base(budget_cells) + bucket * BWD_VM_BUCKET_WORDS +
                                                       (threadIdx.x & BWD_VM_LANE_MASK) * BWD_VM_E4_WORDS);
  return *reinterpret_cast<const e4 *>(&value);
}

DEVICE_FORCEINLINE void smem_st_e4(bf *cells, const u32 bucket, const u32 budget_cells, const e4 value) {
  *reinterpret_cast<uint4 *>(cells + smem_warp_base(budget_cells) + bucket * BWD_VM_BUCKET_WORDS + (threadIdx.x & BWD_VM_LANE_MASK) * BWD_VM_E4_WORDS) =
      *reinterpret_cast<const uint4 *>(&value);
}

DEVICE_FORCEINLINE e4 role_combine(const e4 endpoint, const u32 active_mask) {
  const u32 paired_low_lane = threadIdx.x & BWD_VM_HALF_WARP_MASK;
  const uint4 endpoint_words = *reinterpret_cast<const uint4 *>(&endpoint);
  uint4 a_words;
  a_words.x = __shfl_sync(active_mask, endpoint_words.x, paired_low_lane);
  a_words.y = __shfl_sync(active_mask, endpoint_words.y, paired_low_lane);
  a_words.z = __shfl_sync(active_mask, endpoint_words.z, paired_low_lane);
  a_words.w = __shfl_sync(active_mask, endpoint_words.w, paired_low_lane);
  const e4 a = *reinterpret_cast<const e4 *>(&a_words);
  if ((threadIdx.x & BWD_VM_LANE_MASK) < BWD_VM_HALF_WARP_LANES)
    return a;
  return e4::sub(e4::add(endpoint, endpoint), a);
}

DEVICE_FORCEINLINE const char *source_column(const bwd_vm_source_window &window, const u32 column) {
  return window.read_base + static_cast<size_t>(column) * window.read_stride_bytes;
}

DEVICE_FORCEINLINE char *publish_column(const bwd_vm_source_window &window, const u32 column) {
  return window.publish_base + static_cast<size_t>(column) * window.publish_stride_bytes;
}

template <bool BASE> DEVICE_FORCEINLINE e4 load_source_value(const char *column, const size_t index) {
  if constexpr (BASE)
    return e4::from_scalar(load<bf, ld_modifier::ca>(reinterpret_cast<const bf *>(column), index));
  else
    return load<e4, ld_modifier::ca>(reinterpret_cast<const e4 *>(column), index);
}

template <bool BASE> DEVICE_FORCEINLINE void store_source_value(char *column, const size_t index, const e4 value) {
  if constexpr (BASE)
    store<bf, st_modifier::cs>(reinterpret_cast<bf *>(column), value[0][0], index);
  else
    store<e4, st_modifier::cs>(reinterpret_cast<e4 *>(column), value, index);
}

template <bool BASE, bool VALIDATE, typename Loader>
DEVICE_FORCEINLINE e4 fold_endpoint(const bwd_vm_desc &desc, Loader load_value, const size_t endpoint, const u8 backing_depth, const u8 target_depth,
                                    u32 &error) {
  if constexpr (VALIDATE) {
    if (backing_depth > target_depth || target_depth > desc.n_round_challenges || (target_depth != 0 && desc.round_challenges == nullptr)) {
      error |= BWD_VM_ERR_DESC_BOUNDS;
      return e4::ZERO();
    }
  }
  const u32 delta = target_depth - backing_depth;
  if (delta == 0)
    return load_value(endpoint);
  if constexpr (VALIDATE) {
    if (delta >= 31) {
      error |= BWD_VM_ERR_DESC_BOUNDS;
      return e4::ZERO();
    }
  }
  const u32 leaves = 1u << delta;
  e4 folded = e4::ZERO();
  for (u32 leaf = 0; leaf < leaves; leaf++) {
    e4 weight = e4::ONE();
    for (u32 round = 0; round < delta; round++) {
      const e4 challenge = desc.round_challenges[backing_depth + round];
      const e4 factor = ((leaf >> round) & 1u) != 0 ? challenge : e4::sub(e4::ONE(), challenge);
      weight = e4::mul(weight, factor);
    }
    folded = e4::fma(load_value(endpoint * leaves + leaf), weight, folded);
  }
  return folded;
}

DEVICE_FORCEINLINE gkr_base_source_kind virtual_kind(const u32 payload) {
  return static_cast<gkr_base_source_kind>(GKR_BASE_SOURCE_VIRTUAL_RANGE_CHECK_16_BITS + payload);
}

template <bool BASE, bool VALIDATE>
DEVICE_FORCEINLINE e4 resolve_source_endpoint(const bwd_vm_desc &desc, const u32 window_index, const u32 column, const bool first_access, const size_t endpoint,
                                              u32 &error) {
  if constexpr (VALIDATE) {
    if (window_index >= desc.n_source_windows || window_index >= BWD_VM_SOURCE_WINDOW_CAP) {
      error |= BWD_VM_ERR_SOURCE_OOB;
      return e4::ZERO();
    }
  }
  const bwd_vm_source_window &window = desc.source_windows[window_index];
  if constexpr (VALIDATE) {
    if (window.materialize > 1 || (window.materialize != 0 && (window.publish_base == nullptr || window.publish_stride_bytes == 0))) {
      error |= window.materialize != 0 && window.publish_base == nullptr ? BWD_VM_ERR_NULL_POINTER : BWD_VM_ERR_DESC_BOUNDS;
      return e4::ZERO();
    }
    if (window.source_kind == BWD_VM_SOURCE_VIRTUAL) {
      const bool procedural = window.backing_depth == 0;
      if constexpr (BASE) {
        error |= EVAL_VM_ERR_FIELD_MISMATCH;
        return e4::ZERO();
      }
      if (column > BWD_VM_VIRTUAL_INITS_AND_TEARDOWNS_HIGH) {
        error |= BWD_VM_ERR_BAD_SPECIAL;
        return e4::ZERO();
      }
      if (window.target_depth != desc.n_round_challenges || (procedural && window.target_depth > BWD_VM_VIRTUAL_MATERIALIZE_DEPTH) ||
          (!procedural && (window.backing_depth < BWD_VM_VIRTUAL_MATERIALIZE_DEPTH || static_cast<u32>(window.backing_depth) + 1 != window.target_depth))) {
        error |= BWD_VM_ERR_DESC_BOUNDS;
        return e4::ZERO();
      }
      const bool expected_materialize = window.target_depth >= BWD_VM_VIRTUAL_MATERIALIZE_DEPTH;
      if ((window.materialize != 0) != expected_materialize) {
        error |= BWD_VM_ERR_DESC_BOUNDS;
        return e4::ZERO();
      }
      if ((procedural && (window.read_base != nullptr || window.read_stride_bytes != 0)) ||
          (!procedural && (window.read_base == nullptr || window.read_stride_bytes == 0)) ||
          (window.materialize == 0 && (window.publish_base != nullptr || window.publish_stride_bytes != 0))) {
        error |= (!procedural && window.read_base == nullptr) ? BWD_VM_ERR_NULL_POINTER : BWD_VM_ERR_DESC_BOUNDS;
        return e4::ZERO();
      }
    } else {
      const u8 expected_source_kind = BASE ? BWD_VM_SOURCE_READ_BASE : BWD_VM_SOURCE_READ_EXT;
      if (window.source_kind != expected_source_kind) {
        error |= EVAL_VM_ERR_FIELD_MISMATCH;
        return e4::ZERO();
      }
      if (window.read_base == nullptr || window.read_stride_bytes == 0) {
        error |= window.read_base == nullptr ? BWD_VM_ERR_NULL_POINTER : BWD_VM_ERR_DESC_BOUNDS;
        return e4::ZERO();
      }
    }
  }
  if (window.materialize != 0 && !first_access)
    return load_source_value<BASE>(publish_column(window, column), endpoint);

  if (window.source_kind == BWD_VM_SOURCE_VIRTUAL) {
    const gkr_base_source_kind kind = virtual_kind(column);
    e4 value;
    if (window.backing_depth == 0) {
      value = fold_endpoint<true, VALIDATE>(
          desc, [kind](const size_t index) { return e4::from_scalar(gkr_virtual_base_value(kind, index)); }, endpoint, 0, window.target_depth, error);
    } else {
      const char *read = source_column(window, column);
      value = fold_endpoint<false, VALIDATE>(
          desc, [read](const size_t index) { return load_source_value<false>(read, index); }, endpoint, window.backing_depth, window.target_depth, error);
    }
    if (window.materialize != 0)
      store_source_value<false>(publish_column(window, column), endpoint, value);
    return value;
  }

  const char *read = source_column(window, column);
  const e4 value = fold_endpoint<BASE, VALIDATE>(
      desc, [read](const size_t index) { return load_source_value<BASE>(read, index); }, endpoint, window.backing_depth, window.target_depth, error);
  if (window.materialize != 0 && first_access)
    store_source_value<BASE>(publish_column(window, column), endpoint, value);
  return value;
}

template <bool VALIDATE>
DEVICE_FORCEINLINE e4 read_source(const bwd_vm_desc &desc, const u16 lane, const u32 active_mask, const size_t endpoint, const bool expect_base, u32 &error) {
  const bool first_access = ((lane >> FWD_VM_FIRST_ACCESS_SHIFT) & 1u) != 0;
  const u32 window = (lane >> FWD_VM_SOURCE_WINDOW_SHIFT) & FWD_VM_SOURCE_WINDOW_MASK;
  const u32 column = (lane >> FWD_VM_SOURCE_COLUMN_SHIFT) & FWD_VM_SOURCE_COLUMN_MASK;
  const e4 value = expect_base ? resolve_source_endpoint<true, VALIDATE>(desc, window, column, first_access, endpoint, error)
                               : resolve_source_endpoint<false, VALIDATE>(desc, window, column, first_access, endpoint, error);
  return role_combine(value, active_mask);
}

template <bool VALIDATE>
DEVICE_FORCEINLINE e4 read_virtual(const bwd_vm_desc &desc, const u32 payload, const u32 active_mask, const size_t endpoint, u32 &error) {
  if constexpr (VALIDATE) {
    if (payload > BWD_VM_VIRTUAL_INITS_AND_TEARDOWNS_HIGH) {
      error |= BWD_VM_ERR_BAD_SPECIAL;
      return e4::ZERO();
    }
  }
  const gkr_base_source_kind kind = virtual_kind(payload);
  const e4 value = e4::from_scalar(gkr_virtual_base_value(kind, endpoint));
  return role_combine(value, active_mask);
}

template <bool VALIDATE> DEVICE_FORCEINLINE u16 bwd_vm_lane(const bwd_vm_desc &desc, const u32 index, u32 &lane_error) {
  if constexpr (VALIDATE) {
    if (index >= desc.program_lanes || index >= BWD_VM_PROGRAM_CAP) {
      lane_error |= BWD_VM_ERR_PROGRAM_OOB;
      return 0xffffu;
    }
  }
  return desc.program[index];
}

// VALIDATE-only structural pass through the exact shared decoder. Typed
// operand/destination hooks are deliberately side-effect-free: this pass
// proves every encoded lane can be consumed before the real adapter is allowed
// to read or publish a source.
struct BwdVmPreflightAdapter {
  const bwd_vm_desc &desc;
  mutable u32 lane_error;

  DEVICE_FORCEINLINE u16 lane(const u32 index) const { return bwd_vm_lane<true>(desc, index, lane_error); }
  DEVICE_FORCEINLINE bf read_bf(const u16, u32 &) { return bf::ZERO(); }
  DEVICE_FORCEINLINE e4 read_e4(const u16, u32 &) { return e4::ZERO(); }
  DEVICE_FORCEINLINE void write_bf(const u16, const bf, u32 &) {}
  DEVICE_FORCEINLINE void write_e4(const u16, const e4, u32 &) {}
};

DEVICE_FORCEINLINE u32 preflight_error(const bwd_vm_desc &desc) {
  BwdVmPreflightAdapter adapter{desc, 0};
  const eval_vm_result result = eval_vm_execute<true, BwdVmPreflightAdapter>(adapter, desc.n_instr, desc.program_lanes);
  if (adapter.lane_error != 0)
    return adapter.lane_error;
  return result.error;
}

template <bool VALIDATE> struct BwdVmAdapter {
  const bwd_vm_desc &desc;
  bf *cells;
  u32 budget_cells;
  u32 active_mask;
  size_t endpoint;
  mutable u32 lane_error;

  DEVICE_FORCEINLINE u16 lane(const u32 index) const { return bwd_vm_lane<VALIDATE>(desc, index, lane_error); }

  DEVICE_FORCEINLINE bf read_bf(const u16 lane, u32 &error) {
    if constexpr (VALIDATE) {
      if (lane_error != 0)
        return bf::ZERO();
    }
    switch (lane & FWD_VM_OPERAND_TAG_MASK) {
    case FWD_VM_OPERAND_SOURCE:
      return read_source<VALIDATE>(desc, lane, active_mask, endpoint, true, error)[0][0];
    case FWD_VM_OPERAND_SMEM: {
      const u32 cell = lane >> FWD_VM_OPERAND_CELL_SHIFT;
      if constexpr (VALIDATE) {
        if (cell >= budget_cells * BWD_VM_BF_PER_BUCKET) {
          error |= BWD_VM_ERR_CELL_OOB;
          return bf::ZERO();
        }
      }
      return smem_ld_bf(cells, cell, budget_cells);
    }
    case FWD_VM_OPERAND_LDC: {
      const u32 sub = (lane >> FWD_VM_LDC_SUB_SHIFT) & FWD_VM_LDC_SUB_MASK;
      const u32 index = lane >> FWD_VM_LDC_IDX_SHIFT;
      if (sub == LDC_CONST) {
        if constexpr (VALIDATE) {
          if (index >= desc.n_bf_constants) {
            error |= BWD_VM_ERR_LDC_OOB;
            return bf::ZERO();
          }
        }
        return desc.bf_constants[index];
      }
      if (sub == LDC_SPECIAL) {
        if (index == SPECIAL_ONE)
          return bf::ONE();
        if (index == SPECIAL_NEG_ONE)
          return bf_minus_one();
        if constexpr (VALIDATE)
          error |= BWD_VM_ERR_BAD_SPECIAL;
        return bf::ZERO();
      }
      if constexpr (VALIDATE)
        error |= EVAL_VM_ERR_FIELD_MISMATCH;
      return bf::ZERO();
    }
    default: {
      const u32 index = lane >> FWD_VM_OPERAND_DESC_SHIFT;
      if constexpr (VALIDATE) {
        if (index >= desc.n_specials || index >= BWD_VM_SPECIAL_CAP) {
          error |= BWD_VM_ERR_SPECIAL_OOB;
          return bf::ZERO();
        }
      }
      const bwd_vm_special special = desc.specials[index];
      const u32 kind = special.packed & BWD_VM_SPECIAL_KIND_MASK;
      const u32 payload = special.packed >> BWD_VM_SPECIAL_PAYLOAD_SHIFT;
      if (kind != BWD_VM_SPECIAL_KIND_VIRTUAL_SETUP) {
        if constexpr (VALIDATE)
          error |= EVAL_VM_ERR_FIELD_MISMATCH;
        return bf::ZERO();
      }
      return read_virtual<VALIDATE>(desc, payload, active_mask, endpoint, error)[0][0];
    }
    }
  }

  DEVICE_FORCEINLINE e4 read_e4(const u16 lane, u32 &error) {
    if constexpr (VALIDATE) {
      if (lane_error != 0)
        return e4::ZERO();
    }
    switch (lane & FWD_VM_OPERAND_TAG_MASK) {
    case FWD_VM_OPERAND_SOURCE:
      return read_source<VALIDATE>(desc, lane, active_mask, endpoint, false, error);
    case FWD_VM_OPERAND_SMEM: {
      const u32 cell = lane >> FWD_VM_OPERAND_CELL_SHIFT;
      if constexpr (VALIDATE) {
        if (cell >= budget_cells) {
          error |= BWD_VM_ERR_CELL_OOB;
          return e4::ZERO();
        }
      }
      return smem_ld_e4(cells, cell, budget_cells);
    }
    case FWD_VM_OPERAND_LDC: {
      const u32 sub = (lane >> FWD_VM_LDC_SUB_SHIFT) & FWD_VM_LDC_SUB_MASK;
      const u32 index = lane >> FWD_VM_LDC_IDX_SHIFT;
      if (sub == LDC_CONST_DERIVED_E4) {
        if constexpr (VALIDATE) {
          if (index >= desc.n_const_derived_e4) {
            error |= BWD_VM_ERR_LDC_OOB;
            return e4::ZERO();
          }
        }
        return ::ab_gkr_fwd_vm_const_derived_e4[index];
      }
      if (sub == LDC_ARG_DERIVED_E4) {
        if constexpr (VALIDATE) {
          if (index >= desc.n_arg_derived_e4) {
            error |= BWD_VM_ERR_LDC_OOB;
            return e4::ZERO();
          }
        }
        return desc.arg_derived_e4[index];
      }
      if (sub == LDC_SPECIAL) {
        if (index == SPECIAL_ONE)
          return e4::ONE();
        if (index == SPECIAL_NEG_ONE)
          return e4_minus_one();
        if constexpr (VALIDATE)
          error |= BWD_VM_ERR_BAD_SPECIAL;
        return e4::ZERO();
      }
      if constexpr (VALIDATE)
        error |= EVAL_VM_ERR_FIELD_MISMATCH;
      return e4::ZERO();
    }
    default: {
      const u32 index = lane >> FWD_VM_OPERAND_DESC_SHIFT;
      if constexpr (VALIDATE) {
        if (index >= desc.n_specials || index >= BWD_VM_SPECIAL_CAP) {
          error |= BWD_VM_ERR_SPECIAL_OOB;
          return e4::ZERO();
        }
      }
      const bwd_vm_special special = desc.specials[index];
      const u32 kind = special.packed & BWD_VM_SPECIAL_KIND_MASK;
      const u32 payload = special.packed >> BWD_VM_SPECIAL_PAYLOAD_SHIFT;
      if (kind == BWD_VM_SPECIAL_KIND_COEFFICIENT || kind == BWD_VM_SPECIAL_KIND_ACC_INIT) {
        if constexpr (VALIDATE) {
          if (payload >= desc.n_coefficients || payload >= BWD_VM_COEFFICIENT_CAP) {
            error |= BWD_VM_ERR_BAD_SPECIAL;
            return e4::ZERO();
          }
        }
        return ::ab_gkr_flat_coefficients[payload];
      }
      if constexpr (VALIDATE)
        error |= BWD_VM_ERR_BAD_SPECIAL;
      return e4::ZERO();
    }
    }
  }

  DEVICE_FORCEINLINE void write_bf(const u16 dst, const bf value, u32 &error) {
    if constexpr (VALIDATE) {
      if (lane_error != 0)
        return;
    }
    if ((dst & FWD_VM_DST_TAG_MASK) != FWD_VM_DST_SMEM) {
      if constexpr (VALIDATE)
        error |= BWD_VM_ERR_BAD_DST;
      return;
    }
    const u32 cell = dst >> FWD_VM_DST_CELL_SHIFT;
    if constexpr (VALIDATE) {
      if (cell >= budget_cells * BWD_VM_BF_PER_BUCKET) {
        error |= BWD_VM_ERR_CELL_OOB;
        return;
      }
    }
    smem_st_bf(cells, cell, budget_cells, value);
  }

  DEVICE_FORCEINLINE void write_e4(const u16 dst, const e4 value, u32 &error) {
    if constexpr (VALIDATE) {
      if (lane_error != 0)
        return;
    }
    if ((dst & FWD_VM_DST_TAG_MASK) != FWD_VM_DST_SMEM) {
      if constexpr (VALIDATE)
        error |= BWD_VM_ERR_BAD_DST;
      return;
    }
    const u32 cell = dst >> FWD_VM_DST_CELL_SHIFT;
    if constexpr (VALIDATE) {
      if (cell >= budget_cells) {
        error |= BWD_VM_ERR_CELL_OOB;
        return;
      }
    }
    smem_st_e4(cells, cell, budget_cells, value);
  }
};

template <bool VALIDATE> DEVICE_FORCEINLINE u32 descriptor_error(const bwd_vm_desc &desc, const u32 budget_cells, const u32 smem_bytes) {
  if constexpr (!VALIDATE)
    return 0;
  u32 error = 0;
  const u32 cell_bytes = blockDim.x * static_cast<u32>(sizeof(e4));
  if (blockDim.x != BWD_VM_THREADS_PER_BLOCK || smem_bytes % cell_bytes != 0 || budget_cells < BWD_VM_MIN_BUDGET_CELLS ||
      budget_cells > BWD_VM_MAX_BUDGET_CELLS)
    error |= BWD_VM_ERR_BUDGET;
  if (desc.program_lanes > BWD_VM_PROGRAM_CAP || desc.n_instr > desc.program_lanes || desc.n_source_windows > BWD_VM_SOURCE_WINDOW_CAP ||
      desc.n_specials > BWD_VM_SPECIAL_CAP || desc.n_coefficients > BWD_VM_COEFFICIENT_CAP || desc.n_bf_constants > BWD_VM_BF_CONSTANT_CAP ||
      desc.n_arg_derived_e4 > BWD_VM_ARG_DERIVED_E4_CAP || desc.n_const_derived_e4 > BWD_VM_CONST_DERIVED_E4_CAP ||
      desc.cell_count > budget_cells * BWD_VM_BF_PER_BUCKET)
    error |= BWD_VM_ERR_DESC_BOUNDS;
  if (desc.contributions != nullptr && desc.eq_low == nullptr)
    error |= BWD_VM_ERR_NULL_POINTER;
  return error;
}

template <bool VALIDATE> DEVICE_FORCEINLINE void bwd_vm_body(const bwd_vm_desc &desc, u32 *error_flag, e4 *diagnostic_t0_t2) {
  extern __shared__ e4 bwd_vm_cells_dyn[];
  u32 smem_bytes;
  asm("mov.u32 %0, %%dynamic_smem_size;" : "=r"(smem_bytes));
  const u32 cell_bytes = blockDim.x * static_cast<u32>(sizeof(e4));
  const u32 budget_cells = cell_bytes == 0 ? 0 : smem_bytes / cell_bytes;
  bf *cells = reinterpret_cast<bf *>(bwd_vm_cells_dyn);
  for (u32 cell = 0; cell < budget_cells * BWD_VM_BF_PER_BUCKET; cell++)
    smem_st_bf(cells, cell, budget_cells, bf::ZERO());

  u32 error = descriptor_error<VALIDATE>(desc, budget_cells, smem_bytes);
  if constexpr (VALIDATE) {
    // Descriptor-level bounds are uniform and fatal. In particular, do not
    // let a malformed count reach adapter lane fetches or source side effects.
    if (error != 0) {
      if (threadIdx.x == 0)
        atomicOr(error_flag, error);
      return;
    }
    const u32 structural_error = preflight_error(desc);
    if (structural_error != 0) {
      if (threadIdx.x == 0)
        atomicOr(error_flag, structural_error);
      return;
    }
  }
  const u32 lane = threadIdx.x & BWD_VM_LANE_MASK;
  const size_t global_warp = static_cast<size_t>(blockIdx.x) * (blockDim.x / BWD_VM_WARP_LANES) + (threadIdx.x >> BWD_VM_WARP_SHIFT);
  const size_t logical_row = global_warp * BWD_VM_HALF_WARP_LANES + (lane & BWD_VM_HALF_WARP_MASK);
  const bool active = logical_row < desc.logical_rows;
  const u32 active_mask = __ballot_sync(0xffffffffu, active);
  if (!active) {
    if constexpr (VALIDATE) {
      if (error != 0)
        atomicOr(error_flag, error);
    }
    return;
  }

  const size_t endpoint = 2 * logical_row + (lane >= BWD_VM_HALF_WARP_LANES ? 1 : 0);
  BwdVmAdapter<VALIDATE> adapter{desc, cells, budget_cells, active_mask, endpoint, 0};
  const eval_vm_result result = eval_vm_execute<VALIDATE, BwdVmAdapter<VALIDATE>>(adapter, desc.n_instr, desc.program_lanes);
  u32 executor_error = result.error;
  if constexpr (VALIDATE) {
    // A logical lane overrun is more precise than the executor's final
    // consumption mismatch and proves no inline-array OOB occurred.
    if (adapter.lane_error != 0)
      executor_error &= ~EVAL_VM_ERR_TRAILING_LANES;
    error |= adapter.lane_error;
  }
  error |= executor_error;
  if (desc.contributions != nullptr && error == 0) {
    const e4 eq = gkr_compute_eq_inline<e4>(desc.eq_low, desc.eq_sizes, static_cast<u32>(logical_row));
    const e4 contribution = e4::mul(result.acc, eq);
    const size_t role_offset = lane >= BWD_VM_HALF_WARP_LANES ? desc.logical_rows : 0;
    store<e4, st_modifier::cs>(desc.contributions + role_offset, contribution, logical_row);
  }
  if constexpr (VALIDATE) {
    if (diagnostic_t0_t2 != nullptr && error == 0) {
      const size_t role_offset = lane >= BWD_VM_HALF_WARP_LANES ? desc.logical_rows : 0;
      store<e4, st_modifier::cs>(diagnostic_t0_t2 + role_offset, result.acc, logical_row);
    }
    if (error != 0)
      atomicOr(error_flag, error);
  }
}

} // namespace airbender::prover::gkr

EXTERN __launch_bounds__(airbender::prover::gkr::BWD_VM_THREADS_PER_BLOCK) __global__
    void ab_gkr_bwd_vm_release_kernel(const __grid_constant__ airbender::prover::gkr::bwd_vm_desc desc) {
  airbender::prover::gkr::bwd_vm_body<false>(desc, nullptr, nullptr);
}

EXTERN __launch_bounds__(airbender::prover::gkr::BWD_VM_THREADS_PER_BLOCK) __global__
    void ab_gkr_bwd_vm_validate_kernel(const __grid_constant__ airbender::prover::gkr::bwd_vm_desc desc, u32 *error_flag, e4 *diagnostic_t0_t2) {
  airbender::prover::gkr::bwd_vm_body<true>(desc, error_flag, diagnostic_t0_t2);
}
