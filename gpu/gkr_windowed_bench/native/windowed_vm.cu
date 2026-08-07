#include "windowed_vm_abi.cuh"
#include <nvtx3/nvToolsExt.h>

__device__ __constant__ e4 ab_gkr_windowed_coeff_bank[80];
__device__ __constant__ e4 ab_gkr_windowed_eq_high[2 * 256];

static_assert((80 + 2 * 256) * sizeof(e4) < 64 * 1024);

extern "C" u64 ab_gkr_windowed_nvtx_range_start(const char *message) { return nvtxRangeStartA(message); }

extern "C" void ab_gkr_windowed_nvtx_range_end(const u64 id) { nvtxRangeEnd(id); }

namespace airbender::gkr_windowed_bench {

using namespace ::airbender::primitives::memory;

constexpr u16 WINDOW_CLASS_LINEAR_BF = 0;
constexpr u16 WINDOW_CLASS_LINEAR_E4 = 1;
constexpr u16 WINDOW_CLASS_PRODUCT_BF_BF = 2;
constexpr u16 WINDOW_CLASS_PRODUCT_BF_E4 = 3;
constexpr u16 WINDOW_CLASS_PRODUCT_E4_E4 = 5;
constexpr u16 WINDOW_CLASS_GROUP_BF = 6;
constexpr u16 WINDOW_CLASS_GROUP_E4 = 7;
constexpr u16 WINDOW_CLASS_FIELD_E4 = 1;
constexpr u16 WINDOW_IMMEDIATE_ONE = 0;
constexpr u16 WINDOW_IMMEDIATE_NEG_ONE = 1;
constexpr u16 WINDOW_IMMEDIATE_RESERVED = 2;
constexpr u32 WINDOW_C_INIT_NONE = 0xffffffffu;

DEVICE_FORCEINLINE bf initialized_bf(const u64 index, const u32 seed, const u32 component) {
  const u64 mixed = static_cast<u64>(seed) + index * 17u + static_cast<u64>(component) * 0x101u;
  const u32 canonical = static_cast<u32>(mixed % (static_cast<u64>(bf::ORDER) - 1u)) + 1u;
  return bf::from_u32_unchecked(canonical);
}

EXTERN __global__ void ab_gkr_windowed_init_bf_kernel(bf *values, const u64 count, const u32 seed) {
  for (u64 index = static_cast<u64>(blockIdx.x) * blockDim.x + threadIdx.x; index < count; index += static_cast<u64>(blockDim.x) * gridDim.x) {
    values[index] = initialized_bf(index, seed, 0);
  }
}

EXTERN __global__ void ab_gkr_windowed_init_e4_kernel(e4 *values, const u64 count, const u32 seed) {
  for (u64 index = static_cast<u64>(blockIdx.x) * blockDim.x + threadIdx.x; index < count; index += static_cast<u64>(blockDim.x) * gridDim.x) {
    const bf coefficients[4] = {initialized_bf(index, seed, 0), initialized_bf(index, seed, 1), initialized_bf(index, seed, 2), initialized_bf(index, seed, 3)};
    values[index] = e4(coefficients);
  }
}

struct window_bf_source {
  const bf *column;

  DEVICE_FORCEINLINE bf value(const u32 index) const { return ::airbender::primitives::memory::load<bf, ld_modifier::ca>(column, index); }
};

struct window_e4_source {
  const e4 *column;

  DEVICE_FORCEINLINE e4 value(const u32 index) const { return ::airbender::primitives::memory::load<e4, ld_modifier::ca>(column, index); }
};

DEVICE_FORCEINLINE window_bf_source window_resolve_bf_source(const window_vm_desc &desc, const u16 source, const u32 log_trace) {
  const window_source_record record = desc.sources[source];
  const u16 window = static_cast<u16>(record.packed);
  const u16 column = static_cast<u16>(record.packed >> 16);
  const bf *window_base = reinterpret_cast<const bf *>(desc.window_bases[window].base);
  return {window_base + (static_cast<size_t>(column) << log_trace)};
}

DEVICE_FORCEINLINE window_e4_source window_resolve_e4_source(const window_vm_desc &desc, const u16 source, const u32 log_trace) {
  const window_source_record record = desc.sources[source];
  const u16 window = static_cast<u16>(record.packed);
  const u16 column = static_cast<u16>(record.packed >> 16);
  const e4 *window_base = reinterpret_cast<const e4 *>(desc.window_bases[window].base);
  return {window_base + (static_cast<size_t>(column) << log_trace)};
}

DEVICE_FORCEINLINE bf window_sub(const bf one, const bf zero) { return bf::sub(one, zero); }

DEVICE_FORCEINLINE e4 window_sub(const e4 &one, const e4 &zero) { return e4::sub(one, zero); }

constexpr HOST_DEVICE_FORCEINLINE u32 window_corner_index(const u32 row, const u32 log_rows, const u32 bit0, const u32 bit1, const u32 bit2) {
  const u32 corner = bit2 | (bit1 << 1) | (bit0 << 2);
  return row | (corner << log_rows);
}

static_assert(window_corner_index(3, 5, 0, 0, 0) == 3);
static_assert(window_corner_index(3, 5, 0, 0, 1) == 35);
static_assert(window_corner_index(3, 5, 0, 1, 0) == 67);
static_assert(window_corner_index(3, 5, 0, 1, 1) == 99);
static_assert(window_corner_index(3, 5, 1, 0, 0) == 131);
static_assert(window_corner_index(3, 5, 1, 0, 1) == 163);
static_assert(window_corner_index(3, 5, 1, 1, 0) == 195);
static_assert(window_corner_index(3, 5, 1, 1, 1) == 227);

struct window_selector {
  u32 x0;
  u32 x1;
  bool infinity0;
  bool infinity1;
};

template <typename T, typename Source>
DEVICE_FORCEINLINE T window_xy_endpoint(const Source &source, const u32 row, const u32 log_rows, const window_selector selector, const u32 bit2) {
  const u32 bit0_zero = selector.infinity0 ? 0 : selector.x0;
  const u32 bit1_zero = selector.infinity1 ? 0 : selector.x1;

  const T corner00 = source.value(window_corner_index(row, log_rows, bit0_zero, bit1_zero, bit2));
  T corner10 = T::ZERO();
  T corner01 = T::ZERO();
  T corner11 = T::ZERO();
  if (selector.infinity0)
    corner10 = source.value(window_corner_index(row, log_rows, 1, bit1_zero, bit2));
  if (selector.infinity1)
    corner01 = source.value(window_corner_index(row, log_rows, bit0_zero, 1, bit2));
  if (selector.infinity0 && selector.infinity1)
    corner11 = source.value(window_corner_index(row, log_rows, 1, 1, bit2));

  const T at_x1_zero = selector.infinity0 ? window_sub(corner10, corner00) : corner00;
  if (!selector.infinity1)
    return at_x1_zero;
  const T at_x1_one = selector.infinity0 ? window_sub(corner11, corner01) : corner01;
  return window_sub(at_x1_one, at_x1_zero);
}

template <typename T> struct window_triplet {
  T values[3];

  template <typename F> DEVICE_FORCEINLINE void apply(F fn) {
#pragma unroll
    for (u32 cell = 0; cell < 3; ++cell)
      fn(values[cell], cell);
  }

  template <typename F> DEVICE_FORCEINLINE void apply(F fn) const {
#pragma unroll
    for (u32 cell = 0; cell < 3; ++cell)
      fn(values[cell], cell);
  }
};

struct window_accumulator_view {
  e4 *thread_base;

  DEVICE_FORCEINLINE e4 &operator[](const u32 cell) const { return thread_base[cell * WINDOW_THREADS_PER_BLOCK]; }
};

template <typename T, typename Source>
DEVICE_FORCEINLINE window_triplet<T> window_resolve_triplet(const Source &source, const u32 row, const u32 log_rows, const window_selector selector) {
  const T endpoint0 = window_xy_endpoint<T>(source, row, log_rows, selector, 0);
  const T endpoint1 = window_xy_endpoint<T>(source, row, log_rows, selector, 1);
  return {{endpoint0, endpoint1, window_sub(endpoint1, endpoint0)}};
}

DEVICE_FORCEINLINE void window_apply_bf_immediate(const window_vm_desc &desc, const u16 immediate_id, const window_triplet<bf> &value,
                                                  window_triplet<bf> &sum) {
  if (immediate_id == WINDOW_IMMEDIATE_ONE) {
    sum.apply([&](bf &cell_sum, const u32 cell) { cell_sum = bf::add(cell_sum, value.values[cell]); });
  } else if (immediate_id == WINDOW_IMMEDIATE_NEG_ONE) {
    sum.apply([&](bf &cell_sum, const u32 cell) { cell_sum = bf::sub(cell_sum, value.values[cell]); });
  } else {
    const bf immediate = bf::from_reduced_raw_repr(desc.immediates[immediate_id - WINDOW_IMMEDIATE_RESERVED]);
    sum.apply([&](bf &cell_sum, const u32 cell) { cell_sum = bf::add(cell_sum, bf::mul(immediate, value.values[cell])); });
  }
}

DEVICE_FORCEINLINE void window_apply_e4_sign(const u16 immediate_id, const window_triplet<e4> &value, window_triplet<e4> &sum) {
  if (immediate_id == WINDOW_IMMEDIATE_ONE) {
    sum.apply([&](e4 &cell_sum, const u32 cell) { cell_sum = e4::add(cell_sum, value.values[cell]); });
  } else {
    sum.apply([&](e4 &cell_sum, const u32 cell) { cell_sum = e4::sub(cell_sum, value.values[cell]); });
  }
}

DEVICE_FORCEINLINE void window_init_bf_immediate(const window_vm_desc &desc, const u16 immediate_id, window_triplet<bf> &value) {
  if (immediate_id == WINDOW_IMMEDIATE_ONE)
    return;
  if (immediate_id == WINDOW_IMMEDIATE_NEG_ONE) {
    value.apply([](bf &cell_value, const u32) { cell_value = bf::sub(bf::ZERO(), cell_value); });
  } else {
    const bf immediate = bf::from_reduced_raw_repr(desc.immediates[immediate_id - WINDOW_IMMEDIATE_RESERVED]);
    value.apply([&](bf &cell_value, const u32) { cell_value = bf::mul(immediate, cell_value); });
  }
}

DEVICE_FORCEINLINE void window_init_e4_sign(const u16 immediate_id, window_triplet<e4> &value) {
  if (immediate_id == WINDOW_IMMEDIATE_ONE)
    return;
  value.apply([](e4 &cell_value, const u32) { cell_value = e4::sub(e4::ZERO(), cell_value); });
}

DEVICE_FORCEINLINE window_triplet<bf> window_eval_bf_term(const window_vm_desc &desc, const window_instruction instruction, const u32 row, const u32 log_rows,
                                                          const u32 log_trace, const window_selector selector) {
  switch (instruction.term_class) {
  case WINDOW_CLASS_LINEAR_BF: {
    if (selector.infinity0 || selector.infinity1)
      return {{bf::ZERO(), bf::ZERO(), bf::ZERO()}};
    const window_bf_source source = window_resolve_bf_source(desc, instruction.source_a, log_trace);
    const window_triplet<bf> a = window_resolve_triplet<bf>(source, row, log_rows, selector);
    return {{a.values[0], a.values[1], bf::ZERO()}};
  }
  case WINDOW_CLASS_PRODUCT_BF_BF: {
    const window_bf_source source_a_view = window_resolve_bf_source(desc, instruction.source_a, log_trace);
    const window_bf_source source_b_view = window_resolve_bf_source(desc, instruction.source_b, log_trace);
    const window_triplet<bf> a = window_resolve_triplet<bf>(source_a_view, row, log_rows, selector);
    const window_triplet<bf> b = window_resolve_triplet<bf>(source_b_view, row, log_rows, selector);
    return {{bf::mul(a.values[0], b.values[0]), bf::mul(a.values[1], b.values[1]), bf::mul(a.values[2], b.values[2])}};
  }
  default:
    return {{bf::ZERO(), bf::ZERO(), bf::ZERO()}};
  }
}

DEVICE_FORCEINLINE window_triplet<e4> window_eval_e4_term(const window_vm_desc &desc, const window_instruction instruction, const u32 row, const u32 log_rows,
                                                          const u32 log_trace, const window_selector selector) {
  switch (instruction.term_class) {
  case WINDOW_CLASS_LINEAR_E4: {
    if (selector.infinity0 || selector.infinity1)
      return {{e4::ZERO(), e4::ZERO(), e4::ZERO()}};
    const window_e4_source source = window_resolve_e4_source(desc, instruction.source_a, log_trace);
    const window_triplet<e4> a = window_resolve_triplet<e4>(source, row, log_rows, selector);
    return {{a.values[0], a.values[1], e4::ZERO()}};
  }
  case WINDOW_CLASS_PRODUCT_BF_E4: {
    const window_bf_source source_bf = window_resolve_bf_source(desc, instruction.source_a, log_trace);
    const window_e4_source source_e4 = window_resolve_e4_source(desc, instruction.source_b, log_trace);
    const window_triplet<bf> a = window_resolve_triplet<bf>(source_bf, row, log_rows, selector);
    const window_triplet<e4> b = window_resolve_triplet<e4>(source_e4, row, log_rows, selector);
    return {{e4::mul(b.values[0], a.values[0]), e4::mul(b.values[1], a.values[1]), e4::mul(b.values[2], a.values[2])}};
  }
  case WINDOW_CLASS_PRODUCT_E4_E4: {
    const window_e4_source source_a_view = window_resolve_e4_source(desc, instruction.source_a, log_trace);
    const window_e4_source source_b_view = window_resolve_e4_source(desc, instruction.source_b, log_trace);
    const window_triplet<e4> a = window_resolve_triplet<e4>(source_a_view, row, log_rows, selector);
    const window_triplet<e4> b = window_resolve_triplet<e4>(source_b_view, row, log_rows, selector);
    return {{e4::mul(a.values[0], b.values[0]), e4::mul(a.values[1], b.values[1]), e4::mul(a.values[2], b.values[2])}};
  }
  default:
    return {{e4::ZERO(), e4::ZERO(), e4::ZERO()}};
  }
}

DEVICE_FORCEINLINE u32 window_execute_bf_atom(const window_vm_desc &desc, const window_instruction head, u32 pc, const u32 row, const u32 log_rows,
                                              const u32 log_trace, const window_selector selector, const window_accumulator_view accumulators) {
  const bool grouped = head.term_class == WINDOW_CLASS_GROUP_BF;
  const u16 arity = grouped ? head.source_a : 1;
  const window_instruction first = grouped ? desc.program[pc++] : head;
  const window_triplet<bf> first_value = window_eval_bf_term(desc, first, row, log_rows, log_trace, selector);
  window_triplet<bf> sums = first_value;
  if (grouped)
    window_init_bf_immediate(desc, first.factor, sums);

#pragma unroll 1
  for (u16 member = 1; member < arity; ++member) {
    const window_instruction tail = desc.program[pc++];
    const window_triplet<bf> value = window_eval_bf_term(desc, tail, row, log_rows, log_trace, selector);
    window_apply_bf_immediate(desc, tail.factor, value, sums);
  }

  const e4 core = ::ab_gkr_windowed_coeff_bank[head.factor];
  sums.apply([&](const bf sum, const u32 cell) { accumulators[cell] = e4::fma(core, sum, accumulators[cell]); });
  return pc;
}

DEVICE_FORCEINLINE u32 window_execute_e4_atom(const window_vm_desc &desc, const window_instruction head, u32 pc, const u32 row, const u32 log_rows,
                                              const u32 log_trace, const window_selector selector, const window_accumulator_view accumulators) {
  const bool grouped = head.term_class == WINDOW_CLASS_GROUP_E4;
  const window_instruction first = grouped ? desc.program[pc++] : head;
  const window_triplet<e4> first_value = window_eval_e4_term(desc, first, row, log_rows, log_trace, selector);
  window_triplet<e4> sums = first_value;
  if (grouped)
    window_init_e4_sign(first.factor, sums);

  if (grouped) {
    const window_instruction second = desc.program[pc++];
    const window_triplet<e4> second_value = window_eval_e4_term(desc, second, row, log_rows, log_trace, selector);
    window_apply_e4_sign(second.factor, second_value, sums);
  }

  const e4 core = ::ab_gkr_windowed_coeff_bank[head.factor];
  sums.apply([&](const e4 &sum, const u32 cell) { accumulators[cell] = e4::fma(core, sum, accumulators[cell]); });
  return pc;
}

DEVICE_FORCEINLINE e4 window_eq(const window_vm_desc &desc, const u32 row) {
  const u32 shift1 = desc.eq_sizes.low;
  const u32 shift0 = desc.eq_sizes.low + desc.eq_sizes.high[1];
  const u32 hi0 = (row >> shift0) & ((1u << desc.eq_sizes.high[0]) - 1u);
  const u32 hi1 = (row >> shift1) & ((1u << desc.eq_sizes.high[1]) - 1u);
  const u32 low = row & ((1u << desc.eq_sizes.low) - 1u);
  e4 value = ::ab_gkr_windowed_eq_high[hi0];
  value = e4::mul(value, ::ab_gkr_windowed_eq_high[256 + hi1]);
  return e4::mul(value, load<e4, ld_modifier::ca>(desc.eq_low, low));
}

DEVICE_FORCEINLINE e4 window_warp_sum(e4 value) {
#pragma unroll
  for (u32 lane_mask = 16; lane_mask != 0; lane_mask >>= 1) {
    e4 shuffled;
    const uint4 *source = reinterpret_cast<const uint4 *>(&value);
    uint4 *destination = reinterpret_cast<uint4 *>(&shuffled);
    destination[0] = shfl_xor(0xffffffffu, source[0], lane_mask, 32);
    value = e4::add(value, shuffled);
  }
  return value;
}

EXTERN __global__ __launch_bounds__(WINDOW_THREADS_PER_BLOCK, 4) void ab_gkr_windowed_vm_kernel(const __grid_constant__ window_vm_desc desc) {
  if (blockDim.x != WINDOW_THREADS_PER_BLOCK)
    return;
  __shared__ e4 shared_accumulators[3 * WINDOW_THREADS_PER_BLOCK];
  const u32 warp = threadIdx.x >> 5;
  const u32 lane = threadIdx.x & 31;
  const u32 x0 = warp / 3;
  const u32 x1 = warp % 3;
  const window_selector selector{x0, x1, static_cast<bool>(__all_sync(0xffffffffu, x0 == 2)), static_cast<bool>(__all_sync(0xffffffffu, x1 == 2))};
  const u32 candidate_row = blockIdx.x * 32 + lane;
  const u32 log_trace = desc.log_rows + 3;
  const u32 rows = 1u << desc.log_rows;
  const bool active = candidate_row < rows;
  const u32 row = active ? candidate_row : 0;
  const window_accumulator_view accumulators{shared_accumulators + threadIdx.x};
#pragma unroll
  for (u32 cell = 0; cell < 3; ++cell)
    accumulators[cell] = e4::ZERO();

  if (desc.c_init_coeff != WINDOW_C_INIT_NONE && !selector.infinity0 && !selector.infinity1) {
    const e4 c_init = ::ab_gkr_windowed_coeff_bank[desc.c_init_coeff];
    accumulators[0] = e4::add(accumulators[0], c_init);
    accumulators[1] = e4::add(accumulators[1], c_init);
  }

  u32 pc = 0;
  while (pc < desc.record_count) {
    const window_instruction instruction = desc.program[pc++];
    if (instruction.term_class & WINDOW_CLASS_FIELD_E4)
      pc = window_execute_e4_atom(desc, instruction, pc, row, desc.log_rows, log_trace, selector, accumulators);
    else
      pc = window_execute_bf_atom(desc, instruction, pc, row, desc.log_rows, log_trace, selector, accumulators);
  }

  const e4 eq = window_eq(desc, row);
#pragma unroll
  for (u32 cell = 0; cell < 3; ++cell) {
    e4 accumulator = active ? e4::mul(accumulators[cell], eq) : e4::ZERO();
    accumulator = window_warp_sum(accumulator);
    if (lane == 0) {
      const size_t partial_index = static_cast<size_t>(blockIdx.x) * WINDOW_CELLS + 3 * warp + cell;
      store<e4, st_modifier::cs>(desc.partials, accumulator, partial_index);
    }
  }
}

EXTERN __global__ void ab_gkr_windowed_finalize_kernel(const e4 *partials, e4 *output, const u32 num_blocks) {
  const u32 cell = blockIdx.x;
  if (cell >= WINDOW_CELLS)
    return;
  e4 sum = e4::ZERO();
  for (u32 block = threadIdx.x; block < num_blocks; block += blockDim.x)
    sum = e4::add(sum, partials[static_cast<size_t>(block) * WINDOW_CELLS + cell]);
  sum = window_warp_sum(sum);

  __shared__ e4 warp_sums[8];
  const u32 lane = threadIdx.x & 31;
  const u32 warp = threadIdx.x >> 5;
  if (lane == 0)
    warp_sums[warp] = sum;
  __syncthreads();
  if (warp == 0) {
    sum = lane < 8 ? warp_sums[lane] : e4::ZERO();
    sum = window_warp_sum(sum);
    if (lane == 0)
      output[cell] = sum;
  }
}

} // namespace airbender::gkr_windowed_bench
