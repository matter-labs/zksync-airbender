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
constexpr u16 WINDOW_CLASS_LINEAR_BF_PROCEDURAL_A = 4;
constexpr u16 WINDOW_CLASS_PRODUCT_E4_E4 = 5;
constexpr u16 WINDOW_CLASS_GROUP_BF = 6;
constexpr u16 WINDOW_CLASS_GROUP_E4 = 7;
constexpr u16 WINDOW_CLASS_PRODUCT_BF_BF_PROCEDURAL_B = 8;
constexpr u16 WINDOW_CLASS_FIELD_E4 = 1;
constexpr u16 WINDOW_IMMEDIATE_ONE = 0;
constexpr u16 WINDOW_IMMEDIATE_NEG_ONE = 1;
constexpr u16 WINDOW_IMMEDIATE_RESERVED = 2;
constexpr u16 WINDOW_REDUCE_AFTER = 1u << 15;
constexpr u16 WINDOW_IMMEDIATE_ID_MASK = WINDOW_REDUCE_AFTER - 1u;
constexpr u16 WINDOW_SOURCE_COLUMN_BITS = 7;
constexpr u16 WINDOW_SOURCE_COLUMN_MASK = (1u << WINDOW_SOURCE_COLUMN_BITS) - 1u;
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

template <typename T, u32 COUNT> struct alignas((sizeof(T) * COUNT < 32) ? sizeof(T) * COUNT : 32) window_packed_values {
  T values[COUNT];
};

using window_bf_pair = window_packed_values<bf, 2>;
using window_bf_quad = window_packed_values<bf, 4>;
using window_bf_cube = window_packed_values<bf, 8>;
using window_e4_pair = window_packed_values<e4, 2>;
using window_e4_quad = window_packed_values<e4, 4>;
using window_e4_cube = window_packed_values<e4, 8>;

static_assert(sizeof(window_bf_pair) == 8 && alignof(window_bf_pair) == 8);
static_assert(sizeof(window_bf_quad) == 16 && alignof(window_bf_quad) == 16);
static_assert(sizeof(window_bf_cube) == 32 && alignof(window_bf_cube) == 32);
static_assert(sizeof(window_e4_pair) == 32 && alignof(window_e4_pair) == 32);
static_assert(sizeof(window_e4_quad) == 64 && alignof(window_e4_quad) == 32);
static_assert(sizeof(window_e4_cube) == 128 && alignof(window_e4_cube) == 32);

template <typename T> struct window_direct_source {
  const T *column;

  DEVICE_FORCEINLINE T value(const u32 index) const { return ::airbender::primitives::memory::load<T, ld_modifier::ca>(column, index); }

  template <u32 COUNT> DEVICE_FORCEINLINE window_packed_values<T, COUNT> load_contiguous(const u32 index) const {
    using packed = window_packed_values<T, COUNT>;
    return ::airbender::primitives::memory::load<packed, ld_modifier::ca>(reinterpret_cast<const packed *>(column + index));
  }
};

using window_bf_source = window_direct_source<bf>;
using window_e4_source = window_direct_source<e4>;

constexpr HOST_DEVICE_FORCEINLINE u32 window_procedural_raw(const u16 kind, const u32 index) {
  switch (kind) {
  case 0:
    return index < (1u << 16) ? index : 0;
  case 1:
    return index < (1u << 19) ? index : 0;
  case 2:
    return (index << 2) & 0xffffu;
  case 3:
    return index >> 14;
  default:
    return 0;
  }
}

static_assert(window_procedural_raw(0, 0xffffu) == 0xffffu);
static_assert(window_procedural_raw(0, 0x10000u) == 0);
static_assert(window_procedural_raw(1, 0x7ffffu) == 0x7ffffu);
static_assert(window_procedural_raw(1, 0x80000u) == 0);
static_assert(window_procedural_raw(2, 0x12345u) == 0x8d14u);
static_assert(window_procedural_raw(3, 1u << 14) == 1);

struct window_procedural_source {
  u16 kind;

  DEVICE_FORCEINLINE bf value(const u32 index) const { return bf::from_u32_unchecked(window_procedural_raw(kind, index)); }
};

DEVICE_FORCEINLINE window_bf_source window_resolve_bf_source(const window_vm_desc &desc, const u16 source, const u32 log_trace) {
  const u16 window = source >> WINDOW_SOURCE_COLUMN_BITS;
  const u16 column = source & WINDOW_SOURCE_COLUMN_MASK;
  const bf *window_base = reinterpret_cast<const bf *>(desc.window_bases[window].base);
  return {window_base + (static_cast<size_t>(column) << log_trace)};
}

DEVICE_FORCEINLINE window_e4_source window_resolve_e4_source(const window_vm_desc &desc, const u16 source, const u32 log_trace) {
  const u16 window = source >> WINDOW_SOURCE_COLUMN_BITS;
  const u16 column = source & WINDOW_SOURCE_COLUMN_MASK;
  const e4 *window_base = reinterpret_cast<const e4 *>(desc.window_bases[window].base);
  return {window_base + (static_cast<size_t>(column) << log_trace)};
}

DEVICE_FORCEINLINE bf window_sub(const bf one, const bf zero) { return bf::sub(one, zero); }

DEVICE_FORCEINLINE e4 window_sub(const e4 &one, const e4 &zero) { return e4::sub(one, zero); }

constexpr HOST_DEVICE_FORCEINLINE u32 window_corner_index(const u32 row, const u32 /*log_rows*/, const u32 bit0, const u32 bit1, const u32 bit2) {
  const u32 corner = bit2 | (bit1 << 1) | (bit0 << 2);
  return (row << 3) | corner;
}

static_assert(window_corner_index(3, 5, 0, 0, 0) == 24);
static_assert(window_corner_index(3, 5, 0, 0, 1) == 25);
static_assert(window_corner_index(3, 5, 0, 1, 0) == 26);
static_assert(window_corner_index(3, 5, 0, 1, 1) == 27);
static_assert(window_corner_index(3, 5, 1, 0, 0) == 28);
static_assert(window_corner_index(3, 5, 1, 0, 1) == 29);
static_assert(window_corner_index(3, 5, 1, 1, 0) == 30);
static_assert(window_corner_index(3, 5, 1, 1, 1) == 31);
static_assert(window_corner_index(3, 24, 1, 1, 1) == 31);

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

template <typename T> struct window_pair {
  T values[2];

  template <typename F> DEVICE_FORCEINLINE void apply(F fn) {
#pragma unroll
    for (u32 cell = 0; cell < 2; ++cell)
      fn(values[cell], cell);
  }

  template <typename F> DEVICE_FORCEINLINE void apply(F fn) const {
#pragma unroll
    for (u32 cell = 0; cell < 2; ++cell)
      fn(values[cell], cell);
  }
};

template <typename T>
DEVICE_FORCEINLINE window_pair<T> window_direct_xy_pair(const window_direct_source<T> &source, const u32 row, const u32 log_rows,
                                                        const window_selector selector) {
  if (!selector.infinity0 && !selector.infinity1) {
    const auto values = source.template load_contiguous<2>(window_corner_index(row, log_rows, selector.x0, selector.x1, 0));
    return {{values.values[0], values.values[1]}};
  }
  if (selector.infinity0 && !selector.infinity1) {
    const auto zero = source.template load_contiguous<2>(window_corner_index(row, log_rows, 0, selector.x1, 0));
    const auto one = source.template load_contiguous<2>(window_corner_index(row, log_rows, 1, selector.x1, 0));
    return {{window_sub(one.values[0], zero.values[0]), window_sub(one.values[1], zero.values[1])}};
  }
  if (!selector.infinity0 && selector.infinity1) {
    const auto values = source.template load_contiguous<4>(window_corner_index(row, log_rows, selector.x0, 0, 0));
    return {{window_sub(values.values[2], values.values[0]), window_sub(values.values[3], values.values[1])}};
  }
  const auto values = source.template load_contiguous<8>(window_corner_index(row, log_rows, 0, 0, 0));
  const T at_x1_zero_0 = window_sub(values.values[4], values.values[0]);
  const T at_x1_zero_1 = window_sub(values.values[5], values.values[1]);
  const T at_x1_one_0 = window_sub(values.values[6], values.values[2]);
  const T at_x1_one_1 = window_sub(values.values[7], values.values[3]);
  return {{window_sub(at_x1_one_0, at_x1_zero_0), window_sub(at_x1_one_1, at_x1_zero_1)}};
}

DEVICE_FORCEINLINE window_triplet<bf> window_zero_bf_triplet() {
  window_triplet<bf> result;
#pragma unroll
  for (u32 cell = 0; cell < 3; ++cell)
    result.values[cell] = bf::from_reduced_raw_repr(0);
  return result;
}

struct window_register_accumulators {
  e4 values[3];

  DEVICE_FORCEINLINE e4 &operator[](const u32 cell) { return values[cell]; }
};

struct window_u96 {
  u32 lo = 0;
  u32 mid = 0;
  u32 hi = 0;

  DEVICE_FORCEINLINE void add_product(const u32 a, const u32 b) {
    lo = mad_lo_cc(a, b, lo);
    mid = madc_hi_cc(a, b, mid);
    hi = addc(hi, 0u);
  }

  DEVICE_FORCEINLINE bf reduce() const {
    const u64 low = static_cast<u64>(lo) | (static_cast<u64>(mid) << 32);
    // red_wide accepts the full u64 domain.  The remaining word contributes
    // hi * 2^64 / 2^32 = hi * R; the campaign's 93-atom bound gives hi <= 20,
    // so from_u32_unchecked is exact and bf::add completes the reduction.
    return bf::add(bf::red_wide(low), bf::from_u32_unchecked(hi));
  }
};

struct window_canonical_fold {
  window_register_accumulators &accumulators;

  template <typename Sums> DEVICE_FORCEINLINE void accumulate_bf(const e4 core, const Sums &sums) const {
    sums.apply([&](const bf sum, const u32 cell) { accumulators[cell] = e4::add(e4::mul(core, sum), accumulators[cell]); });
  }

  template <typename Sums> DEVICE_FORCEINLINE void accumulate_e4(const e4 core, const Sums &sums) const {
    sums.apply([&](const e4 &sum, const u32 cell) { accumulators[cell] = e4::fma(core, sum, accumulators[cell]); });
  }
};

struct window_u96_fold {
  window_u96 values[3][4];

  template <typename Sums> DEVICE_FORCEINLINE void accumulate_bf(const e4 core, const Sums &sums) {
    sums.apply([&](const bf sum, const u32 cell) {
      values[cell][0].add_product(core[0][0].limb, sum.limb);
      values[cell][1].add_product(core[0][1].limb, sum.limb);
      values[cell][2].add_product(core[1][0].limb, sum.limb);
      values[cell][3].add_product(core[1][1].limb, sum.limb);
    });
  }

  DEVICE_FORCEINLINE void reduce_into(window_register_accumulators &accumulators) const {
#pragma unroll
    for (u32 cell = 0; cell < 3; ++cell)
      accumulators[cell] = e4(e2(values[cell][0].reduce(), values[cell][1].reduce()), e2(values[cell][2].reduce(), values[cell][3].reduce()));
  }
};

template <typename T, typename Source>
DEVICE_FORCEINLINE window_triplet<T> window_resolve_triplet(const Source &source, const u32 row, const u32 log_rows, const window_selector selector) {
  const T endpoint0 = window_xy_endpoint<T>(source, row, log_rows, selector, 0);
  const T endpoint1 = window_xy_endpoint<T>(source, row, log_rows, selector, 1);
  return {{endpoint0, endpoint1, window_sub(endpoint1, endpoint0)}};
}

template <typename T>
DEVICE_FORCEINLINE window_triplet<T> window_resolve_triplet(const window_direct_source<T> &source, const u32 row, const u32 log_rows,
                                                            const window_selector selector) {
  const window_pair<T> endpoints = window_direct_xy_pair(source, row, log_rows, selector);
  return {{endpoints.values[0], endpoints.values[1], window_sub(endpoints.values[1], endpoints.values[0])}};
}

template <typename T, typename Source>
DEVICE_FORCEINLINE window_pair<T> window_resolve_boolean_pair(const Source &source, const u32 row, const u32 log_rows, const window_selector selector) {
  return {{source.value(window_corner_index(row, log_rows, selector.x0, selector.x1, 0)),
           source.value(window_corner_index(row, log_rows, selector.x0, selector.x1, 1))}};
}

template <typename T>
DEVICE_FORCEINLINE window_pair<T> window_resolve_boolean_pair(const window_direct_source<T> &source, const u32 row, const u32 log_rows,
                                                              const window_selector selector) {
  const auto values = source.template load_contiguous<2>(window_corner_index(row, log_rows, selector.x0, selector.x1, 0));
  return {{values.values[0], values.values[1]}};
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

DEVICE_FORCEINLINE void window_apply_bf_immediate(const window_vm_desc &desc, const u16 immediate_id, const window_pair<bf> &value, window_pair<bf> &sum) {
  if (immediate_id == WINDOW_IMMEDIATE_ONE) {
    sum.apply([&](bf &cell_sum, const u32 cell) { cell_sum = bf::add(cell_sum, value.values[cell]); });
  } else if (immediate_id == WINDOW_IMMEDIATE_NEG_ONE) {
    sum.apply([&](bf &cell_sum, const u32 cell) { cell_sum = bf::sub(cell_sum, value.values[cell]); });
  } else {
    const bf immediate = bf::from_reduced_raw_repr(desc.immediates[immediate_id - WINDOW_IMMEDIATE_RESERVED]);
    sum.apply([&](bf &cell_sum, const u32 cell) { cell_sum = bf::add(cell_sum, bf::mul(immediate, value.values[cell])); });
  }
}

DEVICE_FORCEINLINE void window_apply_bf_immediate(const window_vm_desc &desc, const u16 immediate_id, const window_pair<bf> &value, window_triplet<bf> &sum) {
  if (immediate_id == WINDOW_IMMEDIATE_ONE) {
    value.apply([&](const bf cell_value, const u32 cell) { sum.values[cell] = bf::add(sum.values[cell], cell_value); });
  } else if (immediate_id == WINDOW_IMMEDIATE_NEG_ONE) {
    value.apply([&](const bf cell_value, const u32 cell) { sum.values[cell] = bf::sub(sum.values[cell], cell_value); });
  } else {
    const bf immediate = bf::from_reduced_raw_repr(desc.immediates[immediate_id - WINDOW_IMMEDIATE_RESERVED]);
    value.apply([&](const bf cell_value, const u32 cell) { sum.values[cell] = bf::add(sum.values[cell], bf::mul(immediate, cell_value)); });
  }
}

DEVICE_FORCEINLINE void window_apply_e4_sign(const u16 immediate_id, const window_triplet<e4> &value, window_triplet<e4> &sum) {
  if (immediate_id == WINDOW_IMMEDIATE_ONE) {
    sum.apply([&](e4 &cell_sum, const u32 cell) { cell_sum = e4::add(cell_sum, value.values[cell]); });
  } else {
    sum.apply([&](e4 &cell_sum, const u32 cell) { cell_sum = e4::sub(cell_sum, value.values[cell]); });
  }
}

DEVICE_FORCEINLINE void window_apply_e4_sign(const u16 immediate_id, const window_pair<e4> &value, window_pair<e4> &sum) {
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

DEVICE_FORCEINLINE void window_init_bf_immediate(const window_vm_desc &desc, const u16 immediate_id, window_pair<bf> &value) {
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

DEVICE_FORCEINLINE void window_init_e4_sign(const u16 immediate_id, window_pair<e4> &value) {
  if (immediate_id == WINDOW_IMMEDIATE_ONE)
    return;
  value.apply([](e4 &cell_value, const u32) { cell_value = e4::sub(e4::ZERO(), cell_value); });
}

DEVICE_FORCEINLINE window_triplet<bf> window_eval_bf_term(const window_vm_desc &desc, const window_instruction instruction, const u32 row, const u32 log_rows,
                                                          const u32 log_trace, const window_selector selector) {
  switch (instruction.term_class) {
  case WINDOW_CLASS_LINEAR_BF: {
    if (selector.infinity0 || selector.infinity1)
      return window_zero_bf_triplet();
    const window_bf_source source = window_resolve_bf_source(desc, instruction.source_a, log_trace);
    const window_triplet<bf> a = window_resolve_triplet<bf>(source, row, log_rows, selector);
    return {{a.values[0], a.values[1], bf::ZERO()}};
  }
  case WINDOW_CLASS_LINEAR_BF_PROCEDURAL_A: {
    if (selector.infinity0 || selector.infinity1)
      return window_zero_bf_triplet();
    const window_procedural_source source{instruction.source_a};
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
  case WINDOW_CLASS_PRODUCT_BF_BF_PROCEDURAL_B: {
    const window_bf_source source_a_view = window_resolve_bf_source(desc, instruction.source_a, log_trace);
    const window_procedural_source source_b_view{instruction.source_b};
    const window_triplet<bf> a = window_resolve_triplet<bf>(source_a_view, row, log_rows, selector);
    const window_triplet<bf> b = window_resolve_triplet<bf>(source_b_view, row, log_rows, selector);
    return {{bf::mul(a.values[0], b.values[0]), bf::mul(a.values[1], b.values[1]), bf::mul(a.values[2], b.values[2])}};
  }
  default:
    return window_zero_bf_triplet();
  }
}

DEVICE_FORCEINLINE void window_accumulate_bf_product_wide(const window_vm_desc &desc, const window_instruction instruction, const u32 row, const u32 log_rows,
                                                          const u32 log_trace, const window_selector selector, window_triplet<u64> &sum) {
  const window_bf_source source_a_view = window_resolve_bf_source(desc, instruction.source_a, log_trace);
  const window_bf_source source_b_view = window_resolve_bf_source(desc, instruction.source_b, log_trace);
  const window_triplet<bf> a = window_resolve_triplet<bf>(source_a_view, row, log_rows, selector);
  const window_triplet<bf> b = window_resolve_triplet<bf>(source_b_view, row, log_rows, selector);
  const u16 immediate_id = instruction.factor & WINDOW_IMMEDIATE_ID_MASK;
  if (immediate_id == WINDOW_IMMEDIATE_ONE) {
    sum.apply([&](u64 &value, const u32 cell) { value = mad_wide(a.values[cell].limb, b.values[cell].limb, value); });
  } else if (immediate_id == WINDOW_IMMEDIATE_NEG_ONE) {
    sum.apply([&](u64 &value, const u32 cell) { value = mad_wide(bf::ORDER - a.values[cell].limb, b.values[cell].limb, value); });
  } else {
    const bf immediate = bf::from_reduced_raw_repr(desc.immediates[immediate_id - WINDOW_IMMEDIATE_RESERVED]);
    sum.apply([&](u64 &value, const u32 cell) { value = mad_wide(bf::mul(immediate, a.values[cell]).limb, b.values[cell].limb, value); });
  }
}

DEVICE_FORCEINLINE void window_reduce_and_rebase_bf_wide(window_triplet<u64> &sum) {
  sum.apply([](u64 &cell_sum, const u32) { cell_sum = mul_wide(bf::red_wide(cell_sum).limb, bf::MONT_R); });
}

DEVICE_FORCEINLINE window_triplet<bf> window_reduce_bf_wide(const window_triplet<u64> &sum) {
  window_triplet<bf> result;
  result.apply([&](bf &value, const u32 cell) { value = bf::red_wide(sum.values[cell]); });
  return result;
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

template <typename Fold>
DEVICE_FORCEINLINE u32 window_execute_bf_atom(const window_vm_desc &desc, const window_instruction head, u32 pc, const u32 row, const u32 log_rows,
                                              const u32 log_trace, const window_selector selector, Fold &fold) {
  const bool grouped = head.term_class == WINDOW_CLASS_GROUP_BF;
  const u16 arity = grouped ? head.source_a : 1;
  const bool has_product = grouped ? (head.source_b & WINDOW_GROUP_HAS_PRODUCT) != 0
                                   : head.term_class == WINDOW_CLASS_PRODUCT_BF_BF || head.term_class == WINDOW_CLASS_PRODUCT_BF_BF_PROCEDURAL_B;
  const u16 product_prefix_count = grouped ? head.source_b & WINDOW_GROUP_PRODUCT_PREFIX_COUNT_MASK : 0;

  if (!has_product) {
    if (selector.infinity0 || selector.infinity1)
      return pc + (grouped ? arity : 0);

    window_pair<bf> sums;
    if (grouped) {
      const window_instruction first = desc.program[pc++];
      const window_bf_source source = window_resolve_bf_source(desc, first.source_a, log_trace);
      sums = window_resolve_boolean_pair<bf>(source, row, log_rows, selector);
      window_init_bf_immediate(desc, first.factor, sums);

#pragma unroll 1
      for (u16 member = 1; member < arity; ++member) {
        const window_instruction tail = desc.program[pc++];
        const window_bf_source tail_source = window_resolve_bf_source(desc, tail.source_a, log_trace);
        const window_pair<bf> value = window_resolve_boolean_pair<bf>(tail_source, row, log_rows, selector);
        window_apply_bf_immediate(desc, tail.factor, value, sums);
      }
    } else if (head.term_class == WINDOW_CLASS_LINEAR_BF_PROCEDURAL_A) {
      const window_procedural_source source{head.source_a};
      sums = window_resolve_boolean_pair<bf>(source, row, log_rows, selector);
    } else {
      const window_bf_source source = window_resolve_bf_source(desc, head.source_a, log_trace);
      sums = window_resolve_boolean_pair<bf>(source, row, log_rows, selector);
    }

    const e4 core = ::ab_gkr_windowed_coeff_bank[head.factor];
    fold.accumulate_bf(core, sums);
    return pc;
  }

  window_triplet<bf> sums;
  if (grouped && product_prefix_count >= 2) {
    window_triplet<u64> wide_sums{{0, 0, 0}};
#pragma unroll 1
    for (u16 member = 0; member < product_prefix_count; ++member) {
      const window_instruction product = desc.program[pc++];
      window_accumulate_bf_product_wide(desc, product, row, log_rows, log_trace, selector, wide_sums);
      if (product.factor & WINDOW_REDUCE_AFTER)
        window_reduce_and_rebase_bf_wide(wide_sums);
    }
    sums = window_reduce_bf_wide(wide_sums);

    if (selector.infinity0 || selector.infinity1) {
      pc += arity - product_prefix_count;
    } else {
#pragma unroll 1
      for (u16 member = product_prefix_count; member < arity; ++member) {
        const window_instruction tail = desc.program[pc++];
        const window_bf_source source = window_resolve_bf_source(desc, tail.source_a, log_trace);
        const window_pair<bf> value = window_resolve_boolean_pair<bf>(source, row, log_rows, selector);
        window_apply_bf_immediate(desc, tail.factor, value, sums);
      }
    }
  } else if (grouped && product_prefix_count == 1) {
    const window_instruction first = desc.program[pc++];
    sums = window_eval_bf_term(desc, first, row, log_rows, log_trace, selector);
    window_init_bf_immediate(desc, first.factor, sums);

    if (selector.infinity0 || selector.infinity1) {
      pc += arity - 1;
    } else {
#pragma unroll 1
      for (u16 member = 1; member < arity; ++member) {
        const window_instruction tail = desc.program[pc++];
        const window_bf_source source = window_resolve_bf_source(desc, tail.source_a, log_trace);
        const window_pair<bf> value = window_resolve_boolean_pair<bf>(source, row, log_rows, selector);
        window_apply_bf_immediate(desc, tail.factor, value, sums);
      }
    }
  } else {
    const window_instruction first = grouped ? desc.program[pc++] : head;
    sums = window_eval_bf_term(desc, first, row, log_rows, log_trace, selector);
    if (grouped)
      window_init_bf_immediate(desc, first.factor, sums);

#pragma unroll 1
    for (u16 member = 1; member < arity; ++member) {
      const window_instruction tail = desc.program[pc++];
      const window_triplet<bf> value = window_eval_bf_term(desc, tail, row, log_rows, log_trace, selector);
      window_apply_bf_immediate(desc, tail.factor, value, sums);
    }
  }

  const e4 core = ::ab_gkr_windowed_coeff_bank[head.factor];
  fold.accumulate_bf(core, sums);
  return pc;
}

template <typename Fold>
DEVICE_FORCEINLINE u32 window_execute_e4_atom(const window_vm_desc &desc, const window_instruction head, u32 pc, const u32 row, const u32 log_rows,
                                              const u32 log_trace, const window_selector selector, Fold &fold) {
  const bool grouped = head.term_class == WINDOW_CLASS_GROUP_E4;
  const bool has_product = grouped ? (head.source_b & WINDOW_GROUP_HAS_PRODUCT) != 0 : head.term_class != WINDOW_CLASS_LINEAR_E4;
  if (!has_product) {
    if (selector.infinity0 || selector.infinity1)
      return pc + (grouped ? 2 : 0);

    const window_instruction first = grouped ? desc.program[pc++] : head;
    const window_e4_source first_source = window_resolve_e4_source(desc, first.source_a, log_trace);
    window_pair<e4> sums = window_resolve_boolean_pair<e4>(first_source, row, log_rows, selector);
    if (grouped)
      window_init_e4_sign(first.factor, sums);

    if (grouped) {
      const window_instruction second = desc.program[pc++];
      const window_e4_source second_source = window_resolve_e4_source(desc, second.source_a, log_trace);
      const window_pair<e4> second_value = window_resolve_boolean_pair<e4>(second_source, row, log_rows, selector);
      window_apply_e4_sign(second.factor, second_value, sums);
    }

    const e4 core = ::ab_gkr_windowed_coeff_bank[head.factor];
    fold.accumulate_e4(core, sums);
    return pc;
  }

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
  fold.accumulate_e4(core, sums);
  return pc;
}

DEVICE_FORCEINLINE e4 window_eq(const window_vm_desc &desc, const u32 row, const u32 lane) {
  const u32 shift1 = desc.eq_sizes.low;
  const u32 shift0 = desc.eq_sizes.low + desc.eq_sizes.high[1];
  const u32 hi0 = (row >> shift0) & ((1u << desc.eq_sizes.high[0]) - 1u);
  const u32 hi1 = (row >> shift1) & ((1u << desc.eq_sizes.high[1]) - 1u);
  const u32 low = row & ((1u << desc.eq_sizes.low) - 1u);
  const u32 leader_lane = lane & ~low;
  e4 high = e4::ZERO();
  if (lane == leader_lane) {
    high = ::ab_gkr_windowed_eq_high[hi0];
    high = e4::mul(high, ::ab_gkr_windowed_eq_high[256 + hi1]);
  }
  const uint4 packed = reinterpret_cast<const uint4 *>(&high)[0];
  uint4 broadcast;
  broadcast.x = __shfl_sync(0xffffffffu, packed.x, leader_lane);
  broadcast.y = __shfl_sync(0xffffffffu, packed.y, leader_lane);
  broadcast.z = __shfl_sync(0xffffffffu, packed.z, leader_lane);
  broadcast.w = __shfl_sync(0xffffffffu, packed.w, leader_lane);
  high = reinterpret_cast<const e4 *>(&broadcast)[0];
  return e4::mul(high, load<e4, ld_modifier::ca>(desc.eq_low, low));
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

DEVICE_FORCEINLINE void window_add_c_init(const window_vm_desc &desc, const window_selector selector, window_register_accumulators &accumulators) {
  if (desc.c_init_coeff == WINDOW_C_INIT_NONE || selector.infinity0 || selector.infinity1)
    return;
  const e4 c_init = ::ab_gkr_windowed_coeff_bank[desc.c_init_coeff];
  accumulators[0] = e4::add(accumulators[0], c_init);
  accumulators[1] = e4::add(accumulators[1], c_init);
}

EXTERN __global__ __launch_bounds__(WINDOW_THREADS_PER_BLOCK, 8) void ab_gkr_windowed_vm_kernel(const __grid_constant__ window_vm_desc desc) {
  if (blockDim.x != WINDOW_THREADS_PER_BLOCK)
    return;
  const u32 warp = threadIdx.x >> 5;
  const u32 lane = threadIdx.x & 31;
  const u32 blocks_per_row_tile = WINDOW_SELECTOR_BLOCKS_PER_ROW_TILE;
  const u32 row_tile = blockIdx.x / blocks_per_row_tile;
  const u32 selector_group = blockIdx.x % blocks_per_row_tile;
  const u32 selector_id = selector_group * WINDOW_WARPS_PER_BLOCK + warp;
  const u32 x0 = selector_id / 3;
  const u32 x1 = selector_id % 3;
  const window_selector selector{x0, x1, static_cast<bool>(__all_sync(0xffffffffu, x0 == 2)), static_cast<bool>(__all_sync(0xffffffffu, x1 == 2))};
  const u32 candidate_row = row_tile * 32 + lane;
  const u32 log_trace = desc.log_rows + 3;
  const u32 rows = 1u << desc.log_rows;
  const bool active = candidate_row < rows;
  const u32 row = active ? candidate_row : 0;
  window_register_accumulators accumulators;
#pragma unroll
  for (u32 cell = 0; cell < 3; ++cell)
    accumulators[cell] = e4::ZERO();

  window_u96_fold wide_fold;
  u32 pc = 0;
  while (pc < desc.bf_record_count) {
    const window_instruction instruction = desc.program[pc++];
    pc = window_execute_bf_atom(desc, instruction, pc, row, desc.log_rows, log_trace, selector, wide_fold);
  }
  wide_fold.reduce_into(accumulators);

  window_canonical_fold canonical_fold{accumulators};
  while (pc < desc.record_count) {
    const window_instruction instruction = desc.program[pc++];
    pc = window_execute_e4_atom(desc, instruction, pc, row, desc.log_rows, log_trace, selector, canonical_fold);
  }

  window_add_c_init(desc, selector, accumulators);
  const e4 eq = window_eq(desc, row, lane);
#pragma unroll
  for (u32 cell = 0; cell < 3; ++cell) {
    e4 accumulator = active ? e4::mul(eq, accumulators[cell]) : e4::ZERO();
    accumulator = window_warp_sum(accumulator);
    if (lane == 0) {
      const size_t partial_index = static_cast<size_t>(row_tile) * WINDOW_CELLS + 3 * selector_id + cell;
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
