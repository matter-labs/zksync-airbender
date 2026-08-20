#pragma once

#include "primitives/memory.cuh"
#include "primitives/ptx.cuh"
#include "windowed_r0_abi.cuh"

extern __device__ __constant__ e4 ab_gkr_windowed_r0_coeff_bank[airbender::gkr_windowed_bench::R0_COEFFICIENT_CAPACITY];
extern __device__ __constant__ e4 ab_gkr_windowed_r0_eq_high[airbender::gkr_windowed_bench::R0_EQ_HIGH_ELEMENTS];

namespace airbender::gkr_windowed_bench {

using namespace ::airbender::primitives::memory;
using R0VmDesc = r0_vm_desc;

constexpr u16 R0_COEFFICIENT_MASK = 0x1fffu;
constexpr u32 R0_CLASS_SHIFT = 13;
constexpr u8 R0_ORIGIN_PROCEDURAL = 2;
constexpr u32 R0_WINDOW_CELLS = 27;

struct r0_selector_pair {
  u32 x0;
  u32 x1;
  bool inf0;
  bool inf1;

  DEVICE_FORCEINLINE r0_selector_pair(const u32 a, const u32 b) : x0(a), x1(b), inf0(a == 2), inf1(b == 2) {}
  DEVICE_FORCEINLINE r0_selector_pair(const u32 a, const u32 b, const bool a_inf, const bool b_inf) : x0(a), x1(b), inf0(a_inf), inf1(b_inf) {}

  DEVICE_FORCEINLINE bool x0_infinity() const { return inf0; }
  DEVICE_FORCEINLINE bool x1_infinity() const { return inf1; }
  DEVICE_FORCEINLINE bool has_infinity() const { return inf0 || inf1; }
};

enum class r0_axis : u32 { x0 = 0, x1 = 1, x2 = 2 };

constexpr HOST_DEVICE_FORCEINLINE u32 r0_corner_index(const u32 row, const u32 bit0, const u32 bit1, const u32 bit2) {
  return (row << 3) | (bit2 | (bit1 << 1) | (bit0 << 2));
}

static_assert(r0_corner_index(3, 0, 0, 0) == 24);
static_assert(r0_corner_index(3, 0, 0, 1) == 25);
static_assert(r0_corner_index(3, 0, 1, 0) == 26);
static_assert(r0_corner_index(3, 0, 1, 1) == 27);
static_assert(r0_corner_index(3, 1, 0, 0) == 28);
static_assert(r0_corner_index(3, 1, 0, 1) == 29);
static_assert(r0_corner_index(3, 1, 1, 0) == 30);
static_assert(r0_corner_index(3, 1, 1, 1) == 31);

constexpr HOST_DEVICE_FORCEINLINE u32 r0_procedural_raw(const u8 kind, const u32 index) {
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

struct r0_bf_source {
  const bf *column;
  u8 procedural_kind;
  bool procedural;

  DEVICE_FORCEINLINE bf value(const u32 index) const {
    if (procedural)
      return bf::from_u32_unchecked(r0_procedural_raw(procedural_kind, index));
    return load<bf, ld_modifier::ca>(column, index);
  }
};

struct r0_e4_source {
  const e4 *column;

  DEVICE_FORCEINLINE e4 value(const u32 index) const { return load<e4, ld_modifier::ca>(column, index); }
};

DEVICE_FORCEINLINE r0_bf_source r0_resolve_bf_source(const R0VmDesc &desc, const u16 packed) {
  const u16 window = packed >> R0_SOURCE_COLUMN_BITS;
  const u16 column = packed & R0_SOURCE_COLUMN_MASK;
  const r0_window_addr &address = desc.window_bases[window];
  const bf *base = reinterpret_cast<const bf *>(address.base);
  return {base + (static_cast<size_t>(column) << address.log2_stride), address.procedural_kind, address.origin == R0_ORIGIN_PROCEDURAL};
}

DEVICE_FORCEINLINE r0_e4_source r0_resolve_e4_source(const R0VmDesc &desc, const u16 packed) {
  const u16 window = packed >> R0_SOURCE_COLUMN_BITS;
  const u16 column = packed & R0_SOURCE_COLUMN_MASK;
  const r0_window_addr &address = desc.window_bases[window];
  const e4 *base = reinterpret_cast<const e4 *>(address.base);
  return {base + (static_cast<size_t>(column) << address.log2_stride)};
}

DEVICE_FORCEINLINE bf r0_sub(const bf one, const bf zero) { return bf::sub(one, zero); }

DEVICE_FORCEINLINE e4 r0_sub(const e4 one, const e4 zero) { return e4::sub(one, zero); }

template <typename T, typename Source>
DEVICE_FORCEINLINE T r0_xy_endpoint(const Source &source, const u32 row, const r0_selector_pair selector, const u32 bit2) {
  const u32 bit0_zero = selector.x0_infinity() ? 0 : selector.x0;
  const u32 bit1_zero = selector.x1_infinity() ? 0 : selector.x1;
  const T corner00 = source.value(r0_corner_index(row, bit0_zero, bit1_zero, bit2));
  T corner10 = T::ZERO();
  T corner01 = T::ZERO();
  T corner11 = T::ZERO();
  if (selector.x0_infinity())
    corner10 = source.value(r0_corner_index(row, 1, bit1_zero, bit2));
  if (selector.x1_infinity())
    corner01 = source.value(r0_corner_index(row, bit0_zero, 1, bit2));
  if (selector.x0_infinity() && selector.x1_infinity())
    corner11 = source.value(r0_corner_index(row, 1, 1, bit2));
  const T at_x1_zero = selector.x0_infinity() ? r0_sub(corner10, corner00) : corner00;
  if (!selector.x1_infinity())
    return at_x1_zero;
  const T at_x1_one = selector.x0_infinity() ? r0_sub(corner11, corner01) : corner01;
  return r0_sub(at_x1_one, at_x1_zero);
}

template <typename T, typename Source> DEVICE_FORCEINLINE T r0_x2_delta(const Source &source, const u32 row, const r0_selector_pair selector) {
  const T at_zero = r0_xy_endpoint<T>(source, row, selector, 0);
  const T at_one = r0_xy_endpoint<T>(source, row, selector, 1);
  return r0_sub(at_one, at_zero);
}

DEVICE_FORCEINLINE e4 r0_coefficient(const u16 id) {
  if (id == R0_COEFFICIENT_ONE)
    return e4::ONE();
  if (id == R0_COEFFICIENT_NEG_ONE)
    return e4::neg(e4::ONE());
  return ::ab_gkr_windowed_r0_coeff_bank[id - R0_COEFFICIENT_BANK_BIAS];
}

struct r0_decoded_record {
  u8 term_class;
  u16 coefficient_id;
  e4 coefficient;
  u16 source_a;
  u16 source_b;
  u16 packed_source_a;
  u16 packed_source_b;
};

DEVICE_FORCEINLINE r0_decoded_record r0_decode_record(const R0VmDesc &desc, const u32 record) {
  const u32 word = record * R0_RECORD_WORDS;
  const u16 header = desc.program[word];
  const u8 term_class = header >> R0_CLASS_SHIFT;
  const u16 coefficient_id = header & R0_COEFFICIENT_MASK;
  const u16 source_a = desc.program[word + 1];
  const u16 source_b = desc.program[word + 2];
  return {
      term_class,
      coefficient_id,
      r0_coefficient(coefficient_id),
      source_a,
      source_b,
      desc.source_slots[source_a],
      term_class >= R0_CLASS_C2_PRODUCT_BF_BF ? desc.source_slots[source_b] : 0,
  };
}

DEVICE_FORCEINLINE void r0_accumulate_c0_bf(const e4 coefficient, const r0_bf_source &source, const u32 row, const r0_selector_pair selector,
                                            e4 *accumulators) {
  if (selector.has_infinity())
    return;
  accumulators[0] = e4::add(accumulators[0], e4::mul(coefficient, r0_xy_endpoint<bf>(source, row, selector, 0)));
  accumulators[1] = e4::add(accumulators[1], e4::mul(coefficient, r0_xy_endpoint<bf>(source, row, selector, 1)));
}

DEVICE_FORCEINLINE void r0_accumulate_c0_e4(const e4 coefficient, const r0_e4_source &source, const u32 row, const r0_selector_pair selector,
                                            e4 *accumulators) {
  if (selector.has_infinity())
    return;
  accumulators[0] = e4::add(accumulators[0], e4::mul(coefficient, r0_xy_endpoint<e4>(source, row, selector, 0)));
  accumulators[1] = e4::add(accumulators[1], e4::mul(coefficient, r0_xy_endpoint<e4>(source, row, selector, 1)));
}

DEVICE_FORCEINLINE void r0_accumulate_c2(const e4 contribution, e4 *accumulators) {
  accumulators[1] = e4::add(accumulators[1], contribution);
  accumulators[2] = e4::add(accumulators[2], contribution);
}

DEVICE_FORCEINLINE void r0_execute_pair(const R0VmDesc &desc, const u32 row, const r0_selector_pair selector, e4 (&accumulators)[3]) {
  accumulators[0] = e4::ZERO();
  accumulators[1] = e4::ZERO();
  accumulators[2] = e4::ZERO();
#pragma unroll 1
  for (u32 record = 0; record < desc.record_count; ++record) {
    const r0_decoded_record decoded = r0_decode_record(desc, record);
    switch (decoded.term_class) {
    case R0_CLASS_C0_LINEAR_BF:
      r0_accumulate_c0_bf(decoded.coefficient, r0_resolve_bf_source(desc, decoded.packed_source_a), row, selector, accumulators);
      break;
    case R0_CLASS_C0_LINEAR_E4:
      r0_accumulate_c0_e4(decoded.coefficient, r0_resolve_e4_source(desc, decoded.packed_source_a), row, selector, accumulators);
      break;
    case R0_CLASS_C2_PRODUCT_BF_BF: {
      const bf delta_a = r0_x2_delta<bf>(r0_resolve_bf_source(desc, decoded.packed_source_a), row, selector);
      const bf delta_b = r0_x2_delta<bf>(r0_resolve_bf_source(desc, decoded.packed_source_b), row, selector);
      r0_accumulate_c2(e4::mul(decoded.coefficient, bf::mul(delta_a, delta_b)), accumulators);
      break;
    }
    case R0_CLASS_C2_PRODUCT_BF_E4: {
      const bf delta_a = r0_x2_delta<bf>(r0_resolve_bf_source(desc, decoded.packed_source_a), row, selector);
      const e4 delta_b = r0_x2_delta<e4>(r0_resolve_e4_source(desc, decoded.packed_source_b), row, selector);
      r0_accumulate_c2(e4::mul(decoded.coefficient, e4::mul(delta_a, delta_b)), accumulators);
      break;
    }
    case R0_CLASS_C2_PRODUCT_E4_E4: {
      const e4 delta_a = r0_x2_delta<e4>(r0_resolve_e4_source(desc, decoded.packed_source_a), row, selector);
      const e4 delta_b = r0_x2_delta<e4>(r0_resolve_e4_source(desc, decoded.packed_source_b), row, selector);
      r0_accumulate_c2(e4::mul(decoded.coefficient, e4::mul(delta_a, delta_b)), accumulators);
      break;
    }
    }
  }
}

template <r0_axis FixedAxis, r0_axis EnumeratedAxis> DEVICE_FORCEINLINE r0_selector_pair r0_axis_pair(const u32 fixed, const u32 enumerated) {
  static_assert((FixedAxis == r0_axis::x0 && EnumeratedAxis == r0_axis::x1) || (FixedAxis == r0_axis::x1 && EnumeratedAxis == r0_axis::x0));
  if constexpr (FixedAxis == r0_axis::x0)
    return {fixed, enumerated};
  else
    return {enumerated, fixed};
}

template <r0_axis FixedAxis, r0_axis EnumeratedAxis, typename Source>
DEVICE_FORCEINLINE void r0_accumulate_axis_x2_linear(const e4 coefficient, const Source &source, const u32 row, const u32 fixed, e4 (&accumulators)[9]) {
#pragma unroll
  for (u32 enumerated = 0; enumerated < 3; ++enumerated) {
    const r0_selector_pair selector = r0_axis_pair<FixedAxis, EnumeratedAxis>(fixed, enumerated);
    if constexpr (requires { r0_accumulate_c0_bf(coefficient, source, row, selector, accumulators); })
      r0_accumulate_c0_bf(coefficient, source, row, selector, accumulators + 3 * enumerated);
    else
      r0_accumulate_c0_e4(coefficient, source, row, selector, accumulators + 3 * enumerated);
  }
}

DEVICE_FORCEINLINE e4 r0_scaled_product(const e4 coefficient, const bf a, const bf b) { return e4::mul(coefficient, bf::mul(a, b)); }

DEVICE_FORCEINLINE e4 r0_scaled_product(const e4 coefficient, const bf a, const e4 b) { return e4::mul(coefficient, e4::mul(a, b)); }

DEVICE_FORCEINLINE e4 r0_scaled_product(const e4 coefficient, const e4 a, const e4 b) { return e4::mul(coefficient, e4::mul(a, b)); }

template <r0_axis FixedAxis, r0_axis EnumeratedAxis, typename T, typename SourceA, typename U, typename SourceB>
DEVICE_FORCEINLINE void r0_accumulate_axis_x2_product(const e4 coefficient, const SourceA &source_a, const SourceB &source_b, const u32 row, const u32 fixed,
                                                      e4 (&accumulators)[9]) {
#pragma unroll
  for (u32 enumerated = 0; enumerated < 3; ++enumerated) {
    const r0_selector_pair selector = r0_axis_pair<FixedAxis, EnumeratedAxis>(fixed, enumerated);
    const T delta_a = r0_x2_delta<T>(source_a, row, selector);
    const U delta_b = r0_x2_delta<U>(source_b, row, selector);
    r0_accumulate_c2(r0_scaled_product(coefficient, delta_a, delta_b), accumulators + 3 * enumerated);
  }
}

template <typename T> struct r0_x1_factor_endpoints {
  T at_zero;
  T at_one;
};

template <typename T, typename Source> DEVICE_FORCEINLINE T r0_boolean_x2_delta(const Source &source, const u32 row, const u32 x0, const u32 x1) {
  const T at_zero = source.value(r0_corner_index(row, x0, x1, 0));
  const T at_one = source.value(r0_corner_index(row, x0, x1, 1));
  return r0_sub(at_one, at_zero);
}

template <typename T, typename Source> DEVICE_FORCEINLINE r0_x1_factor_endpoints<T> r0_x1_factor(const Source &source, const u32 row, const u32 x0) {
  if (x0 != 2)
    return {
        r0_boolean_x2_delta<T>(source, row, x0, 0),
        r0_boolean_x2_delta<T>(source, row, x0, 1),
    };
  return {
      r0_sub(r0_boolean_x2_delta<T>(source, row, 1, 0), r0_boolean_x2_delta<T>(source, row, 0, 0)),
      r0_sub(r0_boolean_x2_delta<T>(source, row, 1, 1), r0_boolean_x2_delta<T>(source, row, 0, 1)),
  };
}

DEVICE_FORCEINLINE e4 r0_scaled_linear(const e4 coefficient, const bf value) { return e4::mul(coefficient, value); }

DEVICE_FORCEINLINE e4 r0_scaled_linear(const e4 coefficient, const e4 value) { return e4::mul(coefficient, value); }

template <typename T, typename Source>
DEVICE_FORCEINLINE void r0_accumulate_x1_linear(const e4 coefficient, const Source &source, const u32 row, const u32 fixed_x2, const u32 x0, e4 *accumulators) {
  if (fixed_x2 == 2 || x0 == 2)
    return;
  const T at_zero = source.value(r0_corner_index(row, x0, 0, fixed_x2));
  const T at_one = source.value(r0_corner_index(row, x0, 1, fixed_x2));
  accumulators[0] = e4::add(accumulators[0], r0_scaled_linear(coefficient, at_zero));
  accumulators[1] = e4::add(accumulators[1], r0_scaled_linear(coefficient, at_one));
}

template <typename T, typename SourceA, typename U, typename SourceB>
DEVICE_FORCEINLINE void r0_accumulate_x1_product(const e4 coefficient, const SourceA &source_a, const SourceB &source_b, const u32 row, const u32 x0,
                                                 e4 *accumulators) {
  const r0_x1_factor_endpoints<T> a = r0_x1_factor<T>(source_a, row, x0);
  const r0_x1_factor_endpoints<U> b = r0_x1_factor<U>(source_b, row, x0);
  accumulators[0] = e4::add(accumulators[0], r0_scaled_product(coefficient, a.at_zero, b.at_zero));
  accumulators[1] = e4::add(accumulators[1], r0_scaled_product(coefficient, a.at_one, b.at_one));
  accumulators[2] = e4::add(accumulators[2], r0_scaled_product(coefficient, r0_sub(a.at_one, a.at_zero), r0_sub(b.at_one, b.at_zero)));
}

template <r0_axis FixedAxis, r0_axis TripletAxis, r0_axis EnumeratedAxis>
DEVICE_FORCEINLINE void r0_execute_axis_major(const R0VmDesc &desc, const u32 row, const u32 fixed, e4 (&accumulators)[9]) {
  static_assert(FixedAxis != TripletAxis && FixedAxis != EnumeratedAxis && TripletAxis != EnumeratedAxis);
  static_assert((FixedAxis == r0_axis::x0 && TripletAxis == r0_axis::x2 && EnumeratedAxis == r0_axis::x1) ||
                (FixedAxis == r0_axis::x1 && TripletAxis == r0_axis::x2 && EnumeratedAxis == r0_axis::x0) ||
                (FixedAxis == r0_axis::x2 && TripletAxis == r0_axis::x1 && EnumeratedAxis == r0_axis::x0));
#pragma unroll
  for (u32 cell = 0; cell < 9; ++cell)
    accumulators[cell] = e4::ZERO();
#pragma unroll 1
  for (u32 record = 0; record < desc.record_count; ++record) {
    const r0_decoded_record decoded = r0_decode_record(desc, record);
    if constexpr (TripletAxis == r0_axis::x2) {
      switch (decoded.term_class) {
      case R0_CLASS_C0_LINEAR_BF:
        r0_accumulate_axis_x2_linear<FixedAxis, EnumeratedAxis>(decoded.coefficient, r0_resolve_bf_source(desc, decoded.packed_source_a), row, fixed,
                                                                accumulators);
        break;
      case R0_CLASS_C0_LINEAR_E4:
        r0_accumulate_axis_x2_linear<FixedAxis, EnumeratedAxis>(decoded.coefficient, r0_resolve_e4_source(desc, decoded.packed_source_a), row, fixed,
                                                                accumulators);
        break;
      case R0_CLASS_C2_PRODUCT_BF_BF:
        r0_accumulate_axis_x2_product<FixedAxis, EnumeratedAxis, bf, r0_bf_source, bf>(decoded.coefficient, r0_resolve_bf_source(desc, decoded.packed_source_a),
                                                                                       r0_resolve_bf_source(desc, decoded.packed_source_b), row, fixed,
                                                                                       accumulators);
        break;
      case R0_CLASS_C2_PRODUCT_BF_E4:
        r0_accumulate_axis_x2_product<FixedAxis, EnumeratedAxis, bf, r0_bf_source, e4>(decoded.coefficient, r0_resolve_bf_source(desc, decoded.packed_source_a),
                                                                                       r0_resolve_e4_source(desc, decoded.packed_source_b), row, fixed,
                                                                                       accumulators);
        break;
      case R0_CLASS_C2_PRODUCT_E4_E4:
        r0_accumulate_axis_x2_product<FixedAxis, EnumeratedAxis, e4, r0_e4_source, e4>(decoded.coefficient, r0_resolve_e4_source(desc, decoded.packed_source_a),
                                                                                       r0_resolve_e4_source(desc, decoded.packed_source_b), row, fixed,
                                                                                       accumulators);
        break;
      }
    } else {
      switch (decoded.term_class) {
      case R0_CLASS_C0_LINEAR_BF: {
        const r0_bf_source source = r0_resolve_bf_source(desc, decoded.packed_source_a);
#pragma unroll
        for (u32 x0 = 0; x0 < 3; ++x0)
          r0_accumulate_x1_linear<bf>(decoded.coefficient, source, row, fixed, x0, accumulators + 3 * x0);
        break;
      }
      case R0_CLASS_C0_LINEAR_E4: {
        const r0_e4_source source = r0_resolve_e4_source(desc, decoded.packed_source_a);
#pragma unroll
        for (u32 x0 = 0; x0 < 3; ++x0)
          r0_accumulate_x1_linear<e4>(decoded.coefficient, source, row, fixed, x0, accumulators + 3 * x0);
        break;
      }
      case R0_CLASS_C2_PRODUCT_BF_BF: {
        if (fixed == 0)
          break;
        const r0_bf_source source_a = r0_resolve_bf_source(desc, decoded.packed_source_a);
        const r0_bf_source source_b = r0_resolve_bf_source(desc, decoded.packed_source_b);
#pragma unroll
        for (u32 x0 = 0; x0 < 3; ++x0)
          r0_accumulate_x1_product<bf, r0_bf_source, bf>(decoded.coefficient, source_a, source_b, row, x0, accumulators + 3 * x0);
        break;
      }
      case R0_CLASS_C2_PRODUCT_BF_E4: {
        if (fixed == 0)
          break;
        const r0_bf_source source_a = r0_resolve_bf_source(desc, decoded.packed_source_a);
        const r0_e4_source source_b = r0_resolve_e4_source(desc, decoded.packed_source_b);
#pragma unroll
        for (u32 x0 = 0; x0 < 3; ++x0)
          r0_accumulate_x1_product<bf, r0_bf_source, e4>(decoded.coefficient, source_a, source_b, row, x0, accumulators + 3 * x0);
        break;
      }
      case R0_CLASS_C2_PRODUCT_E4_E4: {
        if (fixed == 0)
          break;
        const r0_e4_source source_a = r0_resolve_e4_source(desc, decoded.packed_source_a);
        const r0_e4_source source_b = r0_resolve_e4_source(desc, decoded.packed_source_b);
#pragma unroll
        for (u32 x0 = 0; x0 < 3; ++x0)
          r0_accumulate_x1_product<e4, r0_e4_source, e4>(decoded.coefficient, source_a, source_b, row, x0, accumulators + 3 * x0);
        break;
      }
      }
    }
  }
}

constexpr HOST_DEVICE_FORCEINLINE u32 r0_bit_mask(const u32 bits) { return bits == 0 ? 0 : (1u << bits) - 1u; }

DEVICE_FORCEINLINE e4 r0_eq(const R0VmDesc &desc, const u32 row) {
  const u32 low = row & r0_bit_mask(desc.eq_sizes.low);
  const u32 high1 = (row >> desc.eq_sizes.low) & r0_bit_mask(desc.eq_sizes.high[1]);
  const u32 high0 = (row >> (desc.eq_sizes.low + desc.eq_sizes.high[1])) & r0_bit_mask(desc.eq_sizes.high[0]);
  e4 value = load<e4, ld_modifier::ca>(desc.eq_low, low);
  if (desc.eq_sizes.high[1] != 0)
    value = e4::mul(value, ::ab_gkr_windowed_r0_eq_high[256 + high1]);
  if (desc.eq_sizes.high[0] != 0)
    value = e4::mul(value, ::ab_gkr_windowed_r0_eq_high[high0]);
  return value;
}

DEVICE_FORCEINLINE e4 r0_warp_sum(e4 value) {
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

DEVICE_FORCEINLINE void r0_publish_pair(const R0VmDesc &desc, const u32 row_tile, const u32 selector_id, const u32 lane, const bool active,
                                        e4 (&accumulators)[3]) {
  const e4 equality = r0_eq(desc, active ? row_tile * 32 + lane : 0);
#pragma unroll
  for (u32 x2 = 0; x2 < 3; ++x2) {
    e4 value = active ? e4::mul(equality, accumulators[x2]) : e4::ZERO();
    value = r0_warp_sum(value);
    if (lane == 0) {
      const size_t tensor_index = static_cast<size_t>(3 * selector_id + x2);
      store<e4, st_modifier::cs>(desc.partials, value, static_cast<size_t>(row_tile) * R0_WINDOW_CELLS + tensor_index);
    }
  }
}

template <r0_axis FixedAxis, r0_axis TripletAxis, r0_axis EnumeratedAxis>
constexpr DEVICE_FORCEINLINE u32 r0_axis_tensor_index(const u32 fixed, const u32 triplet, const u32 enumerated) {
  if constexpr (FixedAxis == r0_axis::x0)
    return 9 * fixed + 3 * enumerated + triplet;
  else if constexpr (FixedAxis == r0_axis::x1)
    return 9 * enumerated + 3 * fixed + triplet;
  else
    return 9 * enumerated + 3 * triplet + fixed;
}

template <r0_axis FixedAxis, r0_axis TripletAxis, r0_axis EnumeratedAxis>
DEVICE_FORCEINLINE void r0_publish_axis_major(const R0VmDesc &desc, const u32 row_tile, const u32 fixed, const u32 lane, const bool active,
                                              e4 (&accumulators)[9]) {
  const e4 equality = r0_eq(desc, active ? row_tile * 32 + lane : 0);
#pragma unroll
  for (u32 enumerated = 0; enumerated < 3; ++enumerated) {
#pragma unroll
    for (u32 triplet = 0; triplet < 3; ++triplet) {
      const u32 accumulator = 3 * enumerated + triplet;
      e4 value = active ? e4::mul(equality, accumulators[accumulator]) : e4::ZERO();
      value = r0_warp_sum(value);
      if (lane == 0) {
        const size_t tensor_index = r0_axis_tensor_index<FixedAxis, TripletAxis, EnumeratedAxis>(fixed, triplet, enumerated);
        store<e4, st_modifier::cs>(desc.partials, value, static_cast<size_t>(row_tile) * R0_WINDOW_CELLS + tensor_index);
      }
    }
  }
}

} // namespace airbender::gkr_windowed_bench
