#pragma once

#include "field.cuh"
#include "memory.cuh"

using namespace ::airbender::field;
using namespace ::airbender::memory;

namespace airbender::vectorized {

// I'm basically imitating the wrapping_matrix pattern.
// vectorized_e4_matrix_setter and getter both use "internal" and the add_row and add_col methods,
// so it's nice to inherit them from a common parent.
// But I don't want to inherit directly from matrix_setter<bf, LD_MODIFIER> like this
// template <ld_modifier LD_MODIFIER> vectorized_e4_matrix_setter: matrix_setter<bf, LD_MODIFIER>
// because that would accidentally expose methods of matrix_setter I don't need and
// haven't checked or modified for vector-safety.
// So I inherit from a middleman Accessor parent that only exposes the needed, safe members.
template <typename T, unsigned WIDTH> struct vectorized_matrix_accessor {
  T internal;
  DEVICE_FORCEINLINE void add_row(const unsigned offset) { this->internal.add_row(offset); };
  DEVICE_FORCEINLINE void sub_row(const unsigned offset) { this->internal.sub_row(offset); };
  DEVICE_FORCEINLINE void add_col(const unsigned offset) { this->internal.add_col(WIDTH * offset); };
};

template <unsigned WIDTH> struct width_to_value_type;
template <> struct width_to_value_type<2> {
  using VALUE_TYPE = field::ext2_field;
};
template <> struct width_to_value_type<4> {
  using VALUE_TYPE = field::ext4_field;
};

template <memory::ld_modifier LD_MODIFIER, unsigned WIDTH>
struct vectorized_matrix_getter : vectorized_matrix_accessor<memory::matrix_getter<field::base_field, LD_MODIFIER>, WIDTH> {
  using VALUE_TYPE = width_to_value_type<WIDTH>::VALUE_TYPE;

  DEVICE_FORCEINLINE VALUE_TYPE get() const {
    field::base_field coeffs[WIDTH];
    coeffs[0] = this->internal.get();
#pragma unroll
    for (unsigned i = 1; i < WIDTH; i++)
      coeffs[i] = this->internal.get_at_col(i);
    return VALUE_TYPE(coeffs);
  }

  DEVICE_FORCEINLINE VALUE_TYPE get_at_row(const unsigned row) const {
    field::base_field coeffs[WIDTH];
    coeffs[0] = this->internal.get_at_row(row);
#pragma unroll
    for (unsigned i = 1; i < WIDTH; i++)
      coeffs[1] = this->internal.get(row, i);
    return VALUE_TYPE(coeffs);
  }

  DEVICE_FORCEINLINE VALUE_TYPE get_at_col(const unsigned col) const {
    field::base_field coeffs[WIDTH];
    const unsigned bf_col = WIDTH * col;
    coeffs[0] = this->internal.get_at_col(bf_col);
#pragma unroll
    for (unsigned i = 1; i < WIDTH; i++)
      coeffs[i] = this->internal.get_at_col(bf_col + i);
    return VALUE_TYPE(coeffs);
  }
};

template <memory::st_modifier ST_MODIFIER, unsigned WIDTH>
struct vectorized_matrix_setter : vectorized_matrix_accessor<memory::matrix_setter<field::base_field, ST_MODIFIER>, WIDTH> {
  using VALUE_TYPE = width_to_value_type<WIDTH>::VALUE_TYPE;

  DEVICE_FORCEINLINE void set(const VALUE_TYPE &value) const {
    this->internal.set(value.base_coefficient_from_flat_idx(0));
#pragma unroll
    for (unsigned i = 1; i < WIDTH; i++)
      this->internal.set_at_col(i, value.base_coefficient_from_flat_idx(i));
  }

  DEVICE_FORCEINLINE void set_at_row(const unsigned row, const VALUE_TYPE &value) const {
    this->internal.set_at_row(row, value.base_coefficient_from_flat_idx(0));
#pragma unroll
    for (unsigned i = 1; i < WIDTH; i++)
      this->internal.set(row, i, value.base_coefficient_from_flat_idx(i));
  }

  DEVICE_FORCEINLINE void set_at_col(const unsigned col, const VALUE_TYPE &value) const {
    const unsigned bf_col = WIDTH * col;
    this->internal.set_at_col(bf_col, value.base_coefficient_from_flat_idx(0));
#pragma unroll
    for (unsigned i = 1; i < WIDTH; i++)
      this->internal.set_at_col(bf_col + i, value.base_coefficient_from_flat_idx(i));
  }
};

// screw it, no fancier layers of deduplication
template <memory::ld_modifier LD_MODIFIER, memory::st_modifier ST_MODIFIER, unsigned WIDTH>
struct vectorized_matrix_getter_setter : vectorized_matrix_accessor<memory::matrix_getter_setter<field::base_field, LD_MODIFIER, ST_MODIFIER>, WIDTH> {
  using VALUE_TYPE = width_to_value_type<WIDTH>::VALUE_TYPE;

  DEVICE_FORCEINLINE VALUE_TYPE get() const {
    field::base_field coeffs[WIDTH];
    coeffs[0] = this->internal.get();
#pragma unroll
    for (unsigned i = 1; i < WIDTH; i++)
      coeffs[i] = this->internal.get_at_col(i);
    return VALUE_TYPE(coeffs);
  }

  DEVICE_FORCEINLINE void set(const VALUE_TYPE &value) const {
    this->internal.set(value.base_coefficient_from_flat_idx(0));
#pragma unroll
    for (unsigned i = 1; i < WIDTH; i++)
      this->internal.set_at_col(i, value.base_coefficient_from_flat_idx(i));
  }
};

template <memory::ld_modifier LD_MODIFIER> using vectorized_e4_matrix_getter = vectorized_matrix_getter<LD_MODIFIER, 4>;
template <memory::st_modifier ST_MODIFIER> using vectorized_e4_matrix_setter = vectorized_matrix_setter<ST_MODIFIER, 4>;
template <memory::ld_modifier LD_MODIFIER, memory::st_modifier ST_MODIFIER>
using vectorized_e4_matrix_getter_setter = vectorized_matrix_getter_setter<LD_MODIFIER, ST_MODIFIER, 4>;

template <memory::ld_modifier LD_MODIFIER> struct vectorized_e2_matrix_getter : vectorized_matrix_getter<LD_MODIFIER, 2> {
  DEVICE_FORCEINLINE void get_two_adjacent(const unsigned row, field::ext2_field &val0, field::ext2_field &val1) const {
    const field::base_field *ptr = this->internal.ptr + row;
    const auto c0s = memory::load<uint2, LD_MODIFIER>(reinterpret_cast<const uint2 *>(ptr));
    const auto c1s = memory::load<uint2, LD_MODIFIER>(reinterpret_cast<const uint2 *>(ptr + this->internal.stride));
    val0 = field::ext2_field{field::base_field{c0s.x}, field::base_field{c1s.x}};
    val1 = field::ext2_field{field::base_field{c0s.y}, field::base_field{c1s.y}};
  }
};

template <memory::st_modifier ST_MODIFIER> struct vectorized_e2_matrix_setter : vectorized_matrix_setter<ST_MODIFIER, 2> {
  DEVICE_FORCEINLINE void set_two_adjacent(const unsigned row, const field::ext2_field val0, const field::ext2_field val1) const {
    field::base_field *ptr = this->internal.ptr + row;
    const uint2 c0s{val0[0].limb, val1[0].limb};
    const uint2 c1s{val0[1].limb, val1[1].limb};
    memory::store<uint2, ST_MODIFIER>(reinterpret_cast<uint2 *>(ptr), c0s);
    memory::store<uint2, ST_MODIFIER>(reinterpret_cast<uint2 *>(ptr + this->internal.stride), c1s);
  }
};
} // namespace airbender::vectorized