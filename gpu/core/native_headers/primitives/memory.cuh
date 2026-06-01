#pragma once

#include "../common.cuh"
#include "ptx.cuh"

namespace airbender::primitives::memory {

using namespace std;
namespace ptx = ::airbender::primitives::ptx;

using ptx::u32x8;

enum class ld_modifier { none, g, cg, ca, cs, lu, cv };

template <typename T, ld_modifier MODIFIER> static DEVICE_FORCEINLINE T ld_single(const T *ptr) {
  if constexpr (MODIFIER == ld_modifier::none) {
    return *ptr;
  } else {
    auto ld = [&](auto *typed_ptr) {
      using P = std::remove_pointer_t<std::remove_const_t<decltype(typed_ptr)>>;
      if constexpr (MODIFIER == ld_modifier::g)
        return ptx::ld_g(reinterpret_cast<const P *>(ptr));
      else if constexpr (MODIFIER == ld_modifier::cg)
        return ptx::ld_cg(reinterpret_cast<const P *>(ptr));
      else if constexpr (MODIFIER == ld_modifier::ca)
        return ptx::ld_ca(reinterpret_cast<const P *>(ptr));
      else if constexpr (MODIFIER == ld_modifier::cs)
        return ptx::ld_cs(reinterpret_cast<const P *>(ptr));
      else if constexpr (MODIFIER == ld_modifier::lu)
        return ptx::ld_lu(reinterpret_cast<const P *>(ptr));
      else if constexpr (MODIFIER == ld_modifier::cv)
        return ptx::ld_cv(reinterpret_cast<const P *>(ptr));
    };
    if constexpr (sizeof(T) == 4) {
      const u32 r = ld(static_cast<const u32 *>(nullptr));
      return *reinterpret_cast<const T *>(&r);
    } else if constexpr (sizeof(T) == 8) {
      const uint2 r = ld(static_cast<const uint2 *>(nullptr));
      return *reinterpret_cast<const T *>(&r);
    } else if constexpr (sizeof(T) == 16) {
      const uint4 r = ld(static_cast<const uint4 *>(nullptr));
      return *reinterpret_cast<const T *>(&r);
    } else if constexpr (sizeof(T) == 32) {
      const u32x8 r = ld(static_cast<const u32x8 *>(nullptr));
      return *reinterpret_cast<const T *>(&r);
    } else {
      static_assert(sizeof(T) == 4 || sizeof(T) == 8 || sizeof(T) == 16 || sizeof(T) == 32, "ld_single only handles 4/8/16/32-byte T");
    }
  }
}

enum class st_modifier { none, wb, cg, cs, wt };

template <typename T, st_modifier MODIFIER> static DEVICE_FORCEINLINE void st_single(T *ptr, T value) {
  if constexpr (MODIFIER == st_modifier::none) {
    *ptr = value;
  } else {
    auto st = [&](auto *typed_ptr, auto v) {
      using P = std::remove_pointer_t<decltype(typed_ptr)>;
      if constexpr (MODIFIER == st_modifier::wb)
        ptx::st_wb(reinterpret_cast<P *>(ptr), v);
      else if constexpr (MODIFIER == st_modifier::cg)
        ptx::st_cg(reinterpret_cast<P *>(ptr), v);
      else if constexpr (MODIFIER == st_modifier::cs)
        ptx::st_cs(reinterpret_cast<P *>(ptr), v);
      else if constexpr (MODIFIER == st_modifier::wt)
        ptx::st_wt(reinterpret_cast<P *>(ptr), v);
    };
    if constexpr (sizeof(T) == 4) {
      st(static_cast<u32 *>(nullptr), *reinterpret_cast<const u32 *>(&value));
    } else if constexpr (sizeof(T) == 8) {
      st(static_cast<uint2 *>(nullptr), *reinterpret_cast<const uint2 *>(&value));
    } else if constexpr (sizeof(T) == 16) {
      st(static_cast<uint4 *>(nullptr), *reinterpret_cast<const uint4 *>(&value));
    } else if constexpr (sizeof(T) == 32) {
      st(static_cast<u32x8 *>(nullptr), *reinterpret_cast<const u32x8 *>(&value));
    } else {
      static_assert(sizeof(T) == 4 || sizeof(T) == 8 || sizeof(T) == 16 || sizeof(T) == 32, "st_single only handles 4/8/16/32-byte T");
    }
  }
}

template <typename T> DEVICE_FORCEINLINE void swap(T &a, T &b) noexcept {
  T temp = a;
  a = b;
  b = temp;
}

template <unsigned STRIDE> DEVICE_FORCEINLINE unsigned swap_index(const unsigned index) {
  const unsigned i1 = index % STRIDE;
  const unsigned i2 = index / STRIDE;
  const unsigned i3 = i2 * STRIDE * 2;
  return i3 + i1;
}

template <typename T> DEVICE_FORCEINLINE T shfl_xor(unsigned mask, T var, int laneMask, int width = warpSize) {
  return __shfl_xor_sync(mask, var, laneMask, width);
}

template <> DEVICE_FORCEINLINE uint2 shfl_xor(const unsigned mask, const uint2 var, const int laneMask, const int width) {
  uint2 result{};
  result.x = __shfl_xor_sync(mask, var.x, laneMask, width);
  result.y = __shfl_xor_sync(mask, var.y, laneMask, width);
  return result;
}

template <> DEVICE_FORCEINLINE uint4 shfl_xor(const unsigned mask, const uint4 var, const int laneMask, const int width) {
  uint4 result{};
  result.x = __shfl_xor_sync(mask, var.x, laneMask, width);
  result.y = __shfl_xor_sync(mask, var.y, laneMask, width);
  result.z = __shfl_xor_sync(mask, var.z, laneMask, width);
  result.w = __shfl_xor_sync(mask, var.w, laneMask, width);
  return result;
}

template <typename T, unsigned STRIDE_ROW, unsigned COUNT_ROW, unsigned STRIDE_COL = STRIDE_ROW, unsigned COUNT_COL = COUNT_ROW>
DEVICE_FORCEINLINE void transpose_tile(unsigned mask, T *u, const unsigned lane_id) {
  const bool swap_rows = !(lane_id & STRIDE_ROW);
  if (swap_rows) {
#pragma unroll
    for (unsigned i = 0; i < COUNT_ROW; i++) {
      const unsigned index = swap_index<STRIDE_ROW>(i);
      swap(u[index], u[index + STRIDE_ROW]);
    }
  }
#pragma unroll
  for (unsigned i = 0; i < COUNT_COL; i++) {
    const unsigned index = swap_index<STRIDE_COL>(i);
    u[index] = shfl_xor(mask, u[index], STRIDE_COL);
  }
  if (swap_rows) {
#pragma unroll
    for (unsigned i = 0; i < COUNT_ROW; i++) {
      const unsigned index = swap_index<STRIDE_ROW>(i);
      swap(u[index], u[index + STRIDE_ROW]);
    }
  }
}

template <class T, typename U, ld_modifier MODIFIER, unsigned STRIDE> static constexpr DEVICE_FORCEINLINE T ld(const T *address, const unsigned offset) {
  static_assert(alignof(T) % alignof(U) == 0);
  static_assert(sizeof(T) % sizeof(U) == 0);
  constexpr size_t count = sizeof(T) / sizeof(U);
  T result;
  auto pa = reinterpret_cast<const U *>(address) + offset;
  auto pr = reinterpret_cast<U *>(&result);
#ifdef __CUDA_ARCH__
#pragma unroll
#endif
  for (unsigned i = 0; i < count; i++) {
    const auto pai = pa + i * STRIDE;
    const auto pri = pr + i;
    *pri = ld_single<U, MODIFIER>(pai);
  }
  return result;
}

template <class T, typename U, st_modifier MODIFIER, unsigned STRIDE>
static constexpr DEVICE_FORCEINLINE void st(T *address, const T &value, const unsigned offset) {
  static_assert(alignof(T) % alignof(U) == 0);
  static_assert(sizeof(T) % sizeof(U) == 0);
  constexpr size_t count = sizeof(T) / sizeof(U);
  auto pa = reinterpret_cast<U *>(address) + offset;
  auto pv = reinterpret_cast<const U *>(&value);
#ifdef __CUDA_ARCH__
#pragma unroll
#endif
  for (unsigned i = 0; i < count; i++) {
    auto pai = pa + i * STRIDE;
    auto pvi = pv + i;
    st_single<U, MODIFIER>(pai, *pvi);
  }
}

template <typename U, unsigned STRIDE_COL> DEVICE_FORCEINLINE void transpose_tile(const unsigned stride_row, U *tile, const unsigned lane_id) {
  switch (stride_row) {
  case 0:
    transpose_tile<U, 1, STRIDE_COL>(UINT32_MAX, tile, lane_id);
    break;
  case 1:
    transpose_tile<U, 2, STRIDE_COL>(UINT32_MAX, tile, lane_id);
    break;
  case 2:
    transpose_tile<U, 4, STRIDE_COL>(UINT32_MAX, tile, lane_id);
    break;
  case 3:
    transpose_tile<U, 8, STRIDE_COL>(UINT32_MAX, tile, lane_id);
    break;
  case 4:
    transpose_tile<U, 16, STRIDE_COL>(UINT32_MAX, tile, lane_id);
    break;
  default:
    break;
  }
}

template <class T, typename U, unsigned LOG_WARP_SIZE, ld_modifier MODIFIER, bool CHECK_INACTIVE>
DEVICE_FORCEINLINE T ld_warp(const T *address, const unsigned offset, const unsigned lane_id) {
  static_assert(alignof(T) % alignof(U) == 0);
  static_assert(sizeof(T) % (sizeof(U) << LOG_WARP_SIZE) == 0);
  constexpr size_t count = sizeof(T) / (sizeof(U) << LOG_WARP_SIZE);
  constexpr unsigned threads_count = 1u << LOG_WARP_SIZE;
  const unsigned l = lane_id & (threads_count - 1);
  T result;
  auto pr = reinterpret_cast<U *>(&result);
#pragma unroll
  for (int i = 0; i < threads_count; i++) {
    const unsigned o = __shfl_sync(UINT32_MAX, offset, i, threads_count);
    if (CHECK_INACTIVE && o == UINT32_MAX)
      continue;
    const U *ap = reinterpret_cast<const U *>(address + o) + l;
#pragma unroll
    for (unsigned j = 0; j < count; j++) {
      const unsigned shift = j << LOG_WARP_SIZE;
      pr[i + shift] = ld_single<U, MODIFIER>(ap + shift);
    }
  }
#pragma unroll
  for (unsigned i = 0; i < count; i++) {
    const unsigned shift = i << LOG_WARP_SIZE;
    U *tile = pr + shift;
    constexpr unsigned stride = threads_count >> 1;
#pragma unroll
    for (unsigned j = 0; j < LOG_WARP_SIZE; j++)
      transpose_tile<U, stride>(j, tile, l);
  }
  return result;
}

template <class T, typename U, unsigned LOG_WARP_SIZE, st_modifier MODIFIER, bool CHECK_INACTIVE>
DEVICE_FORCEINLINE void st_warp(T *address, const unsigned offset, const T &value, const unsigned lane_id) {
  static_assert(alignof(T) % alignof(U) == 0);
  static_assert(sizeof(T) % (sizeof(U) << LOG_WARP_SIZE) == 0);
  constexpr size_t count = sizeof(T) / (sizeof(U) << LOG_WARP_SIZE);
  constexpr unsigned threads_count = 1u << LOG_WARP_SIZE;
  const unsigned l = lane_id & (threads_count - 1);
  T value_copy = value;
  auto pv = reinterpret_cast<U *>(&value_copy);
#pragma unroll
  for (unsigned i = 0; i < count; i++) {
    const unsigned shift = i << LOG_WARP_SIZE;
    U *tile = pv + shift;
    constexpr unsigned stride = threads_count >> 1;
#pragma unroll
    for (int j = LOG_WARP_SIZE - 1; j >= 0; --j)
      transpose_tile<U, stride>(j, tile, l);
  }
#pragma unroll
  for (int i = 0; i < threads_count; i++) {
    const unsigned o = __shfl_sync(UINT32_MAX, offset, i, threads_count);
    if (CHECK_INACTIVE && o == UINT32_MAX)
      continue;
    U *ap = reinterpret_cast<U *>(address + o) + l;
#pragma unroll
    for (unsigned j = 0; j < count; j++) {
      const unsigned shift = j << LOG_WARP_SIZE;
      st_single<U, MODIFIER>(ap + shift, pv[i + shift]);
    }
  }
}

template <class T> struct load_unit {
  using type = std::conditional_t<sizeof(T) % 32 == 0 && alignof(T) % 32 == 0, u32x8,
                                  std::conditional_t<sizeof(T) % 16 == 0, uint4, std::conditional_t<sizeof(T) % 8 == 0, uint2, unsigned>>>;
};
template <class T, unsigned LOG_WARP_SIZE> struct load_unit_warp {
  static constexpr size_t WARP = 1u << LOG_WARP_SIZE;
  using type = std::conditional_t<sizeof(T) % (32 * WARP) == 0 && alignof(T) % 32 == 0, u32x8,
                                  std::conditional_t<sizeof(T) % (16 * WARP) == 0, uint4, std::conditional_t<sizeof(T) % (8 * WARP) == 0, uint2, unsigned>>>;
};

template <class T, ld_modifier MODIFIER = ld_modifier::none, unsigned STRIDE = 1>
static constexpr DEVICE_FORCEINLINE T load(const T *address, const unsigned offset = 0) {
  return ld<T, typename load_unit<T>::type, MODIFIER, STRIDE>(address, offset);
}

template <class T, unsigned LOG_WARP_SIZE, ld_modifier MODIFIER = ld_modifier::none, bool CHECK_INACTIVE = true>
static constexpr DEVICE_FORCEINLINE T load_warp(const T *address, const unsigned offset, const unsigned lane_id) {
  return ld_warp<T, typename load_unit_warp<T, LOG_WARP_SIZE>::type, LOG_WARP_SIZE, MODIFIER, CHECK_INACTIVE>(address, offset, lane_id);
}

template <class T, st_modifier MODIFIER = st_modifier::none, unsigned STRIDE = 1>
static constexpr DEVICE_FORCEINLINE void store(T *address, const T &value, const unsigned offset = 0) {
  st<T, typename load_unit<T>::type, MODIFIER, STRIDE>(address, value, offset);
}

template <class T, unsigned LOG_WARP_SIZE, st_modifier MODIFIER = st_modifier::none, bool CHECK_INACTIVE = true>
static constexpr DEVICE_FORCEINLINE void store_warp(T *address, const unsigned offset, const T &value, const unsigned lane_id) {
  st_warp<T, typename load_unit_warp<T, LOG_WARP_SIZE>::type, LOG_WARP_SIZE, MODIFIER, CHECK_INACTIVE>(address, offset, value, lane_id);
}

template <class T> static constexpr DEVICE_FORCEINLINE T load_g(const T *address) { return load<T, ld_modifier::g>(address); }

template <class T> static constexpr DEVICE_FORCEINLINE T load_cg(const T *address) { return load<T, ld_modifier::cg>(address); }

template <class T> static constexpr DEVICE_FORCEINLINE T load_ca(const T *address) { return load<T, ld_modifier::ca>(address); }

template <class T> static constexpr DEVICE_FORCEINLINE T load_cs(const T *address) { return load<T, ld_modifier::cs>(address); }

template <class T> static constexpr DEVICE_FORCEINLINE T load_lu(const T *address) { return load<T, ld_modifier::lu>(address); }

template <class T> static constexpr DEVICE_FORCEINLINE T load_cv(const T *address) { return load<T, ld_modifier::cv>(address); }

template <class T> static constexpr DEVICE_FORCEINLINE void store_wb(T *address, const T &value) { store<T, st_modifier::wb>(address, value); }

template <class T> static constexpr DEVICE_FORCEINLINE void store_cg(T *address, const T &value) { store<T, st_modifier::cg>(address, value); }

template <class T> static constexpr DEVICE_FORCEINLINE void store_cs(T *address, const T &value) { store<T, st_modifier::cs>(address, value); }

template <class T> static constexpr DEVICE_FORCEINLINE void store_wt(T *address, const T &value) { store<T, st_modifier::wt>(address, value); }

template <typename T, typename U = T> struct vector_accessor {
  using value_type = T;

  T *__restrict__ ptr;

  DEVICE_FORCEINLINE U *self() { return reinterpret_cast<U *>(this); }

  DEVICE_FORCEINLINE const U *self() const { return reinterpret_cast<const U *>(this); }

  DEVICE_FORCEINLINE U copy() const { return *self(); }

  DEVICE_FORCEINLINE U operator+(const unsigned offset) const {
    U result = *self();
    result.ptr += offset;
    return result;
  }

  DEVICE_FORCEINLINE U operator-(const unsigned offset) const {
    U result = *self();
    result.ptr -= offset;
    return result;
  }

  DEVICE_FORCEINLINE U operator+=(const unsigned offset) {
    U *s = self();
    s->ptr += offset;
    return *s;
  }

  DEVICE_FORCEINLINE U operator-=(const unsigned offset) {
    U *s = self();
    s->ptr -= offset;
    return *s;
  }

  DEVICE_FORCEINLINE U operator++() {
    U *s = self();
    ++s->ptr;
    return *s;
  }

  DEVICE_FORCEINLINE U operator--() {
    U *s = self();
    --s->ptr;
    return *s;
  }

  DEVICE_FORCEINLINE U operator++(int) {
    U pre_inc_copy = copy();
    ++self()->ptr;
    return pre_inc_copy;
  }

  DEVICE_FORCEINLINE U operator--(int) {
    U pre_dec_copy = copy();
    --self()->ptr;
    return pre_dec_copy;
  }
};

template <typename T, ld_modifier LD_MODIFIER = ld_modifier::none> struct vector_getter : vector_accessor<T, vector_getter<T, LD_MODIFIER>> {
  DEVICE_FORCEINLINE T get() const { return load<T, LD_MODIFIER>(this->ptr); }
  DEVICE_FORCEINLINE T get(const unsigned i) const { return this->operator+(i).get(); }
};

template <typename T, st_modifier ST_MODIFIER = st_modifier::none> struct vector_setter : vector_accessor<T, vector_setter<T, ST_MODIFIER>> {
  DEVICE_FORCEINLINE void set(const T &value) const { store<T, ST_MODIFIER>(this->ptr, value); }
  DEVICE_FORCEINLINE void set(const unsigned i, const T &value) const { this->operator+(i).set(value); }
};

template <typename T, ld_modifier LD_MODIFIER = ld_modifier::none, st_modifier ST_MODIFIER = st_modifier::none>
struct vector_getter_setter : vector_accessor<T, vector_getter_setter<T, LD_MODIFIER, ST_MODIFIER>> {
  DEVICE_FORCEINLINE const vector_getter<T, LD_MODIFIER> *as_getter() const { return reinterpret_cast<const vector_getter<T, LD_MODIFIER> *>(this); }

  DEVICE_FORCEINLINE const vector_setter<T, ST_MODIFIER> *as_setter() const { return reinterpret_cast<const vector_setter<T, ST_MODIFIER> *>(this); }

  DEVICE_FORCEINLINE T get() const { return as_getter()->get(); }
  DEVICE_FORCEINLINE T get(const unsigned i) const { return as_getter()->get(i); }
  DEVICE_FORCEINLINE void set(const T &value) const { as_setter()->set(value); }
  DEVICE_FORCEINLINE void set(const unsigned i, const T &value) const { as_setter()->set(i, value); }
};

template <typename T, typename U = T> struct matrix_accessor : vector_accessor<T, U> {
  const size_t stride;

  explicit matrix_accessor(const size_t stride) : stride(stride) {}

  DEVICE_FORCEINLINE U inc_row() { return this->operator++(); }
  DEVICE_FORCEINLINE U inc_col() { return this->operator+=(this->stride); }
  DEVICE_FORCEINLINE U dec_row() { return this->operator--(); }
  DEVICE_FORCEINLINE U dec_col() { return this->operator-=(this->stride); }
  DEVICE_FORCEINLINE U add_row(const unsigned offset) { return this->operator+=(offset); }
  DEVICE_FORCEINLINE U add_col(const unsigned offset) { return this->operator+=(offset * this->stride); }
  DEVICE_FORCEINLINE U sub_row(const unsigned offset) { return this->operator-=(offset); }
  DEVICE_FORCEINLINE U sub_col(const unsigned offset) { return this->operator-=(offset * this->stride); }
};

template <typename T, ld_modifier LD_MODIFIER = ld_modifier::none> struct matrix_getter : matrix_accessor<T, matrix_getter<T, LD_MODIFIER>> {
  explicit matrix_getter(const size_t stride) : matrix_accessor<T, matrix_getter>(stride) {}

  DEVICE_FORCEINLINE T get() const { return load<T, LD_MODIFIER>(this->ptr); }
  DEVICE_FORCEINLINE T get_at_row(const unsigned row) const { return this->copy().add_row(row).get(); }
  DEVICE_FORCEINLINE T get_at_col(const unsigned col) const { return this->copy().add_col(col).get(); }
  DEVICE_FORCEINLINE T get(const unsigned row, const unsigned col) const { return this->copy().add_row(row).add_col(col).get(); }
};

template <typename T, st_modifier ST_MODIFIER = st_modifier::none> struct matrix_setter : matrix_accessor<T, matrix_setter<T, ST_MODIFIER>> {
  explicit matrix_setter(const size_t stride) : matrix_accessor<T, matrix_setter>(stride) {}

  DEVICE_FORCEINLINE void set(const T &value) const { store<T, ST_MODIFIER>(this->ptr, value); }
  DEVICE_FORCEINLINE void set_at_row(const unsigned row, const T &value) const { this->copy().add_row(row).set(value); }

  DEVICE_FORCEINLINE void set_at_col(const unsigned col, const T &value) const { this->copy().add_col(col).set(value); }

  DEVICE_FORCEINLINE void set(const unsigned row, const unsigned col, const T &value) const { this->copy().add_row(row).add_col(col).set(value); }
};

template <typename T, ld_modifier LD_MODIFIER = ld_modifier::none, st_modifier ST_MODIFIER = st_modifier::none>
struct matrix_getter_setter : matrix_accessor<T, matrix_getter_setter<T, LD_MODIFIER, ST_MODIFIER>> {
  explicit matrix_getter_setter(const size_t stride) : matrix_accessor<T, matrix_getter_setter>(stride) {}

  DEVICE_FORCEINLINE const matrix_getter<T, LD_MODIFIER> *as_getter() const { return reinterpret_cast<const matrix_getter<T, LD_MODIFIER> *>(this); }

  DEVICE_FORCEINLINE const matrix_setter<T, ST_MODIFIER> *as_setter() const { return reinterpret_cast<const matrix_setter<T, ST_MODIFIER> *>(this); }

  DEVICE_FORCEINLINE T get() const { return as_getter()->get(); }
  DEVICE_FORCEINLINE T get_at_row(const unsigned row) const { return as_getter()->get_at_row(row); }
  DEVICE_FORCEINLINE T get_at_col(const unsigned col) const { return as_getter()->get_at_col(col); }
  DEVICE_FORCEINLINE T get(const unsigned row, const unsigned col) const { return as_getter()->get(row, col); }
  DEVICE_FORCEINLINE void set(const T &value) const { as_setter()->set(value); }
  DEVICE_FORCEINLINE void set_at_row(const unsigned row, const T &value) const { as_setter()->set_at_row(row, value); }

  DEVICE_FORCEINLINE void set_at_col(const unsigned col, const T &value) const { as_setter()->set_at_col(col, value); }

  DEVICE_FORCEINLINE void set(const unsigned row, const unsigned col, const T &value) const { as_setter()->set(row, col, value); }
};

template <typename T> struct wrapping_vector_accessor {
  using value_type = typename T::value_type;
  T internal;
  unsigned count;
};

template <typename T> struct wrapping_vector_getter : wrapping_vector_accessor<T> {
  DEVICE_FORCEINLINE typename T::value_type get() const { return this->internal.get(); }
  DEVICE_FORCEINLINE typename T::value_type get(const unsigned i) const { return this->internal.get(i % this->count); }
};

template <typename T> struct wrapping_vector_setter : wrapping_vector_accessor<T> {
  DEVICE_FORCEINLINE void set(const typename T::value_type &value) const { this->internal.set(value); }
  DEVICE_FORCEINLINE void set(const unsigned i, const typename T::value_type &value) const { this->internal.set(i % this->count, value); }
};

template <typename T> struct wrapping_vector_getter_setter : wrapping_vector_accessor<T> {
  DEVICE_FORCEINLINE const wrapping_vector_getter<T> *as_getter() const { return reinterpret_cast<const wrapping_vector_getter<T> *>(this); }

  DEVICE_FORCEINLINE const wrapping_vector_setter<T> *as_setter() const { return reinterpret_cast<const wrapping_vector_setter<T> *>(this); }

  DEVICE_FORCEINLINE typename T::value_type get() const { return as_getter()->get(); }
  DEVICE_FORCEINLINE typename T::value_type get(const unsigned i) const { return as_getter()->get(i); }
  DEVICE_FORCEINLINE void set(const typename T::value_type &value) const { as_setter()->set(value); }
  DEVICE_FORCEINLINE void set(const unsigned i, const typename T::value_type &value) const { as_setter()->set(i, value); }
};

template <typename T> struct wrapping_matrix_accessor {
  using value_type = typename T::value_type;
  T internal;
  unsigned rows;
  unsigned cols;
};

template <typename T> struct wrapping_matrix_getter : wrapping_matrix_accessor<T> {
  DEVICE_FORCEINLINE typename T::value_type get() const { return this->internal.get(); }
  DEVICE_FORCEINLINE typename T::value_type get_at_row(const unsigned row) const { return this->internal.get_at_row(row % this->rows); }

  DEVICE_FORCEINLINE typename T::value_type get_at_col(const unsigned col) const { return this->internal.get_at_col(col % this->cols); }

  DEVICE_FORCEINLINE typename T::value_type get(const unsigned row, const unsigned col) const { return this->internal.get(row % this->rows, col % this->cols); }
};

template <typename T> struct wrapping_matrix_setter : wrapping_matrix_accessor<T> {
  DEVICE_FORCEINLINE void set(const typename T::value_type &value) const { this->internal.set(value); }
  DEVICE_FORCEINLINE void set_at_row(const unsigned row, const typename T::value_type &value) const { this->internal.set_at_row(row % this->rows, value); }

  DEVICE_FORCEINLINE void set_at_col(const unsigned col, const typename T::value_type &value) const { this->internal.set_at_col(col % this->cols, value); }

  DEVICE_FORCEINLINE void set(const unsigned row, const unsigned col, const typename T::value_type &value) const {
    this->internal.set(row % this->rows, col % this->cols, value);
  }
};

template <typename T> struct wrapping_matrix_getter_setter : wrapping_matrix_accessor<T> {
  DEVICE_FORCEINLINE typename T::value_type get() const { return this->internal.get(); }
  DEVICE_FORCEINLINE typename T::value_type get_at_row(const unsigned row) const { return this->internal.get_at_row(row % this->rows); }

  DEVICE_FORCEINLINE typename T::value_type get_at_col(const unsigned col) const { return this->internal.get_at_col(col % this->cols); }

  DEVICE_FORCEINLINE typename T::value_type get(const unsigned row, const unsigned col) const { return this->internal.get(row % this->rows, col % this->cols); }

  DEVICE_FORCEINLINE void set(const typename T::value_type &value) const { this->internal.set(value); }
  DEVICE_FORCEINLINE void set_at_row(const unsigned row, const typename T::value_type &value) const { this->internal.set_at_row(row % this->rows, value); }

  DEVICE_FORCEINLINE void set_at_col(const unsigned col, const typename T::value_type &value) const { this->internal.set_at_col(col % this->cols, value); }

  DEVICE_FORCEINLINE void set(const unsigned row, const unsigned col, const typename T::value_type &value) const {
    this->internal.set(row % this->rows, col % this->cols, value);
  }
};
} // namespace airbender::primitives::memory
