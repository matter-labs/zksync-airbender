#pragma once

#include "primitives/memory.cuh"

using namespace ::airbender::primitives::memory;

namespace airbender::trace::witness {

// A fused row intentionally reads values through the same object that produced
// them. Keep the pointer non-restrict: fixed generation, generated continuation,
// and lookup mapping are consecutive phases over one materialized row.
template <typename T, ld_modifier LD, st_modifier ST> struct FusedTraceAccessor {
  T *ptr;
  unsigned stride;

  DEVICE_FORCEINLINE FusedTraceAccessor copy() const { return *this; }

  DEVICE_FORCEINLINE FusedTraceAccessor add_row(const unsigned row) {
    ptr += row;
    return *this;
  }

  DEVICE_FORCEINLINE FusedTraceAccessor add_col(const unsigned col) {
    ptr += col * stride;
    return *this;
  }

  DEVICE_FORCEINLINE T get() const { return load<T, LD>(ptr); }
  DEVICE_FORCEINLINE T get_at_row(const unsigned row) const { return copy().add_row(row).get(); }
  DEVICE_FORCEINLINE T get_at_col(const unsigned col) const { return copy().add_col(col).get(); }
  DEVICE_FORCEINLINE T get(const unsigned row, const unsigned col) const { return copy().add_row(row).add_col(col).get(); }

  DEVICE_FORCEINLINE void set(const T &value) const { store<T, ST>(ptr, value); }
  DEVICE_FORCEINLINE void set_at_row(const unsigned row, const T &value) const { copy().add_row(row).set(value); }
  DEVICE_FORCEINLINE void set_at_col(const unsigned col, const T &value) const { copy().add_col(col).set(value); }
  DEVICE_FORCEINLINE void set(const unsigned row, const unsigned col, const T &value) const { copy().add_row(row).add_col(col).set(value); }
};

template <typename T> using FusedValueTraceAccessor = FusedTraceAccessor<T, ld_modifier::cg, st_modifier::cg>;
template <typename T> using FusedMappingTraceAccessor = FusedTraceAccessor<T, ld_modifier::cg, st_modifier::cg>;

} // namespace airbender::trace::witness
