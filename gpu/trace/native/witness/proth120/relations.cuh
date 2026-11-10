#pragma once

#include "../lookup_mapping.cuh"
#include "field.cuh"
#include <cstddef>

namespace airbender::trace::witness::multiplicities {
template <unsigned N> struct LookupExpressions<pr, N> {
  static constexpr u32 relations_count = N;
  LinearRelation<pr> relations[N];
};
} // namespace airbender::trace::witness::multiplicities

namespace airbender::trace::witness::proth120 {

using Proth120LinearTerm = LinearTerm<pr>;
using Proth120LinearRelation = LinearRelation<pr>;
template <unsigned N> using Proth120LookupExpressions = ::airbender::trace::witness::multiplicities::LookupExpressions<pr, N>;
static_assert(sizeof(Address) == 12 && alignof(Address) == 4);
static_assert(offsetof(Address, tag) == 0 && offsetof(Address, offset) == 4 && offsetof(Address, layer) == 8);
static_assert(sizeof(Proth120LinearTerm) == 32 && alignof(Proth120LinearTerm) == 16);
static_assert(offsetof(Proth120LinearTerm, coefficient) == 0 && offsetof(Proth120LinearTerm, address) == 16 && offsetof(Proth120LinearTerm, padding) == 28);
static_assert(sizeof(Proth120LinearRelation) == 160 && alignof(Proth120LinearRelation) == 16);
static_assert(offsetof(Proth120LinearRelation, constant) == 0 && offsetof(Proth120LinearRelation, linear_terms) == 16);
static_assert(offsetof(Proth120LinearRelation, linear_terms_count) == 144 && offsetof(Proth120LinearRelation, padding) == 148);
static_assert(sizeof(Proth120LookupExpressions<15>) == 2400 && alignof(Proth120LookupExpressions<15>) == 16);
static_assert(sizeof(Proth120LookupExpressions<8>) == 1280 && alignof(Proth120LookupExpressions<8>) == 16);

} // namespace airbender::trace::witness::proth120
