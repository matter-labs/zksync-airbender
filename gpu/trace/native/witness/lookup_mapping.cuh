#pragma once

#include "common.cuh"

namespace airbender::trace::witness::multiplicities {

#define MAX_LOOKUP_EXPRESSIONS_RELATIONS_COUNT 128

template <typename F, unsigned N> struct LookupExpressions {
  u32 relations_count;
  LinearRelation<F> relations[N];
};

using LookupExpressionsBf = LookupExpressions<bf, MAX_LOOKUP_EXPRESSIONS_RELATIONS_COUNT>;

template <typename Memory, typename Witness, typename Scratch, typename Mapping, typename F, unsigned N>
DEVICE_FORCEINLINE void process_lookup_expressions(const Memory &memory, const Witness &witness, const Scratch &scratch,
                                                   const LookupExpressions<F, N> expressions, Mapping &mapping) {
#pragma unroll
  for (int i = 0; i < N; i++) {
    if (i == expressions.relations_count)
      break;
    const auto relation = expressions.relations[i];
    const F field_value = evaluate_linear_relation(memory, witness, scratch, relation);
    const u32 value = witness_field<F>::to_bounded(field_value);
    mapping.set(value);
    mapping.add_col(1);
  }
}

} // namespace airbender::trace::witness::multiplicities
