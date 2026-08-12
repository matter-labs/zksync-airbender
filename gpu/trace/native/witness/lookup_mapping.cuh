#pragma once

#include "common.cuh"

namespace airbender::trace::witness::multiplicities {

#define MAX_LOOKUP_EXPRESSIONS_RELATIONS_COUNT 128

struct LookupExpressions {
  u32 relations_count;
  NoFieldLinearRelation relations[MAX_LOOKUP_EXPRESSIONS_RELATIONS_COUNT];
};

template <typename Memory, typename Witness, typename Scratch, typename Mapping>
DEVICE_FORCEINLINE void process_lookup_expressions(const Memory &memory, const Witness &witness, const Scratch &scratch, const LookupExpressions expressions,
                                                   Mapping &mapping) {
#pragma unroll
  for (int i = 0; i < MAX_LOOKUP_EXPRESSIONS_RELATIONS_COUNT; i++) {
    if (i == expressions.relations_count)
      break;
    const auto relation = expressions.relations[i];
    const bf field_value = evaluate_linear_relation(memory, witness, scratch, relation);
    const u32 value = bf::into_canonical_u32(field_value);
    mapping.set(value);
    mapping.add_col(1);
  }
}

} // namespace airbender::trace::witness::multiplicities
