#pragma once

#include "field.cuh"
#include <cstddef>

namespace airbender::trace::witness::proth120 {

struct __align__(16) Proth120LinearTerm {
  pr coefficient;
  Address address;
  u32 padding;
};

struct __align__(16) Proth120LinearRelation {
  pr constant;
  Proth120LinearTerm terms[MAX_LINEAR_TERMS_COUNT];
  u32 terms_count;
  u32 padding[3];
};

struct Proth120LookupExpressions {
  const Proth120LinearRelation *relations;
  u32 count;
  u32 padding;
};

static_assert(sizeof(Address) == 12 && alignof(Address) == 4);
static_assert(offsetof(Address, tag) == 0 && offsetof(Address, offset) == 4 && offsetof(Address, layer) == 8);
static_assert(sizeof(Proth120LinearTerm) == 32 && alignof(Proth120LinearTerm) == 16);
static_assert(offsetof(Proth120LinearTerm, coefficient) == 0 && offsetof(Proth120LinearTerm, address) == 16 && offsetof(Proth120LinearTerm, padding) == 28);
static_assert(sizeof(Proth120LinearRelation) == 160 && alignof(Proth120LinearRelation) == 16);
static_assert(offsetof(Proth120LinearRelation, constant) == 0 && offsetof(Proth120LinearRelation, terms) == 16);
static_assert(offsetof(Proth120LinearRelation, terms_count) == 144 && offsetof(Proth120LinearRelation, padding) == 148);
static_assert(sizeof(Proth120LookupExpressions) == 16 && alignof(Proth120LookupExpressions) == 8);
static_assert(offsetof(Proth120LookupExpressions, relations) == 0 && offsetof(Proth120LookupExpressions, count) == 8 &&
              offsetof(Proth120LookupExpressions, padding) == 12);

template <typename Memory, typename Witness, typename Scratch>
DEVICE_FORCEINLINE pr evaluate_linear_relation(const Memory &memory, const Witness &witness, const Scratch &scratch, const Proth120LinearRelation &relation) {
  if (relation.terms_count > MAX_LINEAR_TERMS_COUNT)
    __trap();
  pr result = relation.constant;
#pragma unroll
  for (u32 i = 0; i < MAX_LINEAR_TERMS_COUNT; i++) {
    if (i == relation.terms_count)
      break;
    const auto &term = relation.terms[i];
    pr value = pr::ZERO();
    switch (term.address.tag) {
    case BaseLayerMemory:
      value = memory.get_at_col(term.address.offset);
      break;
    case BaseLayerWitness:
      value = witness.get_at_col(term.address.offset);
      break;
    case ScratchSpace:
      value = scratch.get_at_col(term.address.offset);
      break;
    default:
      __trap();
    }
    if (pr::is_zero(term.coefficient))
      __trap();
    result = pr::fma(term.coefficient, value, result);
  }
  return result;
}

template <typename Memory, typename Witness, typename Scratch, typename Mapping>
DEVICE_FORCEINLINE void process_lookup_expressions(const Memory &memory, const Witness &witness, const Scratch &scratch,
                                                   const Proth120LookupExpressions expressions, Mapping &mapping) {
  for (u32 i = 0; i < expressions.count; i++) {
    const pr field_value = evaluate_linear_relation(memory, witness, scratch, expressions.relations[i]);
    mapping.set(pr_to_u32_bounded(field_value));
    mapping.add_col(1);
  }
}

} // namespace airbender::trace::witness::proth120
