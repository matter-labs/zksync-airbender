#pragma once

#include "window/common.cuh"

namespace airbender::gkr {

// The continuation evaluator consumes either endpoint zero alone or the
// endpoint-zero/delta pair implied by one semantic source. Callers own source
// addressing and folding; this is the only contract between the lean evaluator
// and its backing.
enum bwd_continuation_projection : u32 {
  BWD_CONTINUATION_PROJ_ENDPOINT0 = 0,
  BWD_CONTINUATION_PROJ_PAIR = 1,
};

struct bwd_continuation_pair {
  e4 endpoint0;
  e4 delta;
};

// Add `immediate * value` to one side of a grouped atom. Non-literal words are
// reduced Montgomery representations prepared at the descriptor ABI boundary.
DEVICE_FORCEINLINE void bwd_continuation_apply_immediate(const u32 *immediates, const u16 immediate_id, const e4 &value, e4 &sum) {
  if (immediate_id == BWD_PROGRAM_IMMEDIATE_ONE) {
    sum = e4::add(sum, value);
  } else if (immediate_id == BWD_PROGRAM_IMMEDIATE_NEG_ONE) {
    sum = e4::sub(sum, value);
  } else {
    const bf immediate = bf::from_reduced_raw_repr(immediates[immediate_id - BWD_PROGRAM_IMMEDIATE_RESERVED]);
    sum = e4::fma(value, immediate, sum);
  }
}

// A resolver implements
//
//   template <bwd_continuation_projection P>
//   bwd_continuation_pair resolve(u16 source) const;
//
// so continuation windows can preserve their endpoint-only load while main-tail can resolve a
// canonical pair from its current dense ping-pong level.
template <typename SourcePairResolver>
DEVICE_FORCEINLINE void bwd_continuation_execute_group_member(const u32 *immediates, const SourcePairResolver &resolver, const u16 member_class,
                                                              const u16 immediate_id, const u16 source_a, const u16 source_b, e4 &sum_c0, e4 &sum_c2) {
  switch (member_class) {
  case BWD_CONTINUATION_CLASS_C0_LINEAR_E4: {
    const bwd_continuation_pair a = resolver.template resolve<BWD_CONTINUATION_PROJ_ENDPOINT0>(source_a);
    bwd_continuation_apply_immediate(immediates, immediate_id, a.endpoint0, sum_c0);
    break;
  }
  case BWD_CONTINUATION_CLASS_DUAL_PRODUCT_E4: {
    const bwd_continuation_pair a = resolver.template resolve<BWD_CONTINUATION_PROJ_PAIR>(source_a);
    const bwd_continuation_pair b = resolver.template resolve<BWD_CONTINUATION_PROJ_PAIR>(source_b);
    bwd_continuation_apply_immediate(immediates, immediate_id, e4::mul(a.endpoint0, b.endpoint0), sum_c0);
    bwd_continuation_apply_immediate(immediates, immediate_id, e4::mul(a.delta, b.delta), sum_c2);
    break;
  }
  default:
    // Host validation excludes dead classes. A release kernel has no error
    // channel, so an invalid record contributes nothing.
    break;
  }
}

DEVICE_FORCEINLINE void bwd_continuation_apply_group_core(const e4 &core, const u16 flags, const e4 &sum_c0, const e4 &sum_c2, e4 &acc_c0, e4 &acc_c2) {
  if ((flags & BWD_CONTINUATION_GROUP_FLAG_C0) != 0)
    acc_c0 = e4::fma(core, sum_c0, acc_c0);
  if ((flags & BWD_CONTINUATION_GROUP_FLAG_C2) != 0)
    acc_c2 = e4::fma(core, sum_c2, acc_c2);
}

// Execute one dealt continuation list. Exactly one list per row may receive
// `c_init`; absence is tested before narrowing the caller's sentinel to a bank
// index. Every coefficient access stays behind AB_GKR_BWD_COEFF.
template <typename SourcePairResolver>
DEVICE_FORCEINLINE void bwd_continuation_evaluate_list(const u16 *program, const u32 *immediates, u32 pc, const u32 pc_end, const bool apply_c_init,
                                                       const bool has_c_init, const u16 c_init_coeff_id, const SourcePairResolver &resolver, e4 &acc_c0,
                                                       e4 &acc_c2) {
  acc_c0 = e4::ZERO();
  acc_c2 = e4::ZERO();
  if (apply_c_init && has_c_init)
    acc_c0 = AB_GKR_BWD_COEFF(c_init_coeff_id);

#pragma unroll 1
  for (; pc < pc_end; pc += BWD_CONTINUATION_WORDS_PER_TERM) {
    const u16 header = program[pc];
    const u16 term_class = (header >> BWD_CONTINUATION_CLASS_SHIFT) & BWD_CONTINUATION_CLASS_MASK;
    const u16 coefficient_index = (header >> BWD_CONTINUATION_COEFFICIENT_SHIFT) & BWD_CONTINUATION_COEFFICIENT_MASK;
    const u16 source_a = program[pc + 1];
    const u16 source_b = program[pc + 2];

    if (term_class == BWD_CONTINUATION_CLASS_GROUP_HEADER) {
      const u16 member_count = source_a;
      const u16 flags = source_b;
      e4 sum_c0 = e4::ZERO();
      e4 sum_c2 = e4::ZERO();
#pragma unroll 1
      for (u16 member = 0; member < member_count; member++) {
        pc += BWD_CONTINUATION_WORDS_PER_TERM;
        const u16 member_header = program[pc];
        const u16 member_class = (member_header >> BWD_CONTINUATION_CLASS_SHIFT) & BWD_CONTINUATION_CLASS_MASK;
        const u16 immediate_id = (member_header >> BWD_CONTINUATION_COEFFICIENT_SHIFT) & BWD_CONTINUATION_COEFFICIENT_MASK;
        bwd_continuation_execute_group_member(immediates, resolver, member_class, immediate_id, program[pc + 1], program[pc + 2], sum_c0, sum_c2);
      }
      const e4 core = AB_GKR_BWD_COEFF(coefficient_index);
      bwd_continuation_apply_group_core(core, flags, sum_c0, sum_c2, acc_c0, acc_c2);
      continue;
    }

    const e4 coefficient = AB_GKR_BWD_COEFF(coefficient_index);
    switch (term_class) {
    case BWD_CONTINUATION_CLASS_C0_LINEAR_E4: {
      const bwd_continuation_pair a = resolver.template resolve<BWD_CONTINUATION_PROJ_ENDPOINT0>(source_a);
      acc_c0 = e4::fma(coefficient, a.endpoint0, acc_c0);
      break;
    }
    case BWD_CONTINUATION_CLASS_DUAL_PRODUCT_E4: {
      const bwd_continuation_pair a = resolver.template resolve<BWD_CONTINUATION_PROJ_PAIR>(source_a);
      const bwd_continuation_pair b = resolver.template resolve<BWD_CONTINUATION_PROJ_PAIR>(source_b);
      acc_c0 = e4::fma(coefficient, e4::mul(a.endpoint0, b.endpoint0), acc_c0);
      acc_c2 = e4::fma(coefficient, e4::mul(a.delta, b.delta), acc_c2);
      break;
    }
    default:
      break;
    }
  }
}

} // namespace airbender::gkr
