#pragma once

#include "windowed_r0_prototype_accumulator.cuh"

namespace airbender::gkr_windowed_bench {

constexpr u32 R0PB_NO_GROUP = 0xffffffffu;
constexpr u8 R0PB_PHASE_BF = 0;
constexpr u8 R0PB_PHASE_E4 = 1;
constexpr u8 R0PB_SOURCE_SLOT = 0;
constexpr u8 R0PB_SOURCE_DIRECT = 1;

struct decoded_r0_op {
  u8 term_class;
  u32 coefficient_id;
  u16 source_a;
  u16 source_b;
  u32 group_id;
  u32 member_index;
  u32 immediate;
  u8 phase;
  u8 source_mode;
  u8 group_last;
};

template <typename Desc> DEVICE_FORCEINLINE u32 r0pb_record_count(const Desc &desc) {
  if constexpr (requires { desc.common.record_count; })
    return desc.common.record_count;
  else
    return desc.record_count;
}

template <typename Desc> DEVICE_FORCEINLINE const u16 *r0pb_program(const Desc &desc) { return desc.program; }

template <typename Desc> DEVICE_FORCEINLINE u32 r0pb_section(const Desc &desc, const u32 index) { return desc.meta.sections[index]; }

DEVICE_FORCEINLINE u8 r0pb_phase_for_class(const u8 term_class) { return term_class == 0 || term_class == 2 ? R0PB_PHASE_BF : R0PB_PHASE_E4; }

template <typename Desc, u8 SourceMode> struct r0pb_fixed_cursor_state {
  const Desc &desc;
  u32 record = 0;

  DEVICE_FORCEINLINE bool done() const { return record == r0pb_record_count(desc); }

  DEVICE_FORCEINLINE decoded_r0_op next() {
    const u16 *program = r0pb_program(desc);
    const u32 word = 4 * record++;
    const u16 header = program[word];
    const u8 term_class = header >> 13;
    return {
        term_class, static_cast<u32>(header & 0x1fffu), program[word + 1], program[word + 2], R0PB_NO_GROUP, 0, 1, r0pb_phase_for_class(term_class), SourceMode,
        1};
  }
};

template <typename Desc> struct r0pb_compact_cursor_state {
  const Desc &desc;
  u32 word = 0;
  u32 emitted = 0;

  DEVICE_FORCEINLINE u32 load_u32(const u32 offset) const {
    const u16 *program = r0pb_program(desc);
    return static_cast<u32>(program[offset]) | (static_cast<u32>(program[offset + 1]) << 16);
  }

  DEVICE_FORCEINLINE bool done() const { return emitted == r0pb_record_count(desc); }

  DEVICE_FORCEINLINE decoded_r0_op next() {
    const u32 head = load_u32(word);
    const u32 tag = head & 7u;
    ++emitted;
    if (tag == 7u) {
      const u32 first = load_u32(word + 2);
      const u32 second = load_u32(word + 4);
      word += 6;
      const u16 header = static_cast<u16>(first);
      const u8 term_class = header >> 13;
      return {term_class,
              static_cast<u32>(header & 0x1fffu),
              static_cast<u16>(first >> 16),
              static_cast<u16>(second),
              R0PB_NO_GROUP,
              0,
              1,
              r0pb_phase_for_class(term_class),
              R0PB_SOURCE_SLOT,
              1};
    }
    const u8 term_class = static_cast<u8>((head >> 3) & 7u);
    const u32 coefficient = (head >> 6) & 0x1fffu;
    u16 source_a = 0;
    u16 source_b = 0;
    if (tag == 0u) {
      source_a = static_cast<u16>((head >> 19) & 0xfffu);
      word += 2;
    } else if (tag == 1u) {
      const u32 tail = load_u32(word + 2);
      const u16 window = static_cast<u16>((head >> 19) & 0x1fu);
      source_a = static_cast<u16>((window << 7) | ((head >> 24) & 0x7fu));
      source_b = static_cast<u16>((window << 7) | (tail & 0x7fu));
      word += 4;
    } else {
      const u32 tail = load_u32(word + 2);
      source_a = static_cast<u16>(tail & 0xfffu);
      source_b = static_cast<u16>((tail >> 12) & 0xfffu);
      word += 4;
    }
    return {term_class, coefficient, source_a, source_b, R0PB_NO_GROUP, 0, 1, r0pb_phase_for_class(term_class), R0PB_SOURCE_DIRECT, 1};
  }
};

template <typename Desc, u8 SourceMode> struct r0pb_homogeneous_cursor_state {
  const Desc &desc;
  u32 emitted = 0;
  u32 class_cursor[5]{};

  DEVICE_FORCEINLINE bool done() const { return emitted == r0pb_record_count(desc); }

  DEVICE_FORCEINLINE decoded_r0_op next() {
    const u16 *program = r0pb_program(desc);
    const u8 term_class = static_cast<u8>(program[emitted]);
    const u32 width = term_class <= 1 ? 2 : 3;
    const u32 offset = r0pb_section(desc, 2 + 2 * term_class) + width * class_cursor[term_class]++;
    ++emitted;
    return {term_class,
            static_cast<u32>(program[offset] & 0x1fffu),
            program[offset + 1],
            term_class <= 1 ? 0 : program[offset + 2],
            R0PB_NO_GROUP,
            0,
            1,
            r0pb_phase_for_class(term_class),
            SourceMode,
            1};
  }
};

template <typename Desc, u8 SourceMode> struct r0pb_grouped_cursor_state {
  const Desc &desc;
  u32 word = 0;
  u32 emitted = 0;
  u32 group_id = R0PB_NO_GROUP;
  u32 group_member = 0;
  u32 group_remaining = 0;
  u32 group_core = 0;
  u8 group_phase = R0PB_PHASE_BF;

  DEVICE_FORCEINLINE bool done() const { return emitted == r0pb_record_count(desc); }

  DEVICE_FORCEINLINE u32 immediate(const u16 id) const {
    if (id == 0)
      return 1;
    if (id == 1)
      return bf::ORDER - 1;
    return desc.immediates[id - 2];
  }

  DEVICE_FORCEINLINE decoded_r0_op next() {
    const u16 *program = r0pb_program(desc);
    if (group_remaining == 0 && program[word] == 0xffffu) {
      group_core = program[word + 1];
      group_remaining = program[word + 2];
      const u16 tagged_id = program[word + 3];
      group_phase = tagged_id & 0x8000u ? R0PB_PHASE_E4 : R0PB_PHASE_BF;
      group_id = tagged_id & 0x7fffu;
      group_member = 0;
      word += 4;
    }
    ++emitted;
    if (group_remaining != 0) {
      const u8 term_class = static_cast<u8>(program[word++]);
      const u16 immediate_id = program[word++];
      const u16 source_a = program[word++];
      const u16 source_b = term_class <= 1 ? 0 : program[word++];
      const u32 member = group_member++;
      --group_remaining;
      const u32 id = group_id;
      if (group_remaining == 0)
        group_id = R0PB_NO_GROUP;
      return {term_class, group_core, source_a, source_b, id, member, immediate(immediate_id), group_phase, SourceMode, static_cast<u8>(group_remaining == 0)};
    }
    const u16 header = program[word++];
    const u8 term_class = header >> 13;
    const u16 source_a = program[word++];
    const u16 source_b = term_class <= 1 ? 0 : program[word++];
    return {term_class, static_cast<u32>(header & 0x1fffu), source_a, source_b, R0PB_NO_GROUP, 0, 1, r0pb_phase_for_class(term_class), SourceMode, 1};
  }
};

template <typename Desc> using r0pb_fixed_cursor_state_slot = r0pb_fixed_cursor_state<Desc, R0PB_SOURCE_SLOT>;
template <typename Desc> using r0pb_fixed_cursor_state_direct = r0pb_fixed_cursor_state<Desc, R0PB_SOURCE_DIRECT>;
template <typename Desc> using r0pb_homogeneous_cursor_state_slot = r0pb_homogeneous_cursor_state<Desc, R0PB_SOURCE_SLOT>;
template <typename Desc> using r0pb_homogeneous_cursor_state_direct = r0pb_homogeneous_cursor_state<Desc, R0PB_SOURCE_DIRECT>;
template <typename Desc> using r0pb_grouped_cursor_state_slot = r0pb_grouped_cursor_state<Desc, R0PB_SOURCE_SLOT>;
template <typename Desc> using r0pb_grouped_cursor_state_direct = r0pb_grouped_cursor_state<Desc, R0PB_SOURCE_DIRECT>;

#define AB_R0PB_CURSOR_TAG(Name, State, Ordinary, Materialized)                                                                                                \
  struct Name {                                                                                                                                                \
    using ordinary_desc = Ordinary;                                                                                                                            \
    using materialized_desc = Materialized;                                                                                                                    \
    template <typename Desc> using state = State<Desc>;                                                                                                        \
  }

AB_R0PB_CURSOR_TAG(r0pb_current_fixed_slot_cursor, r0pb_fixed_cursor_state_slot, r0_vm_desc, r0_current_materialized);
AB_R0PB_CURSOR_TAG(r0pb_compact_r0_port_cursor, r0pb_compact_cursor_state, r0_compact_ordinary, r0_compact_materialized);
AB_R0PB_CURSOR_TAG(r0pb_split_fixed_slot_cursor, r0pb_fixed_cursor_state_slot, r0_split_slot_ordinary, r0_split_slot_materialized);
AB_R0PB_CURSOR_TAG(r0pb_split_fixed_direct_cursor, r0pb_fixed_cursor_state_direct, r0_split_direct_ordinary, r0_split_direct_materialized);
AB_R0PB_CURSOR_TAG(r0pb_homogeneous_slot_cursor, r0pb_homogeneous_cursor_state_slot, r0_homogeneous_slot_ordinary, r0_homogeneous_slot_materialized);
AB_R0PB_CURSOR_TAG(r0pb_homogeneous_direct_cursor, r0pb_homogeneous_cursor_state_direct, r0_homogeneous_direct_ordinary, r0_homogeneous_direct_materialized);
AB_R0PB_CURSOR_TAG(r0pb_grouped_slot_cursor, r0pb_grouped_cursor_state_slot, r0_grouped_slot_ordinary, r0_grouped_slot_materialized);
AB_R0PB_CURSOR_TAG(r0pb_grouped_direct_cursor, r0pb_grouped_cursor_state_direct, r0_grouped_direct_ordinary, r0_grouped_direct_materialized);

#undef AB_R0PB_CURSOR_TAG

} // namespace airbender::gkr_windowed_bench
