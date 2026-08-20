#pragma once

#include "windowed_r0_prototype_geometry.cuh"

namespace airbender::gkr_windowed_bench {

using r0pb_inner_canonical = r0_inner_canonical;
using r0pb_inner_u64 = r0_inner_u64;
using r0pb_outer_canonical = r0_outer_canonical;
using r0pb_outer_u64 = r0_outer_u64;
using r0pb_outer_u96 = r0_outer_u96;

template <typename Desc> DEVICE_FORCEINLINE u32 r0pb_log_rows(const Desc &desc) {
  if constexpr (requires { desc.common.log_rows; })
    return desc.common.log_rows;
  else
    return desc.log_rows;
}

template <typename Desc> DEVICE_FORCEINLINE const e4 *r0pb_eq_low(const Desc &desc) {
  if constexpr (requires { desc.common.eq_low; })
    return desc.common.eq_low;
  else
    return desc.eq_low;
}

template <typename Desc> DEVICE_FORCEINLINE e4 *r0pb_partials(const Desc &desc) {
  if constexpr (requires { desc.common.partials; })
    return desc.common.partials;
  else
    return desc.partials;
}

template <typename Desc> DEVICE_FORCEINLINE r0_window_eq_sizes r0pb_eq_sizes(const Desc &desc) {
  if constexpr (requires { desc.meta.eq_sizes; })
    return desc.meta.eq_sizes;
  else
    return desc.eq_sizes;
}

template <typename Desc> DEVICE_FORCEINLINE e4 r0pb_eq(const Desc &desc, const u32 row) {
  const r0_window_eq_sizes sizes = r0pb_eq_sizes(desc);
  const u32 low = row & r0_bit_mask(sizes.low);
  const u32 high1 = (row >> sizes.low) & r0_bit_mask(sizes.high[1]);
  const u32 high0 = (row >> (sizes.low + sizes.high[1])) & r0_bit_mask(sizes.high[0]);
  e4 value = load<e4, ld_modifier::ca>(r0pb_eq_low(desc), low);
  if (sizes.high[1] != 0)
    value = e4::mul(value, ::ab_gkr_windowed_r0_eq_high[256 + high1]);
  if (sizes.high[0] != 0)
    value = e4::mul(value, ::ab_gkr_windowed_r0_eq_high[high0]);
  return value;
}

template <typename Policy, u32 Cells> struct r0pb_outer_state;

template <u32 Cells> struct r0pb_outer_state<r0pb_outer_canonical, Cells> {
  e4 values[Cells]{};

  DEVICE_FORCEINLINE void add_bf(const u32 cell, const e4 core, const bf value) { values[cell] = e4::add(values[cell], e4::mul(core, value)); }
  DEVICE_FORCEINLINE void finish_bf() {}
};

template <u32 Cells> struct r0pb_outer_state<r0pb_outer_u64, Cells> {
  r0_u64_accumulator wide[Cells][4]{};
  e4 values[Cells]{};

  DEVICE_FORCEINLINE void add_bf(const u32 cell, const e4 core, const bf value) {
    wide[cell][0].add_product(core[0][0].limb, value.limb);
    wide[cell][1].add_product(core[0][1].limb, value.limb);
    wide[cell][2].add_product(core[1][0].limb, value.limb);
    wide[cell][3].add_product(core[1][1].limb, value.limb);
  }

  DEVICE_FORCEINLINE void finish_bf() {
#pragma unroll
    for (u32 cell = 0; cell < Cells; ++cell)
      values[cell] = e4(e2(wide[cell][0].reduce(), wide[cell][1].reduce()), e2(wide[cell][2].reduce(), wide[cell][3].reduce()));
  }
};

template <u32 Cells> struct r0pb_outer_state<r0pb_outer_u96, Cells> {
  r0_u96_accumulator wide[Cells][4]{};
  e4 values[Cells]{};

  DEVICE_FORCEINLINE void add_bf(const u32 cell, const e4 core, const bf value) {
    wide[cell][0].add_product(core[0][0].limb, value.limb);
    wide[cell][1].add_product(core[0][1].limb, value.limb);
    wide[cell][2].add_product(core[1][0].limb, value.limb);
    wide[cell][3].add_product(core[1][1].limb, value.limb);
  }

  DEVICE_FORCEINLINE void finish_bf() {
#pragma unroll
    for (u32 cell = 0; cell < Cells; ++cell)
      values[cell] = e4(e2(wide[cell][0].reduce(), wide[cell][1].reduce()), e2(wide[cell][2].reduce(), wide[cell][3].reduce()));
  }
};

template <typename Inner, u32 Cells> struct r0pb_inner_state;

template <u32 Cells> struct r0pb_inner_state<r0pb_inner_canonical, Cells> {
  template <typename Outer> DEVICE_FORCEINLINE void add_bf(Outer &outer, const u32 cell, const decoded_r0_op &op, const e4 core, const bf value) {
    outer.add_bf(cell, core, bf::mul(bf::from_u32_unchecked(op.immediate), value));
  }
};

template <u32 Cells> struct r0pb_inner_state<r0pb_inner_u64, Cells> {
  r0_u64_accumulator groups[Cells]{};
  u32 active_group = R0PB_NO_GROUP;

  template <typename Outer> DEVICE_FORCEINLINE void add_bf(Outer &outer, const u32 cell, const decoded_r0_op &op, const e4 core, const bf value) {
    if (op.group_id == R0PB_NO_GROUP) {
      outer.add_bf(cell, core, value);
      return;
    }
    if (op.member_index == 0) {
      if (cell == 0)
        active_group = op.group_id;
      groups[cell] = r0_u64_accumulator{};
    }
    groups[cell].add_product(bf::from_u32_unchecked(op.immediate).limb, value.limb);
    if (op.group_last)
      outer.add_bf(cell, core, groups[cell].reduce());
  }
};

template <typename SourceA> DEVICE_FORCEINLINE bf r0pb_bf_term(const decoded_r0_op &op, const r0pb_owned_cell owned, const u32 row, const SourceA &source_a) {
  if (op.term_class == 0) {
    if (owned.selector.has_infinity() || owned.x2 == 2)
      return bf::ZERO();
    return r0_xy_endpoint<bf>(source_a, row, owned.selector, owned.x2);
  }
  if (owned.x2 == 0)
    return bf::ZERO();
  return r0_x2_delta<bf>(source_a, row, owned.selector);
}

template <typename SourceA, typename SourceB>
DEVICE_FORCEINLINE bf r0pb_bf_product(const r0pb_owned_cell owned, const u32 row, const SourceA &source_a, const SourceB &source_b) {
  if (owned.x2 == 0)
    return bf::ZERO();
  return bf::mul(r0_x2_delta<bf>(source_a, row, owned.selector), r0_x2_delta<bf>(source_b, row, owned.selector));
}

template <typename SourceA> DEVICE_FORCEINLINE e4 r0pb_e4_linear(const r0pb_owned_cell owned, const u32 row, const SourceA &source_a) {
  if (owned.selector.has_infinity() || owned.x2 == 2)
    return e4::ZERO();
  return r0_xy_endpoint<e4>(source_a, row, owned.selector, owned.x2);
}

DEVICE_FORCEINLINE e4 r0pb_scaled_core(const decoded_r0_op &op) {
  return e4::mul(r0_coefficient(static_cast<u16>(op.coefficient_id)), bf::from_u32_unchecked(op.immediate));
}

template <typename InnerPolicy, typename OuterPolicy, typename Geometry, typename ResolveBf, typename ResolveE4>
DEVICE_FORCEINLINE void r0pb_accumulate_op(const decoded_r0_op &op, const u32 row, ResolveBf resolve_bf, ResolveE4 resolve_e4,
                                           r0pb_inner_state<InnerPolicy, Geometry::owned_cells> &inner,
                                           r0pb_outer_state<OuterPolicy, Geometry::owned_cells> &outer, const bool e4_phase) {
  const e4 core = r0_coefficient(static_cast<u16>(op.coefficient_id));
#pragma unroll
  for (u32 cell = 0; cell < Geometry::owned_cells; ++cell) {
    const r0pb_owned_cell owned = Geometry::cell(cell);
    if (!e4_phase) {
      const bf value = op.term_class == 0 ? r0pb_bf_term(op, owned, row, resolve_bf(0)) : r0pb_bf_product(owned, row, resolve_bf(0), resolve_bf(1));
      inner.add_bf(outer, cell, op, core, value);
      continue;
    }
    e4 value = e4::ZERO();
    switch (op.term_class) {
    case 0:
      value = e4::mul(r0pb_scaled_core(op), r0pb_bf_term(op, owned, row, resolve_bf(0)));
      break;
    case 1:
      value = e4::mul(r0pb_scaled_core(op), r0pb_e4_linear(owned, row, resolve_e4(0)));
      break;
    case 2:
      value = e4::mul(r0pb_scaled_core(op), r0pb_bf_product(owned, row, resolve_bf(0), resolve_bf(1)));
      break;
    case 3:
      if (owned.x2 != 0)
        value =
            e4::mul(r0pb_scaled_core(op), e4::mul(r0_x2_delta<bf>(resolve_bf(0), row, owned.selector), r0_x2_delta<e4>(resolve_e4(1), row, owned.selector)));
      break;
    case 4:
      if (owned.x2 != 0)
        value =
            e4::mul(r0pb_scaled_core(op), e4::mul(r0_x2_delta<e4>(resolve_e4(0), row, owned.selector), r0_x2_delta<e4>(resolve_e4(1), row, owned.selector)));
      break;
    }
    outer.values[cell] = e4::add(outer.values[cell], value);
  }
}

template <typename Desc, typename Geometry>
DEVICE_FORCEINLINE void r0pb_publish(const Desc &desc, const u32 row_tile, const u32 lane, const bool active, e4 (&values)[Geometry::owned_cells]);

template <typename Desc, typename Cursor, typename InnerPolicy, typename OuterPolicy, typename Geometry>
DEVICE_FORCEINLINE void r0pb_execute_program(const Desc &desc) {
  const u32 lane = threadIdx.x & 31;
  const u32 row_tile = Geometry::row_tile();
  const u32 global_row = row_tile * 32 + lane;
  const bool active = global_row < (1u << r0pb_log_rows(desc));
  const u32 row = active ? global_row : 0;
  typename Cursor::template state<Desc> cursor{desc};
  r0pb_inner_state<InnerPolicy, Geometry::owned_cells> inner{};
  r0pb_outer_state<OuterPolicy, Geometry::owned_cells> outer{};
  bool e4_phase = false;
#pragma unroll 1
  while (!cursor.done()) {
    const decoded_r0_op op = cursor.next();
    if (!e4_phase && op.phase == R0PB_PHASE_E4) {
      outer.finish_bf();
      e4_phase = true;
    }
    const auto resolve_bf = [&](const u32 operand) { return r0pb_ordinary_slot_resolver::bf_source(desc, op, operand); };
    const auto resolve_e4 = [&](const u32 operand) { return r0pb_ordinary_slot_resolver::e4_source(desc, op, operand); };
    r0pb_accumulate_op<InnerPolicy, OuterPolicy, Geometry>(op, row, resolve_bf, resolve_e4, inner, outer, e4_phase);
  }
  if (!e4_phase)
    outer.finish_bf();
  r0pb_publish<Desc, Geometry>(desc, row_tile, lane, active, outer.values);
}

template <typename Desc, typename Cursor, typename InnerPolicy, typename OuterPolicy, typename Geometry>
DEVICE_FORCEINLINE void r0pb_execute_materialized(const Desc &desc, u8 *shared_storage) {
  const u32 lane = threadIdx.x & 31;
  const u32 row_tile = Geometry::row_tile();
  const u32 global_row = row_tile * 32 + lane;
  const bool active = global_row < (1u << r0pb_log_rows(desc.ordinary));
  typename Cursor::template state<decltype(desc.ordinary)> cursor{desc.ordinary};
  r0pb_inner_state<InnerPolicy, Geometry::owned_cells> inner{};
  r0pb_outer_state<OuterPolicy, Geometry::owned_cells> outer{};
  r0pb_materialized_resolver resolver{shared_storage};
  bool e4_phase = false;
  u32 record = 0;
  for (u32 tile = 0; tile < desc.tile_meta.tile_count; ++tile) {
    resolver.begin_tile(desc, tile, row_tile);
    const r0_prototype_tile_header header = desc.tiles[tile];
    for (u32 local_record = 0; local_record < header.record_count; ++local_record, ++record) {
      const decoded_r0_op op = cursor.next();
      if (!e4_phase && op.phase == R0PB_PHASE_E4) {
        outer.finish_bf();
        e4_phase = true;
      }
      const u8 *local = desc.record_local_sources[record];
      const auto resolve_bf = [&](const u32 operand) { return resolver.bf_source(local[operand]); };
      const auto resolve_e4 = [&](const u32 operand) { return resolver.e4_source(local[operand]); };
      r0pb_accumulate_op<InnerPolicy, OuterPolicy, Geometry>(op, lane, resolve_bf, resolve_e4, inner, outer, e4_phase);
    }
    resolver.end_tile();
  }
  if (!e4_phase)
    outer.finish_bf();
  r0pb_publish<decltype(desc.ordinary), Geometry>(desc.ordinary, row_tile, lane, active, outer.values);
}

template <typename Desc, typename Geometry>
DEVICE_FORCEINLINE void r0pb_publish(const Desc &desc, const u32 row_tile, const u32 lane, const bool active, e4 (&values)[Geometry::owned_cells]) {
  const e4 equality = r0pb_eq(desc, active ? row_tile * 32 + lane : 0);
#pragma unroll
  for (u32 cell = 0; cell < Geometry::owned_cells; ++cell) {
    e4 value = active ? e4::mul(equality, values[cell]) : e4::ZERO();
    value = r0_warp_sum(value);
    if (lane == 0)
      store<e4, st_modifier::cs>(r0pb_partials(desc), value, static_cast<size_t>(row_tile) * R0_WINDOW_CELLS + Geometry::cell(cell).output_index());
  }
}

#define AB_R0PB_DEFINE_ORDINARY_KERNEL(Name, Cursor, Inner, Outer, Geometry)                                                                                   \
  EXTERN __global__ void Name(const __grid_constant__ typename Cursor::ordinary_desc desc) {                                                                   \
    if (blockDim.x != Geometry::threads)                                                                                                                       \
      return;                                                                                                                                                  \
    r0pb_execute_program<typename Cursor::ordinary_desc, Cursor, Inner, Outer, Geometry>(desc);                                                                \
  }

#define AB_R0PB_DEFINE_MATERIALIZED_KERNEL(Name, Cursor, Inner, Outer, Geometry)                                                                               \
  EXTERN __global__ void Name(const __grid_constant__ typename Cursor::materialized_desc desc) {                                                               \
    if (blockDim.x != Geometry::threads)                                                                                                                       \
      return;                                                                                                                                                  \
    extern __shared__ __align__(16) u8 r0pb_dynamic_shared[];                                                                                                  \
    r0pb_execute_materialized<typename Cursor::materialized_desc, Cursor, Inner, Outer, Geometry>(desc, r0pb_dynamic_shared);                                  \
  }

} // namespace airbender::gkr_windowed_bench
