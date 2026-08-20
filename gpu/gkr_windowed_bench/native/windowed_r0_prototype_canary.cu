#include "windowed_r0_prototype_dedicated_control.cuh"
#include "windowed_r0_prototype_kernel.cuh"

namespace airbender::gkr_windowed_bench {

#define AB_R0PB_CANARY_KERNEL(Name, Cursor, Inner, Outer, Geometry) AB_R0PB_DEFINE_ORDINARY_KERNEL(Name, Cursor, Inner, Outer, Geometry)

AB_R0PB_CANARY_KERNEL(ab_gkr_r0pb_canary_current, r0pb_current_fixed_slot_cursor, r0pb_inner_canonical, r0pb_outer_canonical, r0pb_cta288_pair_geometry);
AB_R0PB_CANARY_KERNEL(ab_gkr_r0pb_canary_compact, r0pb_compact_r0_port_cursor, r0pb_inner_canonical, r0pb_outer_u64, r0pb_cta96_partitioned_geometry);
AB_R0PB_CANARY_KERNEL(ab_gkr_r0pb_canary_split_slot, r0pb_split_fixed_slot_cursor, r0pb_inner_canonical, r0pb_outer_u96, r0pb_cta96_x0_major_geometry);
AB_R0PB_CANARY_KERNEL(ab_gkr_r0pb_canary_split_direct, r0pb_split_fixed_direct_cursor, r0pb_inner_canonical, r0pb_outer_canonical,
                      r0pb_cta96_x1_major_geometry);
AB_R0PB_CANARY_KERNEL(ab_gkr_r0pb_canary_homogeneous_slot, r0pb_homogeneous_slot_cursor, r0pb_inner_canonical, r0pb_outer_u64, r0pb_cta96_x2_major_geometry);
AB_R0PB_CANARY_KERNEL(ab_gkr_r0pb_canary_homogeneous_direct, r0pb_homogeneous_direct_cursor, r0pb_inner_canonical, r0pb_outer_u96, r0pb_cta288_pair_geometry);
AB_R0PB_CANARY_KERNEL(ab_gkr_r0pb_canary_grouped_slot, r0pb_grouped_slot_cursor, r0pb_inner_u64, r0pb_outer_u64, r0pb_cta96_partitioned_geometry);
AB_R0PB_CANARY_KERNEL(ab_gkr_r0pb_canary_grouped_direct, r0pb_grouped_direct_cursor, r0pb_inner_u64, r0pb_outer_u96, r0pb_cta96_x2_major_geometry);

AB_R0PB_DEFINE_SECTIONED_WIDE9_KERNEL(ab_gkr_r0pb_canary_sectioned_wide9, R0PB_SHAPE_UNIVERSAL);
AB_R0PB_DEFINE_SECTIONED_WIDE9_BOUNDED_KERNEL(ab_gkr_r0pb_canary_sectioned_wide9_b4, R0PB_SHAPE_UNIVERSAL, 4);
AB_R0PB_DEFINE_SECTIONED_SPLIT3_KERNEL(ab_gkr_r0pb_canary_sectioned_split3, R0PB_SHAPE_UNIVERSAL);
AB_R0PB_DEFINE_SECTIONED_SERIAL3_LOW_KERNEL(ab_gkr_r0pb_canary_sectioned_serial3_low, R0PB_SHAPE_UNIVERSAL);
AB_R0PB_DEFINE_SECTIONED_SERIAL3_HIGH_KERNEL(ab_gkr_r0pb_canary_sectioned_serial3_high, R0PB_SHAPE_UNIVERSAL);
AB_R0PB_DEFINE_SECTIONED_SPLIT3_BOUNDED_KERNEL(ab_gkr_r0pb_canary_sectioned_split3_b7, R0PB_SHAPE_UNIVERSAL, 7);
AB_R0PB_DEFINE_SECTIONED_SPLIT3_BOUNDED_KERNEL(ab_gkr_r0pb_canary_sectioned_split3_b8, R0PB_SHAPE_UNIVERSAL, 8);
AB_R0PB_DEFINE_SECTIONED_SPLIT3_BOUNDED_KERNEL(ab_gkr_r0pb_canary_sectioned_split3_b9, R0PB_SHAPE_UNIVERSAL, 9);
AB_R0PB_DEFINE_SECTIONED_SPLIT3_BOUNDED_KERNEL(ab_gkr_r0pb_canary_sectioned_split3_b10, R0PB_SHAPE_UNIVERSAL, 10);
AB_R0PB_DEFINE_SECTIONED_SPLIT3_BOUNDED_KERNEL(ab_gkr_r0pb_canary_sectioned_split3_b12, R0PB_SHAPE_UNIVERSAL, 12);
AB_R0PB_DEFINE_SECTIONED_SPLIT3_BOUNDED_KERNEL(ab_gkr_r0pb_canary_sectioned_split3_b16, R0PB_SHAPE_UNIVERSAL, 16);
AB_R0PB_DEFINE_SECTIONED_SERIAL3_LOW_BOUNDED_KERNEL(ab_gkr_r0pb_canary_sectioned_serial3_low_b7, R0PB_SHAPE_UNIVERSAL, 7);
AB_R0PB_DEFINE_SECTIONED_SERIAL3_LOW_BOUNDED_KERNEL(ab_gkr_r0pb_canary_sectioned_serial3_low_b8, R0PB_SHAPE_UNIVERSAL, 8);
AB_R0PB_DEFINE_SECTIONED_SERIAL3_LOW_BOUNDED_KERNEL(ab_gkr_r0pb_canary_sectioned_serial3_low_b9, R0PB_SHAPE_UNIVERSAL, 9);
AB_R0PB_DEFINE_SECTIONED_SERIAL3_LOW_BOUNDED_KERNEL(ab_gkr_r0pb_canary_sectioned_serial3_low_b10, R0PB_SHAPE_UNIVERSAL, 10);
AB_R0PB_DEFINE_SECTIONED_SERIAL3_LOW_BOUNDED_KERNEL(ab_gkr_r0pb_canary_sectioned_serial3_low_b12, R0PB_SHAPE_UNIVERSAL, 12);
AB_R0PB_DEFINE_SECTIONED_SERIAL3_LOW_BOUNDED_KERNEL(ab_gkr_r0pb_canary_sectioned_serial3_low_b16, R0PB_SHAPE_UNIVERSAL, 16);

AB_R0PB_DEFINE_MATERIALIZED_KERNEL(ab_gkr_r0pb_canary_materialized_current, r0pb_current_fixed_slot_cursor, r0pb_inner_canonical, r0pb_outer_canonical,
                                   r0pb_cta288_pair_geometry);
AB_R0PB_DEFINE_MATERIALIZED_KERNEL(ab_gkr_r0pb_canary_materialized_compact, r0pb_compact_r0_port_cursor, r0pb_inner_canonical, r0pb_outer_u64,
                                   r0pb_cta96_partitioned_geometry);
AB_R0PB_DEFINE_MATERIALIZED_KERNEL(ab_gkr_r0pb_canary_materialized_split_slot, r0pb_split_fixed_slot_cursor, r0pb_inner_canonical, r0pb_outer_u96,
                                   r0pb_cta96_x0_major_geometry);
AB_R0PB_DEFINE_MATERIALIZED_KERNEL(ab_gkr_r0pb_canary_materialized_split_direct, r0pb_split_fixed_direct_cursor, r0pb_inner_canonical, r0pb_outer_canonical,
                                   r0pb_cta96_x1_major_geometry);
AB_R0PB_DEFINE_MATERIALIZED_KERNEL(ab_gkr_r0pb_canary_materialized_homogeneous_slot, r0pb_homogeneous_slot_cursor, r0pb_inner_canonical, r0pb_outer_u64,
                                   r0pb_cta96_x2_major_geometry);
AB_R0PB_DEFINE_MATERIALIZED_KERNEL(ab_gkr_r0pb_canary_materialized_homogeneous_direct, r0pb_homogeneous_direct_cursor, r0pb_inner_canonical, r0pb_outer_u96,
                                   r0pb_cta288_pair_geometry);
AB_R0PB_DEFINE_MATERIALIZED_KERNEL(ab_gkr_r0pb_canary_materialized_grouped_slot, r0pb_grouped_slot_cursor, r0pb_inner_u64, r0pb_outer_canonical,
                                   r0pb_cta96_partitioned_geometry);
AB_R0PB_DEFINE_MATERIALIZED_KERNEL(ab_gkr_r0pb_canary_materialized_grouped_direct, r0pb_grouped_direct_cursor, r0pb_inner_u64, r0pb_outer_u96,
                                   r0pb_cta96_x2_major_geometry);

#undef AB_R0PB_CANARY_KERNEL

} // namespace airbender::gkr_windowed_bench
