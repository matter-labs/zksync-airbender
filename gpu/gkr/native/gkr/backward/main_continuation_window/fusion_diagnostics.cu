// Feature-only whole-tile fusion candidates; production dispatch is unchanged.
#include "fold_diagnostics.cuh"
#include "fold_wide_diagnostic.cuh"
#include "fused_executor.cuh"

namespace airbender::gkr::backward {

AB_GKR_BWD_MAIN_CONT_WINDOW_DEFINE_X01_EVAL_IMPL(ab_gkr_main_cont_split_reference_00_b4, 0x00, 4, true, false);
AB_GKR_BWD_MAIN_CONT_WINDOW_DEFINE_X01_EVAL_IMPL(ab_gkr_main_cont_split_reference_01_b4, 0x01, 4, true, false);
AB_GKR_BWD_MAIN_CONT_WINDOW_DEFINE_X01_EVAL_IMPL(ab_gkr_main_cont_split_reference_03_b4, 0x03, 4, true, false);
AB_GKR_BWD_MAIN_CONT_WINDOW_DEFINE_X01_EVAL_IMPL(ab_gkr_main_cont_split_reference_07_b4, 0x07, 4, true, false);
AB_GKR_BWD_MAIN_CONT_WINDOW_DEFINE_X01_EVAL_IMPL(ab_gkr_main_cont_split_reference_13_b4, 0x13, 4, true, false);
AB_GKR_BWD_MAIN_CONT_WINDOW_DEFINE_X01_EVAL_IMPL(ab_gkr_main_cont_split_reference_17_b4, 0x17, 4, true, false);
AB_GKR_BWD_MAIN_CONT_WINDOW_DEFINE_X01_EVAL_IMPL(ab_gkr_main_cont_split_reference_1f_b4, 0x1f, 4, true, false);

AB_GKR_BWD_MAIN_CONT_WINDOW_DEFINE_X01_EVAL_IMPL(ab_gkr_main_cont_split_compact_00_b4, 0x00, 4, true, true);
AB_GKR_BWD_MAIN_CONT_WINDOW_DEFINE_X01_EVAL_IMPL(ab_gkr_main_cont_split_compact_01_b4, 0x01, 4, true, true);
AB_GKR_BWD_MAIN_CONT_WINDOW_DEFINE_X01_EVAL_IMPL(ab_gkr_main_cont_split_compact_03_b4, 0x03, 4, true, true);
AB_GKR_BWD_MAIN_CONT_WINDOW_DEFINE_X01_EVAL_IMPL(ab_gkr_main_cont_split_compact_07_b4, 0x07, 4, true, true);
AB_GKR_BWD_MAIN_CONT_WINDOW_DEFINE_X01_EVAL_IMPL(ab_gkr_main_cont_split_compact_13_b4, 0x13, 4, true, true);
AB_GKR_BWD_MAIN_CONT_WINDOW_DEFINE_X01_EVAL_IMPL(ab_gkr_main_cont_split_compact_17_b4, 0x17, 4, true, true);
AB_GKR_BWD_MAIN_CONT_WINDOW_DEFINE_X01_EVAL_IMPL(ab_gkr_main_cont_split_compact_1f_b4, 0x1f, 4, true, true);

AB_GKR_MAIN_CONT_DEFINE_FUSED_EVAL_IMPL(ab_gkr_main_cont_static_reference_00_b2, 0x00, 2, true, true, 0, 0, true, false);
AB_GKR_MAIN_CONT_DEFINE_FUSED_EVAL_IMPL(ab_gkr_main_cont_static_reference_01_b2, 0x01, 2, true, true, 0, 0, true, false);
AB_GKR_MAIN_CONT_DEFINE_FUSED_EVAL_IMPL(ab_gkr_main_cont_static_reference_03_b2, 0x03, 2, true, true, 0, 0, true, false);
AB_GKR_MAIN_CONT_DEFINE_FUSED_EVAL_IMPL(ab_gkr_main_cont_static_reference_07_b2, 0x07, 2, true, true, 0, 0, true, false);
AB_GKR_MAIN_CONT_DEFINE_FUSED_EVAL_IMPL(ab_gkr_main_cont_static_reference_13_b2, 0x13, 2, true, true, 0, 0, true, false);
AB_GKR_MAIN_CONT_DEFINE_FUSED_EVAL_IMPL(ab_gkr_main_cont_static_reference_17_b2, 0x17, 2, true, true, 0, 0, true, false);
AB_GKR_MAIN_CONT_DEFINE_FUSED_EVAL_IMPL(ab_gkr_main_cont_static_reference_1f_b2, 0x1f, 2, true, true, 0, 0, true, false);

AB_GKR_MAIN_CONT_DEFINE_FUSED_EVAL_IMPL(ab_gkr_main_cont_compact_00_b2, 0x00, 2, true, true, 0, 0, true, true);
AB_GKR_MAIN_CONT_DEFINE_FUSED_EVAL_IMPL(ab_gkr_main_cont_compact_01_b2, 0x01, 2, true, true, 0, 0, true, true);
AB_GKR_MAIN_CONT_DEFINE_FUSED_EVAL_IMPL(ab_gkr_main_cont_compact_03_b2, 0x03, 2, true, true, 0, 0, true, true);
AB_GKR_MAIN_CONT_DEFINE_FUSED_EVAL_IMPL(ab_gkr_main_cont_compact_07_b2, 0x07, 2, true, true, 0, 0, true, true);
AB_GKR_MAIN_CONT_DEFINE_FUSED_EVAL_IMPL(ab_gkr_main_cont_compact_13_b2, 0x13, 2, true, true, 0, 0, true, true);
AB_GKR_MAIN_CONT_DEFINE_FUSED_EVAL_IMPL(ab_gkr_main_cont_compact_17_b2, 0x17, 2, true, true, 0, 0, true, true);
AB_GKR_MAIN_CONT_DEFINE_FUSED_EVAL_IMPL(ab_gkr_main_cont_compact_1f_b2, 0x1f, 2, true, true, 0, 0, true, true);

AB_GKR_MAIN_CONT_DEFINE_FUSED_IMPL(ab_gkr_main_cont_fused_00_narrow_b2, 0x00, 2, false, true, 48, 1024);
AB_GKR_MAIN_CONT_DEFINE_FUSED_IMPL(ab_gkr_main_cont_fused_00_narrow_b2_x01, 0x00, 2, true, true, 0, 1024);
AB_GKR_MAIN_CONT_DEFINE_FUSED_IMPL(ab_gkr_main_cont_fused_01_narrow_b2, 0x01, 2, false, true, 48, 1024);
AB_GKR_MAIN_CONT_DEFINE_FUSED_IMPL(ab_gkr_main_cont_fused_01_narrow_b2_x01, 0x01, 2, true, true, 0, 1024);
AB_GKR_MAIN_CONT_DEFINE_FUSED_IMPL(ab_gkr_main_cont_fused_03_narrow_b2, 0x03, 2, false, true, 48, 1024);
AB_GKR_MAIN_CONT_DEFINE_FUSED_IMPL(ab_gkr_main_cont_fused_03_narrow_b2_x01, 0x03, 2, true, true, 0, 1024);
AB_GKR_MAIN_CONT_DEFINE_FUSED_IMPL(ab_gkr_main_cont_fused_07_narrow_b2, 0x07, 2, false, true, 48, 1024);
AB_GKR_MAIN_CONT_DEFINE_FUSED_IMPL(ab_gkr_main_cont_fused_07_narrow_b2_x01, 0x07, 2, true, true, 0, 1024);
AB_GKR_MAIN_CONT_DEFINE_FUSED_IMPL(ab_gkr_main_cont_fused_13_narrow_b2, 0x13, 2, false, true, 48, 1024);
AB_GKR_MAIN_CONT_DEFINE_FUSED_IMPL(ab_gkr_main_cont_fused_13_narrow_b2_x01, 0x13, 2, true, true, 0, 1024);
AB_GKR_MAIN_CONT_DEFINE_FUSED_IMPL(ab_gkr_main_cont_fused_17_narrow_b2, 0x17, 2, false, true, 48, 1024);
AB_GKR_MAIN_CONT_DEFINE_FUSED_IMPL(ab_gkr_main_cont_fused_17_narrow_b2_x01, 0x17, 2, true, true, 0, 1024);
AB_GKR_MAIN_CONT_DEFINE_FUSED_IMPL(ab_gkr_main_cont_fused_1f_narrow_b2, 0x1f, 2, false, true, 48, 1024);
AB_GKR_MAIN_CONT_DEFINE_FUSED_IMPL(ab_gkr_main_cont_fused_1f_narrow_b2_x01, 0x1f, 2, true, true, 0, 1024);

AB_GKR_MAIN_CONT_DEFINE_WIDE(ab_gkr_main_cont_fold_wide_00_b2, 0x00, false);
AB_GKR_MAIN_CONT_DEFINE_WIDE(ab_gkr_main_cont_fold_wide_00_b2_x01, 0x00, true);
AB_GKR_MAIN_CONT_DEFINE_WIDE(ab_gkr_main_cont_fold_wide_01_b2, 0x01, false);
AB_GKR_MAIN_CONT_DEFINE_WIDE(ab_gkr_main_cont_fold_wide_01_b2_x01, 0x01, true);
AB_GKR_MAIN_CONT_DEFINE_WIDE(ab_gkr_main_cont_fold_wide_03_b2, 0x03, false);
AB_GKR_MAIN_CONT_DEFINE_WIDE(ab_gkr_main_cont_fold_wide_03_b2_x01, 0x03, true);
AB_GKR_MAIN_CONT_DEFINE_WIDE(ab_gkr_main_cont_fold_wide_07_b2, 0x07, false);
AB_GKR_MAIN_CONT_DEFINE_WIDE(ab_gkr_main_cont_fold_wide_07_b2_x01, 0x07, true);
AB_GKR_MAIN_CONT_DEFINE_WIDE(ab_gkr_main_cont_fold_wide_13_b2, 0x13, false);
AB_GKR_MAIN_CONT_DEFINE_WIDE(ab_gkr_main_cont_fold_wide_13_b2_x01, 0x13, true);
AB_GKR_MAIN_CONT_DEFINE_WIDE(ab_gkr_main_cont_fold_wide_17_b2, 0x17, false);
AB_GKR_MAIN_CONT_DEFINE_WIDE(ab_gkr_main_cont_fold_wide_17_b2_x01, 0x17, true);
AB_GKR_MAIN_CONT_DEFINE_WIDE(ab_gkr_main_cont_fold_wide_1f_b2, 0x1f, false);
AB_GKR_MAIN_CONT_DEFINE_WIDE(ab_gkr_main_cont_fold_wide_1f_b2_x01, 0x1f, true);

AB_GKR_MAIN_CONT_DEFINE_LANE8(ab_gkr_main_cont_fold_lane8_00_b2, 0x00, false);
AB_GKR_MAIN_CONT_DEFINE_LANE8(ab_gkr_main_cont_fold_lane8_00_b2_x01, 0x00, true);
AB_GKR_MAIN_CONT_DEFINE_LANE8(ab_gkr_main_cont_fold_lane8_01_b2, 0x01, false);
AB_GKR_MAIN_CONT_DEFINE_LANE8(ab_gkr_main_cont_fold_lane8_01_b2_x01, 0x01, true);
AB_GKR_MAIN_CONT_DEFINE_LANE8(ab_gkr_main_cont_fold_lane8_03_b2, 0x03, false);
AB_GKR_MAIN_CONT_DEFINE_LANE8(ab_gkr_main_cont_fold_lane8_03_b2_x01, 0x03, true);
AB_GKR_MAIN_CONT_DEFINE_LANE8(ab_gkr_main_cont_fold_lane8_07_b2, 0x07, false);
AB_GKR_MAIN_CONT_DEFINE_LANE8(ab_gkr_main_cont_fold_lane8_07_b2_x01, 0x07, true);
AB_GKR_MAIN_CONT_DEFINE_LANE8(ab_gkr_main_cont_fold_lane8_13_b2, 0x13, false);
AB_GKR_MAIN_CONT_DEFINE_LANE8(ab_gkr_main_cont_fold_lane8_13_b2_x01, 0x13, true);
AB_GKR_MAIN_CONT_DEFINE_LANE8(ab_gkr_main_cont_fold_lane8_17_b2, 0x17, false);
AB_GKR_MAIN_CONT_DEFINE_LANE8(ab_gkr_main_cont_fold_lane8_17_b2_x01, 0x17, true);
AB_GKR_MAIN_CONT_DEFINE_LANE8(ab_gkr_main_cont_fold_lane8_1f_b2, 0x1f, false);
AB_GKR_MAIN_CONT_DEFINE_LANE8(ab_gkr_main_cont_fold_lane8_1f_b2_x01, 0x1f, true);

AB_GKR_MAIN_CONT_DEFINE_FUSED(ab_gkr_main_cont_fused_00_b1, 0x00, 1, false);
AB_GKR_MAIN_CONT_DEFINE_FUSED(ab_gkr_main_cont_fused_00_b1_x01, 0x00, 1, true);
AB_GKR_MAIN_CONT_DEFINE_FUSED(ab_gkr_main_cont_fused_01_b1, 0x01, 1, false);
AB_GKR_MAIN_CONT_DEFINE_FUSED(ab_gkr_main_cont_fused_01_b1_x01, 0x01, 1, true);
AB_GKR_MAIN_CONT_DEFINE_FUSED(ab_gkr_main_cont_fused_03_b1, 0x03, 1, false);
AB_GKR_MAIN_CONT_DEFINE_FUSED(ab_gkr_main_cont_fused_03_b1_x01, 0x03, 1, true);
AB_GKR_MAIN_CONT_DEFINE_FUSED(ab_gkr_main_cont_fused_07_b1, 0x07, 1, false);
AB_GKR_MAIN_CONT_DEFINE_FUSED(ab_gkr_main_cont_fused_07_b1_x01, 0x07, 1, true);
AB_GKR_MAIN_CONT_DEFINE_FUSED(ab_gkr_main_cont_fused_13_b1, 0x13, 1, false);
AB_GKR_MAIN_CONT_DEFINE_FUSED(ab_gkr_main_cont_fused_13_b1_x01, 0x13, 1, true);
AB_GKR_MAIN_CONT_DEFINE_FUSED(ab_gkr_main_cont_fused_17_b1, 0x17, 1, false);
AB_GKR_MAIN_CONT_DEFINE_FUSED(ab_gkr_main_cont_fused_17_b1_x01, 0x17, 1, true);
AB_GKR_MAIN_CONT_DEFINE_FUSED(ab_gkr_main_cont_fused_1f_b1, 0x1f, 1, false);
AB_GKR_MAIN_CONT_DEFINE_FUSED(ab_gkr_main_cont_fused_1f_b1_x01, 0x1f, 1, true);

AB_GKR_MAIN_CONT_DEFINE_FUSED(ab_gkr_main_cont_fused_00_b3, 0x00, 3, false);
AB_GKR_MAIN_CONT_DEFINE_FUSED(ab_gkr_main_cont_fused_00_b3_x01, 0x00, 3, true);
AB_GKR_MAIN_CONT_DEFINE_FUSED(ab_gkr_main_cont_fused_01_b3, 0x01, 3, false);
AB_GKR_MAIN_CONT_DEFINE_FUSED(ab_gkr_main_cont_fused_01_b3_x01, 0x01, 3, true);
AB_GKR_MAIN_CONT_DEFINE_FUSED(ab_gkr_main_cont_fused_03_b3, 0x03, 3, false);
AB_GKR_MAIN_CONT_DEFINE_FUSED(ab_gkr_main_cont_fused_03_b3_x01, 0x03, 3, true);
AB_GKR_MAIN_CONT_DEFINE_FUSED(ab_gkr_main_cont_fused_07_b3, 0x07, 3, false);
AB_GKR_MAIN_CONT_DEFINE_FUSED(ab_gkr_main_cont_fused_07_b3_x01, 0x07, 3, true);
AB_GKR_MAIN_CONT_DEFINE_FUSED(ab_gkr_main_cont_fused_13_b3, 0x13, 3, false);
AB_GKR_MAIN_CONT_DEFINE_FUSED(ab_gkr_main_cont_fused_13_b3_x01, 0x13, 3, true);
AB_GKR_MAIN_CONT_DEFINE_FUSED(ab_gkr_main_cont_fused_17_b3, 0x17, 3, false);
AB_GKR_MAIN_CONT_DEFINE_FUSED(ab_gkr_main_cont_fused_17_b3_x01, 0x17, 3, true);
AB_GKR_MAIN_CONT_DEFINE_FUSED(ab_gkr_main_cont_fused_1f_b3, 0x1f, 3, false);
AB_GKR_MAIN_CONT_DEFINE_FUSED(ab_gkr_main_cont_fused_1f_b3_x01, 0x1f, 3, true);

AB_GKR_MAIN_CONT_DEFINE_FUSED(ab_gkr_main_cont_fused_00_unpacked_b2, 0x00, 2, false);
AB_GKR_MAIN_CONT_DEFINE_FUSED(ab_gkr_main_cont_fused_00_unpacked_b2_x01, 0x00, 2, true);
AB_GKR_MAIN_CONT_DEFINE_FUSED(ab_gkr_main_cont_fused_01_unpacked_b2, 0x01, 2, false);
AB_GKR_MAIN_CONT_DEFINE_FUSED(ab_gkr_main_cont_fused_01_unpacked_b2_x01, 0x01, 2, true);
AB_GKR_MAIN_CONT_DEFINE_FUSED(ab_gkr_main_cont_fused_03_unpacked_b2, 0x03, 2, false);
AB_GKR_MAIN_CONT_DEFINE_FUSED(ab_gkr_main_cont_fused_03_unpacked_b2_x01, 0x03, 2, true);
AB_GKR_MAIN_CONT_DEFINE_FUSED(ab_gkr_main_cont_fused_07_unpacked_b2, 0x07, 2, false);
AB_GKR_MAIN_CONT_DEFINE_FUSED(ab_gkr_main_cont_fused_07_unpacked_b2_x01, 0x07, 2, true);
AB_GKR_MAIN_CONT_DEFINE_FUSED(ab_gkr_main_cont_fused_13_unpacked_b2, 0x13, 2, false);
AB_GKR_MAIN_CONT_DEFINE_FUSED(ab_gkr_main_cont_fused_13_unpacked_b2_x01, 0x13, 2, true);
AB_GKR_MAIN_CONT_DEFINE_FUSED(ab_gkr_main_cont_fused_17_unpacked_b2, 0x17, 2, false);
AB_GKR_MAIN_CONT_DEFINE_FUSED(ab_gkr_main_cont_fused_17_unpacked_b2_x01, 0x17, 2, true);
AB_GKR_MAIN_CONT_DEFINE_FUSED(ab_gkr_main_cont_fused_1f_unpacked_b2, 0x1f, 2, false);
AB_GKR_MAIN_CONT_DEFINE_FUSED(ab_gkr_main_cont_fused_1f_unpacked_b2_x01, 0x1f, 2, true);

// Retained 128-bit split reference; production uses paired reads.
AB_GKR_BWD_MAIN_CONT_WINDOW_DEFINE_KERNEL_IMPL(ab_gkr_main_cont_split_00_unpacked_b4, 0x00, 4, false);
AB_GKR_BWD_MAIN_CONT_WINDOW_DEFINE_X01_KERNEL_IMPL(ab_gkr_main_cont_split_00_unpacked_b4_x01, 0x00, 4, false);
AB_GKR_BWD_MAIN_CONT_WINDOW_DEFINE_KERNEL_IMPL(ab_gkr_main_cont_split_01_unpacked_b4, 0x01, 4, false);
AB_GKR_BWD_MAIN_CONT_WINDOW_DEFINE_X01_KERNEL_IMPL(ab_gkr_main_cont_split_01_unpacked_b4_x01, 0x01, 4, false);
AB_GKR_BWD_MAIN_CONT_WINDOW_DEFINE_KERNEL_IMPL(ab_gkr_main_cont_split_03_unpacked_b4, 0x03, 4, false);
AB_GKR_BWD_MAIN_CONT_WINDOW_DEFINE_X01_KERNEL_IMPL(ab_gkr_main_cont_split_03_unpacked_b4_x01, 0x03, 4, false);
AB_GKR_BWD_MAIN_CONT_WINDOW_DEFINE_KERNEL_IMPL(ab_gkr_main_cont_split_07_unpacked_b4, 0x07, 4, false);
AB_GKR_BWD_MAIN_CONT_WINDOW_DEFINE_X01_KERNEL_IMPL(ab_gkr_main_cont_split_07_unpacked_b4_x01, 0x07, 4, false);
AB_GKR_BWD_MAIN_CONT_WINDOW_DEFINE_KERNEL_IMPL(ab_gkr_main_cont_split_13_unpacked_b4, 0x13, 4, false);
AB_GKR_BWD_MAIN_CONT_WINDOW_DEFINE_X01_KERNEL_IMPL(ab_gkr_main_cont_split_13_unpacked_b4_x01, 0x13, 4, false);
AB_GKR_BWD_MAIN_CONT_WINDOW_DEFINE_KERNEL_IMPL(ab_gkr_main_cont_split_17_unpacked_b4, 0x17, 4, false);
AB_GKR_BWD_MAIN_CONT_WINDOW_DEFINE_X01_KERNEL_IMPL(ab_gkr_main_cont_split_17_unpacked_b4_x01, 0x17, 4, false);
AB_GKR_BWD_MAIN_CONT_WINDOW_DEFINE_KERNEL_IMPL(ab_gkr_main_cont_split_1f_unpacked_b4, 0x1f, 4, false);
AB_GKR_BWD_MAIN_CONT_WINDOW_DEFINE_X01_KERNEL_IMPL(ab_gkr_main_cont_split_1f_unpacked_b4_x01, 0x1f, 4, false);

// One pacing point per 16 three-word VM records, including grouped members.
AB_GKR_MAIN_CONT_DEFINE_FUSED_IMPL(ab_gkr_main_cont_fused_00_pace16_b2, 0x00, 2, false, true, 48, 0);
AB_GKR_MAIN_CONT_DEFINE_FUSED_IMPL(ab_gkr_main_cont_fused_00_pace16_b2_x01, 0x00, 2, true, true, 48, 0);
AB_GKR_MAIN_CONT_DEFINE_FUSED_IMPL(ab_gkr_main_cont_fused_01_pace16_b2, 0x01, 2, false, true, 48, 0);
AB_GKR_MAIN_CONT_DEFINE_FUSED_IMPL(ab_gkr_main_cont_fused_01_pace16_b2_x01, 0x01, 2, true, true, 48, 0);
AB_GKR_MAIN_CONT_DEFINE_FUSED_IMPL(ab_gkr_main_cont_fused_03_pace16_b2, 0x03, 2, false, true, 48, 0);
AB_GKR_MAIN_CONT_DEFINE_FUSED_IMPL(ab_gkr_main_cont_fused_03_pace16_b2_x01, 0x03, 2, true, true, 48, 0);
AB_GKR_MAIN_CONT_DEFINE_FUSED_IMPL(ab_gkr_main_cont_fused_07_pace16_b2, 0x07, 2, false, true, 48, 0);
AB_GKR_MAIN_CONT_DEFINE_FUSED_IMPL(ab_gkr_main_cont_fused_07_pace16_b2_x01, 0x07, 2, true, true, 48, 0);
AB_GKR_MAIN_CONT_DEFINE_FUSED_IMPL(ab_gkr_main_cont_fused_13_pace16_b2, 0x13, 2, false, true, 48, 0);
AB_GKR_MAIN_CONT_DEFINE_FUSED_IMPL(ab_gkr_main_cont_fused_13_pace16_b2_x01, 0x13, 2, true, true, 48, 0);
AB_GKR_MAIN_CONT_DEFINE_FUSED_IMPL(ab_gkr_main_cont_fused_17_pace16_b2, 0x17, 2, false, true, 48, 0);
AB_GKR_MAIN_CONT_DEFINE_FUSED_IMPL(ab_gkr_main_cont_fused_17_pace16_b2_x01, 0x17, 2, true, true, 48, 0);
AB_GKR_MAIN_CONT_DEFINE_FUSED_IMPL(ab_gkr_main_cont_fused_1f_pace16_b2, 0x1f, 2, false, true, 48, 0);
AB_GKR_MAIN_CONT_DEFINE_FUSED_IMPL(ab_gkr_main_cont_fused_1f_pace16_b2_x01, 0x1f, 2, true, true, 48, 0);

// Retained packed, unpaced reference; production dynamic-X0 uses the runtime gate.
AB_GKR_MAIN_CONT_DEFINE_FUSED_IMPL(ab_gkr_main_cont_fused_00_unpaced_b2, 0x00, 2, false, true, 0, 0);
AB_GKR_MAIN_CONT_DEFINE_FUSED_IMPL(ab_gkr_main_cont_fused_01_unpaced_b2, 0x01, 2, false, true, 0, 0);
AB_GKR_MAIN_CONT_DEFINE_FUSED_IMPL(ab_gkr_main_cont_fused_03_unpaced_b2, 0x03, 2, false, true, 0, 0);
AB_GKR_MAIN_CONT_DEFINE_FUSED_IMPL(ab_gkr_main_cont_fused_07_unpaced_b2, 0x07, 2, false, true, 0, 0);
AB_GKR_MAIN_CONT_DEFINE_FUSED_IMPL(ab_gkr_main_cont_fused_13_unpaced_b2, 0x13, 2, false, true, 0, 0);
AB_GKR_MAIN_CONT_DEFINE_FUSED_IMPL(ab_gkr_main_cont_fused_17_unpaced_b2, 0x17, 2, false, true, 0, 0);
AB_GKR_MAIN_CONT_DEFINE_FUSED_IMPL(ab_gkr_main_cont_fused_1f_unpaced_b2, 0x1f, 2, false, true, 0, 0);

} // namespace airbender::gkr::backward

// Bit flags avoid counter overflow even for a completely poisoned large arena.
EXTERN __global__ void ab_gkr_main_cont_fused_compare(const u32 *expected, const u32 *actual, const u32 limbs, u32 *status, const u32 inject) {
  const u32 i = blockIdx.x * blockDim.x + threadIdx.x;
  if (i >= limbs)
    return;
  const u32 value = actual[i] ^ ((inject && i == 0) ? 1u : 0u);
  u32 flags = expected[i] != value ? 1u : 0u;
  if (actual[i] == 0xa5a5a5a5u)
    flags |= 2u;
  if (flags)
    atomicOr(status, flags);
}
