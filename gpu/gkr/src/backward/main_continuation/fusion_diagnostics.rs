//! Feature-only continuation fusion diagnostics. All scheduling remains enqueue-only;
//! counter readback happens in `finish`, after the proof job has completed.
use super::*;
use era_cudart::event::{elapsed_time, CudaEvent};
use era_cudart::memory::{memory_copy_async, memory_set_async};
use era_cudart::slice::DeviceSlice;
use gpu_core::primitives::context::DeviceAllocation;
use std::cell::RefCell;
use std::io::Write;
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_x1_reference_00_dynamic(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_x1_reference_01_dynamic(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_x1_reference_03_dynamic(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_x1_reference_07_dynamic(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_x1_reference_13_dynamic(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_x1_reference_17_dynamic(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_x1_reference_1f_dynamic(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_x1_fused_00_dynamic(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_x1_split_00_dynamic(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_x1_fused_00_static(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_x1_split_00_static(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_x1_fused_01_dynamic(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_x1_split_01_dynamic(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_x1_fused_01_static(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_x1_split_01_static(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_x1_fused_03_dynamic(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_x1_split_03_dynamic(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_x1_fused_03_static(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_x1_split_03_static(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_x1_fused_07_dynamic(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_x1_split_07_dynamic(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_x1_fused_07_static(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_x1_split_07_static(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_x1_fused_13_dynamic(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_x1_split_13_dynamic(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_x1_fused_13_static(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_x1_split_13_static(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_x1_fused_17_dynamic(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_x1_split_17_dynamic(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_x1_fused_17_static(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_x1_split_17_static(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_x1_fused_1f_dynamic(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_x1_split_1f_dynamic(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_x1_fused_1f_static(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_x1_split_1f_static(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_split_reference_00_b4(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_split_reference_01_b4(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_split_reference_03_b4(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_split_reference_07_b4(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_split_reference_13_b4(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_split_reference_17_b4(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_split_reference_1f_b4(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_split_compact_00_b4(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_split_compact_01_b4(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_split_compact_03_b4(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_split_compact_07_b4(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_split_compact_13_b4(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_split_compact_17_b4(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_split_compact_1f_b4(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_static_reference_00_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_static_reference_01_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_static_reference_03_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_static_reference_07_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_static_reference_13_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_static_reference_17_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_static_reference_1f_b2(desc: MainContinuationWindowLaunchBinding));

era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_compact_00_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_compact_01_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_compact_03_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_compact_07_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_compact_13_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_compact_17_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_compact_1f_b2(desc: MainContinuationWindowLaunchBinding));

era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_00_narrow_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_00_narrow_b2_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_01_narrow_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_01_narrow_b2_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_03_narrow_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_03_narrow_b2_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_07_narrow_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_07_narrow_b2_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_13_narrow_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_13_narrow_b2_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_17_narrow_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_17_narrow_b2_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_1f_narrow_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_1f_narrow_b2_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fold_wide_00_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fold_wide_00_b2_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fold_wide_01_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fold_wide_01_b2_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fold_wide_03_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fold_wide_03_b2_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fold_wide_07_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fold_wide_07_b2_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fold_wide_13_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fold_wide_13_b2_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fold_wide_17_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fold_wide_17_b2_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fold_wide_1f_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fold_wide_1f_b2_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fold_wide_publish(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fold_lane8_00_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fold_lane8_00_b2_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fold_lane8_01_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fold_lane8_01_b2_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fold_lane8_03_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fold_lane8_03_b2_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fold_lane8_07_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fold_lane8_07_b2_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fold_lane8_13_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fold_lane8_13_b2_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fold_lane8_17_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fold_lane8_17_b2_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fold_lane8_1f_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fold_lane8_1f_b2_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fold_lane8_publish(desc: MainContinuationWindowLaunchBinding));

era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_00_b1(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_00_b1_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_00_unpacked_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_00_unpacked_b2_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_01_b1(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_01_b1_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_01_unpacked_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_01_unpacked_b2_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_03_b1(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_03_b1_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_03_unpacked_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_03_unpacked_b2_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_07_b1(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_07_b1_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_07_unpacked_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_07_unpacked_b2_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_13_b1(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_13_b1_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_13_unpacked_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_13_unpacked_b2_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_17_b1(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_17_b1_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_17_unpacked_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_17_unpacked_b2_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_1f_b1(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_1f_b1_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_1f_unpacked_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_1f_unpacked_b2_x01(desc: MainContinuationWindowLaunchBinding));

era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_00_b3(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_00_b3_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_01_b3(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_01_b3_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_03_b3(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_03_b3_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_07_b3(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_07_b3_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_13_b3(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_13_b3_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_17_b3(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_17_b3_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_1f_b3(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_1f_b3_x01(desc: MainContinuationWindowLaunchBinding));

era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_00_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_00_b2_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_01_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_01_b2_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_03_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_03_b2_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_07_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_07_b2_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_13_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_13_b2_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_17_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_17_b2_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_1f_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_1f_b2_x01(desc: MainContinuationWindowLaunchBinding));

era_cudart::cuda_kernel!(Compare, ab_gkr_main_cont_fused_compare(
    expected: *const u32, actual: *const u32, limbs: u32, status: *mut u32, inject: u32
));

era_cudart::cuda_kernel_declaration!(ab_gkr_bwd_main_cont_window3_shape_00_b4_kernel(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_bwd_main_cont_window3_shape_00_b4_x01_kernel(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_bwd_main_cont_window3_shape_01_b4_kernel(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_bwd_main_cont_window3_shape_01_b4_x01_kernel(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_bwd_main_cont_window3_shape_03_b4_kernel(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_bwd_main_cont_window3_shape_03_b4_x01_kernel(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_bwd_main_cont_window3_shape_07_b4_kernel(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_bwd_main_cont_window3_shape_07_b4_x01_kernel(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_bwd_main_cont_window3_shape_13_b4_kernel(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_bwd_main_cont_window3_shape_13_b4_x01_kernel(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_bwd_main_cont_window3_shape_17_b4_kernel(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_bwd_main_cont_window3_shape_17_b4_x01_kernel(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_bwd_main_cont_window3_shape_1f_b4_kernel(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_bwd_main_cont_window3_shape_1f_b4_x01_kernel(desc: MainContinuationWindowLaunchBinding));

era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_split_00_unpacked_b4(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_split_00_unpacked_b4_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_split_01_unpacked_b4(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_split_01_unpacked_b4_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_split_03_unpacked_b4(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_split_03_unpacked_b4_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_split_07_unpacked_b4(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_split_07_unpacked_b4_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_split_13_unpacked_b4(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_split_13_unpacked_b4_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_split_17_unpacked_b4(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_split_17_unpacked_b4_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_split_1f_unpacked_b4(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_split_1f_unpacked_b4_x01(desc: MainContinuationWindowLaunchBinding));

era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_00_pace16_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_00_pace16_b2_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_01_pace16_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_01_pace16_b2_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_03_pace16_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_03_pace16_b2_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_07_pace16_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_07_pace16_b2_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_13_pace16_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_13_pace16_b2_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_17_pace16_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_17_pace16_b2_x01(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_1f_pace16_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_1f_pace16_b2_x01(desc: MainContinuationWindowLaunchBinding));

era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_00_unpaced_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_01_unpaced_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_03_unpaced_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_07_unpaced_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_13_unpaced_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_17_unpaced_b2(desc: MainContinuationWindowLaunchBinding));
era_cudart::cuda_kernel_declaration!(ab_gkr_main_cont_fused_1f_unpaced_b2(desc: MainContinuationWindowLaunchBinding));

fn resolve(mask: u16, bound: u32, x01: bool) -> MainContinuationWindowEvaluatorKernel {
    // Forced current production bodies for selector/fusion crossovers.
    match bound {
        19 => return resolve(mask, 17, false),
        20 => return resolve(mask, 17, true),
        21 => return resolve(mask, 5, false),
        22 => return resolve(mask, 18, true),
        _ => {}
    }
    if bound == 15 && !x01 {
        return resolve(mask, 12, false);
    }
    // Reuse the existing packed kernels; no extra native specialization.
    if bound == 6 || bound == 7 {
        return resolve(mask, 4, bound == 7);
    }
    if bound == 11 || bound == 13 {
        return resolve(mask, 5, x01);
    }
    let symbol: GkrBwdMainContinuationWindow3Signature = match (mask, bound, x01) {
        (0x00, 17, false) => ab_gkr_main_cont_fused_00_b2,
        (0x00, 18, false) => ab_gkr_main_cont_x1_split_00_dynamic,
        (0x00, 17, true) => ab_gkr_main_cont_fused_00_b2_x01,
        (0x00, 18, true) => ab_gkr_bwd_main_cont_window3_shape_00_b4_x01_kernel,
        (0x01, 17, false) => ab_gkr_main_cont_fused_01_b2,
        (0x01, 18, false) => ab_gkr_main_cont_x1_split_01_dynamic,
        (0x01, 17, true) => ab_gkr_main_cont_fused_01_b2_x01,
        (0x01, 18, true) => ab_gkr_bwd_main_cont_window3_shape_01_b4_x01_kernel,
        (0x03, 17, false) => ab_gkr_main_cont_fused_03_b2,
        (0x03, 18, false) => ab_gkr_main_cont_x1_split_03_dynamic,
        (0x03, 17, true) => ab_gkr_main_cont_fused_03_b2_x01,
        (0x03, 18, true) => ab_gkr_bwd_main_cont_window3_shape_03_b4_x01_kernel,
        (0x07, 17, false) => ab_gkr_main_cont_fused_07_b2,
        (0x07, 18, false) => ab_gkr_main_cont_x1_split_07_dynamic,
        (0x07, 17, true) => ab_gkr_main_cont_fused_07_b2_x01,
        (0x07, 18, true) => ab_gkr_bwd_main_cont_window3_shape_07_b4_x01_kernel,
        (0x13, 17, false) => ab_gkr_main_cont_fused_13_b2,
        (0x13, 18, false) => ab_gkr_main_cont_x1_split_13_dynamic,
        (0x13, 17, true) => ab_gkr_main_cont_fused_13_b2_x01,
        (0x13, 18, true) => ab_gkr_bwd_main_cont_window3_shape_13_b4_x01_kernel,
        (0x17, 17, false) => ab_gkr_main_cont_fused_17_b2,
        (0x17, 18, false) => ab_gkr_main_cont_x1_split_17_dynamic,
        (0x17, 17, true) => ab_gkr_main_cont_fused_17_b2_x01,
        (0x17, 18, true) => ab_gkr_bwd_main_cont_window3_shape_17_b4_x01_kernel,
        (0x1f, 17, false) => ab_gkr_main_cont_fused_1f_b2,
        (0x1f, 18, false) => ab_gkr_main_cont_x1_split_1f_dynamic,
        (0x1f, 17, true) => ab_gkr_main_cont_fused_1f_b2_x01,
        (0x1f, 18, true) => ab_gkr_bwd_main_cont_window3_shape_1f_b4_x01_kernel,
        (0x00, 15, true) => ab_gkr_main_cont_static_reference_00_b2,
        (0x01, 15, true) => ab_gkr_main_cont_static_reference_01_b2,
        (0x03, 15, true) => ab_gkr_main_cont_static_reference_03_b2,
        (0x07, 15, true) => ab_gkr_main_cont_static_reference_07_b2,
        (0x13, 15, true) => ab_gkr_main_cont_static_reference_13_b2,
        (0x17, 15, true) => ab_gkr_main_cont_static_reference_17_b2,
        (0x1f, 15, true) => ab_gkr_main_cont_static_reference_1f_b2,

        (0x00, 16, true) => ab_gkr_main_cont_split_compact_00_b4,
        (0x00, 16, _) => ab_gkr_main_cont_split_compact_00_b4,
        (0x01, 16, true) => ab_gkr_main_cont_split_compact_01_b4,
        (0x01, 16, _) => ab_gkr_main_cont_split_compact_01_b4,
        (0x03, 16, true) => ab_gkr_main_cont_split_compact_03_b4,
        (0x03, 16, _) => ab_gkr_main_cont_split_compact_03_b4,
        (0x07, 16, true) => ab_gkr_main_cont_split_compact_07_b4,
        (0x07, 16, _) => ab_gkr_main_cont_split_compact_07_b4,
        (0x13, 16, true) => ab_gkr_main_cont_split_compact_13_b4,
        (0x13, 16, _) => ab_gkr_main_cont_split_compact_13_b4,
        (0x17, 16, true) => ab_gkr_main_cont_split_compact_17_b4,
        (0x17, 16, _) => ab_gkr_main_cont_split_compact_17_b4,
        (0x1f, 16, true) => ab_gkr_main_cont_split_compact_1f_b4,
        (0x1f, 16, _) => ab_gkr_main_cont_split_compact_1f_b4,
        (0x00, 14, _) => ab_gkr_main_cont_compact_00_b2,
        (0x01, 14, _) => ab_gkr_main_cont_compact_01_b2,
        (0x03, 14, _) => ab_gkr_main_cont_compact_03_b2,
        (0x07, 14, _) => ab_gkr_main_cont_compact_07_b2,
        (0x13, 14, _) => ab_gkr_main_cont_compact_13_b2,
        (0x17, 14, _) => ab_gkr_main_cont_compact_17_b2,
        (0x1f, 14, _) => ab_gkr_main_cont_compact_1f_b2,

        (0x00, 12, false) => ab_gkr_main_cont_x1_reference_00_dynamic,
        (0x00, 12, true) => ab_gkr_main_cont_compact_00_b2,
        (0x01, 12, false) => ab_gkr_main_cont_x1_reference_01_dynamic,
        (0x01, 12, true) => ab_gkr_main_cont_compact_01_b2,
        (0x03, 12, false) => ab_gkr_main_cont_x1_reference_03_dynamic,
        (0x03, 12, true) => ab_gkr_main_cont_compact_03_b2,
        (0x07, 12, false) => ab_gkr_main_cont_x1_reference_07_dynamic,
        (0x07, 12, true) => ab_gkr_main_cont_compact_07_b2,
        (0x13, 12, false) => ab_gkr_main_cont_x1_reference_13_dynamic,
        (0x13, 12, true) => ab_gkr_main_cont_compact_13_b2,
        (0x17, 12, false) => ab_gkr_main_cont_x1_reference_17_dynamic,
        (0x17, 12, true) => ab_gkr_main_cont_compact_17_b2,
        (0x1f, 12, false) => ab_gkr_main_cont_x1_reference_1f_dynamic,
        (0x1f, 12, true) => ab_gkr_main_cont_compact_1f_b2,
        (0x00, 10, false) => ab_gkr_main_cont_fold_lane8_00_b2,
        (0x00, 10, true) => ab_gkr_main_cont_fold_lane8_00_b2_x01,
        (0x01, 10, false) => ab_gkr_main_cont_fold_lane8_01_b2,
        (0x01, 10, true) => ab_gkr_main_cont_fold_lane8_01_b2_x01,
        (0x03, 10, false) => ab_gkr_main_cont_fold_lane8_03_b2,
        (0x03, 10, true) => ab_gkr_main_cont_fold_lane8_03_b2_x01,
        (0x07, 10, false) => ab_gkr_main_cont_fold_lane8_07_b2,
        (0x07, 10, true) => ab_gkr_main_cont_fold_lane8_07_b2_x01,
        (0x13, 10, false) => ab_gkr_main_cont_fold_lane8_13_b2,
        (0x13, 10, true) => ab_gkr_main_cont_fold_lane8_13_b2_x01,
        (0x17, 10, false) => ab_gkr_main_cont_fold_lane8_17_b2,
        (0x17, 10, true) => ab_gkr_main_cont_fold_lane8_17_b2_x01,
        (0x1f, 10, false) => ab_gkr_main_cont_fold_lane8_1f_b2,
        (0x1f, 10, true) => ab_gkr_main_cont_fold_lane8_1f_b2_x01,
        (0x00, 9, false) => ab_gkr_main_cont_fused_00_narrow_b2,
        (0x00, 9, true) => ab_gkr_main_cont_fused_00_narrow_b2_x01,
        (0x01, 9, false) => ab_gkr_main_cont_fused_01_narrow_b2,
        (0x01, 9, true) => ab_gkr_main_cont_fused_01_narrow_b2_x01,
        (0x03, 9, false) => ab_gkr_main_cont_fused_03_narrow_b2,
        (0x03, 9, true) => ab_gkr_main_cont_fused_03_narrow_b2_x01,
        (0x07, 9, false) => ab_gkr_main_cont_fused_07_narrow_b2,
        (0x07, 9, true) => ab_gkr_main_cont_fused_07_narrow_b2_x01,
        (0x13, 9, false) => ab_gkr_main_cont_fused_13_narrow_b2,
        (0x13, 9, true) => ab_gkr_main_cont_fused_13_narrow_b2_x01,
        (0x17, 9, false) => ab_gkr_main_cont_fused_17_narrow_b2,
        (0x17, 9, true) => ab_gkr_main_cont_fused_17_narrow_b2_x01,
        (0x1f, 9, false) => ab_gkr_main_cont_fused_1f_narrow_b2,
        (0x1f, 9, true) => ab_gkr_main_cont_fused_1f_narrow_b2_x01,
        (0x00, 8, false) => ab_gkr_main_cont_fused_00_pace16_b2,
        (0x00, 8, true) => ab_gkr_main_cont_fused_00_pace16_b2_x01,
        (0x01, 8, false) => ab_gkr_main_cont_fused_01_pace16_b2,
        (0x01, 8, true) => ab_gkr_main_cont_fused_01_pace16_b2_x01,
        (0x03, 8, false) => ab_gkr_main_cont_fused_03_pace16_b2,
        (0x03, 8, true) => ab_gkr_main_cont_fused_03_pace16_b2_x01,
        (0x07, 8, false) => ab_gkr_main_cont_fused_07_pace16_b2,
        (0x07, 8, true) => ab_gkr_main_cont_fused_07_pace16_b2_x01,
        (0x13, 8, false) => ab_gkr_main_cont_fused_13_pace16_b2,
        (0x13, 8, true) => ab_gkr_main_cont_fused_13_pace16_b2_x01,
        (0x17, 8, false) => ab_gkr_main_cont_fused_17_pace16_b2,
        (0x17, 8, true) => ab_gkr_main_cont_fused_17_pace16_b2_x01,
        (0x1f, 8, false) => ab_gkr_main_cont_fused_1f_pace16_b2,
        (0x1f, 8, true) => ab_gkr_main_cont_fused_1f_pace16_b2_x01,
        (0x00, 1, false) => ab_gkr_main_cont_fused_00_b1,
        (0x00, 1, true) => ab_gkr_main_cont_fused_00_b1_x01,
        (0x00, 2, false) => ab_gkr_main_cont_fused_00_unpacked_b2,
        (0x00, 2, true) => ab_gkr_main_cont_fused_00_unpacked_b2_x01,
        (0x01, 1, false) => ab_gkr_main_cont_fused_01_b1,
        (0x01, 1, true) => ab_gkr_main_cont_fused_01_b1_x01,
        (0x01, 2, false) => ab_gkr_main_cont_fused_01_unpacked_b2,
        (0x01, 2, true) => ab_gkr_main_cont_fused_01_unpacked_b2_x01,
        (0x03, 1, false) => ab_gkr_main_cont_fused_03_b1,
        (0x03, 1, true) => ab_gkr_main_cont_fused_03_b1_x01,
        (0x03, 2, false) => ab_gkr_main_cont_fused_03_unpacked_b2,
        (0x03, 2, true) => ab_gkr_main_cont_fused_03_unpacked_b2_x01,
        (0x07, 1, false) => ab_gkr_main_cont_fused_07_b1,
        (0x07, 1, true) => ab_gkr_main_cont_fused_07_b1_x01,
        (0x07, 2, false) => ab_gkr_main_cont_fused_07_unpacked_b2,
        (0x07, 2, true) => ab_gkr_main_cont_fused_07_unpacked_b2_x01,
        (0x13, 1, false) => ab_gkr_main_cont_fused_13_b1,
        (0x13, 1, true) => ab_gkr_main_cont_fused_13_b1_x01,
        (0x13, 2, false) => ab_gkr_main_cont_fused_13_unpacked_b2,
        (0x13, 2, true) => ab_gkr_main_cont_fused_13_unpacked_b2_x01,
        (0x17, 1, false) => ab_gkr_main_cont_fused_17_b1,
        (0x17, 1, true) => ab_gkr_main_cont_fused_17_b1_x01,
        (0x17, 2, false) => ab_gkr_main_cont_fused_17_unpacked_b2,
        (0x17, 2, true) => ab_gkr_main_cont_fused_17_unpacked_b2_x01,
        (0x1f, 1, false) => ab_gkr_main_cont_fused_1f_b1,
        (0x1f, 1, true) => ab_gkr_main_cont_fused_1f_b1_x01,
        (0x1f, 2, false) => ab_gkr_main_cont_fused_1f_unpacked_b2,
        (0x1f, 2, true) => ab_gkr_main_cont_fused_1f_unpacked_b2_x01,
        (0x00, 3, false) => ab_gkr_main_cont_fused_00_b3,
        (0x00, 3, true) => ab_gkr_main_cont_fused_00_b3_x01,
        (0x01, 3, false) => ab_gkr_main_cont_fused_01_b3,
        (0x01, 3, true) => ab_gkr_main_cont_fused_01_b3_x01,
        (0x03, 3, false) => ab_gkr_main_cont_fused_03_b3,
        (0x03, 3, true) => ab_gkr_main_cont_fused_03_b3_x01,
        (0x07, 3, false) => ab_gkr_main_cont_fused_07_b3,
        (0x07, 3, true) => ab_gkr_main_cont_fused_07_b3_x01,
        (0x13, 3, false) => ab_gkr_main_cont_fused_13_b3,
        (0x13, 3, true) => ab_gkr_main_cont_fused_13_b3_x01,
        (0x17, 3, false) => ab_gkr_main_cont_fused_17_b3,
        (0x17, 3, true) => ab_gkr_main_cont_fused_17_b3_x01,
        (0x1f, 3, false) => ab_gkr_main_cont_fused_1f_b3,
        (0x1f, 3, true) => ab_gkr_main_cont_fused_1f_b3_x01,
        (0x00, 4, false) => ab_gkr_main_cont_fused_00_unpaced_b2,
        (0x00, 4, true) => ab_gkr_main_cont_fused_00_narrow_b2_x01,
        (0x01, 4, false) => ab_gkr_main_cont_fused_01_unpaced_b2,
        (0x01, 4, true) => ab_gkr_main_cont_fused_01_narrow_b2_x01,
        (0x03, 4, false) => ab_gkr_main_cont_fused_03_unpaced_b2,
        (0x03, 4, true) => ab_gkr_main_cont_fused_03_narrow_b2_x01,
        (0x07, 4, false) => ab_gkr_main_cont_fused_07_unpaced_b2,
        (0x07, 4, true) => ab_gkr_main_cont_fused_07_narrow_b2_x01,
        (0x13, 4, false) => ab_gkr_main_cont_fused_13_unpaced_b2,
        (0x13, 4, true) => ab_gkr_main_cont_fused_13_narrow_b2_x01,
        (0x17, 4, false) => ab_gkr_main_cont_fused_17_unpaced_b2,
        (0x17, 4, true) => ab_gkr_main_cont_fused_17_narrow_b2_x01,
        (0x1f, 4, false) => ab_gkr_main_cont_fused_1f_unpaced_b2,
        (0x1f, 4, true) => ab_gkr_main_cont_fused_1f_narrow_b2_x01,
        (0x00, 5, false) => ab_gkr_bwd_main_cont_window3_shape_00_b4_kernel,
        (0x00, 5, true) => ab_gkr_main_cont_split_reference_00_b4,
        (0x01, 5, false) => ab_gkr_bwd_main_cont_window3_shape_01_b4_kernel,
        (0x01, 5, true) => ab_gkr_main_cont_split_reference_01_b4,
        (0x03, 5, false) => ab_gkr_bwd_main_cont_window3_shape_03_b4_kernel,
        (0x03, 5, true) => ab_gkr_main_cont_split_reference_03_b4,
        (0x07, 5, false) => ab_gkr_bwd_main_cont_window3_shape_07_b4_kernel,
        (0x07, 5, true) => ab_gkr_main_cont_split_reference_07_b4,
        (0x13, 5, false) => ab_gkr_bwd_main_cont_window3_shape_13_b4_kernel,
        (0x13, 5, true) => ab_gkr_main_cont_split_reference_13_b4,
        (0x17, 5, false) => ab_gkr_bwd_main_cont_window3_shape_17_b4_kernel,
        (0x17, 5, true) => ab_gkr_main_cont_split_reference_17_b4,
        (0x1f, 5, false) => ab_gkr_bwd_main_cont_window3_shape_1f_b4_kernel,
        (0x1f, 5, true) => ab_gkr_main_cont_split_reference_1f_b4,
        (0x00, 0, false) => ab_gkr_main_cont_split_00_unpacked_b4,
        (0x00, 0, true) => ab_gkr_main_cont_split_00_unpacked_b4_x01,
        (0x01, 0, false) => ab_gkr_main_cont_split_01_unpacked_b4,
        (0x01, 0, true) => ab_gkr_main_cont_split_01_unpacked_b4_x01,
        (0x03, 0, false) => ab_gkr_main_cont_split_03_unpacked_b4,
        (0x03, 0, true) => ab_gkr_main_cont_split_03_unpacked_b4_x01,
        (0x07, 0, false) => ab_gkr_main_cont_split_07_unpacked_b4,
        (0x07, 0, true) => ab_gkr_main_cont_split_07_unpacked_b4_x01,
        (0x13, 0, false) => ab_gkr_main_cont_split_13_unpacked_b4,
        (0x13, 0, true) => ab_gkr_main_cont_split_13_unpacked_b4_x01,
        (0x17, 0, false) => ab_gkr_main_cont_split_17_unpacked_b4,
        (0x17, 0, true) => ab_gkr_main_cont_split_17_unpacked_b4_x01,
        (0x1f, 0, false) => ab_gkr_main_cont_split_1f_unpacked_b4,
        (0x1f, 0, true) => ab_gkr_main_cont_split_1f_unpacked_b4_x01,
        _ => panic!("unsupported fused continuation entry: {mask:x} b{bound} x01={x01}"),
    };
    MainContinuationWindowEvaluatorKernel(symbol)
}

struct Pass {
    layer: usize,
    round: usize,
    mask: u16,
    words: u16,
    row_tiles: usize,
    publication_cells: usize,
    tensor_cells: usize,
}
struct Sample {
    pass: usize,
    iteration: usize,
    position: usize,
    bound: u32,
    start: CudaEvent,
    end: CudaEvent,
}
struct Timing {
    arms_override: Option<[u32; 2]>,
    split_packed: bool,
    compare_x0: bool,
    pacing: bool,
    gated: bool,
    crossover: bool,
    fold_trial: bool,
    wide_trial: bool,
    compact_trial: bool,
    split_compact_trial: bool,
    x1_trial: bool,
    current_selector: bool,
    current_fusion: bool,
    coordinates: Vec<(usize, usize)>,
    samples: Vec<Sample>,
    output: String,
    session: usize,
}
struct State {
    split_packed: bool,
    compare_x0: bool,
    pacing: bool,
    gated: bool,
    crossover: bool,
    fold_trial: bool,
    wide_trial: bool,
    compact_trial: bool,
    split_compact_trial: bool,
    x1_trial: bool,
    current_selector: bool,
    current_fusion: bool,
    status: DeviceAllocation<u32>,
    passes: Vec<Pass>,
    coordinate: Option<(usize, usize)>,
    timing: Option<Timing>,
}

/// Actual enqueue choices for the feature-only whole-proof policy experiment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PolicyPass {
    pub layer: usize,
    pub round: usize,
    pub tiles: usize,
    pub min_tiles: usize,
    pub canonical_input: bool,
    pub fused: bool,
    pub packed: bool,
    pub split_packed: bool,
    pub words: usize,
    pub static_x0: bool,
    pub gated: bool,
    pub paced: bool,
    pub fold_candidate: bool,
    pub fold_arm: u32,
}

struct Policy {
    candidate: bool,
    packed_comparison: bool,
    split_comparison: bool,
    gated_comparison: bool,
    canonical_comparison: bool,
    fold_comparison: bool,
    wide_comparison: u8,
    compact_comparison: bool,
    split_compact_comparison: bool,
    x1_comparison: bool,
    current_comparison: bool,
    candidate_words: usize,
    candidate_fused_upper: usize,
    candidate_waves: usize,
    candidate_large_canonical: bool,
    coordinate: Option<(usize, usize)>,
    passes: Vec<PolicyPass>,
}

thread_local! {
    static STATE: RefCell<Option<State>> = const { RefCell::new(None) };
    static POLICY: RefCell<Option<Policy>> = const { RefCell::new(None) };
}
const MAX_PASSES: usize = 256;
const STATUS_ARMS: usize = 22;

/// Select outside prove's timed region. No validation probes or host waits are
/// inserted into this path. Comparison modes record their actual launch cutoff.
pub fn start_policy(candidate: bool) {
    assert!(std::env::var_os("AB_CONT_FUSION_VALIDATE").is_none());
    STATE.with_borrow(|state| assert!(state.is_none()));
    POLICY.with_borrow_mut(|policy| {
        assert!(policy.is_none());
        *policy = Some(Policy {
            candidate,
            compact_comparison: std::env::var("AB_CONT_EVALUATOR_POLICY")
                .map(|mode| {
                    assert!(matches!(
                        mode.as_str(),
                        "compact" | "split_compact" | "x1" | "current"
                    ));
                    true
                })
                .unwrap_or(false),
            split_compact_comparison: std::env::var("AB_CONT_EVALUATOR_POLICY").as_deref()
                == Ok("split_compact"),
            current_comparison: std::env::var("AB_CONT_EVALUATOR_POLICY").as_deref()
                == Ok("current"),
            candidate_words: std::env::var("AB_CONT_CURRENT_WORDS")
                .map(|v| v.parse().expect("word cutoff"))
                .unwrap_or(MAIN_CONTINUATION_WINDOW_X01_PROGRAM_WORD_THRESHOLD),
            candidate_fused_upper: std::env::var("AB_CONT_CURRENT_FUSED_UPPER")
                .map(|v| v.parse().expect("fused upper cutoff"))
                .unwrap_or(MAIN_CONTINUATION_WINDOW_FUSED_X01_PROGRAM_WORD_UPPER_BOUND),
            candidate_large_canonical: std::env::var_os("AB_CONT_LARGE_CANONICAL_FUSION").is_some(),
            candidate_waves: std::env::var("AB_CONT_CURRENT_WAVES")
                .map(|v| {
                    let n = v.parse::<usize>().expect("wave cutoff");
                    assert!((1..=3).contains(&n));
                    n
                })
                .unwrap_or(MAIN_CONTINUATION_WINDOW_FUSION_MIN_WAVES),
            x1_comparison: std::env::var("AB_CONT_EVALUATOR_POLICY").as_deref() == Ok("x1"),
            wide_comparison: match std::env::var("AB_CONT_FOLD_WIDE_POLICY").as_deref() {
                Err(_) => 0,
                Ok("fused") => 1,
                Ok("fused_original") => 5,
                Ok("split") => 2,
                Ok("both") => 3,
                Ok(_) => {
                    panic!("AB_CONT_FOLD_WIDE_POLICY must be fused, split, both, or fused_original")
                }
            },
            split_comparison: std::env::var_os("AB_CONT_SPLIT_PACKED").is_some(),
            gated_comparison: std::env::var_os("AB_CONT_PACING_GATED").is_some(),
            canonical_comparison: std::env::var_os("AB_CONT_CANONICAL_FUSION").is_some(),
            fold_comparison: std::env::var_os("AB_CONT_FOLD_LANE8_POLICY").is_some(),
            packed_comparison: std::env::var_os("AB_CONT_PACKED_POLICY").is_some(),
            coordinate: None,
            passes: Vec::new(),
        });
    });
}

pub fn finish_policy() -> Vec<PolicyPass> {
    let policy = POLICY
        .with_borrow_mut(Option::take)
        .expect("no policy proof started");
    assert!(policy.coordinate.is_none());
    assert!(!policy.passes.is_empty(), "no continuation passes observed");
    policy.passes
}

/// Enable exact full-arena validation via AB_CONT_FUSION_VALIDATE=1.
/// Called before prove's allocation-balance boundary.
pub fn begin_from_env(context: &ProverContext) -> CudaResult<()> {
    if std::env::var_os("AB_CONT_FUSION_VALIDATE").is_none() {
        return Ok(());
    }
    assert_eq!(std::env::var("AB_CONT_FUSION_VALIDATE").unwrap(), "1");
    assert!(
        std::env::var_os("AB_CONT_FUSION_CLUSTER").is_none(),
        "cluster diagnostic was rejected; use its frozen artifact"
    );
    let split_packed = std::env::var_os("AB_CONT_SPLIT_PACKED").is_some();
    let compare_x0 = std::env::var_os("AB_CONT_COMPARE_X0").is_some();
    let pacing = std::env::var_os("AB_CONT_PACING16").is_some();
    let gated = std::env::var_os("AB_CONT_PACING_GATED").is_some();
    let crossover = std::env::var_os("AB_CONT_CROSSOVER").is_some();
    let fold_trial = std::env::var_os("AB_CONT_FOLD_LANE8").is_some();
    let wide_trial = std::env::var_os("AB_CONT_FOLD_WIDE").is_some();
    let current_selector = std::env::var_os("AB_CONT_CURRENT_SELECTOR").is_some();
    let current_fusion = std::env::var_os("AB_CONT_CURRENT_FUSION").is_some();
    let x1_trial = std::env::var_os("AB_CONT_COMPACT_X1").is_some();
    let split_compact_trial = std::env::var_os("AB_CONT_SPLIT_COMPACT_X0").is_some();
    let compact_trial = std::env::var_os("AB_CONT_COMPACT_X0").is_some();
    assert!(
        [
            split_packed,
            compare_x0,
            pacing,
            gated,
            crossover,
            fold_trial,
            wide_trial,
            compact_trial,
            split_compact_trial,
            x1_trial,
            current_selector,
            current_fusion
        ]
        .into_iter()
        .filter(|v| *v)
        .count()
            <= 1
    );
    let timing = std::env::var("AB_CONT_FUSION_TIMING").ok().map(|targets| {
        let coordinates: Vec<_> = targets
            .split(',')
            .map(|target| {
                let (layer, round) = target
                    .split_once(':')
                    .expect("timing coordinate layer:round");
                (
                    layer.parse::<usize>().unwrap(),
                    round.parse::<usize>().unwrap(),
                )
            })
            .collect();
        assert!(!coordinates.is_empty());
        for (index, coordinate) in coordinates.iter().enumerate() {
            assert!(
                !coordinates[..index].contains(coordinate),
                "duplicate timing coordinate"
            );
        }
        Timing {
            arms_override: std::env::var("AB_CONT_CURRENT_ARMS").ok().map(|value| {
                assert!(
                    current_selector || current_fusion,
                    "current-arm override requires a current validation mode"
                );
                let arms: Vec<u32> = value
                    .split(',')
                    .map(|v| v.parse().expect("current arm number"))
                    .collect();
                assert_eq!(arms.len(), 2);
                assert!(arms.iter().all(|arm| (19..=22).contains(arm)) && arms[0] != arms[1]);
                [arms[0], arms[1]]
            }),
            split_packed,
            compare_x0,
            pacing,
            gated,
            crossover,
            fold_trial,
            wide_trial,
            compact_trial,
            split_compact_trial,
            x1_trial,
            current_selector,
            current_fusion,
            coordinates,
            samples: Vec::new(),
            output: std::env::var("AB_CONT_FUSION_OUTPUT").expect("timing CSV output"),
            session: std::env::var("AB_CONT_FUSION_SESSION")
                .expect("timing session")
                .parse()
                .unwrap(),
        }
    });
    let mut status: DeviceAllocation<u32> =
        context.alloc(STATUS_ARMS * MAX_PASSES + 1, AllocationPlacement::Top)?;
    // SAFETY: this byte view covers exactly the owned counter allocation.
    let bytes = unsafe {
        DeviceSlice::from_raw_parts_mut(status.as_mut_ptr().cast::<u8>(), status.len() * 4)
    };
    memory_set_async(bytes, 0, context.get_exec_stream())?;
    STATE.with_borrow_mut(|state| {
        assert!(state.is_none(), "unfinished continuation diagnostic");
        *state = Some(State {
            split_packed,
            compare_x0,
            pacing,
            gated,
            crossover,
            fold_trial,
            wide_trial,
            compact_trial,
            split_compact_trial,
            x1_trial,
            current_selector,
            current_fusion,
            status,
            passes: Vec::new(),
            coordinate: None,
            timing,
        });
    });
    Ok(())
}

pub(crate) fn set_coordinate(layer: usize, round: usize) {
    POLICY.with_borrow_mut(|policy| {
        if let Some(policy) = policy.as_mut() {
            assert!(policy.coordinate.replace((layer, round)).is_none());
        }
    });
    STATE.with_borrow_mut(|state| {
        if let Some(state) = state.as_mut() {
            assert!(state.coordinate.replace((layer, round)).is_none());
        }
    });
}

fn baseline_desc(
    launch: &MainContinuationWindowLaunch<'_>,
    desc: &MainContinuationWindowLaunchBinding,
    context: &ProverContext,
) -> CudaResult<()> {
    let arguments = GkrBwdMainContinuationWindow3Arguments::new(*desc);
    launch.publish_kernel.launch(
        &CudaLaunchConfig::basic(
            launch.publication_grid_blocks,
            MAIN_CONTINUATION_WINDOW_PUBLICATION_THREADS,
            context.get_exec_stream(),
        ),
        &arguments,
    )?;
    resolve(
        launch.publish_kernel.0.mask,
        0,
        use_x01_specialization(desc.program_words as usize),
    )
    .launch(
        &CudaLaunchConfig::basic(
            launch.grid_blocks,
            MAIN_CONTINUATION_WINDOW_BLOCK_THREADS,
            context.get_exec_stream(),
        ),
        &arguments,
    )
}

fn enqueue_arm(
    launch: &MainContinuationWindowLaunch<'_>,
    bound: u32,
    context: &ProverContext,
) -> CudaResult<()> {
    enqueue_arm_desc(launch, bound, &launch.binding, context)
}

fn enqueue_arm_desc(
    launch: &MainContinuationWindowLaunch<'_>,
    bound: u32,
    desc: &MainContinuationWindowLaunchBinding,
    context: &ProverContext,
) -> CudaResult<()> {
    if bound == 0 {
        return baseline_desc(launch, desc, context);
    }
    if bound == 11 || bound == 13 {
        MainContinuationWindowEvaluatorKernel(if bound == 13 {
            ab_gkr_main_cont_fold_wide_publish
        } else {
            ab_gkr_main_cont_fold_lane8_publish
        })
        .launch(
            &CudaLaunchConfig::basic(launch.row_tiles as u32 * 24, 96, context.get_exec_stream()),
            &GkrBwdMainContinuationWindow3Arguments::new(*desc),
        )?;
    }
    if bound == 5 || bound == 16 || bound == 18 || bound == 21 || bound == 22 {
        launch.publish_kernel.launch(
            &CudaLaunchConfig::basic(
                launch.publication_grid_blocks,
                MAIN_CONTINUATION_WINDOW_PUBLICATION_THREADS,
                context.get_exec_stream(),
            ),
            &GkrBwdMainContinuationWindow3Arguments::new(*desc),
        )?;
    }
    let split = matches!(bound, 5 | 11 | 13 | 16 | 18 | 21 | 22);
    resolve(
        launch.publish_kernel.0.mask,
        bound,
        if split {
            use_x01_specialization(desc.program_words as usize)
        } else {
            use_fused_x01_specialization(desc.program_words as usize)
        },
    )
    .launch(
        &CudaLaunchConfig::basic(
            if split {
                launch.grid_blocks
            } else {
                launch.row_tiles as u32
            },
            if split {
                MAIN_CONTINUATION_WINDOW_BLOCK_THREADS
            } else {
                288
            },
            context.get_exec_stream(),
        ),
        &GkrBwdMainContinuationWindow3Arguments::new(*desc),
    )
}

// Each timing mode encloses the complete selected continuation arm.
fn schedule_timing(
    timing: &mut Timing,
    pass: usize,
    launch: &MainContinuationWindowLaunch<'_>,
    context: &ProverContext,
) -> CudaResult<()> {
    let arms = if let Some(arms) = timing.arms_override {
        arms
    } else if timing.current_selector {
        if launch.row_tiles
            >= main_continuation_launch_min_tiles(
                context.get_device_properties().sm_count,
                launch.binding.program_words as usize,
                launch.canonical_input,
            )
        {
            [19, 20]
        } else {
            [21, 22]
        }
    } else if timing.current_fusion {
        if use_x01_specialization(launch.binding.program_words as usize) {
            [22, 20]
        } else {
            [21, 19]
        }
    } else if timing.x1_trial {
        if launch.row_tiles
            >= main_continuation_fusion_min_tiles(context.get_device_properties().sm_count)
        {
            [12, 17]
        } else if use_x01_specialization(launch.binding.program_words as usize) {
            [16, 18]
        } else {
            [5, 18]
        }
    } else if timing.split_compact_trial {
        [5, 16]
    } else if timing.compact_trial {
        [15, 12]
    } else if timing.wide_trial {
        if launch.row_tiles
            >= main_continuation_fusion_min_tiles(context.get_device_properties().sm_count)
        {
            [9, 12]
        } else {
            [11, 13]
        }
    } else if timing.fold_trial {
        if launch.row_tiles
            >= main_continuation_fusion_min_tiles(context.get_device_properties().sm_count)
        {
            [9, 10]
        } else {
            [5, 11]
        }
    } else if timing.crossover {
        [5, 9]
    } else if timing.gated {
        [4, 9]
    } else if timing.pacing {
        [4, 8]
    } else if timing.compare_x0 {
        [7, 6]
    } else if timing.split_packed {
        [0, 5]
    } else {
        [2, 4]
    };
    for _ in 0..5 {
        for bound in arms {
            enqueue_arm(launch, bound, context)?;
        }
    }
    for iteration in 0..24 {
        let order = if (iteration + timing.session) % 2 == 0 {
            arms
        } else {
            [arms[1], arms[0]]
        };
        for (position, bound) in order.into_iter().enumerate() {
            let start = CudaEvent::create()?;
            let end = CudaEvent::create()?;
            start.record(context.get_exec_stream())?;
            enqueue_arm(launch, bound, context)?;
            end.record(context.get_exec_stream())?;
            timing.samples.push(Sample {
                pass,
                iteration,
                position,
                bound,
                start,
                end,
            });
        }
    }
    // The packed candidate feeds the remainder of the proof.
    enqueue_arm(launch, arms[1], context)
}

pub(super) fn schedule(
    launch: &MainContinuationWindowLaunch<'_>,
    context: &ProverContext,
) -> CudaResult<bool> {
    if launch.binding.publication_fold != 3 {
        return Ok(false);
    }
    let selected = POLICY.with_borrow_mut(|policy| {
        policy.as_mut().map(|policy| {
            let (layer, round) = policy.coordinate.take().expect("missing policy coordinate");
            let sm_count = context.get_device_properties().sm_count;
            let min_tiles = if policy.current_comparison
                && policy.candidate
                && policy.candidate_large_canonical
                && launch.canonical_input
                && launch.binding.program_words as usize
                    >= MAIN_CONTINUATION_WINDOW_FUSED_X01_PROGRAM_WORD_UPPER_BOUND
            {
                sm_count
            } else if policy.current_comparison && policy.candidate {
                policy.candidate_waves
                    * MAIN_CONTINUATION_WINDOW_FUSED_MIN_BLOCKS as usize
                    * sm_count
            } else if policy.canonical_comparison && policy.candidate && launch.canonical_input {
                sm_count
            } else {
                main_continuation_fusion_min_tiles(sm_count)
            };
            let fused = (policy.candidate
                || policy.packed_comparison
                || policy.split_comparison
                || policy.gated_comparison
                || policy.canonical_comparison
                || policy.fold_comparison
                || policy.wide_comparison != 0
                || policy.compact_comparison)
                && launch.row_tiles >= min_tiles;
            let packed = fused
                && (policy.candidate
                    || policy.split_comparison
                    || policy.gated_comparison
                    || policy.canonical_comparison
                    || policy.fold_comparison
                    || policy.wide_comparison != 0
                    || policy.compact_comparison);
            let split_packed = !fused
                && (policy.candidate
                    || policy.packed_comparison
                    || policy.gated_comparison
                    || policy.canonical_comparison
                    || policy.fold_comparison
                    || policy.wide_comparison != 0
                    || policy.compact_comparison);
            let words = launch.binding.program_words as usize;
            let static_x0 = if policy.current_comparison && policy.candidate {
                words >= policy.candidate_words && (!fused || words < policy.candidate_fused_upper)
            } else {
                if fused {
                    use_fused_x01_specialization(words)
                } else {
                    use_x01_specialization(words)
                }
            };
            let gated = (policy.compact_comparison
                || policy.wide_comparison != 0
                || policy.fold_comparison
                || policy.canonical_comparison
                || (policy.gated_comparison && policy.candidate))
                && fused
                && !static_x0;
            let paced = gated && words >= 1024;
            let fold_candidate = policy.fold_comparison && policy.candidate && !fused;
            let fold_arm = if policy.current_comparison {
                match (fused, static_x0) {
                    (true, false) => 19,
                    (true, true) => 20,
                    (false, false) => 21,
                    (false, true) => 22,
                }
            } else if policy.x1_comparison {
                if fused {
                    if policy.candidate {
                        17
                    } else {
                        12
                    }
                } else if static_x0 {
                    if policy.candidate {
                        18
                    } else {
                        16
                    }
                } else {
                    5
                }
            } else if policy.split_compact_comparison {
                if fused {
                    12
                } else if static_x0 && policy.candidate {
                    16
                } else {
                    5
                }
            } else if policy.compact_comparison {
                if fused {
                    if static_x0 && !policy.candidate {
                        15
                    } else {
                        12
                    }
                } else if static_x0 {
                    16
                } else {
                    5
                }
            } else if policy.wide_comparison != 0 {
                if fused {
                    if policy.candidate && policy.wide_comparison & 1 != 0 {
                        12
                    } else {
                        9
                    }
                } else if policy.candidate && policy.wide_comparison & 2 != 0 {
                    13
                } else if policy.wide_comparison & 4 != 0 {
                    5
                } else {
                    11
                }
            } else {
                if fold_candidate {
                    11
                } else if gated {
                    9
                } else if split_packed {
                    5
                } else if packed {
                    4
                } else if fused {
                    2
                } else {
                    0
                }
            };
            policy.passes.push(PolicyPass {
                layer,
                round,
                tiles: launch.row_tiles,
                min_tiles,
                canonical_input: launch.canonical_input,
                fused,
                packed,
                split_packed,
                words,
                static_x0,
                gated,
                paced,
                fold_candidate,
                fold_arm,
            });
            fold_arm
        })
    });
    if let Some(arm) = selected {
        // Explicitly handle both arms: the default path now applies the policy,
        // so falling through would no longer give an unfused reference.
        enqueue_arm(launch, arm, context)?;
        return Ok(true);
    }
    STATE.with_borrow_mut(|state| {
        let Some(state) = state.as_mut() else {
            return Ok(false);
        };
        let (layer, round) = state
            .coordinate
            .take()
            .expect("missing continuation coordinate");
        let index = state.passes.len();
        assert!(index < MAX_PASSES);
        let stream = context.get_exec_stream();
        let publication_cells = launch.published.allocation().len();
        let tensor_cells = launch.row_tiles * MAIN_CONTINUATION_WINDOW_TENSOR_CELLS;
        let mut reference: DeviceAllocation<E4> = context.alloc(
            publication_cells + tensor_cells,
            AllocationPlacement::BestFit,
        )?;
        // SAFETY: these two disjoint output spans are owned by the launch and its
        // scratch. Their handles survive every enqueue in this function. All
        // writes and reads use the same execution stream.
        let published = unsafe {
            DeviceSlice::from_raw_parts_mut(launch.published.as_ptr().cast_mut(), publication_cells)
        };
        let tensor =
            unsafe { DeviceSlice::from_raw_parts_mut(launch.binding.partials, tensor_cells) };
        // A depth-zero projection reads a prefix of the same input columns;
        // depth three already proves those larger input spans are available.
        // Compare both evaluators on that arena, then restore the actual fold
        // before any timing or downstream proof work. Counters retain errors
        // from either depth. This is a kernel diagnostic, not a second proof.
        let folds: &[u32] = if state.split_packed
            || state.fold_trial
            || state.wide_trial
            || state.split_compact_trial
            || state.x1_trial
            || state.current_selector
            || state.current_fusion
        {
            &[0, 3]
        } else {
            &[3]
        };
        for &fold in folds {
            let mut desc = *launch.binding;
            desc.publication_fold = fold;
            baseline_desc(launch, &desc, context)?;
            memory_copy_async(&mut reference[..publication_cells], &*published, stream)?;
            memory_copy_async(&mut reference[publication_cells..], &*tensor, stream)?;
            let bounds: &[u32] = if state.current_selector || state.current_fusion {
                if fold == 0 {
                    &[21, 22]
                } else {
                    &[19, 20, 21, 22]
                }
            } else if state.x1_trial {
                if fold == 0 {
                    &[18]
                } else {
                    &[17, 18]
                }
            } else if state.split_compact_trial {
                &[5, 16]
            } else if state.compact_trial {
                &[12, 14, 15]
            } else if state.wide_trial {
                if fold == 0 {
                    &[13]
                } else {
                    &[12, 13]
                }
            } else if state.fold_trial {
                if fold == 0 {
                    &[11]
                } else {
                    &[10, 11]
                }
            } else if state.crossover {
                &[5, 9]
            } else if state.gated {
                &[9]
            } else if state.pacing {
                &[8]
            } else if state.compare_x0 {
                &[7, 6]
            } else if state.split_packed {
                &[5]
            } else {
                &[1, 2, 3, 4, 9, 12]
            };
            for &bound in bounds {
                for output in [&mut *published, &mut *tensor] {
                    // SAFETY: exactly the output span; poison is outside canonical BF range.
                    let bytes = unsafe {
                        DeviceSlice::from_raw_parts_mut(
                            output.as_mut_ptr().cast::<u8>(),
                            output.len() * size_of::<E4>(),
                        )
                    };
                    memory_set_async(bytes, 0xa5, stream)?;
                }
                enqueue_arm_desc(launch, bound, &desc, context)?;
                for (expected, actual, cells) in [
                    (reference.as_ptr(), published.as_ptr(), publication_cells),
                    // SAFETY: tensor reference starts at the validated publication length.
                    (
                        unsafe { reference.as_ptr().add(publication_cells) },
                        tensor.as_ptr(),
                        tensor_cells,
                    ),
                ] {
                    let limbs = u32::try_from(cells * 4).expect("diagnostic limb span fits u32");
                    // SAFETY: index < MAX_PASSES and arm is in 1..=STATUS_ARMS.
                    let status = unsafe {
                        state
                            .status
                            .as_mut_ptr()
                            .add(STATUS_ARMS * index + bound as usize - 1)
                    };
                    CompareFunction::default().launch(
                        &CudaLaunchConfig::basic(limbs.div_ceil(256), 256, stream),
                        &CompareArguments::new(expected.cast(), actual.cast(), limbs, status, 0),
                    )?;
                }
            }
        }
        if state.compact_trial {
            enqueue_arm(launch, 12, context)?;
        }
        let mask = launch.publish_kernel.0.mask;
        if index == 0 {
            // Inject exactly one changed limb through the same comparison kernel.
            let expected = unsafe { reference.as_ptr().add(publication_cells) };
            let status = unsafe { state.status.as_mut_ptr().add(STATUS_ARMS * MAX_PASSES) };
            CompareFunction::default().launch(
                &CudaLaunchConfig::basic(1, 256, stream),
                &CompareArguments::new(expected.cast(), tensor.as_ptr().cast(), 1, status, 1),
            )?;
        }
        state.passes.push(Pass {
            layer,
            round,
            mask,
            words: launch.binding.program_words,
            row_tiles: launch.row_tiles,
            publication_cells,
            tensor_cells,
        });
        if let Some(timing) = state.timing.as_mut() {
            if timing.coordinates.contains(&(layer, round)) {
                schedule_timing(timing, index, launch, context)?;
            }
        }
        // The last selected candidate deliberately feeds subsequent windows and the proof.
        Ok(true)
    })
}

/// Read counters only after proof completion. No performance claim is made by
/// the whole proof in this mode: copies, poisoning, and comparisons add work.
/// Optional timing encloses only each publication+evaluation arm.
pub fn finish(context: &ProverContext) -> CudaResult<()> {
    let Some(state) = STATE.with_borrow_mut(Option::take) else {
        return Ok(());
    };
    assert!(!state.passes.is_empty(), "zero continuation passes checked");
    let mut status = vec![0u32; state.status.len()];
    memory_copy_async(
        &mut status[..],
        &state.status[..],
        context.get_exec_stream(),
    )?;
    context.get_exec_stream().synchronize()?;
    for (index, pass) in state.passes.iter().enumerate() {
        eprintln!("CONT_FUSION_GATE pass={index} layer={} round={} mask={:02x} words={} tiles={} publication_cells={} tensor_cells={} b1_status={} b2_status={} b3_status={} packed_status={} split_status={} dynamic_x0_status={} static_x0_status={} pacing_status={} gated_status={} lane8_fused_status={} lane8_split_status={} wide_fused_status={} wide_split_status={} compact_status={} static_reference_status={} split_compact_status={} x1_fused_status={} x1_split_status={} current_fused_dynamic_status={} current_fused_static_status={} current_split_dynamic_status={} current_split_static_status={}",
            pass.layer, pass.round, pass.mask, pass.words, pass.row_tiles, pass.publication_cells, pass.tensor_cells, status[STATUS_ARMS*index], status[STATUS_ARMS*index+1], status[STATUS_ARMS*index+2], status[STATUS_ARMS*index+3], status[STATUS_ARMS*index+4], status[STATUS_ARMS*index+5], status[STATUS_ARMS*index+6], status[STATUS_ARMS*index+7], status[STATUS_ARMS*index+8], status[STATUS_ARMS*index+9], status[STATUS_ARMS*index+10], status[STATUS_ARMS*index+11], status[STATUS_ARMS*index+12], status[STATUS_ARMS*index+13], status[STATUS_ARMS*index+14], status[STATUS_ARMS*index+15], status[STATUS_ARMS*index+16], status[STATUS_ARMS*index+17], status[STATUS_ARMS*index+18], status[STATUS_ARMS*index+19], status[STATUS_ARMS*index+20], status[STATUS_ARMS*index+21]);
    }
    assert!(
        status[..STATUS_ARMS * state.passes.len()]
            .iter()
            .all(|value| *value == 0),
        "continuation mismatch/poison status: {status:?}"
    );
    assert_eq!(
        status[STATUS_ARMS * MAX_PASSES],
        1,
        "negative control must detect injected mismatch"
    );
    if let Some(timing) = state.timing {
        for coordinate in &timing.coordinates {
            let matching: Vec<_> = state
                .passes
                .iter()
                .enumerate()
                .filter(|(_, pass)| (pass.layer, pass.round) == *coordinate)
                .collect();
            assert_eq!(
                matching.len(),
                1,
                "missing/duplicate timed coordinate {coordinate:?}"
            );
            assert_eq!(
                timing
                    .samples
                    .iter()
                    .filter(|sample| sample.pass == matching[0].0)
                    .count(),
                48
            );
        }
        let mut file = std::fs::File::create(&timing.output).expect("create timing CSV");
        writeln!(file, "session,layer,round,mask,words,tiles,publication_cells,tensor_cells,iteration,position,variant,ms").unwrap();
        for sample in timing.samples {
            let pass = &state.passes[sample.pass];
            writeln!(
                file,
                "{},{},{},{:02x},{},{},{},{},{},{},{},{:.9}",
                timing.session,
                pass.layer,
                pass.round,
                pass.mask,
                pass.words,
                pass.row_tiles,
                pass.publication_cells,
                pass.tensor_cells,
                sample.iteration,
                sample.position,
                match sample.bound {
                    10 => "lane8_fused",
                    11 => "lane8_split",
                    12 => "wide_fused",
                    13 => "wide_split",
                    14 => "compact_x0",
                    15 => "static_reference",
                    16 => "split_compact_x0",
                    17 => "x1_fused",
                    18 => "x1_split",
                    19 => "current_fused_dynamic",
                    20 => "current_fused_static",
                    21 => "current_split_dynamic",
                    22 => "current_split_static",
                    9 => "packed_gated",
                    8 => "packed_pacing16",
                    6 => "packed_dynamic_x0",
                    7 => "packed_static_x0",
                    0 => "split",
                    5 => "packed_split",
                    4 => "packed_b2",
                    2 => "b2",
                    _ => unreachable!(),
                },
                elapsed_time(&sample.start, &sample.end)?
            )
            .unwrap();
        }
    }
    eprintln!("CONT_FUSION_GATE passes={} full_publication_and_tensor=equal poison=absent negative_control=passed candidate_feeds_proof={} tested_arms={} publication_folds={}", state.passes.len(), if state.current_selector || state.current_fusion { "current_forced" } else if state.x1_trial { "x1_fused/x1_split" } else if state.split_compact_trial { "split_compact_x0" } else if state.compact_trial { "compact_x0" } else if state.wide_trial { "wide" } else if state.fold_trial { "lane8" } else if state.gated { "packed_gated" } else if state.pacing { "packed_pacing16" } else if state.compare_x0 { "packed_dynamic_x0" } else if state.split_packed { "packed_split" } else { "wide_fused" }, if state.current_selector || state.current_fusion { "current_forced" } else if state.x1_trial { "x1_fused/x1_split" } else if state.split_compact_trial { "split_compact_x0" } else if state.compact_trial { "compact_x0" } else if state.wide_trial { "wide_fused/wide_split" } else if state.fold_trial { "lane8_fused/lane8_split" } else if state.crossover { "packed_split/packed_gated" } else if state.gated { "packed_gated" } else if state.pacing { "packed_pacing16" } else if state.compare_x0 { "packed_static_x0/packed_dynamic_x0" } else if state.split_packed { "packed_split" } else { "b1/b2/b3/packed_b2/gated/wide_fused" }, if state.split_packed || state.fold_trial || state.wide_trial || state.split_compact_trial || state.x1_trial || state.current_selector || state.current_fusion { "0/3" } else { "3" });
    Ok(())
}
