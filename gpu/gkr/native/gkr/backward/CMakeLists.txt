target_sources(gpu_gkr_native PRIVATE
        dim_reducing.cu
        dr_tail_megakernel.cu
        dr_tail_megakernel.cuh
        mega_finalize.cuh
        seg_coeff_eval.cu
        seg_coeff_eval.cuh
        segmented_vm.cu
        segmented_vm.cuh
        tail_fused.cu
        window_tail.cu
        window/window_abi.cuh
        window/window_accumulator.cuh
        window/window_control.cuh
        window/window_geometry.cuh
        window/window_source.cuh
        window_dr/r0.cuh
        generated/dr_windowed_r0_manifest.cuh
        generated/dr_r0_window_universal.cu
        generated/windowed_r0_manifest.cuh
        generated/r0_window_shape_1b1.cu
        generated/r0_window_shape_3ff.cu
        generated/r0_window_shape_471.cu
        generated/r0_window_shape_4f6.cu
        generated/r0_window_shape_5f7.cu
        generated/r0_window_shape_7f7.cu
        generated/r0_window_shape_7ff.cu
        generated/r0_window_shape_c78.cu
        generated/r0_window_shape_c7a.cu
        generated/r0_window_shape_ffb.cu
        generated/r0_window_shape_fff.cu
)

option(GPU_GKR_DR_TAIL_TRACE "Compile the test-only DR-tail trace oracle" OFF)
if (GPU_GKR_DR_TAIL_TRACE)
    target_sources(gpu_gkr_native PRIVATE dr_tail_megakernel_trace.cu)
endif ()
