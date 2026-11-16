target_sources(gpu_gkr_native PRIVATE
        paired.cu
        publication.cu
        executor.cuh
        fold_prologue.cuh
        fused_executor.cuh
        main_continuation_window_abi.cuh
)

# The compiler checks generated/'s exact contents, including the absence of
# CMakeLists.txt. Keep its source list here, as before the field layout move.
target_sources(gpu_gkr_native PRIVATE
        generated/main_continuation_window_fused.cu
        generated/main_continuation_window_shape_00.cu
        generated/main_continuation_window_shape_01.cu
        generated/main_continuation_window_shape_03.cu
        generated/main_continuation_window_shape_07.cu
        generated/main_continuation_window_shape_0f.cu
        generated/main_continuation_window_shape_13.cu
        generated/main_continuation_window_shape_17.cu
        generated/main_continuation_window_shape_1f.cu
        generated/main_continuation_window_manifest.cuh
)
