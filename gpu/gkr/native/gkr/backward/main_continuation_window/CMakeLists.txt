target_sources(gpu_gkr_native PRIVATE
        executor.cuh
        fold_prologue.cuh
        generated/main_continuation_window_manifest.cuh
        generated/main_continuation_window_shape_00.cu
        generated/main_continuation_window_shape_01.cu
        generated/main_continuation_window_shape_03.cu
        generated/main_continuation_window_shape_07.cu
        generated/main_continuation_window_shape_13.cu
        generated/main_continuation_window_shape_17.cu
        generated/main_continuation_window_shape_1f.cu
        main_continuation_window_abi.cuh
)
