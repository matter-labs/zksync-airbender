target_sources(gpu_gkr_native PRIVATE
        coefficient_bank.cu
        coefficient_bank.cuh
        common.cuh
        ../generated/r0_window_shape_471_b4.cu
        ../generated/r0_window_shape_4f6_b3.cu
        ../generated/r0_window_shape_fff_b3.cu
        ../generated/r0_window_shape_fff_b4.cu
        ../generated/windowed_r0_manifest.cuh
        state.cu
        window_abi.cuh
        window_accumulator.cuh
        window_control.cuh
        window_geometry.cuh
        window_source.cuh
)
