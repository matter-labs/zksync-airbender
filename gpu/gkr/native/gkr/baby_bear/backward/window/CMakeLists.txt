target_sources(gpu_gkr_native PRIVATE
        coefficient_bank.cu
        r0.cu
        state.cu
        coefficient_bank.cuh
        common.cuh
        r0.cuh
        window_abi.cuh
        window_accumulator.cuh
        window_geometry.cuh
        window_source.cuh
)
