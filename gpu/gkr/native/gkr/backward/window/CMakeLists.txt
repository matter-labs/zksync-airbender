target_sources(gpu_gkr_native PRIVATE
        coefficient_bank.cu
        coefficient_bank.cuh
        common.cuh
        recomputed.cu
        recomputed.cuh
        state.cu
        window_abi.cuh
        window_accumulator.cuh
        window_geometry.cuh
        window_source.cuh
)
