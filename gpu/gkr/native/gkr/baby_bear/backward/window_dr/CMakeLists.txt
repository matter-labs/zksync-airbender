target_sources(gpu_gkr_native PRIVATE
        r0.cu
        continuation.cu
        abi.cuh
        accumulator_bounds.cuh
        evaluate.cuh
        math_accumulator_packed.cuh
)
