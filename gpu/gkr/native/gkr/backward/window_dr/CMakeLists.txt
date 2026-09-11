target_sources(gpu_gkr_native PRIVATE
        continuation.cuh
        continuation_packed.cuh
        continuation_split.cuh
        packed_continuation.cu
        ../generated/dr_windowed_cont_manifest.cuh
        ../generated/dr_windowed_r0_manifest.cuh
        r0.cuh
        packed_r0.cu
        accumulator_bounds.cuh
        math_accumulator_packed.cuh
)
