target_sources(gpu_prover_native PRIVATE
        blake2s.cu
        complex.cu
        complex.cuh
        simple.cu
)
add_subdirectory(cub)
