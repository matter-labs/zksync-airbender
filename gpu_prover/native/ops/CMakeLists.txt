target_sources(gpu_prover_native PRIVATE
        batch_inv.cu
        batch_inv.cuh
        bit_reverse.cu
        blake2s.cu
        powers.cu
        simple.cu
        transpose.cu
)
add_subdirectory(cub)
