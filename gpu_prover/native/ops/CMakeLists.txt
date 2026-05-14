target_sources(gpu_prover_native PRIVATE
        batch_inv.cu
        batch_inv.cuh
        bit_reverse.cu
        gather.cu
        gkr_initial_inner_products.cu
        gkr_ops.cu
        hash.cu
        hash.cuh
        powers.cu
        simple.cu
        transpose.cu
)
add_subdirectory(cub)
