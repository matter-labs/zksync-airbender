target_sources(gpu_prover_native PRIVATE
        common.cuh
        dim_reducing_backward.cu
        dim_reducing_forward.cu
        forward_cache.cu
        forward_layer.cu
        main_backward.cu
        setup.cu
)
