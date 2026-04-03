target_sources(gpu_prover_native PRIVATE
        common.cuh
        dim_reducing_backward.cu
        dim_reducing_forward.cu
        forward_cache.cu
        forward_layer.cu
        main_backward_round0.cu
        main_backward_round1_compact.cu
        main_backward_round1_explicit.cu
        main_backward_round2_compact.cu
        main_backward_round2_explicit.cu
        main_backward_round3_compact.cu
        main_backward_round3_explicit.cu
        setup.cu
)
