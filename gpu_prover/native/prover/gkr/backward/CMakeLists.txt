target_sources(gpu_prover_native PRIVATE
        coeff.cuh
        continuation.cuh
        dim_reducing.cu
        flat.cuh
        round0_compute_coeff.cu
        round0_flat.cu
        round1_flat_warp_split.cu
        round2_flat_warp_split.cu
        round3_compute_coeff.cu
        round3_flat_warp_split.cu
)
