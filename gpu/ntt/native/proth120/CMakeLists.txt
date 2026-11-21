target_sources(gpu_ntt_native PRIVATE
        context.cuh
        context.cu
        twiddle_build.cu
        transform.cuh
        lde_dit.cu
        hypercube_mobius.cu
        pack.cu
        hypercube_eq.cu
)
