target_sources(gpu_ntt_native PRIVATE
        context.cuh
        context.cu
        dit_kernels_extern.cu
        dit_twiddle_fill.cu
        hypercube.cu
        hypercube_evals_to_monomials_three_pass.cu
        hypercube_evals_to_monomials_two_pass.cu
        hypercube_evals_to_monomials_two_pass_compact.cu
        lde_intermediate_first_pass.cu
        monomials_to_evals_compact.cu
        monomials_to_evals_smem_packed.cu
        monomials_to_evals_subwarp.cu
        monomials_to_evals_three_pass.cu
        monomials_to_evals_two_pass.cu
        natural_monomials_to_bitrev_evals_three_pass.cu
        natural_monomials_to_bitrev_evals_two_pass.cu
        natural_monomials_to_bitrev_evals_two_pass_compact.cu
        ntt.cuh
        whir_leaf_transform.cuh
)
option(GPU_NTT_BUILD_BENCH "Compile bench-only DIT kernel variants into the archive" OFF)
if (GPU_NTT_BUILD_BENCH)
    target_sources(gpu_ntt_native PRIVATE bench/dit_bench_kernels.cu)
endif ()
