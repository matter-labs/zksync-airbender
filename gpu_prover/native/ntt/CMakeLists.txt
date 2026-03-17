target_sources(gpu_prover_native PRIVATE
        context.cuh
        context.cu
        evals_to_monomials_three_pass.cu
        evals_to_monomials_two_pass.cu
        hypercube.cu
        monomials_to_evals_three_pass.cu
        monomials_to_evals_two_pass.cu
        ntt.cu
        ntt.cuh
)
