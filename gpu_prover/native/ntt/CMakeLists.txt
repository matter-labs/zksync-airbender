target_sources(gpu_prover_ntt PRIVATE
        context.cuh
        context.cu
        evals_to_monomials_three_pass.cu
        evals_to_monomials_two_pass.cu
        hypercube.cu
        hypercube_evals_to_monomials_three_pass.cu
        hypercube_evals_to_monomials_two_pass.cu
        monomials_to_evals_compact.cu
        monomials_to_evals_smem_packed.cu
        monomials_to_evals_subwarp.cu
        monomials_to_evals_three_pass.cu
        monomials_to_evals_two_pass.cu
        ntt.cu
        ntt.cuh
)
