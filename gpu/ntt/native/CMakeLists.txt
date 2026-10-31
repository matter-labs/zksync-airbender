cmake_minimum_required(VERSION 3.28)
project(gpu_ntt LANGUAGES CUDA)
if ((NOT DEFINED CMAKE_CUDA_ARCHITECTURES) OR (CMAKE_CUDA_ARCHITECTURES STREQUAL ""))
    set(CMAKE_CUDA_ARCHITECTURES native)
endif ()
if (NOT DEFINED AB_CUDA_CMAKE_DIR)
    # Standalone/IDE configure fallback; under cargo, gpu_native_build passes -DAB_CUDA_CMAKE_DIR.
    set(AB_CUDA_CMAKE_DIR ${CMAKE_CURRENT_SOURCE_DIR}/../../native_build/cmake)
endif ()
include(${AB_CUDA_CMAKE_DIR}/ab_cuda_target.cmake)
add_library(gpu_ntt_native STATIC
        context.cuh
        context.cu
        dit_kernels_extern.cu
        dit_twiddle_fill.cu
        evals_to_monomials_three_pass.cu
        evals_to_monomials_two_pass.cu
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
        ntt.cu
        ntt.cuh
        proth120/context.cuh
        proth120/context.cu
        proth120/transform.cuh
        proth120/lde_dit.cu
        proth120/lde_scale.cu
        proth120/lde_naturalize.cu
        proth120/hypercube_mobius.cu
        proth120/pack.cu
        proth120/hypercube_eq.cu
        proth120/lde_leaf.cu
        whir_leaf_transform.cuh
)
option(GPU_NTT_BUILD_BENCH "Compile bench-only DIT kernel variants into the archive" OFF)
if (GPU_NTT_BUILD_BENCH)
    target_sources(gpu_ntt_native PRIVATE bench/dit_bench_kernels.cu)
endif ()
ab_cuda_configure_target(gpu_ntt_native PREFIX GPU_NTT INCLUDE_DIRS ${GPU_CORE_NATIVE_INCLUDE})
