cmake_minimum_required(VERSION 3.28)
project(gpu_ntt LANGUAGES CUDA)
if ((NOT DEFINED CMAKE_CUDA_ARCHITECTURES) OR (CMAKE_CUDA_ARCHITECTURES STREQUAL ""))
    set(CMAKE_CUDA_ARCHITECTURES native)
endif ()
option(GPU_NTT_ENABLE_LINEINFO "Enable lineinfo for CUDA profiling builds" OFF)
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
        monomials_to_evals_compact.cu
        monomials_to_evals_smem_packed.cu
        monomials_to_evals_subwarp.cu
        monomials_to_evals_three_pass.cu
        monomials_to_evals_two_pass.cu
        ntt.cu
        ntt.cuh
)
option(GPU_NTT_BUILD_BENCH "Compile bench-only DIT kernel variants into the archive" OFF)
if (GPU_NTT_BUILD_BENCH)
    target_sources(gpu_ntt_native PRIVATE bench/dit_bench_kernels.cu)
endif ()
target_include_directories(gpu_ntt_native PRIVATE ${GPU_CORE_NATIVE_INCLUDE})
set_target_properties(gpu_ntt_native PROPERTIES CUDA_STANDARD 20)
set_target_properties(gpu_ntt_native PROPERTIES CUDA_SEPARABLE_COMPILATION ON)
set_target_properties(gpu_ntt_native PROPERTIES CUDA_RESOLVE_DEVICE_SYMBOLS ON)
# CCCL headers in CUDA 12+ require MSVC's standard conforming preprocessor.
if (MSVC)
    target_compile_options(gpu_ntt_native PRIVATE $<$<COMPILE_LANGUAGE:CUDA>:-Xcompiler=/Zc:preprocessor>)
endif ()
target_compile_options(gpu_ntt_native PRIVATE --expt-relaxed-constexpr)
target_compile_options(gpu_ntt_native PRIVATE --ptxas-options=-v)
if (GPU_NTT_ENABLE_LINEINFO)
    target_compile_options(gpu_ntt_native PRIVATE -lineinfo)
endif ()
target_compile_options(gpu_ntt_native PRIVATE --keep)
install(TARGETS gpu_ntt_native DESTINATION .)
