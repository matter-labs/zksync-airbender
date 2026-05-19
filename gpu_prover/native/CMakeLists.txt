cmake_minimum_required(VERSION 3.28)
# Cmake must be at least 3.28 - the earlier one didn't pass cuda_standard properly.
project(gpu_prover_native)
enable_language(CUDA)
if ((NOT DEFINED CMAKE_CUDA_ARCHITECTURES) OR (CMAKE_CUDA_ARCHITECTURES STREQUAL ""))
    set(CMAKE_CUDA_ARCHITECTURES native)
endif ()
option(AB_DETERMINISTIC_POW "Enable deterministic PoW search" OFF)
option(GPU_PROVER_ENABLE_LINEINFO "Enable lineinfo for CUDA profiling builds" OFF)
# Main native archive: everything except NTT.
add_library(gpu_prover_native STATIC
        common.cuh
)
# NTT archive: device-linked independently so its __constant__ symbols live
# in their own CUDA module with their own 64 KB budget, freeing room in the
# main archive's budget for prover-side constant tables.
add_library(gpu_prover_ntt STATIC
        common.cuh
)
option(GPU_PROVER_BUILD_BENCH "Build bench kernels" OFF)
if (GPU_PROVER_BUILD_BENCH)
    add_subdirectory(bench)
endif ()
add_subdirectory(ntt)
add_subdirectory(ops)
add_subdirectory(prover)
add_subdirectory(primitives)
add_subdirectory(witness)
foreach (gpu_prover_target gpu_prover_native gpu_prover_ntt)
    set_target_properties(${gpu_prover_target} PROPERTIES CUDA_STANDARD 20)
    set_target_properties(${gpu_prover_target} PROPERTIES CUDA_SEPARABLE_COMPILATION ON)
    set_target_properties(${gpu_prover_target} PROPERTIES CUDA_RESOLVE_DEVICE_SYMBOLS ON)
    if (AB_DETERMINISTIC_POW)
        target_compile_definitions(${gpu_prover_target} PRIVATE AB_DETERMINISTIC_POW=1)
    endif ()
    # CCCL headers in CUDA 12+ require MSVC's standard conforming preprocessor.
    if (MSVC)
        target_compile_options(${gpu_prover_target} PRIVATE $<$<COMPILE_LANGUAGE:CUDA>:-Xcompiler=/Zc:preprocessor>)
    endif ()
    target_compile_options(${gpu_prover_target} PRIVATE --expt-relaxed-constexpr)
    target_compile_options(${gpu_prover_target} PRIVATE --ptxas-options=-v)
    if (GPU_PROVER_ENABLE_LINEINFO)
        target_compile_options(${gpu_prover_target} PRIVATE -lineinfo)
    endif ()
    target_compile_options(${gpu_prover_target} PRIVATE --keep)
endforeach ()
install(TARGETS gpu_prover_native gpu_prover_ntt DESTINATION .)
