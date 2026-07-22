cmake_minimum_required(VERSION 3.28)
# Cmake must be at least 3.28 - the earlier one didn't pass cuda_standard properly.
project(circuit_prover_native)
enable_language(CUDA)
if ((NOT DEFINED CMAKE_CUDA_ARCHITECTURES) OR (CMAKE_CUDA_ARCHITECTURES STREQUAL ""))
    set(CMAKE_CUDA_ARCHITECTURES native)
endif ()
if (NOT DEFINED AB_CUDA_CMAKE_DIR)
    # Standalone/IDE configure fallback; under cargo, gpu_native_build passes -DAB_CUDA_CMAKE_DIR.
    set(AB_CUDA_CMAKE_DIR ${CMAKE_CURRENT_SOURCE_DIR}/../../native_build/cmake)
endif ()
include(${AB_CUDA_CMAKE_DIR}/ab_cuda_target.cmake)
# Main native archive: WHIR protocol + PoW kernels. (NTT lives in gpu_ntt; the
# GKR engine + gkr_ops moved to the gpu_gkr crate's own archive — WHIR's
# accumulate_eq.cu includes gkr's eq/kernel headers via GPU_GKR_NATIVE_INCLUDE.)
add_library(circuit_prover_native STATIC)
add_subdirectory(prover)
ab_cuda_configure_target(circuit_prover_native
        PREFIX GPU_PROVER
        DETERMINISTIC_POW
        INCLUDE_DIRS ${GPU_CORE_NATIVE_INCLUDE} ${GPU_HASH_NATIVE_INCLUDE} ${GPU_GKR_NATIVE_INCLUDE})
