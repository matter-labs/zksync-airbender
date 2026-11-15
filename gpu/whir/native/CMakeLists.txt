cmake_minimum_required(VERSION 3.28)
# Cmake must be at least 3.28 - the earlier one didn't pass cuda_standard properly.
project(gpu_whir_native)
enable_language(CUDA)
if ((NOT DEFINED CMAKE_CUDA_ARCHITECTURES) OR (CMAKE_CUDA_ARCHITECTURES STREQUAL ""))
    set(CMAKE_CUDA_ARCHITECTURES native)
endif ()
if (NOT DEFINED AB_CUDA_CMAKE_DIR)
    # Standalone/IDE configure fallback; under cargo, gpu_native_build passes -DAB_CUDA_CMAKE_DIR.
    set(AB_CUDA_CMAKE_DIR ${CMAKE_CURRENT_SOURCE_DIR}/../../native_build/cmake)
endif ()
include(${AB_CUDA_CMAKE_DIR}/ab_cuda_target.cmake)
# WHIR protocol + PoW kernels. `baby_bear/accumulate_eq.cu` resolves gpu_gkr's eq/kernel
# headers via ${GPU_GKR_NATIVE_INCLUDE}; `baby_bear/leaves.cu` resolves gpu_hash's
# `hash.cuh` and gpu_ntt's reusable WHIR transform through their exported
# include directories. These dirs arrive as DEP_* env vars that
# gpu_native_build forwards as CMake -D defines.
add_library(gpu_whir_native STATIC
        fold_shared.cuh
        in_domain_shared.cuh
)
add_subdirectory(baby_bear)
add_subdirectory(proth120)
ab_cuda_configure_target(gpu_whir_native
        PREFIX GPU_WHIR
        INCLUDE_DIRS ${GPU_CORE_NATIVE_INCLUDE} ${GPU_HASH_NATIVE_INCLUDE} ${GPU_GKR_NATIVE_INCLUDE} ${GPU_NTT_NATIVE_INCLUDE})
