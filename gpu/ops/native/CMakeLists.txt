cmake_minimum_required(VERSION 3.28)
project(gpu_ops LANGUAGES CUDA)
if ((NOT DEFINED CMAKE_CUDA_ARCHITECTURES) OR (CMAKE_CUDA_ARCHITECTURES STREQUAL ""))
    set(CMAKE_CUDA_ARCHITECTURES native)
endif ()
if (NOT DEFINED AB_CUDA_CMAKE_DIR)
    # Standalone/IDE configure fallback; under cargo, gpu_native_build passes -DAB_CUDA_CMAKE_DIR.
    set(AB_CUDA_CMAKE_DIR ${CMAKE_CURRENT_SOURCE_DIR}/../../native_build/cmake)
endif ()
include(${AB_CUDA_CMAKE_DIR}/ab_cuda_target.cmake)
add_library(gpu_ops_native STATIC
        batch_inv.cu
        batch_inv.cuh
        bit_reverse.cu
        powers.cu
        simple.cu
        squaring.cu
        transpose.cu
)
ab_cuda_configure_target(gpu_ops_native PREFIX GPU_OPS INCLUDE_DIRS ${GPU_CORE_NATIVE_INCLUDE})
