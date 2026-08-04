cmake_minimum_required(VERSION 3.28)
project(gpu_cub LANGUAGES CUDA)
if ((NOT DEFINED CMAKE_CUDA_ARCHITECTURES) OR (CMAKE_CUDA_ARCHITECTURES STREQUAL ""))
    set(CMAKE_CUDA_ARCHITECTURES native)
endif ()
if (NOT DEFINED AB_CUDA_CMAKE_DIR)
    # Standalone/IDE configure fallback; under cargo, gpu_native_build passes -DAB_CUDA_CMAKE_DIR.
    set(AB_CUDA_CMAKE_DIR ${CMAKE_CURRENT_SOURCE_DIR}/../../native_build/cmake)
endif ()
include(${AB_CUDA_CMAKE_DIR}/ab_cuda_target.cmake)
add_library(gpu_cub_native STATIC
        common.cuh
        device_radix_sort.cu
        device_reduce_basic.cu
        device_reduce_segmented.cu
        device_run_length_encode.cu
)
ab_cuda_configure_target(gpu_cub_native PREFIX GPU_CUB INCLUDE_DIRS ${GPU_CORE_NATIVE_INCLUDE})
