cmake_minimum_required(VERSION 3.28)
# gpu_core has no production CUDA kernels: the archive holds the field-header
# test probes and, under the `bench` feature, the field micro-benchmarks.
project(gpu_core LANGUAGES CUDA)
if ((NOT DEFINED CMAKE_CUDA_ARCHITECTURES) OR (CMAKE_CUDA_ARCHITECTURES STREQUAL ""))
    set(CMAKE_CUDA_ARCHITECTURES native)
endif ()
if (NOT DEFINED AB_CUDA_CMAKE_DIR)
    # Standalone/IDE configure fallback; under cargo, gpu_native_build passes -DAB_CUDA_CMAKE_DIR.
    set(AB_CUDA_CMAKE_DIR ${CMAKE_CURRENT_SOURCE_DIR}/../../native_build/cmake)
endif ()
include(${AB_CUDA_CMAKE_DIR}/ab_cuda_target.cmake)
add_library(gpu_core_native STATIC)
add_subdirectory(baby_bear)
add_subdirectory(proth120)
ab_cuda_configure_target(gpu_core_native PREFIX GPU_CORE INCLUDE_DIRS ${GPU_CORE_NATIVE_INCLUDE})
