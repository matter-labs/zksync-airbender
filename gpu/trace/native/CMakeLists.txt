cmake_minimum_required(VERSION 3.28)
# Cmake must be at least 3.28 - the earlier one didn't pass cuda_standard properly.
project(gpu_trace_native)
enable_language(CUDA)
if ((NOT DEFINED CMAKE_CUDA_ARCHITECTURES) OR (CMAKE_CUDA_ARCHITECTURES STREQUAL ""))
    set(CMAKE_CUDA_ARCHITECTURES native)
endif ()
if (NOT DEFINED AB_CUDA_CMAKE_DIR)
    # Standalone/IDE configure fallback; under cargo, gpu_native_build passes -DAB_CUDA_CMAKE_DIR.
    set(AB_CUDA_CMAKE_DIR ${CMAKE_CURRENT_SOURCE_DIR}/../../native_build/cmake)
endif ()
include(${AB_CUDA_CMAKE_DIR}/ab_cuda_target.cmake)
add_library(gpu_trace_native STATIC)
target_sources(gpu_trace_native PRIVATE
        witness/common.cuh
        witness/fused_trace_accessor.cuh
        witness/fused_unrolled.cuh
        witness/inits_and_teardowns.cuh
        witness/lookup_mapping.cuh
        witness/memory.cuh
        witness/memory_delegation.cuh
        witness/memory_unrolled.cuh
        witness/multiplicities.cuh
        witness/option.cuh
        witness/placeholder.cuh
        witness/ram_access.cuh
        witness/tables.cuh
        witness/trace.cuh
        witness/trace_delegation.cuh
        witness/trace_unrolled.cuh
        witness/witness_generation.cuh
)
add_subdirectory(baby_bear)
add_subdirectory(proth120)
ab_cuda_configure_target(gpu_trace_native
        PREFIX GPU_TRACE
        INCLUDE_DIRS ${CMAKE_CURRENT_SOURCE_DIR} ${GPU_CORE_NATIVE_INCLUDE})
