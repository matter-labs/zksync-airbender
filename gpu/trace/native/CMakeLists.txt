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
add_subdirectory(witness)
add_subdirectory(baby_bear)
add_subdirectory(proth120)
# The Proth120 leaf sink reads gpu_ntt's Proth120 transform and gpu_hash's keccak256
# headers; keep these include directories local to the leaf sink source.
set_source_files_properties(proth120/leaf_sink.cu PROPERTIES
        INCLUDE_DIRECTORIES "${GPU_HASH_NATIVE_INCLUDE};${GPU_NTT_NATIVE_INCLUDE}")
ab_cuda_configure_target(gpu_trace_native
        PREFIX GPU_TRACE
        INCLUDE_DIRS ${CMAKE_CURRENT_SOURCE_DIR} ${GPU_CORE_NATIVE_INCLUDE})
