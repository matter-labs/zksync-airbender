cmake_minimum_required(VERSION 3.28)
project(gpu_hash LANGUAGES CUDA)
if ((NOT DEFINED CMAKE_CUDA_ARCHITECTURES) OR (CMAKE_CUDA_ARCHITECTURES STREQUAL ""))
    set(CMAKE_CUDA_ARCHITECTURES native)
endif ()
if (NOT DEFINED AB_CUDA_CMAKE_DIR)
    # Standalone/IDE configure fallback; under cargo, gpu_native_build passes -DAB_CUDA_CMAKE_DIR.
    set(AB_CUDA_CMAKE_DIR ${CMAKE_CURRENT_SOURCE_DIR}/../../native_build/cmake)
endif ()
include(${AB_CUDA_CMAKE_DIR}/ab_cuda_target.cmake)
add_library(gpu_hash_native STATIC
        gather.cu
        hash.cu
        hash.cuh
        keccak256.cuh
        keccak256_hash.cu
        keccak256_merkle.cu
        keccak256_gather.cu
        keccak256_transcript.cu
)
option(GPU_HASH_BUILD_BENCH "Compile bench-only Keccak256 kernels into the archive" OFF)
if (GPU_HASH_BUILD_BENCH)
    target_sources(gpu_hash_native PRIVATE bench/keccak256_bench.cu bench/keccak_f.cu bench/pow_bench.cu)
endif ()
ab_cuda_configure_target(gpu_hash_native PREFIX GPU_HASH DETERMINISTIC_POW INCLUDE_DIRS ${GPU_CORE_NATIVE_INCLUDE})
