cmake_minimum_required(VERSION 3.28)
# gpu_core has no production CUDA kernels; this archive exists only to back the
# field micro-benchmarks (`benches/field.rs`), built under the `bench` feature.
project(gpu_core_bench LANGUAGES CUDA)
if ((NOT DEFINED CMAKE_CUDA_ARCHITECTURES) OR (CMAKE_CUDA_ARCHITECTURES STREQUAL ""))
    set(CMAKE_CUDA_ARCHITECTURES native)
endif ()
if (NOT DEFINED AB_CUDA_CMAKE_DIR)
    # Standalone/IDE configure fallback; under cargo, gpu_native_build passes -DAB_CUDA_CMAKE_DIR.
    set(AB_CUDA_CMAKE_DIR ${CMAKE_CURRENT_SOURCE_DIR}/../../native_build/cmake)
endif ()
include(${AB_CUDA_CMAKE_DIR}/ab_cuda_target.cmake)
add_library(gpu_core_bench_native STATIC
        bench/field.cu
)
ab_cuda_configure_target(gpu_core_bench_native PREFIX GPU_CORE INCLUDE_DIRS ${GPU_CORE_NATIVE_INCLUDE})
