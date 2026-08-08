cmake_minimum_required(VERSION 3.28)
project(gpu_gkr_uniskip_bench LANGUAGES CUDA)
if ((NOT DEFINED CMAKE_CUDA_ARCHITECTURES) OR (CMAKE_CUDA_ARCHITECTURES STREQUAL ""))
    set(CMAKE_CUDA_ARCHITECTURES native)
endif ()
if (NOT DEFINED AB_CUDA_CMAKE_DIR)
    # Standalone/IDE configure fallback; under cargo, gpu_native_build passes -DAB_CUDA_CMAKE_DIR.
    set(AB_CUDA_CMAKE_DIR ${CMAKE_CURRENT_SOURCE_DIR}/../../native_build/cmake)
endif ()
include(${AB_CUDA_CMAKE_DIR}/ab_cuda_target.cmake)
add_library(gpu_gkr_uniskip_bench_native STATIC
        uniskip.cu
        uniskip_lsb.cu
        uniskip_lsb_compact.cu
        uniskip_lsb_pair.cu
)
ab_cuda_configure_target(gpu_gkr_uniskip_bench_native PREFIX GPU_GKR_UNISKIP_BENCH INCLUDE_DIRS ${GPU_CORE_NATIVE_INCLUDE})
