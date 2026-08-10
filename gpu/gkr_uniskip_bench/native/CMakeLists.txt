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
        uniskip_lsb_seg.cu
        # LAST on purpose: the pair TU's SASS is frozen, and appending the rider's own
        # `__constant__` array must not renumber constant-bank offsets ahead of it.
        uniskip_ldc_probe.cu
)
ab_cuda_configure_target(gpu_gkr_uniskip_bench_native PREFIX GPU_GKR_UNISKIP_BENCH INCLUDE_DIRS ${GPU_CORE_NATIVE_INCLUDE})
if (AB_UNISKIP_WINDOW_DIAG)
    target_compile_definitions(gpu_gkr_uniskip_bench_native PRIVATE AB_UNISKIP_WINDOW_DIAG)
endif ()
