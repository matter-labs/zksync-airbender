cmake_minimum_required(VERSION 3.28)
project(gpu_cub LANGUAGES CUDA)
if ((NOT DEFINED CMAKE_CUDA_ARCHITECTURES) OR (CMAKE_CUDA_ARCHITECTURES STREQUAL ""))
    set(CMAKE_CUDA_ARCHITECTURES native)
endif ()
option(GPU_CUB_ENABLE_LINEINFO "Enable lineinfo for CUDA profiling builds" OFF)
add_library(gpu_cub_archive STATIC
        common.cuh
        device_radix_sort.cu
        device_reduce_basic.cu
        device_reduce_segmented.cu
        device_run_length_encode.cu
)
target_include_directories(gpu_cub_archive PRIVATE ${GPU_CORE_NATIVE_INCLUDE})
set_target_properties(gpu_cub_archive PROPERTIES CUDA_STANDARD 20)
set_target_properties(gpu_cub_archive PROPERTIES CUDA_SEPARABLE_COMPILATION ON)
set_target_properties(gpu_cub_archive PROPERTIES CUDA_RESOLVE_DEVICE_SYMBOLS ON)
# CCCL/CUB headers in CUDA 12+ require MSVC's standard conforming preprocessor.
if (MSVC)
    target_compile_options(gpu_cub_archive PRIVATE $<$<COMPILE_LANGUAGE:CUDA>:-Xcompiler=/Zc:preprocessor>)
endif ()
target_compile_options(gpu_cub_archive PRIVATE --expt-relaxed-constexpr)
target_compile_options(gpu_cub_archive PRIVATE --ptxas-options=-v)
if (GPU_CUB_ENABLE_LINEINFO)
    target_compile_options(gpu_cub_archive PRIVATE -lineinfo)
endif ()
target_compile_options(gpu_cub_archive PRIVATE --keep)
install(TARGETS gpu_cub_archive DESTINATION .)
