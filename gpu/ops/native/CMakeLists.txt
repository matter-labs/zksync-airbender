cmake_minimum_required(VERSION 3.28)
project(gpu_ops LANGUAGES CUDA)
if ((NOT DEFINED CMAKE_CUDA_ARCHITECTURES) OR (CMAKE_CUDA_ARCHITECTURES STREQUAL ""))
    set(CMAKE_CUDA_ARCHITECTURES native)
endif ()
option(GPU_OPS_ENABLE_LINEINFO "Enable lineinfo for CUDA profiling builds" OFF)
add_library(gpu_ops_native STATIC
        batch_inv.cu
        batch_inv.cuh
        bit_reverse.cu
        powers.cu
        simple.cu
        squaring.cu
        transpose.cu
)
target_include_directories(gpu_ops_native PRIVATE ${GPU_CORE_NATIVE_INCLUDE})
set_target_properties(gpu_ops_native PROPERTIES CUDA_STANDARD 20)
set_target_properties(gpu_ops_native PROPERTIES CUDA_SEPARABLE_COMPILATION ON)
set_target_properties(gpu_ops_native PROPERTIES CUDA_RESOLVE_DEVICE_SYMBOLS ON)
# CCCL headers in CUDA 12+ require MSVC's standard conforming preprocessor.
if (MSVC)
    target_compile_options(gpu_ops_native PRIVATE $<$<COMPILE_LANGUAGE:CUDA>:-Xcompiler=/Zc:preprocessor>)
endif ()
target_compile_options(gpu_ops_native PRIVATE --expt-relaxed-constexpr)
target_compile_options(gpu_ops_native PRIVATE --ptxas-options=-v)
if (GPU_OPS_ENABLE_LINEINFO)
    target_compile_options(gpu_ops_native PRIVATE -lineinfo)
endif ()
target_compile_options(gpu_ops_native PRIVATE --keep)
install(TARGETS gpu_ops_native DESTINATION .)
