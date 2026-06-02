cmake_minimum_required(VERSION 3.28)
# gpu_core has no production CUDA kernels; this archive exists only to back the
# field micro-benchmarks (`benches/field.rs`), built under the `bench` feature.
project(gpu_core_bench LANGUAGES CUDA)
if ((NOT DEFINED CMAKE_CUDA_ARCHITECTURES) OR (CMAKE_CUDA_ARCHITECTURES STREQUAL ""))
    set(CMAKE_CUDA_ARCHITECTURES native)
endif ()
option(GPU_CORE_ENABLE_LINEINFO "Enable lineinfo for CUDA profiling builds" OFF)
add_library(gpu_core_bench_native STATIC
        bench/field.cu
)
target_include_directories(gpu_core_bench_native PRIVATE ${GPU_CORE_NATIVE_INCLUDE})
set_target_properties(gpu_core_bench_native PROPERTIES CUDA_STANDARD 20)
set_target_properties(gpu_core_bench_native PROPERTIES CUDA_SEPARABLE_COMPILATION ON)
set_target_properties(gpu_core_bench_native PROPERTIES CUDA_RESOLVE_DEVICE_SYMBOLS ON)
# CCCL headers in CUDA 12+ require MSVC's standard conforming preprocessor.
if (MSVC)
    target_compile_options(gpu_core_bench_native PRIVATE $<$<COMPILE_LANGUAGE:CUDA>:-Xcompiler=/Zc:preprocessor>)
endif ()
target_compile_options(gpu_core_bench_native PRIVATE --expt-relaxed-constexpr)
target_compile_options(gpu_core_bench_native PRIVATE --ptxas-options=-v)
if (GPU_CORE_ENABLE_LINEINFO)
    target_compile_options(gpu_core_bench_native PRIVATE -lineinfo)
endif ()
target_compile_options(gpu_core_bench_native PRIVATE --keep)
install(TARGETS gpu_core_bench_native DESTINATION .)
