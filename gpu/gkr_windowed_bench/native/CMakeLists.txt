cmake_minimum_required(VERSION 3.28)
project(gpu_gkr_windowed_bench LANGUAGES CUDA)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)
set(CMAKE_VERBOSE_MAKEFILE ON)
if ((NOT DEFINED CMAKE_CUDA_ARCHITECTURES) OR (CMAKE_CUDA_ARCHITECTURES STREQUAL ""))
    set(CMAKE_CUDA_ARCHITECTURES native)
endif ()
if (NOT DEFINED AB_CUDA_CMAKE_DIR)
    set(AB_CUDA_CMAKE_DIR ${CMAKE_CURRENT_SOURCE_DIR}/../../native_build/cmake)
endif ()
include(${AB_CUDA_CMAKE_DIR}/ab_cuda_target.cmake)
add_library(
        gpu_gkr_windowed_bench_native STATIC
        windowed_vm.cu
        windowed_r0_abi_probe.cu
        windowed_r0_constants.cu
        windowed_r0_cta288_pair.cu
        windowed_r0_cta96_partitioned.cu
        windowed_r0_cta96_x0_major.cu
        windowed_r0_cta96_x1_major.cu
        windowed_r0_cta96_x2_major.cu)

if (NOT DEFINED GPU_GKR_WINDOWED_R0_PROTOTYPE_NATIVE)
    set(GPU_GKR_WINDOWED_R0_PROTOTYPE_NATIVE "off")
endif ()
if (NOT GPU_GKR_WINDOWED_R0_PROTOTYPE_NATIVE MATCHES "^(off|canary|full)$")
    message(FATAL_ERROR "GPU_GKR_WINDOWED_R0_PROTOTYPE_NATIVE must be exactly off, canary, or full")
endif ()
if (NOT DEFINED GPU_GKR_WINDOWED_R0_PROTOTYPE_FEATURE)
    set(GPU_GKR_WINDOWED_R0_PROTOTYPE_FEATURE OFF)
endif ()
if (GPU_GKR_WINDOWED_R0_PROTOTYPE_FEATURE)
    target_sources(gpu_gkr_windowed_bench_native PRIVATE windowed_r0_prototype_abi_probe.cu)
endif ()
if ((NOT GPU_GKR_WINDOWED_R0_PROTOTYPE_NATIVE STREQUAL "off") AND (NOT GPU_GKR_WINDOWED_R0_PROTOTYPE_FEATURE))
    message(FATAL_ERROR "prototype native mode requires the r0-prototype-bank feature")
endif ()
if (GPU_GKR_WINDOWED_R0_PROTOTYPE_NATIVE STREQUAL "canary")
    target_sources(gpu_gkr_windowed_bench_native PRIVATE windowed_r0_prototype_canary.cu)
elseif (GPU_GKR_WINDOWED_R0_PROTOTYPE_NATIVE STREQUAL "full")
    include(${CMAKE_CURRENT_LIST_DIR}/generated/windowed_r0_prototype_sources.cmake)
    target_sources(gpu_gkr_windowed_bench_native PRIVATE ${GPU_GKR_WINDOWED_R0_PROTOTYPE_SOURCES})
endif ()

function(configure_r0_geometry_source geometry source)
    set(min_blocks_var "GPU_GKR_WINDOWED_R0_${geometry}_MIN_BLOCKS")
    set(maxreg_var "GPU_GKR_WINDOWED_R0_${geometry}_MAXREG")
    if (DEFINED ${min_blocks_var})
        set(min_blocks "${${min_blocks_var}}")
    else ()
        set(min_blocks "0")
    endif ()
    if (DEFINED ${maxreg_var})
        set(maxreg "${${maxreg_var}}")
    else ()
        set(maxreg "0")
    endif ()
    if (NOT min_blocks MATCHES "^[0-9]+$")
        message(FATAL_ERROR "${min_blocks_var} must be a nonnegative integer")
    endif ()
    if (NOT maxreg MATCHES "^[0-9]+$")
        message(FATAL_ERROR "${maxreg_var} must be a nonnegative integer")
    endif ()
    if (min_blocks GREATER 0)
        set_property(
                SOURCE ${source} APPEND PROPERTY
                COMPILE_DEFINITIONS "${min_blocks_var}=${min_blocks}")
    endif ()
    if (maxreg GREATER 0)
        set_property(
                SOURCE ${source} APPEND PROPERTY
                COMPILE_OPTIONS "--maxrregcount=${maxreg}")
    endif ()
endfunction()

configure_r0_geometry_source(CTA288_PAIR windowed_r0_cta288_pair.cu)
configure_r0_geometry_source(CTA96_PARTITIONED windowed_r0_cta96_partitioned.cu)
configure_r0_geometry_source(CTA96_X0_MAJOR windowed_r0_cta96_x0_major.cu)
configure_r0_geometry_source(CTA96_X1_MAJOR windowed_r0_cta96_x1_major.cu)
configure_r0_geometry_source(CTA96_X2_MAJOR windowed_r0_cta96_x2_major.cu)

ab_cuda_configure_target(
        gpu_gkr_windowed_bench_native
        PREFIX GPU_GKR_WINDOWED_BENCH
        INCLUDE_DIRS ${GPU_CORE_NATIVE_INCLUDE})
