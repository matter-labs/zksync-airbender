# Shared CUDA static-archive configuration for the airbender gpu/ kernel crates.
# Shipped by the gpu_native_build crate; its Rust helper passes this file's
# directory to CMake as -DAB_CUDA_CMAKE_DIR (each per-crate CMakeLists keeps a
# relative fallback for standalone/IDE configure).
#
#   ab_cuda_configure_target(<target>
#       PREFIX <PREFIX>            # env/-D prefix, e.g. GPU_OPS / GPU_PROVER
#       [INCLUDE_DIRS <dir>...]    # PRIVATE include dirs (forwarded *_NATIVE_INCLUDE vars)
#       [DETERMINISTIC_POW])       # honor the AB_DETERMINISTIC_POW toggle
#
# Diagnostics (both default OFF, wired from env vars by gpu_native_build):
#   <PREFIX>_ENABLE_LINEINFO   -> nvcc -lineinfo (ncu source correlation; alters device code)
#   <PREFIX>_ENABLE_BUILD_DIAG -> nvcc --ptxas-options=-v + --keep (per-kernel register/
#                                 spill report + retained PTX/cubin intermediates)

function(ab_cuda_configure_target target)
    cmake_parse_arguments(ARG "DETERMINISTIC_POW" "PREFIX" "INCLUDE_DIRS" ${ARGN})

    option(${ARG_PREFIX}_ENABLE_LINEINFO "Enable lineinfo for CUDA profiling builds" OFF)
    option(${ARG_PREFIX}_ENABLE_BUILD_DIAG "Enable nvcc build diagnostics (ptxas -v, --keep)" OFF)

    if (ARG_INCLUDE_DIRS)
        target_include_directories(${target} PRIVATE ${ARG_INCLUDE_DIRS})
    endif ()

    set_target_properties(${target} PROPERTIES
            CUDA_STANDARD 20
            CUDA_SEPARABLE_COMPILATION ON
            CUDA_RESOLVE_DEVICE_SYMBOLS ON)

    if (ARG_DETERMINISTIC_POW)
        option(AB_DETERMINISTIC_POW "Enable deterministic PoW search" OFF)
        if (AB_DETERMINISTIC_POW)
            target_compile_definitions(${target} PRIVATE AB_DETERMINISTIC_POW=1)
        endif ()
    endif ()

    # CCCL headers in CUDA 12+ require MSVC's standard conforming preprocessor.
    if (MSVC)
        target_compile_options(${target} PRIVATE $<$<COMPILE_LANGUAGE:CUDA>:-Xcompiler=/Zc:preprocessor>)
    endif ()

    target_compile_options(${target} PRIVATE --expt-relaxed-constexpr)

    if (${ARG_PREFIX}_ENABLE_LINEINFO)
        target_compile_options(${target} PRIVATE -lineinfo)
    endif ()

    if (${ARG_PREFIX}_ENABLE_BUILD_DIAG)
        target_compile_options(${target} PRIVATE --ptxas-options=-v --keep)
    endif ()

    install(TARGETS ${target} DESTINATION .)
endfunction()
