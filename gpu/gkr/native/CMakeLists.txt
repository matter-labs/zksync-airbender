cmake_minimum_required(VERSION 3.28)
# Cmake must be at least 3.28 - the earlier one didn't pass cuda_standard properly.
project(gpu_gkr_native)
enable_language(CUDA)
if ((NOT DEFINED CMAKE_CUDA_ARCHITECTURES) OR (CMAKE_CUDA_ARCHITECTURES STREQUAL ""))
    set(CMAKE_CUDA_ARCHITECTURES native)
endif ()
if (NOT DEFINED AB_CUDA_CMAKE_DIR)
    # Standalone/IDE configure fallback; under cargo, gpu_native_build passes -DAB_CUDA_CMAKE_DIR.
    set(AB_CUDA_CMAKE_DIR ${CMAKE_CURRENT_SOURCE_DIR}/../../native_build/cmake)
endif ()
include(${AB_CUDA_CMAKE_DIR}/ab_cuda_target.cmake)
add_library(gpu_gkr_native STATIC)
target_sources(gpu_gkr_native PRIVATE
        gkr/backward/dr_tail_shared.cuh
        gkr/backward/tail_common.cuh
        gkr/backward/window/common.cuh
        gkr/backward/window/fold_weights_shared.cuh
        gkr/backward/window/window_abi.cuh
        gkr/backward/window/window_geometry.cuh
        gkr/backward/window/window_source.cuh
        gkr/backward/window_dr/corner_quad.cuh
        gkr/eval_vm_isa.cuh
        gkr/forward/fwd_vm.cuh
        gkr/forward/vm_addresses.cuh
        gkr/support/descriptors.cuh
        gkr/support/eq_high_low.cuh
        gkr/support/eq_inline.cuh
        gkr/support/initial_inner_product.cuh
        gkr/support/kernel_helpers.cuh
        gkr/support/lookup_helpers.cuh
        ops/gkr_ops_shared.cuh
        ops/query_indexes.cu
        ops/round_update_shared.cuh
)
# Preserve the pre-layout source order: device-link constant addresses depend on it.
add_subdirectory(ops/baby_bear)
add_subdirectory(ops/proth120)
add_subdirectory(gkr/baby_bear)
add_subdirectory(gkr/proth120)
# The compiler owns this generated field-specific source list.
add_subdirectory(gkr/proth120/backward/main_continuation_window)
ab_cuda_configure_target(gpu_gkr_native
        PREFIX GPU_GKR
        INCLUDE_DIRS ${CMAKE_CURRENT_SOURCE_DIR} ${GPU_CORE_NATIVE_INCLUDE} ${GPU_HASH_NATIVE_INCLUDE})
