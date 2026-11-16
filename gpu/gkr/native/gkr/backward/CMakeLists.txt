target_sources(gpu_gkr_native PRIVATE
        dr_tail_shared.cuh
        tail_common.cuh
)

add_subdirectory(window)
add_subdirectory(window_dr)
