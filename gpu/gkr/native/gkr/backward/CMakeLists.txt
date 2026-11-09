target_sources(gpu_gkr_native PRIVATE
        continuation_eval.cuh
        dim_reducing.cu
        dr_tail_megakernel.cu
        dr_tail_megakernel.cuh
        dr_tail_shared.cuh
        main_tail.cu
        main_tail.cuh
        tail_common.cuh
        window_tail.cu
)

add_subdirectory(main_continuation_window)
add_subdirectory(window)
add_subdirectory(window_dr)
