target_sources(gpu_gkr_native PRIVATE
        dim_reducing.cu
        dr_tail_megakernel.cu
        main_tail.cu
        window_tail.cu
        continuation_eval.cuh
        dr_tail_megakernel.cuh
        main_tail.cuh
        tail_common.cuh
)

add_subdirectory(main_continuation_window)
add_subdirectory(window)
add_subdirectory(window_dr)
