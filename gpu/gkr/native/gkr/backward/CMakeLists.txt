target_sources(gpu_gkr_native PRIVATE
        continuation_eval.cuh
        dim_reducing.cu
        dr_tail_megakernel.cu
        dr_tail_megakernel.cuh
        main_tail.cu
        main_tail.cuh
        mega_finalize.cuh
        window_tail.cu
)

add_subdirectory(main_continuation_window)
add_subdirectory(window)
add_subdirectory(window_dr)
