target_sources(gpu_gkr_native PRIVATE
    batch_challenges_pr.cuh
    coefficient_bank_pr.cu
    dr_tail_megakernel.cu
    extras.cu
    main_tail.cu
    window_tail.cu
)

add_subdirectory(main_continuation_window)
add_subdirectory(window)
add_subdirectory(window_dr)
