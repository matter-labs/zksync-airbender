target_sources(gpu_gkr_native PRIVATE
        coefficient_bank_pr.cu
        dr_tail_megakernel.cu
        extras.cu
        main_tail.cu
        window_tail.cu
        accumulator_pr.cuh
        batch_challenges_pr.cuh
        coefficient_bank_pr.cuh
        coefficient_storage_pr.cuh
        dr_tail_megakernel.cuh
        fold_prologue_pr.cuh
        main_continuation_executor_pr.cuh
        main_tail.cuh
        tail_common_pr.cuh
)

add_subdirectory(window)
add_subdirectory(window_dr)

# The compiler owns this generated field-specific source list.
add_subdirectory(main_continuation_window)
