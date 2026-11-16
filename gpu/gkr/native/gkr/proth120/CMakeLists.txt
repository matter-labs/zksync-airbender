target_sources(gpu_gkr_native PRIVATE
        # Translation-unit order preserves the pre-layout device-link constant layout.
        forward/fwd_vm.cu
        forward/challenge_banks.cu
        forward/dim_reducing_tower.cu
        setup/kernels.cu
        support/eq_tables.cu
        support/initial_inner_products.cu
        ops/gather_base_claims.cu
        ops/packed_merge.cu
        backward/coefficient_bank_pr.cu
        backward/dr_tail_megakernel.cu
        backward/extras.cu
        backward/main_tail.cu
        backward/window_tail.cu
        backward/window/r0.cu
        backward/window/state.cu
        backward/window_dr/continuation.cu
        backward/window_dr/r0.cu
        # Field-specific headers.
        backward/accumulator_pr.cuh
        backward/batch_challenges_pr.cuh
        backward/coefficient_bank_pr.cuh
        backward/coefficient_storage_pr.cuh
        backward/dr_tail_megakernel.cuh
        backward/fold_prologue_pr.cuh
        backward/main_continuation_executor_pr.cuh
        backward/main_tail.cuh
        backward/tail_common_pr.cuh
        backward/window/r0.cuh
        backward/window_dr/abi_pr.cuh
        backward/window_dr/evaluate_pr.cuh
        forward/eval_vm_exec_pr.cuh
        forward/fwd_vm.cuh
        setup/lookup_helpers_pr.cuh
)
