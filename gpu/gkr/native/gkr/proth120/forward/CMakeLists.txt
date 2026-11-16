target_sources(gpu_gkr_native PRIVATE
        fwd_vm.cu
        challenge_banks.cu
        dim_reducing_tower.cu
        eval_vm_exec_pr.cuh
        fwd_vm.cuh
)
