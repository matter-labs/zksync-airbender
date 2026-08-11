target_sources(gpu_gkr_native PRIVATE
        ../eval_vm_isa.cuh
        ../eval_vm_exec.cuh
        dim_reducing_tower.cu
        fwd_vm.cuh
        fwd_vm.cu
)
