target_sources(gpu_gkr_native PRIVATE
        eval_vm_exec.cuh
)

add_subdirectory(support)
add_subdirectory(forward)
add_subdirectory(backward)
add_subdirectory(setup)
