target_sources(gpu_gkr_native PRIVATE
        eval_vm_isa.cuh
)

add_subdirectory(backward)
add_subdirectory(forward)
add_subdirectory(support)

# Field traversal preserves the existing device-link constant layout.
add_subdirectory(baby_bear)
add_subdirectory(proth120)
