target_sources(gpu_prover_new_native PRIVATE
        common.cuh
        device_radix_sort.cu
        device_reduce.cu
        device_run_length_encode.cu
)
add_subdirectory(device_scan)