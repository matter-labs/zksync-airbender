target_sources(gpu_gkr_native PRIVATE
    forward/fwd_vm.cu
    forward/challenge_banks.cu
    forward/dim_reducing_tower.cu
    setup/kernels.cu
    support/eq_tables.cu
    support/initial_inner_products.cu
)
