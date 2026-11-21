target_sources(gpu_gkr_native PRIVATE
        eq_constant_storage.cu
        gkr_initial_inner_products.cu
        descriptors.cuh
        eq_inline.cuh
        kernel_helpers.cuh
        lookup_helpers.cuh
)
