target_sources(circuit_prover_native PRIVATE
        descriptors.cuh
        eq_constant_storage.cu
        eq_inline.cuh
        gkr_initial_inner_products.cu
        kernel_helpers.cuh
        lookup_helpers.cuh
)
