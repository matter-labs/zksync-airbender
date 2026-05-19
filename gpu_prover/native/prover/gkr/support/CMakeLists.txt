target_sources(gpu_prover_native PRIVATE
        descriptors.cuh
        eq_constant_storage.cu
        eq_inline.cuh
        kernel_helpers.cuh
        lookup_helpers.cuh
)
