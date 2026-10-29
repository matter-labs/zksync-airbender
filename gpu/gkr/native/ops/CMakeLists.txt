target_sources(gpu_gkr_native PRIVATE
        gkr_ops.cu
        packed_merge.cu
        gkr_ops_helpers.cuh
        proth120/gkr_ops.cu
)
