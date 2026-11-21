target_sources(gpu_gkr_native PRIVATE
        gkr_ops_shared.cuh
        query_indexes.cu
        round_update_shared.cuh
)

add_subdirectory(baby_bear)
add_subdirectory(proth120)
