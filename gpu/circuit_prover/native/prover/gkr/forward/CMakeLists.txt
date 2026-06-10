target_sources(circuit_prover_native PRIVATE
        cache.cu
        dim_reducing_tower.cu
        flat.cuh
        flat_layer.cu
        gkr_forward_generation.cuh
        gkr_forward_generation.cu
        add_sub_lui_auipc_mop_fwd.cu
)
