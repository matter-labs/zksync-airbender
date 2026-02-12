target_sources(gpu_prover_native PRIVATE
        add_sub_lui_auipc_mop.cu
        template_delegation.cuh
        template_unrolled_memory.cuh
        template_unrolled_non_memory.cuh
        template_unrolled_unified.cuh
)
