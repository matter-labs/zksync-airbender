target_sources(gpu_prover_new_native PRIVATE
        common.cuh
        memory.cuh
#        memory_delegation.cu
        memory_unrolled.cu
#        multiplicities.cu
        option.cuh
        placeholder.cuh
        ram_access.cuh
        tables.cuh
        trace.cuh
#        trace_delegation.cuh
        trace_unrolled.cuh
        witness_generation.cuh
)
add_subdirectory(circuits)
