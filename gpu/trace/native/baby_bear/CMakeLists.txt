add_subdirectory(circuits)

target_sources(gpu_trace_native PRIVATE
        field.cuh
        fused_delegation.cuh
        fused_unrolled.cuh
        memory_delegation.cu
        memory_unrolled.cu
        multiplicities.cu
        witness_generation.cuh
)
