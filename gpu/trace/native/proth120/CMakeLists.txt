add_subdirectory(circuits)

target_sources(gpu_trace_native PRIVATE
        field.cuh
        fused_unrolled.cuh
        leaf_sink.cu
        memory_unrolled.cu
        multiplicities.cu
        relations.cuh
        witness_generation.cuh
)
