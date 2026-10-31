target_sources(gpu_trace_native PRIVATE
        field.cuh
        memory.cuh
        relations.cuh
        witness_generation.cuh
        fused_unrolled.cuh
        template_unrolled.cuh
        memory_unrolled.cu
        multiplicities.cu
        probe.cu
)
