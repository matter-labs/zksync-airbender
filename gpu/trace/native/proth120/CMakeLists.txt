target_sources(gpu_trace_native PRIVATE
        circuits/template_unrolled.cuh
        circuits/unified_reduced_machine.cu
        field.cuh
        fused_unrolled.cuh
        leaf_sink.cu
        memory_unrolled.cu
        multiplicities.cu
        relations.cuh
        witness_generation.cuh
)
