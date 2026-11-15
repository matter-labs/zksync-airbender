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
# The leaf sink reads gpu_ntt's Proth120 transform and gpu_hash's keccak256 headers;
# keep these include directories local to the leaf sink source.
set_source_files_properties(leaf_sink.cu TARGET_DIRECTORY gpu_trace_native PROPERTIES
        INCLUDE_DIRECTORIES "${GPU_HASH_NATIVE_INCLUDE};${GPU_NTT_NATIVE_INCLUDE}")
