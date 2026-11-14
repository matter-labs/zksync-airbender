# The leaf sink reads gpu_ntt's Proth120 transform and gpu_hash's keccak256 headers; the include
# dirs are set on its source only so the witness sources keep their compile flags.
target_sources(gpu_trace_native PRIVATE leaf_sink.cu)
set_source_files_properties(leaf_sink.cu TARGET_DIRECTORY gpu_trace_native PROPERTIES
        INCLUDE_DIRECTORIES "${GPU_HASH_NATIVE_INCLUDE};${GPU_NTT_NATIVE_INCLUDE}")
