option(GPU_CORE_BUILD_BENCH "Compile the field micro-benchmark kernels into the archive" OFF)
if (GPU_CORE_BUILD_BENCH)
    target_sources(gpu_core_native PRIVATE bench/field.cu)
endif ()
