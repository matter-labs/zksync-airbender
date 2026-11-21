option(GPU_CORE_BUILD_BENCH "Compile the field micro-benchmark kernels into the archive" OFF)
if (GPU_CORE_BUILD_BENCH)
    add_subdirectory(bench)
endif ()
