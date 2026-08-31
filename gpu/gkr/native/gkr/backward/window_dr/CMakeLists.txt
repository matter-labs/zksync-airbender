target_sources(gpu_gkr_native PRIVATE
        continuation.cuh
        ../generated/dr_cont_window_universal.cu
        ../generated/dr_r0_window_universal.cu
        ../generated/dr_windowed_cont_manifest.cuh
        ../generated/dr_windowed_r0_manifest.cuh
        r0.cuh
)
