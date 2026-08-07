fn main() {
    let native_headers =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../core/native_headers");
    gpu_native_build::CudaArchive::new("gpu_gkr_windowed_bench_native", "GPU_GKR_WINDOWED_BENCH")
        .define(
            "GPU_CORE_NATIVE_INCLUDE",
            native_headers
                .to_str()
                .expect("gpu_core native header path must be valid UTF-8"),
        )
        .build();
}
