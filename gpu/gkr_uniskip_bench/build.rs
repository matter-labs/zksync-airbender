fn main() {
    // gpu_core is a dev-dependency here (crate-root serial guard only), so there is
    // no DEP_GPU_CORE_NATIVE_INCLUDE to auto-forward — pass the header dir directly.
    let native_headers =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../core/native_headers");
    gpu_native_build::CudaArchive::new("gpu_gkr_uniskip_bench_native", "GPU_GKR_UNISKIP_BENCH")
        .define("GPU_CORE_NATIVE_INCLUDE", native_headers.to_str().unwrap())
        .build();
}
