use std::env;

fn main() {
    let mut archive = gpu_native_build::CudaArchive::new("gpu_ntt_native", "GPU_NTT");
    if env::var_os("CARGO_FEATURE_BENCH").is_some() {
        archive = archive.define("GPU_NTT_BUILD_BENCH", "ON");
    }
    archive.build();
}
