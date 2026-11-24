use std::fs;

fn main() {
    // `gpu_trace_native` is the witness-generation CUDA archive (the `airbender::
    // trace::witness::*` kernels). Witness kernels use the gpu_core base headers
    // (forwarded as `DEP_GPU_CORE_NATIVE_INCLUDE`), the archive's shared and
    // field-specific headers, and the committed generated witness bodies under
    // `circuit_defs/**/generated/`. No `export_include` — nothing includes the
    // witness headers cross-crate; no `deterministic_pow` — this archive has no
    // PoW kernel (that lives in gpu_hash). The Proth120 leaf sink also reads
    // gpu_ntt and gpu_hash headers through per-source CMake include directories.
    //
    // The generated witness bodies live outside `native/`, so track them here.
    // The two directories match `INCLUDE_PREFIX` and `UNROLLED_INCLUDE_PREFIX` in
    // `native/witness/witness_generation.cuh`.
    for circuits_dir in ["../../circuit_defs", "../../circuit_defs/unrolled_circuits"] {
        let mut headers = fs::read_dir(circuits_dir)
            .unwrap_or_else(|err| panic!("failed to read {circuits_dir}: {err}"))
            .map(|entry| {
                entry
                    .unwrap_or_else(|err| panic!("failed to enumerate {circuits_dir}: {err}"))
                    .path()
                    .join("generated/witness_generation_fn.cuh")
            })
            .filter(|header| header.is_file())
            .collect::<Vec<_>>();
        headers.sort();
        for header in headers {
            println!("cargo:rerun-if-changed={}", header.display());
        }
    }
    gpu_native_build::CudaArchive::new("gpu_trace_native", "GPU_TRACE").build();
}
