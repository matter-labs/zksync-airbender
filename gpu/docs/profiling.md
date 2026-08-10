# Profiling GPU kernels

How to profile a kernel in any `gpu/` crate. Start from the generic GPU workflow
in [`../../.agents/gpu_work.md`](../../.agents/gpu_work.md) (build unlocked, then
run the produced binary under `.agents/bin/with_gpu_lock.sh`).

Tool-specific guides:

- [`profiling_ncu.md`](./profiling_ncu.md): Nsight Compute (`ncu`) — per-kernel
  profiling (quick set, full source-correlated, dependency-sensitive range replay).
  This is about profiling **specific kernels**, so it applies to any crate's
  kernels, not just the prover.
- [`profiling_nsys.md`](./profiling_nsys.md): Nsight Systems (`nsys`) — timeline /
  NVTX-range capture and GPU-projected NVTX stats.

Both guides are written against parameters that the calling crate supplies:

| Parameter | Meaning |
|---|---|
| `$TEST_BINARY` | the unlocked-built test/bench binary that exercises the kernel(s) — capture it via `cargo test\|bench -p <crate> <filter> --release --no-run --message-format=json \| python3 .agents/bin/cargo_test_executables.py` |
| `$NSYS_NVTX_RANGE` | the NVTX capture range as `message@domain` for `nsys` |
| `$NCU_NVTX_RANGE` | the same registered range as `domain@message` for `ncu` (the tools use opposite orderings) |
| `$SOURCE_FOLDERS` | the crate's `native/` dir, for `ncu --import-source` |
| lineinfo rebuild | rebuild with the crate's `GPU_<X>_ENABLE_LINEINFO=1` (e.g. `GPU_NTT_ENABLE_LINEINFO`, `GPU_GKR_ENABLE_LINEINFO`) — `gpu_native_build` wires it to `nvcc -lineinfo` for source correlation |
| build-diag rebuild | rebuild with the crate's `GPU_<X>_ENABLE_BUILD_DIAG=1` (e.g. `GPU_NTT_ENABLE_BUILD_DIAG`, `GPU_GKR_ENABLE_BUILD_DIAG`) — `gpu_native_build` wires it to `nvcc --ptxas-options=-v` (per-kernel register/spill/smem report; captured to `target/<profile>/build/<crate>-<hash>/stderr`, echoed only under `cargo build -vv`) plus `--keep` (PTX/cubin intermediates retained in the crate's CMake build dir; with a compiler launcher such as sccache active, the ptxas report is still cached and replayed but the kept intermediates do not survive — disable the launcher for the run when you need them) |

Crate-specific profiling setups — *which* test/bench, *which* NVTX range — live
with the crate. Example: [`../circuit_prover/docs/profiling.md`](../circuit_prover/docs/profiling.md)
supplies the prover's values (the `run_add_sub_profile_test`
binary and the `test.gpu.prove.profiled_call@gpu_circuit_prover.tests` range).
