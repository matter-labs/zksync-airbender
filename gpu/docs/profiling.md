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
| `$NVTX_RANGE` | the NVTX capture range as `message@domain`, opened around the work to profile (a registered range via `gpu_core`'s `primitives::nvtx`) |
| `$SOURCE_FOLDERS` | the crate's `native/` dir, for `ncu --import-source` |
| lineinfo rebuild | rebuild with the crate's `GPU_<X>_ENABLE_LINEINFO=1` (e.g. `GPU_NTT_ENABLE_LINEINFO`, `GPU_PROVER_ENABLE_LINEINFO`) — `gpu_native_build` wires it to `nvcc -lineinfo` for source correlation |

Crate-specific profiling setups — *which* test/bench, *which* NVTX range — live
with the crate. Example: [`../circuit_prover/docs/profiling.md`](../circuit_prover/docs/profiling.md)
supplies the prover's values (the `run_basic_unrolled_proof_job_profile_test`
binary and the `test.gpu.prove.profiled_call@circuit_prover.tests` range).
