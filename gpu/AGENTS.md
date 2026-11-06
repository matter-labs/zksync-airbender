# AGENTS.md — GPU crate cluster

This governs every crate under `gpu/` (the GPU prover stack). Crates may add a more
specific `AGENTS.md`; this file holds the rules and architecture that span the
cluster. Read it before adding a crate, moving native code, or changing the build.

## Crate stack (dependency DAG)

Dependency edges point only down this order (kept true by review):

```text
gpu_core  <  { gpu_ntt, gpu_ops, gpu_hash }  <  gpu_prover_context  <
gpu_trace  <  gpu_gkr  <  gpu_whir  <  circuit_prover  <  execution_prover
```

Off the DAG: `gpu_witness_eval_generator` (CPU codegen of the committed
`circuit_defs/**/generated/witness_generation_fn.cuh` witness bodies, drift-guarded by
`committed_witness_cuh_is_current`; see its `AGENTS.md`), `gpu_gkr_model` (CPU GKR
layout model used by `gpu_gkr`), `gpu_gkr_compiler` (CPU compiler for the committed
forward and backward programs; search behind the `search` feature, built on the
workspace-root `gkr_eval_ir`), and `gpu_native_build` (the shared build-script helper).

- **`gpu_core`**: allocators and GPU primitives, and the base CUDA headers
  (`native_headers/`, exported as `DEP_GPU_CORE_NATIVE_INCLUDE`). No production
  kernels. Its headers are a complete library on purpose: the PTX cache-operator set,
  u32 and u64 carry chains, the field operations (incl. `e6`) and the full accessor
  matrix stay even when unused in-project. Broken or incomplete vestiges may still go.
- **`gpu_ntt`**: NTT launchers, twiddles and `native/ntt`; exports `native/` so
  `gpu_whir` can include `whir_leaf_transform.cuh`.
- **`gpu_ops`**: generic math and transform kernels. `bit_reverse_in_place<T>` is
  size-generic (4/16/32-byte elements) and asserts payload alignment.
- **`gpu_hash`**: blake2s hashing, Merkle trees, gather and the Fiat-Shamir transcript
  (commit/squeeze/PoW); exports `hash.cuh` for `gpu_gkr` and `gpu_whir`. Its
  `deterministic_pow` feature must be on for CPU proof-byte parity tests (enabled via
  `gpu_whir/deterministic_pow`, which `circuit_prover/deterministic_pow` forwards);
  without it PoW search is nondeterministic.
- **`gpu_prover_context`**: `ProverContext` (device and host allocators, `exec_stream`,
  `h2d_stream`, NTT twiddles) and the H2D `Transfer`. Every crate from `gpu_trace` up
  threads a `&ProverContext` through its scheduling functions.
- **`gpu_trace`**: witness generation and trace commit/holder; owns the
  upstream-constant drift guards (`src/witness/mod.rs`).
- **`gpu_gkr`**: the GKR engine and the GKR/WHIR protocol kernels; holds the
  cluster's `__constant__` symbols and exports its headers for `gpu_whir`.
- **`gpu_whir`**: WHIR folds, PoW and query scheduling, and the recursive WHIR oracle.
- **`circuit_prover`**: proof orchestration and config over the crates above; no
  native code.
- **`execution_prover`** (`gpu_execution_prover`): implements the root
  `execution_prover` backend; the root `program_prover` assembles proofs from either
  backend. GPU program-level tests are in `gpu/execution_prover/tests/program.rs`
  (feature `verifiers`).

Test-and-production helpers used across crate boundaries are `#[doc(hidden)] pub`,
because a dependency's `#[cfg(test)]` items are invisible to its consumers.

## Cross-crate conventions

- **Build:** each kernel crate's `build.rs` is one `gpu_native_build::CudaArchive`
  call. The static lib, CMake target and `links` key are `<crate>_native`; header
  include dirs propagate as `DEP_<X>_NATIVE_INCLUDE`. Shared CMake configuration is
  `native_build/cmake/ab_cuda_target.cmake`; change behavior for all kernel crates
  there.
- **C++ namespace = owning crate** (`airbender::{hash, ntt, ops, primitives,
  trace::witness, gkr, whir}`). Launched kernels are `extern "C"`: the bare symbol
  name is the ABI.
- **Benches** live in the owning crate behind a non-default `bench` feature; bench
  `.cu` files compile only under it.
- **Tests:** no `#[serial]` (and no `serial_test` dependency).
  - `cargo nextest` (default for unattended and full runs): the `gpu-serial` group in
    `.config/nextest.toml` runs one GPU test at a time in its own process.
  - `cargo test` (attended, filtered runs): the pre-main
    `gpu_core::force_serial_libtest!()` guard at each GPU crate root forces one test
    thread; `AB_GPU_TESTS_ALLOW_PARALLEL=1` bypasses it. Integration-test targets
    invoke the macro themselves; GPU doctests stay `ignore`/`no_run`.
  - Tests or modules named `cpu_*` are GPU-free and run in parallel under nextest.
  - A new GPU crate must join the `gpu-serial` filter and invoke the guard
    (checked by `cpu_nextest_config_covers_all_gpu_crates`).

## Native code (CUDA/C++)

- **Formatting:** `clang-format` with [`.clang-format`](.clang-format) for every touched
  `.cu`/`.cuh`/`.h`; `cargo fmt` does not cover native code.
- **Rust↔CUDA interface:** keep kernel symbol names and launcher expectations stable
  unless both sides change together in the same task.
- **Never permute the lane→leaf axis of a bulk read or write.** A hashing or
  commitment kernel must not route a per-lane index through `bitreverse` (or any
  permutation) before addressing leaf values; it destroys coalescing. Put order
  conversions on a warp-uniform index, a 32-byte digest slot, or query/cap emission.

## Profiling

Methodology: [`docs/profiling.md`](docs/profiling.md) (with `profiling_ncu.md` and
`profiling_nsys.md`). Crate-specific setups live with the crate, e.g.
[`circuit_prover/docs/profiling.md`](circuit_prover/docs/profiling.md).

## Per-crate files

[`prover_context/AGENTS.md`](prover_context/AGENTS.md),
[`trace/AGENTS.md`](trace/AGENTS.md), [`gkr/AGENTS.md`](gkr/AGENTS.md),
[`whir/AGENTS.md`](whir/AGENTS.md), [`circuit_prover/AGENTS.md`](circuit_prover/AGENTS.md).
`gpu_core`, `gpu_ntt`, `gpu_ops`, `gpu_hash` and `gpu_gkr_model` have none; this file is
their contract.
