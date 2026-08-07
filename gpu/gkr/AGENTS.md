# AGENTS.md

`gpu_gkr` owns the GKR engine: the forward pass (`forward/`), the
backward/sumcheck rounds (`backward/`), setup (`setup/`), base-layer claims
(`base_layer_claims/`), the proof layout model (`proof_layout/`), and the
GKR/WHIR protocol kernels (`gkr_ops/`, e.g. transcript/PoW-adjacent
sumcheck-round helpers) that used to live in `circuit_prover`'s
`ops::gkr_ops`. It carries the `gpu_gkr_native` CUDA archive (the tree that
used to live under `circuit_prover/native/gkr/` and `native/ops/gkr_ops.cu`).

## Layer position

`gpu_core < { gpu_ntt, gpu_ops, gpu_hash, gpu_cub } < gpu_prover_context <
gpu_trace < gpu_gkr < gpu_whir < gpu_circuit_prover < gpu_execution_prover <
gpu_program_prover` — see [`../AGENTS.md`](../AGENTS.md) for the full cluster
DAG. Dependencies point only down: this crate depends on `gpu_core`,
`gpu_ops`, `gpu_hash`, `gpu_cub`, `gpu_prover_context`, `gpu_trace`,
`gpu_gkr_model`, `gpu_gkr_compiler`, and `gkr_eval_ir`, plus the upstream crates below;
`gpu_whir` and `gpu_circuit_prover` depend on it, never the reverse.

The GPU-free CPU model of the GKR layout lives in the standalone
`gpu_gkr_model` crate; this crate imports it internally.

The GPU-independent evaluation DAG lives in the root `gkr_eval_ir` crate. The
CPU-only `gpu_gkr_compiler` consumes that DAG and produces the checked forward,
R0, and continuation programs used here; its offline search is feature-gated and
never runs during prover initialization.

## GPU Scheduling Contract

`forward`, `backward`, `setup`, and `gkr_ops` all schedule GPU work directly
(kernel launches, host callbacks, pool allocations). Before editing any of
these, or anything else that launches kernels or manages streams, read
[`../docs/gpu_scheduling_contract.md`](../docs/gpu_scheduling_contract.md) in
full. It governs the async stream-ordered model used by GKR, WHIR, and
related proving workflows.

## Upstream imports

Production code imports items from the upstream crates (`cs`, `prover`,
`field`) **exclusively through `crate::upstream`**. Direct `use cs::…;` /
`use prover::…;` in non-test code is forbidden. `#[cfg(test)]` modules are
exempt.

- Adding a dependency: `pub(crate) use …;` in
  [`src/upstream.rs`](src/upstream.rs), then `use crate::upstream::Item;`
  from the consumer.

## Upstream constant drift guards

This crate's native code hard-codes no upstream-crate-owned values today. The
established drift-guard pattern and its current home (`gpu_trace`'s
`src/witness/mod.rs`, guarding witness-circuit constants owned by `cs` /
`common_constants`) are documented in
[`../trace/AGENTS.md`](../trace/AGENTS.md). If a future change here
hard-codes a value owned by an upstream crate, add a compile-time assert
following that same pattern (a scalar `const _: () = assert!(...)`, or the
struct + `.assert_matches(...)` pattern for grouped values) in an
appropriate Rust module of this crate rather than letting the duplicate
drift by convention.

## Native code (`gpu_gkr_native`)

- **Archive / `links` key**: `gpu_gkr_native` (`build.rs`:
  `gpu_native_build::CudaArchive::new("gpu_gkr_native", "GPU_GKR").export_include(true).build()`).
- Nothing device-side crosses the archive boundary — `gpu_whir` reads only
  pointer-based inline helpers and compile-time constants from this crate,
  never a `__constant__` symbol.
- **Namespace**: `airbender::gkr::{backward, forward, ops, setup}` (plus
  shared support code directly under `airbender::gkr`).
- **Header relationships**: `export_include(true)` — this crate exports its
  `native/` dir as `DEP_GPU_GKR_NATIVE_INCLUDE`, consumed by `gpu_whir`'s
  `accumulate_eq.cu` for `gkr/support/{eq_inline,kernel_helpers}.cuh` (which
  pulls in `descriptors.cuh`). This crate itself reads `gpu_core`'s base
  headers and `gpu_hash`'s `hash.cuh` (via `DEP_GPU_HASH_NATIVE_INCLUDE`) for
  the blake2s-dependent protocol kernels in `ops/gkr_ops.cu`.

## Widening convention

- `#[doc(hidden)] pub use storage_types::{...}` — storage/descriptor types
  the apex e2e suite and proof orchestration name across the crate boundary
  (test-reference surface, not production API).
- Plain `pub` is production cross-crate API.

## Build and Test

- Minimum validation for any code change: `cargo check -p gpu_gkr`
- Build: `cargo build -p gpu_gkr`
- Test: two safe harnesses — `cargo nextest run -p gpu_gkr` for
  unattended/full-suite runs (the `gpu-serial` group in the workspace
  [`.config/nextest.toml`](../../.config/nextest.toml) serializes GPU tests,
  terminates hung tests, and isolates sticky CUDA errors per process), or
  plain `cargo test -p gpu_gkr` as the zero-overhead attended path (the
  pre-main `gpu_core::force_serial_libtest!()` guard at the crate root
  forces `RUST_TEST_THREADS=1`). The crate carries no `#[serial]`
  annotations. CPU-only tests may be named or moduled `cpu_*` to run
  parallel under nextest.
- For compute-heavy GPU tests or prover flows, use `--release` by default.
- Compile first with `cargo nextest run --no-run`, then run under
  `.agents/bin/with_gpu_lock.sh cargo nextest run …` so only the execution
  step holds the GPU lock.

## Formatting

- Rust: `cargo fmt -p gpu_gkr` only — never crate/workspace-wide `cargo fmt`.
- Native CUDA/C++ under `native/`: `clang-format` against the cluster-wide
  [`../.clang-format`](../.clang-format) (see [`../AGENTS.md`](../AGENTS.md)).
  `cargo fmt` does not cover this; CI does not enforce it. A change that
  touches both languages needs both formatters.
