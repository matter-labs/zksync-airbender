# AGENTS.md

`gpu_trace` owns witness generation (`witness/**`) and trace commit/holder
(`trace/**`): the machinery that turns a compiled circuit + captured
non-determinism into a device-resident trace and commits it (LDE, leaf
transform, Merkle-tree build). It carries the `gpu_trace_native` CUDA archive
(the tree that used to live under `circuit_prover/native/witness/`).

## Layer position

`gpu_core < { gpu_ntt, gpu_ops, gpu_hash, gpu_cub } < gpu_prover_context <
gpu_trace < gpu_gkr < gpu_whir < gpu_circuit_prover < gpu_execution_prover <
gpu_program_prover` — see [`../AGENTS.md`](../AGENTS.md) for the full cluster
DAG. Dependencies point only down: this crate depends on `gpu_core`,
`gpu_ntt`, `gpu_ops`, `gpu_hash`, `gpu_cub`, and `gpu_prover_context`, plus
the upstream crates below; `gpu_gkr`/`gpu_whir`/`gpu_circuit_prover` depend on
it, never the reverse.

## GPU Scheduling Contract

`trace::holder` schedules GPU work directly (LDE, leaf-transform, and
leaf-commit kernels; the Merkle-tree build; the trace holder's parallel-commit
use of `side_stream`). Before editing anything under `src/trace/` or
`src/witness/` that launches kernels, schedules host callbacks, or manages
streams, read [`../docs/gpu_scheduling_contract.md`](../docs/gpu_scheduling_contract.md)
in full — in particular the *Side stream* section, which documents this
crate's `commit_trace_from_ntt_single_tree` (`src/trace/holder/mod.rs`) as the
only current consumer of `ProverContext::get_side_stream()`.

## Upstream imports

Production code (`witness/**`, `trace/**`) imports items from the upstream
crates (`cs`, `prover`, `field`, `setups`) **exclusively through
`crate::upstream`**. Direct `use cs::…;` / `use prover::…;` in non-test code
is forbidden. `#[cfg(test)]` modules are exempt.

- Adding a dependency: `pub(crate) use …;` in
  [`src/upstream.rs`](src/upstream.rs), then `use crate::upstream::Item;`
  from the consumer.
- Aliases avoid collisions with crate-local types of the same name (e.g.
  `CSExecutorFamilyDecoderData`, the various `CS*` aliases for
  `cs::definitions::gkr::*` types) — use the aliased names.

## Upstream constant drift guards

When `native/**` hard-codes a value owned by an upstream crate (`cs`,
`common_constants`, …), add a compile-time assert in
[`src/witness/mod.rs`](src/witness/mod.rs) comparing the upstream value
against the native literal. Failures surface at `cargo check`. This is the
same drift-guard location the pre-split `circuit_prover` used — it moved here
because the witness CUDA it guards moved here.

- Scalars: `const _: () = assert!(crate::upstream::FOO == N);`.
- Grouped values (e.g. delegation `AbiDescription`, here `DelegationAbi`): use
  a struct + `.assert_matches(...)` pattern, already established in the file.
- Internal Rust↔CUDA duplicates are not asserted (the assert needs one side
  to be external); fix structurally or rely on tests.
- Do not let a duplicate drift by convention — add or update the guard
  whenever native code hard-codes or duplicates an upstream-owned value,
  rather than relying on the duplicate staying in sync by review alone.

## Native code (`gpu_trace_native`)

- **Archive / `links` key**: `gpu_trace_native` (`build.rs` is a one-line
  `gpu_native_build::CudaArchive::new("gpu_trace_native", "GPU_TRACE").build()`
  call — no `export_include`, no `deterministic_pow`).
- **Kernel count**: 28 (`__global__` kernels, verified by grep) — 17 literal
  (`memory_delegation.cu` 8, `memory_unrolled.cu` 7, `multiplicities.cu` 2)
  plus 11 token-pasted `ab_generate_witness_values_<NAME>_kernel` symbols
  (never appear as literals in native — formed by the `KERNEL_NAME(NAME)`
  macro in `witness_generation.cuh`, one per circuit under
  `witness/circuits/`). No `__device__ __constant__` symbols in this archive
  (all 8 cluster-wide ones live in `gpu_gkr`).
- **Namespace**: `airbender::trace::witness::*` (sub-namespaces per concern:
  `memory`, `memory::delegation`, `memory::unrolled`, `multiplicities`,
  `trace`, `trace::delegation`, `trace::unrolled`, `option`, `placeholder`,
  `tables`, `ram_access`, `generation`, `circuits::NAME`).
  This is the C++-namespace-list line item in [`../AGENTS.md`](../AGENTS.md):
  `circuit_prover` no longer owns any `airbender::witness::*` kernels.
  **Note**: `gpu_hash`'s kernels stay `airbender::hash`, unaffected by this
  split.
- **Header relationships**: self-contained. It needs only `gpu_core`'s base
  headers (`DEP_GPU_CORE_NATIVE_INCLUDE`) plus its own local headers and the
  committed generated witness bodies under
  `circuit_defs/**/generated/witness_generation_fn.cuh`. It does not
  `export_include` — nothing includes `gpu_trace`'s native headers
  cross-crate — and it carries no PoW kernel (that stays in `gpu_hash`).

## Widening convention

Several items in `trace::holder` and elsewhere are exposed across the crate
boundary specifically for the apex e2e test suite or for production
cross-crate consumers — each site carries a `// pub because …` /
`// test-reference` comment naming the caller:

- `#[doc(hidden)] pub` = a test-reference seam only (the apex e2e suite
  reaches in) — not part of the production API surface.
- Plain `pub` + why-pub comment = a genuine production cross-crate API (e.g.
  types/functions `gpu_gkr`/`gpu_whir`/`gpu_circuit_prover` consume directly,
  like `trace::holder::{TraceHolder, TreesCacheMode, PARTIAL_TREE_REDUCTION_LAYERS}`).

## Build and Test

- Minimum validation for any code change: `cargo check -p gpu_trace`
- Build: `cargo build -p gpu_trace`
- Test: two safe harnesses — `cargo nextest run -p gpu_trace` for
  unattended/full-suite runs (the `gpu-serial` group in the workspace
  [`.config/nextest.toml`](../../.config/nextest.toml) serializes GPU tests,
  terminates hung tests, and isolates sticky CUDA errors per process), or
  plain `cargo test -p gpu_trace` as the zero-overhead attended path (the
  pre-main `gpu_core::force_serial_libtest!()` guard at the crate root
  forces `RUST_TEST_THREADS=1`). The crate carries no `#[serial]`
  annotations. CPU-only tests may be named or moduled `cpu_*` to run
  parallel under nextest.
- For compute-heavy GPU tests or prover flows, use `--release` by default.
- Compile first with `cargo nextest run --no-run`, then run under
  `.agents/bin/with_gpu_lock.sh cargo nextest run …` so only the execution
  step holds the GPU lock.

## Formatting

- Rust: `cargo fmt -p gpu_trace` only — never crate/workspace-wide `cargo fmt`.
- Native CUDA/C++ under `native/`: `clang-format` against the cluster-wide
  [`../.clang-format`](../.clang-format) (see [`../AGENTS.md`](../AGENTS.md)).
  `cargo fmt` does not cover this; CI does not enforce it. A change that
  touches both languages needs both formatters.
