# AGENTS.md

`gpu_trace` owns witness generation and trace commit/holder: the machinery
that turns a compiled circuit + captured non-determinism into a device-resident
trace and commits it (LDE, leaf transform, Merkle-tree build). Field-specific
Rust code lives in `src/{baby_bear,proth120}/{trace,witness}/`; shared types and
helpers stay in `src/trace/` and `src/witness/`. Recursive-WHIR oracle commitment
is owned by `gpu_whir/src/baby_bear/oracle_commit.rs`. This crate carries the
`gpu_trace_native` CUDA archive.

## Layer position

`gpu_core < { gpu_ntt, gpu_ops, gpu_hash } < gpu_prover_context <
gpu_trace < gpu_gkr < gpu_whir < gpu_circuit_prover < gpu_execution_prover` — see [`../AGENTS.md`](../AGENTS.md) for the full cluster
DAG. Dependencies point only down: this crate depends on `gpu_core`,
`gpu_ntt`, `gpu_ops`, `gpu_hash`, and `gpu_prover_context`, plus
the upstream crates below; `gpu_gkr`/`gpu_whir`/`gpu_circuit_prover` depend on
it, never the reverse.

## GPU Scheduling Contract

`baby_bear::trace::holder` and `proth120::trace` schedule GPU work directly
(LDE, leaf-transform and leaf-commit kernels, and Merkle-tree builds). Before
editing shared or field-specific trace/witness code that launches kernels,
schedules host callbacks, or manages streams, read [`../docs/gpu_scheduling_contract.md`](../docs/gpu_scheduling_contract.md)
in full. Compute kernels are scheduled on `exec_stream`.

## Upstream imports

Production code (shared and field-specific trace/witness modules) imports items
from the upstream crates (`cs`, `prover`, `field`, `setups`) **exclusively through
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

- **Archive / `links` key**: `gpu_trace_native` (`build.rs` is a
  `gpu_native_build::CudaArchive::new("gpu_trace_native", "GPU_TRACE").build()`
  call — no `export_include`, no `deterministic_pow` — preceded by
  `cargo:rerun-if-changed` for each generated witness header, see below).
- **Layout**: shared headers stay in `native/witness/`; field sources and headers
  live in `native/baby_bear/` and `native/proth120/`, each with a `CMakeLists.txt`
  contributing to the same archive. Circuit templates live at
  `native/<field>/circuits/` so their generated witness include prefixes resolve.
  Include field/shared headers relative to `native/` to disambiguate basenames.
  Every field witness-generation/fused-unrolled wrapper defines its field macros
  before including the shared header; the shared headers enforce this with `#error`.
- No `__device__ __constant__` symbols in this archive (all cluster-wide ones
  live in `gpu_gkr`).
- **Namespace**: `airbender::trace::witness::*` (sub-namespaces per concern:
  `memory`, `memory::delegation`, `memory::unrolled`, `multiplicities`,
  `trace`, `trace::delegation`, `trace::unrolled`, `option`, `placeholder`,
  `tables`, `ram_access`, `generation`, `circuits::NAME`).
  This is the C++-namespace-list line item in [`../AGENTS.md`](../AGENTS.md):
  `circuit_prover` no longer owns any `airbender::witness::*` kernels.
  **Note**: `gpu_hash`'s kernels stay `airbender::hash`, unaffected by this
  split.
- **Header relationships**: witness kernels need `gpu_core`'s base headers
  (`DEP_GPU_CORE_NATIVE_INCLUDE`), their shared and field-specific local headers,
  and the committed generated witness bodies under
  `circuit_defs/**/generated/witness_generation_fn.cuh`. Those bodies sit
  outside `native/`, so `build.rs` tracks each one explicitly; a regenerated
  `.cuh` reruns the native build. `native/proth120/leaf_sink.cu` also reads
  `gpu_ntt` and `gpu_hash` headers through per-source include directories. It does not
  `export_include` — nothing includes `gpu_trace`'s native headers
  cross-crate — and it carries no PoW kernel (that stays in `gpu_hash`).

## Widening convention

Several items in shared `trace::holder`, `baby_bear::trace::holder` and elsewhere
are exposed across the crate boundary specifically for the apex e2e test suite or for production
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
