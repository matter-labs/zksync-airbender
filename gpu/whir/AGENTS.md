# AGENTS.md

`gpu_whir` owns the WHIR polynomial-commitment folding rounds (`fold/`) and
the PoW-verify/query-index scheduling (`pow.rs`), plus the recursive WHIR
extension oracle (`lib.rs`). It carries the `gpu_whir_native` CUDA archive
(the WHIR/PoW protocol kernels that used to live under
`circuit_prover/native/whir/`).

## Layer position

`gpu_core < { gpu_ntt, gpu_ops, gpu_hash, gpu_cub } < gpu_prover_context <
gpu_trace < gpu_gkr < gpu_whir < gpu_circuit_prover < gpu_execution_prover <
gpu_program_prover` — see [`../AGENTS.md`](../AGENTS.md) for the full cluster
DAG. Dependencies point only down: this crate depends on `gpu_core`,
`gpu_ntt`, `gpu_ops`, `gpu_hash`, `gpu_cub`, `gpu_prover_context`, `gpu_trace`,
and `gpu_gkr`, plus the upstream crates below; `gpu_circuit_prover` depends on
it, never the reverse.

## GPU Scheduling Contract

`fold` and `pow` schedule GPU work directly (kernel launches, host callbacks,
pool allocations, D2H readback for query answers). Before editing either, or
anything else that launches kernels or manages streams, read
[`../docs/gpu_scheduling_contract.md`](../docs/gpu_scheduling_contract.md) in
full.

## Upstream imports

Production code imports items from the upstream crates (`field`, `prover`)
**exclusively through `crate::upstream`**. Direct `use field::…;` /
`use prover::…;` in non-test code is forbidden. `#[cfg(test)]` sites are
exempt.

`prover` is a **normal** (not dev-only) dependency here — unlike most kernel
crates — because the `deterministic_pow` feature forwards
`prover/deterministic_pow` (its host-side PoW determinism leg). This crate
therefore owns that forward leg (see Cargo.toml `[features]`);
`gpu_circuit_prover` only needs to enable `gpu_whir/deterministic_pow`.

The WHIR-oracle parity + query test-support surface (`#[doc(hidden)] pub`,
reached by the apex e2e/parity suite, `gpu_circuit_prover`'s
`src/tests/whir_oracle_parity.rs` via `stagewise.rs`) references `prover`
types (`MerkleTreeCapVarLength`, `extension_field_from_base_coeffs`, the
transcript/commitment helpers) — but that surface is **not** compiled into the
normal library. It lives behind the non-default **`test-utils`** feature, gated
`#[cfg(any(test, feature = "test-utils"))]` (the `any(test, …)` half so the
crate's own tests need no feature) — the same precedent as the `prover` crate's
`test-utils`. `gpu_circuit_prover` enables it from its `[dev-dependencies]`
(`gpu_whir = { … , features = ["test-utils"] }`); the normal `[dependencies]`
entry never enables it, so a production build compiles neither the oracle
parity/query helpers, the `fold::debug` checkpoint builders, nor the
`GpuWhirState.scalar` reservation. Every `prover`-sourced re-export in
`crate::upstream` is part of this test-support surface and is gated the same way
(or `#[cfg(test)]` for items only whir's own tests use); `field::FieldExtension`
is the one production upstream item (the kernels' `EXT4_DEGREE`).

## Upstream constant drift guards

This crate's native code hard-codes no upstream-crate-owned values today (no
`assert!(crate::upstream::…)` compile-time guards exist here). The established
drift-guard pattern and its current home (`gpu_trace`'s `src/witness/mod.rs`,
guarding witness-circuit constants owned by `cs` / `common_constants`) are
documented in [`../trace/AGENTS.md`](../trace/AGENTS.md). If a future change
here hard-codes a value owned by an upstream crate, add a compile-time assert
following that same pattern in an appropriate Rust module of this crate
rather than letting the duplicate drift by convention.

## Native code (`gpu_whir_native`)

- **Archive / `links` key**: `gpu_whir_native` (`build.rs`:
  `gpu_native_build::CudaArchive::new("gpu_whir_native", "GPU_WHIR").build()`
  — no `export_include`; nothing above this crate includes its headers).
- **Kernel count**: 17 `__global__` kernels (verified by grep, across
  `whir/{accumulate_eq,columns,fold,leaves}.cu`). No `__constant__` symbols
  (all 8 cluster-wide ones live in `gpu_gkr`).
- **Namespace**: `airbender::whir`.
- **Header relationships**: `accumulate_eq.cu` includes `gpu_gkr`'s
  `gkr/support/{eq_inline,kernel_helpers}.cuh` via
  `DEP_GPU_GKR_NATIVE_INCLUDE` (forwarded because `gpu_gkr`'s build.rs sets
  `export_include(true)`); `leaves.cu` includes `gpu_hash`'s `hash.cuh` via
  `DEP_GPU_HASH_NATIVE_INCLUDE`. Both directories resolve automatically as
  CMake `-D` defines that `gpu_native_build` forwards. This crate also reads
  `gpu_core`'s base headers. `deterministic_pow` is not a native `#define`
  here: the PoW search kernel itself lives in `gpu_hash`, so
  `gpu_whir/deterministic_pow` forwards to `gpu_hash/deterministic_pow`
  (and to `prover/deterministic_pow`, above) instead of defining
  `AB_DETERMINISTIC_POW` on this archive.
- **`eval_leaves` feature**: commits recursive WHIR oracle leaves in
  evaluation form instead of the default coefficient form (#279); the single
  cfg site is `fold/schedule/round_phases.rs`. PROTOCOL-level — the generated
  verifier must be built with the matching encoding
  (`verifier_generator eval_leaves`). The GPU commit transform itself is
  native and independent of `prover`/`gpu_hash`.

## Widening convention

- `#[doc(hidden)] pub struct GpuWhirExtensionOracle` is production API (the
  return type of the production `schedule_from_device_monomial_coeffs_into_slab`
  / `schedule_query_for_folded_indexes_to_slab` fold path), but its
  `from_monomial_coeffs` / `from_device_monomial_coeffs` / `get_tree_cap` /
  `query_for_folded_index` / `schedule_query_for_folded_index` parity+query
  methods are **test-support only**, gated `#[cfg(any(test, feature =
  "test-utils"))]`. They are reached by the apex e2e/parity suite across the
  crate boundary and structurally can't move down (their consumer is a
  full-pipeline apex test), but they are not compiled into a production build —
  see "Upstream imports" for the `test-utils` feature. The same gate covers the
  `fold::debug` checkpoint builders (the ~976-line `fold/debug.rs` module,
  behind `#[doc(hidden)] pub mod debug`) and the `GpuWhirState.scalar`
  device reservation.
- `GpuWhirExtensionOracleKeepalive` stays `pub(crate)` — internal keepalive
  wiring, not reached across the crate boundary.
- Plain `pub` (e.g. `pow` module entry points, `fold` scheduling functions
  `gpu_circuit_prover` calls directly) = production cross-crate API.

## Build and Test

- Minimum validation for any code change: `cargo check -p gpu_whir`
- Build: `cargo build -p gpu_whir`
- Test: two safe harnesses — `cargo nextest run -p gpu_whir` for
  unattended/full-suite runs (the `gpu-serial` group in the workspace
  [`.config/nextest.toml`](../../.config/nextest.toml) serializes GPU tests,
  terminates hung tests, and isolates sticky CUDA errors per process), or
  plain `cargo test -p gpu_whir` as the zero-overhead attended path (the
  pre-main `gpu_core::force_serial_libtest!()` guard at the crate root
  forces `RUST_TEST_THREADS=1`). The crate carries no `#[serial]`
  annotations. CPU-only tests may be named or moduled `cpu_*` to run
  parallel under nextest.
- For compute-heavy GPU tests or prover flows, use `--release` by default.
- Compile first with `cargo nextest run --no-run`, then run under
  `.agents/bin/with_gpu_lock.sh cargo nextest run …` so only the execution
  step holds the GPU lock.

## Formatting

- Rust: `cargo fmt -p gpu_whir` only — never crate/workspace-wide `cargo fmt`.
- Native CUDA/C++ under `native/`: `clang-format` against the cluster-wide
  [`../.clang-format`](../.clang-format) (see [`../AGENTS.md`](../AGENTS.md)).
  `cargo fmt` does not cover this; CI does not enforce it. A change that
  touches both languages needs both formatters.
