# AGENTS.md

`circuit_prover` (crate `gpu_circuit_prover`) is the **apex** of the GPU
prover-cluster DAG: proof orchestration (`proof/`), prover configuration
policy (`config.rs`), and the e2e/parity test suite. It has **no native CUDA
of its own** — the split-out kernel crates below it (`gpu_trace`, `gpu_gkr`,
`gpu_whir`) own all the CUDA; this crate's `build.rs` only emits the
`no_cuda` cfg (`gpu_native_build::emit_no_cuda_cfg()`) that its
`#[cfg(not(no_cuda))]` test sites key off of.

## Layer position

`gpu_core < { gpu_ntt, gpu_ops, gpu_hash, gpu_cub } < gpu_prover_context <
gpu_trace < gpu_gkr < gpu_whir < gpu_circuit_prover < gpu_execution_prover <
gpu_program_prover` — see [`../AGENTS.md`](../AGENTS.md) for the full cluster
DAG. This crate depends on `gpu_core`, `gpu_hash`, `gpu_prover_context`,
`gpu_trace`, `gpu_gkr`, `gpu_whir`, and `gpu_gkr_model`, plus the upstream
crates below; `gpu_execution_prover` depends on it, never the reverse.

## GPU Scheduling Contract

Before editing anything under `src/proof/orchestration/`, or any other code
that launches kernels, schedules host callbacks, or manages streams, you MUST
read [`../docs/gpu_scheduling_contract.md`](../docs/gpu_scheduling_contract.md)
in full. It governs the async stream-ordered model used by GKR, WHIR, trace
commit, and related proving workflows across every crate in the cluster.

The cheatsheet below summarizes the rules most often violated. It is a
summary — the contract document is the source of truth.

- **MUST NOT** dereference pool-backed device or host allocations from the
  scheduling thread. All reads and writes must be expressed as stream ops:
  kernel launches, `memory_copy_async`, or host callbacks scheduled via
  `Callbacks::schedule` / `launch_host_fn`. `UnsafeAccessor::get()` /
  `UnsafeMutAccessor::get_mut()` are only valid inside stream-scheduled
  closures.
- **MUST** fill stream-ordered H2D staging buffers via a scheduled host
  callback (captured `UnsafeMutAccessor`). `.copy_from_slice(...)` right after
  allocation races the prior pool owner's outstanding DMA, even when it
  appears to work.
- **`SchedulerHostAllocator` is the separate pinned host pool for immutable,
  scheduling-time-known H2D sources** (compiled kernel descriptors, recipe
  tables, etc.). Its access rule is **inverted** vs. the stream-ordered pool:
  the scheduling thread writes once during construction, and every stream
  operation thereafter only reads.
- **MUST** consume D2H readback buffers via a scheduled host callback, never
  from the scheduling thread.
- **MUST** fork/join any op on an auxiliary stream (`h2d_stream`,
  `d2h_stream`, or `side_stream`) against `exec_stream` with explicit CUDA
  events. The driver gives independent streams no implicit ordering.
- **MUST** allocate and drop pool-backed handles on `exec_stream`. If a
  secondary stream touched the allocation, the `exec_stream` join wait must be
  scheduled before the Rust drop — otherwise it is a use-after-free.
- **MUST** observe write-exclusivity within any fork/join window: exactly one
  stream writes a shared buffer. Concurrent reads are fine; concurrent writes,
  or a read racing a write across streams, are not.
- **MUST** keep a Rust handle alive until every op holding a raw pointer into
  it (via accessors or embedding structs) has been **scheduled**. Scheduling
  is enough — completion is not required.
- **MUST NOT** call any CUDA API from within a host callback, and callbacks
  must not create or destroy pool-backed allocations. Callbacks exist to
  compute challenge-dependent host data only.
- **MUST** keep `prove()` enqueue-only. No `stream.synchronize()`, no host
  blocking for `exec_stream` progress — not even for profiling or logging.
  Host blocking belongs in `GpuGKRProofJob::finish()`.
- **Default to `exec_stream`** for H2D/D2H copies. Use `h2d_stream` /
  `d2h_stream` only when meaningful copy/compute overlap justifies the
  fork/join machinery.

## Key Files and Structure

- `build.rs`: no native archive — a thin wrapper over
  `gpu_native_build::emit_no_cuda_cfg()` only, since the CUDA moved to
  `gpu_trace`/`gpu_gkr`/`gpu_whir`.
- `src/lib.rs`: crate root; declares `config`, `proof`, `upstream` (+
  `#[cfg(test)]` `test_utils`/`tests`).
- `src/config.rs`: prover configuration policy — maps a `CircuitType` +
  `SecurityLevel` to the canonical upstream `ProverConfig`, and owns
  `GPU_SUPPORTED_SECURITY_LEVELS` / `UnsupportedGpuSecurityLevel`.
- `src/proof/`:
  - `inputs.rs`: the consolidated H2D transfer bundle
    (`GpuGKRProofTransfer`) — one shared `Transfer` (from `gpu_prover_context`)
    for every pre-prove H2D piece.
  - `layout/` (`pub(crate)`): `build_proof_layout_inputs` — the
    gkr-**dependent** BUILDER that derives the proof-image layout inputs from
    a compiled circuit + WHIR schedule + base-layer geometries. The layout
    TYPES themselves (slab byte ranges + typed accessors) live one layer down
    in `gpu_gkr::proof_layout`; this builder calls into `gpu_gkr::transform`
    and `gpu_gkr::backward`, so it must sit above `gpu_gkr` and cannot live in
    that crate's cycle-free `proof_layout` leaf.
  - `orchestration/` (private, selectively re-exported): `backward.rs`,
    `stage1_forward.rs`, `terminal.rs`, `whir.rs` — the phases of the
    `prove()` pipeline. `proof::prove()` (in `proof/mod.rs`) is the sole
    production entry point; it dispatches on `CircuitType` +
    `GpuGKRProofTransfer` shape (no per-family whitelist) and returns a
    `GpuGKRProofJob`.
- `src/upstream.rs`: single-file manifest re-exporting every item the crate
  consumes from `cs`, `prover`, and `field`. See "Upstream imports" below.
- `src/test_utils.rs`, `src/tests/`: the e2e/parity test suite
  (`#[cfg(test)]`), driving full proof workflows through this crate's
  `prove()` while reaching into `gpu_trace`/`gpu_gkr`/`gpu_whir`/
  `gpu_prover_context`/`gpu_ops` test-reference seams
  (`#[doc(hidden)] pub` items in those crates) across crate boundaries.
- No `native/` tree, no `src/prover/`, no `src/witness/` — those moved to
  `gpu_gkr`/`gpu_whir` and `gpu_trace` respectively (Tasks 7–11 of the split).

## Upstream imports

Production code (`proof/**`, `config.rs`) imports from the upstream crates
(`cs`, `prover`, `field`) **exclusively through `crate::upstream`**. Direct
`use cs::…;` / `use prover::…;` in non-test code is forbidden. `#[cfg(test)]`
modules are exempt — the e2e test suite imports a much larger upstream
surface (including `common_constants`) via `use crate::upstream::*` from a
clearly-marked `#[cfg(test)]` section of the same manifest file.

- Adding a production dependency: `pub(crate) use …;` in
  [`src/upstream.rs`](src/upstream.rs), then `use crate::upstream::Item;`
  from the consumer.
- Two aliases avoid collisions with crate-local types, both test-only today:
  `CSExecutorFamilyDecoderData` and `CpuGKRSetup`. Use the aliased names.

## Layer contract

This crate's own module DAG is now small: `config` and `proof::inputs` are
leaves (upstream + the split crates' public APIs only); `proof::layout`
depends on `gpu_gkr` to build layout inputs; `proof::orchestration` is the
top — it depends on `config`, `proof::inputs`, `proof::layout`, and drives
`gpu_trace`/`gpu_gkr`/`gpu_whir` directly. `proof::prove()` is the only
production entry point exposed upward (to `gpu_execution_prover`).

The crate stack itself — which modules became `gpu_core` / `gpu_ntt` /
`gpu_ops` / `gpu_hash` / `gpu_cub` / `gpu_prover_context` / `gpu_trace` /
`gpu_gkr` / `gpu_whir` / `gpu_execution_prover`, the build +
`_native`-naming + C++-namespace + bench conventions, and the native-code
(clang-format / Rust↔CUDA interface-stability) rules — is documented once for
the whole cluster in [`../AGENTS.md`](../AGENTS.md). This crate carries no
native code of its own, so the clang-format / native-build rules there do not
apply here directly.

## Build and Test

- Minimum validation for any code change: `cargo check -p gpu_circuit_prover`
- Build: `cargo build -p gpu_circuit_prover`
- Test: two safe harnesses — `cargo nextest run -p gpu_circuit_prover` for
  unattended/full-suite runs (the `gpu-serial` group in the workspace
  [`.config/nextest.toml`](../../.config/nextest.toml) serializes GPU tests,
  terminates hung tests, and isolates sticky CUDA errors per process, at
  ~220 ms CUDA-init per test), or plain `cargo test -p gpu_circuit_prover` as the
  zero-overhead attended path (the pre-main
  `gpu_core::force_serial_libtest!()` guard at the crate root forces
  `RUST_TEST_THREADS=1`; no hung-test termination). The crate carries no
  `#[serial]` annotations. CPU-only tests may be named or moduled `cpu_*` to run
  parallel under nextest.
- Bench: `cargo bench -p gpu_circuit_prover`
- For compute-heavy GPU tests or prover flows, use `--release` by default. Use debug-mode execution only for quick smoke tests or when debug assertions/symbols are specifically needed.
- Compile first with `cargo nextest run --no-run`, then run under
  `.agents/bin/with_gpu_lock.sh cargo nextest run …` so only the execution
  step holds the GPU lock.

## Formatting

- Rust: `cargo fmt -p gpu_circuit_prover` only — never crate/workspace-wide
  `cargo fmt`.
- No native CUDA/C++ in this crate — `clang-format` does not apply here (see
  [`../trace/AGENTS.md`](../trace/AGENTS.md), [`../gkr/AGENTS.md`](../gkr/AGENTS.md),
  [`../whir/AGENTS.md`](../whir/AGENTS.md) for the crates that do own native code).

## Design Documents

- `docs/gpu_scheduling_contract.md` moved to
  [`../docs/gpu_scheduling_contract.md`](../docs/gpu_scheduling_contract.md) —
  see the "GPU Scheduling Contract" section above for the summary; that file
  is the full source of truth.
- `docs/profiling.md`: prover-specific profiling parameters + the profiling
  test / NVTX range / test-binary build. The generic per-kernel `ncu`/`nsys`
  methodology is cluster-level in [`../docs/`](../docs/)
  (`gpu/docs/profiling{,_ncu,_nsys}.md`).
- `docs/backward_immediate_factor_encoding.md`: design note on the GKR
  backward-pass immediate-factor encoding (the implementation it describes
  now lives in `gpu_gkr`'s `backward/flat` module).

## Code Notes

- Use `log` for diagnostic output rather than `println!`.
- Prefer `rayon` for CPU parallelism when applicable.
- Keep unsafe blocks minimal and justified; comment on non-obvious invariants.
- Add `// SAFETY:` comments for non-trivial unsafe blocks.

## Test layout convention

- Under 100 lines and tightly coupled to one item: inline
  `#[cfg(test)] mod tests { ... }` next to the item.
- More than 100 lines, or shared helpers: sibling `tests.rs` (declared as
  `#[cfg(test)] mod tests;` from the parent).
- Multi-file with shared helpers / fixtures: `tests/` subdir with a
  `tests/mod.rs` that re-exports the helpers needed by sibling test files.
