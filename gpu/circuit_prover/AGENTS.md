# AGENTS.md

`circuit_prover` is the CUDA-backed prover crate. It uses `build/main.rs` and depends on `era_cudart` and `era_cudart_sys`.

## GPU Scheduling Contract

Before editing any file under `src/prover/`, or any other code that launches
kernels, schedules host callbacks, or manages streams, you MUST read
[`docs/gpu_scheduling_contract.md`](docs/gpu_scheduling_contract.md) in full.
It governs the async stream-ordered model used by GKR, WHIR, and related
proving workflows.

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
- **MUST** fork/join any op on an auxiliary stream (`h2d_stream` or `d2h_stream`)
  against `exec_stream` with explicit CUDA events. The driver gives independent
  streams no implicit ordering.
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

## Constraints

- The CUDA build is centralized in the shared `gpu_native_build` helper
  (`gpu/native_build/`); `build/main.rs` is a thin wrapper that names the
  archive and enables `deterministic_pow`. Behavioral build changes are fine
  when the task calls for them: change the shared helper for cross-crate build
  behavior, `build/main.rs` only for circuit_prover-specific wiring.
- Keep CUDA compile flags (arch, `CUDA_STANDARD`, `--expt-relaxed-constexpr`,
  …) aligned with the other kernel crates unless a divergence is intended.

## Key Files and Structure

- `build/main.rs`: thin build script delegating to the shared `gpu_native_build` helper.
- `native/`: native CUDA/C++ sources and build artifacts managed by the build script.
- `src/`: crate modules.
- `src/upstream.rs`: single-file manifest re-exporting every item the crate
  consumes from `cs`, `prover`, `field`, `setups`, and `trace_and_split`. See
  the "Upstream imports" section below.

## Upstream imports

Production code imports from the upstream crates (`cs`, `prover`, `field`,
`setups`, `trace_and_split`) **exclusively through `crate::upstream`**.
Direct `use cs::…;` / `use prover::…;` in non-test code is forbidden.
`#[cfg(test)]` modules and files under `tests/` are exempt.

- Adding a dependency: `pub(crate) use …;` in
  [`src/upstream.rs`](src/upstream.rs), then `use crate::upstream::Item;`
  from the consumer.
- Two aliases avoid collisions with crate-local types:
  `CSExecutorFamilyDecoderData` and `CpuGKRSetup`. Use the aliased names.

## Upstream constant drift guards

When `native/**` hard-codes a value owned by an upstream crate (`cs`,
`common_constants`, …), add a compile-time assert in
[`src/witness/mod.rs`](src/witness/mod.rs) comparing the upstream value
against the native literal. Failures surface at `cargo check`.

- Scalars: `const _: () = assert!(crate::upstream::FOO == N);`.
- Grouped values (e.g. delegation `AbiDescription`): use the `DelegationAbi`
  struct + `.assert_matches(...)` pattern already in the file.
- Internal Rust↔CUDA duplicates are not asserted (the assert needs one side
  to be external); fix structurally or rely on tests.

## Layer contract (post-reorg)

The crate is organized as a strict dependency DAG. `use crate::…` imports may
only point DOWN this order; never up. Enforcement is doc-only (no mechanical
check) — keep it true by review.

Top level: `allocator < primitives < ops < witness < prover < execution`.

The crate stack itself — which modules became `gpu_core` / `gpu_ntt` /
`gpu_ops` / `gpu_hash` / `gpu_cub` / `execution_prover`, the build +
`_native`-naming + C++-namespace + bench conventions, and the native-code
(clang-format / Rust↔CUDA interface-stability) rules — is documented once for
the whole cluster in [`../AGENTS.md`](../AGENTS.md). The rest of this section
covers only `circuit_prover`'s own internal module layering.

Within `prover`: `{proof_layout, config} < {gkr, whir, trace} < proof` (with
`proof/orchestration` at the top of `proof`).
- `proof_layout`, `config`, and `context` are leaves: they depend only on
  `primitives`/`allocator` + `upstream` (no `gkr`/`whir`/`trace`/`proof`).
  `proof_layout` holds the layout TYPES + accessors; `config` owns the
  GPU-supported security-level / PoW policy; **`context` owns `ProverContext`
  (the streams/allocator/scheduling orchestration) + the H2D/D2H `transfer`
  machinery** — relocated here from `primitives`, since `ProverContext` is a
  prover concern. The GPU scheduling-contract surface lives with `context`.
- `gkr`, `whir`, `trace` may depend on `proof_layout`/`config` and on
  `primitives`/`ops`/`witness`, but MUST NOT depend on `proof`.
- The GPU-free CPU model of the GKR layout (address audit, storage layout,
  circuit transform) lives in the standalone `gpu_gkr_model` crate
  (deps: `cs` + `field`; no CUDA). `gkr` consumes it via the
  `gkr::{gkr_address_audit, storage_layout, transform}` facade re-exports.
- `proof` (incl. `proof/orchestration`) is the top of `prover`: it depends down
  on all of the above. The gkr-dependent layout builder
  (`build_proof_layout_inputs`) lives here, not in `proof_layout`.

No-upward-imports rule:
- `primitives` and `ops` MUST NOT `use crate::{witness, prover, execution}`
  (`primitives` is CUDA-substrate-only — it holds device handles/accessors,
  `DeviceProperties`, allocations, NTT twiddles; **no `ProverContext`**, which
  is a `prover::context` concern).
- `witness` MUST NOT `use crate::{prover, execution}`.
- `prover` MUST NOT `use crate::execution`.

This reflects the Phase 0–3 reorg: the two upward edges out of `primitives`
were cut, the `prover`-internal cycles (`proof↔gkr`, `proof↔trace`) were broken
via the `proof_layout`/`config` leaves and the `trace`-owned commit-transfer,
and `ops` is generic-math-bisectable (generic hashing in `ops/blake2s`,
protocol kernels in its `gkr_ops`/`transcript`/`gather` submodules).

## Build and Test

- Minimum validation for any code change: `cargo check -p circuit_prover`
- Build: `cargo build -p circuit_prover`
- Test: `cargo test -p circuit_prover`
- Bench: `cargo bench -p circuit_prover`
- For compute-heavy GPU tests or prover flows, use `cargo test -p circuit_prover --release` by default. Use debug-mode execution only for quick smoke tests or when debug assertions/symbols are specifically needed.
- For Rust GPU tests, compile first with `cargo test --no-run`, then run the produced test binary under `.agents/bin/with_gpu_lock.sh`. Do not run locked `cargo test ...` directly when the binary can be built first.

## Formatting

- Rust: `cargo fmt`.
- Native CUDA/C++ under `native/`: `clang-format` against the cluster-wide [`../.clang-format`](../.clang-format) (see [`../AGENTS.md`](../AGENTS.md)). `cargo fmt` does not cover this; CI does not enforce it.
- A change that touches both languages needs both.

## Build Script

- `build/main.rs` is a thin wrapper over `gpu_native_build::CudaArchive`. The
  shared CUDA build logic (CMake config, link directives, `DEP_*_INCLUDE`
  forwarding, `no_cuda` handling) lives in `gpu/native_build/`; edit it there
  when a change should apply to all kernel crates.

## Design Documents

- `docs/gpu_scheduling_contract.md`: Async scheduling contract for GPU stream-ordered prover work (GKR, WHIR) — see the "GPU Scheduling Contract" section above for the summary; this is the full source of truth.
- `docs/profiling.md`: prover-specific profiling parameters + the profiling test / NVTX range / test-binary build. The generic per-kernel `ncu`/`nsys` methodology is cluster-level in [`../docs/`](../docs/) (`gpu/docs/profiling{,_ncu,_nsys}.md`).

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
