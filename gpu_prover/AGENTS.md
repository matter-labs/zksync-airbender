# AGENTS.md

`gpu_prover` is the CUDA-backed prover crate. It uses `build/main.rs` and depends on `era_cudart` and `era_cudart_sys`.

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

- Do not modify CMake/CUDA flags.
- Do not change build configuration behavior unless explicitly requested.

## Key Files and Structure

- `build/main.rs`: build script that wires cmake/CUDA integration.
- `native/`: native CUDA/C++ sources and build artifacts managed by the build script.
- `src/`: crate modules.
- `src/upstream.rs`: single-file manifest re-exporting every item the crate
  consumes from `cs`, `prover`, `field`, `setups`, and `trace_and_split`. See
  the "Upstream imports" section below.

## Upstream imports

Code under `gpu_prover/src/` imports items from the upstream crates (`cs`,
`prover`, `field`, `setups`, `trace_and_split`) **exclusively through
`crate::upstream`** in production code. Direct `use cs::…;` /
`use prover::…;` / etc. in non-test consumer code is forbidden — the
manifest is the production-surface contract.

`#[cfg(test)]` modules and files under `tests/` subdirectories are
exempt: tests may import upstream items directly. This keeps test-only
utility surface (`field::Rand`, witness-placer traits required by
`include!`'d generated circuits, etc.) out of the production manifest.

- Adding a new dependency on an upstream item from production code: add a
  `pub(crate) use …;` to the appropriate section of
  [`src/upstream.rs`](src/upstream.rs), then `use crate::upstream::Item;`
  from the consumer.
- Two aliases live in the manifest to avoid collisions with crate-local
  types: `cs::gkr_circuits::ExecutorFamilyDecoderData` is re-exported as
  `CSExecutorFamilyDecoderData`, and `prover::gkr::prover::setup::GKRSetup`
  as `CpuGKRSetup`. Consumers must use the aliased name.
- Bumping an upstream version: scan `src/upstream.rs` first. A renamed or
  removed item surfaces as a compile error pointing at the manifest rather
  than at scattered call sites; conversely, anything added to the manifest
  is the documented surface contract.
- The manifest exposes a few module re-exports (`dimension_reduction`,
  `stage1`) so consumers can write `crate::upstream::stage1::stage1(...)`
  without re-importing the entire path.

## Build and Test

- Minimum validation for any code change: `cargo check -p gpu_prover`
- Build: `cargo build -p gpu_prover`
- Test: `cargo test -p gpu_prover`
- Bench: `cargo bench -p gpu_prover`
- For compute-heavy GPU tests or prover flows, use `cargo test -p gpu_prover --release` by default. Use debug-mode execution only for quick smoke tests or when debug assertions/symbols are specifically needed.
- For Rust GPU tests, compile first with `cargo test --no-run`, then run the produced test binary under `.agents/bin/with_gpu_lock.sh`. Do not run locked `cargo test ...` directly when the binary can be built first.

## Formatting

- Rust: `cargo fmt`.
- Native CUDA/C++ under `native/`: `clang-format` against [`native/.clang-format`](native/.clang-format). `cargo fmt` does not cover this; CI does not enforce it.
- A change that touches both languages needs both.

## Build Script

- Unless explicitly requested, changes in `build/main.rs` must be non-behavioral.

## Design Documents

- `docs/gpu_scheduling_contract.md`: Async scheduling contract for GPU stream-ordered prover work (GKR, WHIR) — see the "GPU Scheduling Contract" section above for the summary; this is the full source of truth.
- `docs/profiling.md`: Shared `gpu_prover` profiling setup, including the profiling test, NVTX identifiers, and test-binary workflow.
- `docs/profiling_nsys.md`: `gpu_prover` `nsys` workflow around the existing top-level NVTX capture range.
- `docs/profiling_ncu.md`: `gpu_prover` `ncu` workflow for quick kernel profiling, full-picture/source-correlated profiling, and dependency-sensitive range replay.

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
