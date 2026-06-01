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

The lower layers are being extracted into standalone crates (the GPU-crate
re-architecture):
- **`gpu_core`** = `allocator` + `primitives` (pure GPU substrate: static
  allocators, device_structures/DeviceMatrix, accessors, field, callbacks, nvtx,
  machine_type, utils). It also OWNS the base CUDA headers (`native_headers/`:
  field/memory/ptx/vectorized/common `.cuh`) and exports their include dir via
  `links = "gpu_core_native"` → kernel crates read `DEP_GPU_CORE_NATIVE_INCLUDE`.
  Its `build.rs` is C-only (compiles `native/nvtx.c`); it owns no CUDA kernels.
  To keep it lean, `circuit_type` was relocated → `witness` (it pulled `setups`).
- **`gpu_ntt`** = the NTT subsystem (`ntt` launchers + `ntt_twiddles` + `native/ntt`
  CUDA), with its OWN `CMakeLists.txt` + `build.rs` producing a device-linked
  `gpu_ntt_archive`; `circuit_prover` drops `gpu_prover_ntt` and links gpu_ntt's
  archive via build-script propagation. Co-locating the `cuda_struct_and_stub!`
  twiddle stubs with their `native/ntt __constant__` defs fixes the NTT
  cross-wall pitfall. Its tests are self-contained (raw era_cudart allocations +
  `DeviceContext::create`, no `ProverContext`).

- **`gpu_ops`** = the generic math/transform kernels (`simple`, `powers`,
  `squaring`, `transpose`, `bit_reverse`, `batch_inv`) with its own
  `gpu_ops_archive`. `bit_reverse` is **size-generic**: `bit_reverse_in_place<T>`
  takes any `T` and dispatches on `size_of::<T>()` (4/16/32 bytes), reinterpreting
  the element onto an internal per-size kernel binding — so it carries no blake2s
  vocabulary and callers (incl. blake2s's `Digest = [u32; 8]`) need no per-type
  impl. The reinterpret **asserts** the runtime device pointer is aligned to the
  payload size (native `e4`/`dg` are `__align__(16)`/`__align__(32)`). Test-only
  helpers consumed by `circuit_prover`'s tests (`batch_inv`, `set_by_ref`,
  `get_powers_by_val`) are `#[doc(hidden)] pub`, not `#[cfg(test)]` — a
  dependency's `cfg(test)` items are invisible to consumers.

- **`gpu_hash`** = blake2s hashing + Merkle (`blake2s/mod.rs`) + `gather` +
  `transcript` (Fiat-Shamir commit/squeeze/PoW), with its own `gpu_hash_archive`
  (`native/hash.cu`, `gather.cu`). It **exports `hash.cuh`'s include dir** via
  `links = "gpu_hash_native"` → `circuit_prover` reads `DEP_GPU_HASH_NATIVE_INCLUDE`
  so the blake2s-dependent kernels that stayed here (`gkr_ops.cu`, `leaves.cu`)
  resolve `#include "hash.cuh"`. Deps: `gpu_core` + `gpu_ops`. The GKR/WHIR
  **protocol** kernels lifted OUT of `ops/blake2s/` to **`ops::gkr_ops`** (stays
  in `circuit_prover`, Track 3); the 6 fns re-pointed in 12
  consumers from `ops::blake2s::` to `ops::gkr_ops::`. PoW determinism is
  feature-propagated: `gpu_hash` has a `deterministic_pow` feature →
  `AB_DETERMINISTIC_POW` in its CMake, enabled by `circuit_prover/deterministic_pow`
  (without it the moved `ab_blake2s_pow_kernel` runs a non-deterministic search
  → silent proof-parity divergence that passes compile + breadth). Test helpers
  consumed by `circuit_prover`'s tests (`gather_leaf_rows`, `gather_merkle_paths_*`)
  are `#[doc(hidden)] pub`. The transcript parity test verifies against the host
  `prover::transcript::Blake2sTranscript`, so `prover` is a **dev-only** dep of
  `gpu_hash` (production + downstream stay `gpu_core`/`gpu_ops`-only).

- **`gpu_cub`** = the CUB-library wrappers (`device_reduce`/segmented,
  `device_radix_sort`, `device_run_length_encode` + `CUB_TEMP_STORAGE_EXTRA_ALIGNMENT_LOG2`)
  with its own `gpu_cub_archive` (`native/`: the 4 `.cu` + cub-local `common.cuh`,
  which include `<cub/device/…>` from the CUDA toolkit + gpu_core base headers).
  The compile-heavy CCCL/CUB template instantiations are now isolated to this
  crate (a build-speed win). Fully **self-contained** — it launches only its own
  archive's kernels, so no header export / `DEP_*` is needed (unlike gpu_hash).
  Dep: `gpu_core`.

`circuit_prover` consumes these via facade re-exports (`crate::{allocator, primitives}`,
`crate::ops::{ntt, ntt_twiddles}`, `crate::ops::{simple, powers, squaring,
transpose, bit_reverse, batch_inv}`, `crate::ops::blake2s`, `crate::ops::cub`),
so existing in-crate paths are unchanged. **The kernel-crate layer is now fully
extracted** (`gpu_core` < {`gpu_ntt`, `gpu_ops`, `gpu_hash`, `gpu_cub`}); the
only `native/` left in `circuit_prover` is the GKR/WHIR protocol + witness CUDA.
Next: Track 3 = execution/circuit top-split (moves `ops::gkr_ops` + orchestration
into a new `circuit_prover` crate).

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
  circuit transform) lives in the standalone `gpu_prover_gkr_model` crate
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
- Native CUDA/C++ under `native/`: `clang-format` against [`native/.clang-format`](native/.clang-format). `cargo fmt` does not cover this; CI does not enforce it.
- A change that touches both languages needs both.

## Build Script

- Unless explicitly requested, changes in `build/main.rs` must be non-behavioral.

## Design Documents

- `docs/gpu_scheduling_contract.md`: Async scheduling contract for GPU stream-ordered prover work (GKR, WHIR) — see the "GPU Scheduling Contract" section above for the summary; this is the full source of truth.
- `docs/profiling.md`: Shared `circuit_prover` profiling setup, including the profiling test, NVTX identifiers, and test-binary workflow.
- `docs/profiling_nsys.md`: `circuit_prover` `nsys` workflow around the existing top-level NVTX capture range.
- `docs/profiling_ncu.md`: `circuit_prover` `ncu` workflow for quick kernel profiling, full-picture/source-correlated profiling, and dependency-sensitive range replay.

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
