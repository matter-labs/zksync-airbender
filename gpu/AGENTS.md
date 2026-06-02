# AGENTS.md — GPU crate cluster

This governs every crate under `gpu/` (the GPU prover stack). Each crate may add
a more specific `AGENTS.md`; this file holds the rules and architecture that span
the whole cluster. Read it before adding a crate, moving native code, or changing
the build.

## Crate stack (dependency DAG)

Dependency edges may only point DOWN this order; never up. Enforcement is doc-only
(no mechanical check) — keep it true by review.

```text
gpu_core  <  { gpu_ntt, gpu_ops, gpu_hash, gpu_cub }  <  circuit_prover  <  execution_prover
```

Plus two off-DAG crates: **`gpu_gkr_model`** (pure-CPU GKR layout model — address
audit, storage layout, circuit transform; deps `cs` + `field`, no CUDA; consumed
by `circuit_prover`'s `gkr` via `gkr::{gkr_address_audit, storage_layout,
transform}` facade re-exports) and **`gpu_native_build`** (the shared build-script
helper, a build-dependency only).

- **`gpu_core`** = `allocator` + `primitives` (pure GPU substrate: static
  allocators, device_structures/DeviceMatrix, accessors, field, callbacks, nvtx,
  machine_type, utils). It also OWNS the base CUDA headers (`native_headers/`:
  field/memory/ptx/vectorized/common `.cuh`) and exports their include dir via
  `links = "gpu_core_native"` → kernel crates read `DEP_GPU_CORE_NATIVE_INCLUDE`.
  Its `build.rs` compiles `native/nvtx.c` (C); it owns no production CUDA
  kernels — only a bench-gated `gpu_core_bench_native` archive (`native/bench/field.cu`,
  built solely under the `bench` feature for `benches/field.rs`).
  To keep it lean, `circuit_type` was relocated → `circuit_prover::witness` (it pulled `setups`).
- **`gpu_ntt`** = the NTT subsystem (`ntt` launchers + `ntt_twiddles` + `native/ntt`
  CUDA), with its OWN `CMakeLists.txt` + `build.rs` producing a device-linked
  `gpu_ntt_native`; `circuit_prover` drops `gpu_prover_ntt` and links gpu_ntt's
  archive via build-script propagation. Co-locating the `cuda_struct_and_stub!`
  twiddle stubs with their `native/ntt __constant__` defs fixes the NTT
  cross-wall pitfall. Its tests are self-contained (raw era_cudart allocations +
  `DeviceContext::create`, no `ProverContext`).
- **`gpu_ops`** = the generic math/transform kernels (`simple`, `powers`,
  `squaring`, `transpose`, `bit_reverse`, `batch_inv`) with its own
  `gpu_ops_native`. `bit_reverse` is **size-generic**: `bit_reverse_in_place<T>`
  takes any `T` and dispatches on `size_of::<T>()` (4/16/32 bytes), reinterpreting
  the element onto an internal per-size kernel binding — so it carries no blake2s
  vocabulary and callers (incl. blake2s's `Digest = [u32; 8]`) need no per-type
  impl. The reinterpret **asserts** the runtime device pointer is aligned to the
  payload size (native `e4`/`dg` are `__align__(16)`/`__align__(32)`). Test-only
  helpers consumed by `circuit_prover`'s tests (`batch_inv`, `set_by_ref`,
  `get_powers_by_val`) are `#[doc(hidden)] pub`, not `#[cfg(test)]` — a
  dependency's `cfg(test)` items are invisible to consumers.
- **`gpu_hash`** = blake2s hashing + Merkle (`blake2s/mod.rs`) + `gather` +
  `transcript` (Fiat-Shamir commit/squeeze/PoW), with its own `gpu_hash_native`
  (`native/hash.cu`, `gather.cu`). It **exports `hash.cuh`'s include dir** via
  `links = "gpu_hash_native"` → `circuit_prover` reads `DEP_GPU_HASH_NATIVE_INCLUDE`
  so the blake2s-dependent kernels that stayed there (`gkr_ops.cu`, `leaves.cu`)
  resolve `#include "hash.cuh"`. Deps: `gpu_core` + `gpu_ops`. The GKR/WHIR
  **protocol** kernels lifted OUT of `ops/blake2s/` to **`ops::gkr_ops`** (stays
  in `circuit_prover`); the 6 fns re-pointed in 12 consumers from
  `ops::blake2s::` to `ops::gkr_ops::`. PoW determinism is feature-propagated:
  `gpu_hash` has a `deterministic_pow` feature → `AB_DETERMINISTIC_POW` in its
  CMake, enabled by `circuit_prover/deterministic_pow` (without it the moved
  `ab_blake2s_pow_kernel` runs a non-deterministic search → silent proof-parity
  divergence that passes compile + breadth). Test helpers consumed by
  `circuit_prover`'s tests (`gather_leaf_rows`, `gather_merkle_paths_*`) are
  `#[doc(hidden)] pub`. The transcript parity test verifies against the host
  `prover::transcript::Blake2sTranscript`, so `prover` is a **dev-only** dep of
  `gpu_hash` (production + downstream stay `gpu_core`/`gpu_ops`-only).
- **`gpu_cub`** = the CUB-library wrappers (`device_reduce`/segmented,
  `device_radix_sort`, `device_run_length_encode` + `CUB_TEMP_STORAGE_EXTRA_ALIGNMENT_LOG2`)
  with its own `gpu_cub_native` (`native/`: the 4 `.cu` + cub-local `common.cuh`,
  which include `<cub/device/…>` from the CUDA toolkit + gpu_core base headers).
  The compile-heavy CCCL/CUB template instantiations are isolated to this crate
  (a build-speed win). Fully **self-contained** — it launches only its own
  archive's kernels, so no header export / `DEP_*` is needed (unlike gpu_hash).
  Dep: `gpu_core`.

`circuit_prover` consumes the kernel crates via facade re-exports
(`crate::{allocator, primitives}`, `crate::ops::{ntt, ntt_twiddles}`,
`crate::ops::{simple, powers, squaring, transpose, bit_reverse, batch_inv}`,
`crate::ops::blake2s`, `crate::ops::cub`), so in-crate paths are unchanged. The
only `native/` left in `circuit_prover` is the GKR/WHIR protocol + witness CUDA.
`execution_prover` holds `ExecutionProver` + the 9-symbol facade.

## Cross-crate conventions (apply when adding/editing a kernel crate)

- **Build:** each kernel `build.rs` is a one-line `gpu_native_build::CudaArchive`
  call (helper in `native_build/`); the static lib / CMake target / `links` key
  are all `<crate>_native` (e.g. `gpu_ntt_native`); the nvtx C lib is
  `gpu_core_nvtx`. Cross-crate header includes propagate via `links` +
  `DEP_<X>_NATIVE_INCLUDE`, auto-forwarded by the helper. The shared CUDA build
  logic (CMake config, link directives, `no_cuda` handling) lives in
  `native_build/`; edit it there for behavior that should apply to all kernel crates.
- **C++ namespace = owning crate:** `airbender::hash` (gpu_hash), `airbender::cub`
  (gpu_cub), `airbender::ntt` (gpu_ntt), `airbender::ops::*` (gpu_ops),
  `airbender::primitives::*` (gpu_core); `circuit_prover`'s own kernels are
  `airbender::ops::gkr_ops` / `airbender::prover::*` / `airbender::witness::*`.
- **Benches** live in the owning kernel crate (`gpu_ntt`, `gpu_core`), behind a
  non-default `bench` feature; any bench `.cu` (only `gpu_core`'s `field.cu`)
  compiles **only** under that feature, never in normal/production builds.

## Native code (CUDA/C++)

- **Formatting:** format every touched `.cu`/`.cuh`/`.h` with `clang-format`
  against [`.clang-format`](.clang-format) at this `gpu/` root — it governs the
  native code of all kernel crates AND `circuit_prover` (clang-format finds it by
  walking up from any `gpu/**/native/` file). `cargo fmt` does not touch native
  code; a change spanning both languages needs both formatters.
- **Rust↔CUDA interface stability:** keep exported kernel symbol names and Rust
  launcher expectations stable unless the task explicitly requires a coordinated
  change on both sides; make that dependency explicit and keep the two sides
  consistent in the same task. Launched kernels are `EXTERN` (= `extern "C"`), so
  the C++ namespace is organizational — the bare symbol name is the ABI.

## Profiling

Per-kernel (`ncu`) and timeline (`nsys`) profiling methodology applies to any
crate's kernels and lives at the cluster level in [`docs/profiling.md`](docs/profiling.md)
(+ `docs/profiling_ncu.md`, `docs/profiling_nsys.md`). Crate-specific setups —
which test/bench and NVTX range to profile — live with the crate (e.g.
[`circuit_prover/docs/profiling.md`](circuit_prover/docs/profiling.md)).

## Per-crate specifics

- **`circuit_prover`** (proving pipeline, GPU scheduling contract, upstream
  imports, profiling, its internal `prover` module DAG): see
  [`circuit_prover/AGENTS.md`](circuit_prover/AGENTS.md) and its
  [`native/AGENTS.md`](circuit_prover/native/AGENTS.md) (upstream-constant drift guards).
- The kernel crates (`core`/`ntt`/`ops`/`hash`/`cub`) and `gpu_gkr_model` carry
  no own `AGENTS.md` — this file is their contract.
