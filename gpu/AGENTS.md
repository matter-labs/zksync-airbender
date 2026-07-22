# AGENTS.md — GPU crate cluster

This governs every crate under `gpu/` (the GPU prover stack). Each crate may add
a more specific `AGENTS.md`; this file holds the rules and architecture that span
the whole cluster. Read it before adding a crate, moving native code, or changing
the build.

## Crate stack (dependency DAG)

Dependency edges may only point DOWN this order; never up. Enforcement is doc-only
(no mechanical check) — keep it true by review.

```text
gpu_core  <  { gpu_ntt, gpu_ops, gpu_hash, gpu_cub }  <  gpu_prover_context  <
gpu_trace  <  gpu_gkr  <  gpu_whir  <  circuit_prover  <  execution_prover  <  program_prover
```

Plus three off-DAG crates: **`gpu_witness_eval_generator`** (`witness_eval_generator/`:
pure-CPU codegen producing the committed `circuit_defs/**/generated/witness_generation_fn.cuh`
CUDA witness bodies that `gpu_trace`'s native templates `#include`; run manually via its
`generate` bin; the committed artifacts are drift-guarded by the
`committed_witness_cuh_is_current` test (regenerates each from its committed
`cs/compiled_circuits/*_gkr.json` inputs and asserts byte-identity — GPU-free,
runs in CI) and refreshed by the `regenerate_committed` bin after an intentional
codegen change; has its own `AGENTS.md`),
**`gpu_gkr_model`** (pure-CPU GKR layout model — address
audit, storage layout, circuit transform; deps `cs` + `field`, no CUDA; consumed
by `gpu_gkr` via `gkr::{gkr_address_audit, storage_layout,
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
  To keep it lean, `circuit_type` was relocated out of this crate (it pulled
  `setups`) — it now lives in `gpu_trace::witness::circuit_type`.
  **Completeness policy — `native_headers/` is a library, not a minimal set.**
  gpu_core's base CUDA headers implement *complete* primitive families on
  purpose, kept available for kernel/perf work; **"unused in-project" is NOT a
  deletion signal here.** The deliberate complete families are: the PTX
  cache-operator set (`ld_modifier`/`st_modifier` + the `load_*`/`store_*`
  wrappers), the u32 **and** u64 carry-chain arithmetic in `ptx.cuh`, the field
  operations (incl. `e6`), and the type×shape×access accessor matrix
  (`{bf,e2,e4,e6}` × vector/matrix × getter/setter/getter_setter). Do not prune
  these on usage; consumer kernel crates (gpu_ops, …) wrap only what they
  dispatch, and the completeness lives here in core. This protects the complete
  families specifically — genuine broken/incomplete vestiges (e.g. a
  never-initialized global) are still fair game to remove.
- **`gpu_ntt`** = the NTT subsystem (`ntt` launchers + `ntt_twiddles` + `native/ntt`
  CUDA), with its OWN `CMakeLists.txt` + `build.rs` producing a device-linked
  `gpu_ntt_native`; `circuit_prover` drops `gpu_prover_ntt` and links gpu_ntt's
  archive via build-script propagation. Co-locating the `cuda_struct_and_stub!`
  twiddle stubs with their `native/ntt __constant__` defs fixes the NTT
  cross-wall pitfall. Its tests are self-contained (raw era_cudart allocations +
  `DeviceContext::create`, no `ProverContext`).
- **`gpu_ops`** = the generic math/transform kernels (`simple`, `powers`,
  `squaring`, `transpose`, `bit_reverse`) with its own
  `gpu_ops_native`. `bit_reverse` is **size-generic**: `bit_reverse_in_place<T>`
  takes any `T` and dispatches on `size_of::<T>()` (4/16/32 bytes), reinterpreting
  the element onto an internal per-size kernel binding — so it carries no
  hashing/digest vocabulary; any 32-byte POD (e.g. `[u32; 8]`) needs no per-type
  impl. The reinterpret **asserts** the runtime device pointer is aligned to the
  payload size (native `e4`/`dg` are `__align__(16)`/`__align__(32)`). Test-only
  helpers consumed by `gpu_gkr`'s, `gpu_whir`'s, and `circuit_prover`'s tests
  (`set_by_ref`, `get_powers_by_val`) are `#[doc(hidden)] pub`, not `#[cfg(test)]` — a
  dependency's `cfg(test)` items are invisible to consumers.
- **`gpu_hash`** = blake2s hashing (`blake2s/hash.rs`) + Merkle
  (`blake2s/merkle.rs`) + `gather` + `transcript` (Fiat-Shamir
  commit/squeeze/PoW), re-exported flat as `blake2s::*`, with its own `gpu_hash_native`
  (`native/hash.cu`, `gather.cu`). It **exports `hash.cuh`'s include dir** via
  `links = "gpu_hash_native"` → `gpu_gkr` and `gpu_whir` each read
  `DEP_GPU_HASH_NATIVE_INCLUDE` so their blake2s-dependent kernels
  (`gkr_ops.cu` in `gpu_gkr`, `leaves.cu` in `gpu_whir`) resolve
  `#include "hash.cuh"`. Dep: `gpu_core` (`gpu_ops` is dev-only test
  setup). The GKR/WHIR **protocol** kernels live in `gpu_gkr`'s `ops::gkr_ops`
  (native `ops/gkr_ops.cu`), not `ops/blake2s/`. PoW determinism is
  feature-propagated: `gpu_hash` has a `deterministic_pow` feature →
  `AB_DETERMINISTIC_POW` in its CMake, enabled by `gpu_whir/deterministic_pow`
  (which `circuit_prover/deterministic_pow` forwards to) — without it the
  `ab_blake2s_pow_kernel` runs a non-deterministic search → silent
  proof-parity divergence that passes compile + breadth. Test-and-production
  helpers consumed across the crate boundary (`gather_leaf_rows`,
  `gather_merkle_paths_*`, `build_merkle_tree`) are `#[doc(hidden)] pub` —
  `gpu_trace`'s trace holder and `gpu_whir`'s fold scheduler are the
  production consumers today (the pre-split comments in `gpu_hash`'s source
  naming `circuit_prover` as the consumer predate the split and are stale;
  the functions themselves did not move). `hash_leaves_multi_coset` is
  `#[doc(hidden)] pub` too, but its only cross-crate reference is test-only
  (`gpu_whir/src/kernels/tests.rs`); its real caller is gpu_hash-internal
  (`build_merkle_tree_multi_coset`). The transcript
  parity test verifies against the host `prover::transcript::Blake2sTranscript`,
  so `prover` is a **dev-only** dep of `gpu_hash` (production stays
  `gpu_core`-only).
- **`gpu_cub`** = the CUB-library wrappers (`device_reduce`/segmented,
  `device_radix_sort`, `device_run_length_encode` + `CUB_TEMP_STORAGE_EXTRA_ALIGNMENT_LOG2`)
  with its own `gpu_cub_native` (`native/`: the 4 `.cu` + cub-local `common.cuh`,
  which include `<cub/device/…>` from the CUDA toolkit + gpu_core base headers).
  The compile-heavy CCCL/CUB template instantiations are isolated to this crate
  (a build-speed win). Fully **self-contained** — it launches only its own
  archive's kernels, so no header export / `DEP_*` is needed (unlike gpu_hash).
  Dep: `gpu_core`.
- **`gpu_prover_context`** = `ProverContext` + `ProverContextConfig` (the
  device/host allocators, the four CUDA streams — `exec_stream`, `h2d_stream`,
  `d2h_stream`, `side_stream` — and the NTT twiddle `DeviceContext`) plus the
  H2D/D2H `Transfer` fork/join machinery (`transfer.rs`). No native of its
  own — pure Rust over `gpu_core` + `gpu_ntt`. Every crate from `gpu_trace`
  upward threads a `&ProverContext` through its scheduling functions. See
  [`prover_context/AGENTS.md`](prover_context/AGENTS.md).
- **`gpu_trace`** = witness generation (`witness/**`) + trace commit/holder
  (`trace/**`), with its own `gpu_trace_native` (28 kernels: 17 literal + 11
  token-pasted via the `KERNEL_NAME(NAME)` macro, one per circuit under
  `witness/circuits/`), namespace `airbender::trace::witness::*`.
  Self-contained (only `gpu_core`'s base headers; no `export_include`, no
  PoW kernel). Owns the upstream-constant drift guards (compile-time asserts
  in `src/witness/mod.rs`) for witness-circuit constants borrowed from `cs`
  / `common_constants`. See [`trace/AGENTS.md`](trace/AGENTS.md).
- **`gpu_gkr`** = the GKR engine (forward pass, backward/sumcheck rounds,
  setup, base-layer claims, proof layout) plus the GKR/WHIR protocol kernels
  (`gkr_ops/`), with its own `gpu_gkr_native` (62 kernels + **all 8** of the
  cluster's `__device__ __constant__` symbols), namespaces
  `airbender::gkr::{backward, forward, ops, setup}`. `build.rs` sets
  `export_include(true)`: exports its `native/` dir as
  `DEP_GPU_GKR_NATIVE_INCLUDE` so `gpu_whir` can include its
  `gkr/support/{eq_inline,kernel_helpers}.cuh`; reads `gpu_hash`'s `hash.cuh`
  for its own blake2s-dependent protocol kernels. Re-exports `gpu_gkr_model`
  as `gkr::{gkr_address_audit, storage_layout, transform}`; owns
  `configure_kernel_attributes()`. See [`gkr/AGENTS.md`](gkr/AGENTS.md).
- **`gpu_whir`** = WHIR folds (`fold/`) + PoW/query scheduling (`pow.rs`) +
  the recursive WHIR extension oracle, with its own `gpu_whir_native` (17
  kernels, no `__constant__` symbols), namespace `airbender::whir`. Reads
  `gpu_gkr`'s exported headers (`accumulate_eq.cu`) and `gpu_hash`'s
  `hash.cuh` (`leaves.cu`). Features `deterministic_pow =
  ["prover/deterministic_pow","gpu_hash/deterministic_pow"]` (owns both
  determinism legs since `prover` is a normal, not dev-only, dependency here
  — same precedent as `gpu_gkr`) + `eval_leaves`. See
  [`whir/AGENTS.md`](whir/AGENTS.md).

`circuit_prover` now consumes `gpu_prover_context`/`gpu_trace`/`gpu_gkr`/
`gpu_whir` (and `gpu_core`/`gpu_hash`/`gpu_gkr_model`) as ordinary Cargo
dependencies — there are no more in-crate facade re-exports for the kernel
crates, and **no `native/` tree at all**: its `build.rs` only emits the
`no_cuda` cfg its test sites key off. `execution_prover` holds `ExecutionProver` + the 9-symbol facade.
`program_prover` is the program-level driver on top of `execution_prover`: it
assembles `ProveResult` into `full_statement_verifier::ProgramProof`, builds the
non-determinism streams the `fsv_*` verifier binaries consume, and (behind its
non-default `verifiers` feature) verifies proofs natively. It replaces the dead
`execution_utils` GPU recursion driver; the recursion protocol helpers come
from upstream library code (`full_statement_verifier::host_utils` /
`recursion_chain`, `verifier_common::fsv_binaries`) via its `upstream.rs` shim.

## Cross-crate conventions (apply when adding/editing a kernel crate)

- **Build:** each kernel `build.rs` is a one-line `gpu_native_build::CudaArchive`
  call (helper in `native_build/`); the static lib / CMake target / `links` key
  are all `<crate>_native` (e.g. `gpu_ntt_native`); the nvtx C lib is
  `gpu_core_nvtx`. Cross-crate header includes propagate via `links` +
  `DEP_<X>_NATIVE_INCLUDE`, auto-forwarded by the helper. The shared CUDA build
  logic lives in `native_build/` — the `CudaArchive` helper (CMake configure,
  link directives, `no_cuda` handling) plus `cmake/ab_cuda_target.cmake`, the
  `ab_cuda_configure_target` function that every kernel-crate `CMakeLists.txt`
  includes for the common target configuration (properties, flags, and the
  gated `ENABLE_LINEINFO` / `ENABLE_BUILD_DIAG` diagnostics); edit it there for
  behavior that should apply to all kernel crates.
- **C++ namespace = owning crate:** `airbender::hash` (gpu_hash), `airbender::cub`
  (gpu_cub), `airbender::ntt` (gpu_ntt), `airbender::ops::*` (gpu_ops),
  `airbender::primitives::*` (gpu_core); `airbender::trace::witness::*`
  (gpu_trace); `airbender::gkr::{backward, forward, ops, setup}` (gpu_gkr);
  `airbender::whir` (gpu_whir). `circuit_prover` owns no kernels of its own
  (no `native/` tree) — it no longer has an `airbender::witness::*` or
  `airbender::prover::*` namespace.
- **Benches** live in the owning kernel crate (`gpu_ntt`, `gpu_core`), behind a
  non-default `bench` feature; any bench `.cu` (only `gpu_core`'s `field.cu`)
  compiles **only** under that feature, never in normal/production builds.
- **Testing: two safe harnesses, pick by situation.** The GPU crates carry no
  `#[serial]` annotations (and must not add a `serial_test` dep — its mutex is
  in-process and inert under nextest).
  - **cargo-nextest** — default for unattended, full-suite, and milestone
    runs: the `gpu-serial` test group in the workspace `.config/nextest.toml`
    runs one GPU test at a time, terminates hung tests instead of wedging the
    suite (and the GPU lock), and gives each test a fresh CUDA context so
    sticky errors don't cascade. Cost: ~220 ms CUDA init per test process.
  - **plain `cargo test`** — fast path for attended, iterative, filtered
    runs: a pre-main guard (`gpu_core::force_serial_libtest!()` at every GPU
    crate root) forces `RUST_TEST_THREADS=1`, fail-closed: an inherited env
    value is overridden and a parallel `--test-threads` flag aborts the
    binary (set `AB_GPU_TESTS_ALLOW_PARALLEL=1` to deliberately bypass).
    Zero per-test overhead — but a hung kernel wedges the run and a sticky
    CUDA error poisons the remaining tests' shared context.
  - The guard covers lib unit tests only (where GPU tests live by
    convention). A `tests/` integration target must invoke the macro at its
    own crate root, and GPU doctests must stay `ignore`/`no_run` — rustdoc
    runs doctests in parallel and nextest never runs them.
  - Tests in a module or test named `cpu_*` are declared GPU-free: nextest runs them
    in parallel outside `gpu-serial` (see the override in `.config/nextest.toml`).
  - A new GPU crate must be added to the `gpu-serial` filter AND invoke the
    guard — enforced by the
    `gpu_core::serial_guard::tests::cpu_nextest_config_covers_all_gpu_crates`
    drift guard.

## Native code (CUDA/C++)

- **Formatting:** format every touched `.cu`/`.cuh`/`.h` with `clang-format`
  against [`.clang-format`](.clang-format) at this `gpu/` root — it governs the
  native code of all kernel crates AND `gpu_trace`/`gpu_gkr`/`gpu_whir`
  (clang-format finds it by walking up from any `gpu/**/native/` file).
  `circuit_prover` itself has no native tree to format. `cargo fmt` does not
  touch native code; a change spanning both languages needs both formatters.
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

- **`gpu_prover_context`** (`ProverContext`, the scheduling contract's stream
  ownership, upstream imports — none today, build/test): see
  [`prover_context/AGENTS.md`](prover_context/AGENTS.md).
- **`gpu_trace`** (witness generation + trace commit, GPU scheduling contract,
  upstream imports, the upstream-constant drift guards, native build): see
  [`trace/AGENTS.md`](trace/AGENTS.md).
- **`gpu_gkr`** (GKR engine + protocol kernels, GPU scheduling contract,
  upstream imports, native build, `gpu_gkr_model` re-export facade): see
  [`gkr/AGENTS.md`](gkr/AGENTS.md).
- **`gpu_whir`** (WHIR folds + PoW, GPU scheduling contract, upstream
  imports, native build): see [`whir/AGENTS.md`](whir/AGENTS.md).
- **`circuit_prover`** (proof orchestration + config, GPU scheduling
  contract, upstream imports, profiling, its internal `proof` module
  layering): see [`circuit_prover/AGENTS.md`](circuit_prover/AGENTS.md). It
  has no native code of its own, so it has no `native/AGENTS.md` —
  the upstream-constant drift guards that used to live there are now owned
  by `gpu_trace` (see [`trace/AGENTS.md`](trace/AGENTS.md)).
- The kernel crates (`core`/`ntt`/`ops`/`hash`/`cub`) and `gpu_gkr_model` carry
  no own `AGENTS.md` — this file is their contract.
