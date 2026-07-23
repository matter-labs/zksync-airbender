# AGENTS.md

`gpu_prover_context` owns `ProverContext` + `ProverContextConfig` (device/host
allocators, the four CUDA streams, the NTT twiddle `DeviceContext`) and the
H2D/D2H `Transfer` machinery (`transfer.rs`: `Transfer`, `fork_join_exec_to_d2h`).
It has **no native CUDA of its own** — pure Rust over `gpu_core`'s
allocator/primitives and `gpu_ntt`'s `DeviceContext`.

## Layer position

`gpu_core < { gpu_ntt, gpu_ops, gpu_hash, gpu_cub } < gpu_prover_context <
gpu_trace < gpu_gkr < gpu_whir < gpu_circuit_prover < gpu_execution_prover <
gpu_program_prover` — see [`../AGENTS.md`](../AGENTS.md) for the full
cluster DAG. Dependencies point only down: this crate depends on `gpu_core`
and `gpu_ntt` (for the twiddle-table `DeviceContext` `ProverContext` owns for
its lifetime), nothing above it. Every crate from `gpu_trace` upward
constructs and threads a `&ProverContext` through its scheduling functions.

## GPU Scheduling Contract

This crate **owns** the contract's subject matter — the four streams
(`exec_stream`, `h2d_stream`, `d2h_stream`, `side_stream`), the stream-ordered
device/host allocators, and the `Transfer` fork/join wrapper (`gpu_core` owns
the separate `SchedulerHostAllocator` pool the contract also documents).
Before editing `src/context.rs` or `src/transfer.rs`, read
[`../docs/gpu_scheduling_contract.md`](../docs/gpu_scheduling_contract.md) in
full. It governs the async stream-ordered model used by every crate above
this one (GKR, WHIR, trace commit, and related proving workflows).

The cheatsheet below is a summary — the contract document is the source of
truth.

- **MUST NOT** dereference pool-backed device or host allocations from the
  scheduling thread. All reads and writes must be expressed as stream ops:
  kernel launches, `memory_copy_async`, or host callbacks scheduled via
  `Callbacks::schedule` / `launch_host_fn`. `UnsafeAccessor::get()` /
  `UnsafeMutAccessor::get_mut()` are only valid inside stream-scheduled
  closures.
- **MUST** fill stream-ordered H2D staging buffers via a scheduled host
  callback; consume D2H readback buffers the same way. Never touch either
  from the scheduling thread.
- **MUST** fork/join any op on an auxiliary stream (`h2d_stream`,
  `d2h_stream`, or `side_stream`) against `exec_stream` with explicit CUDA
  events. The driver gives independent streams no implicit ordering.
- **MUST** allocate and drop pool-backed handles on `exec_stream`; if a
  secondary stream touched the allocation, the join wait must be scheduled
  before the Rust drop.
- **MUST** observe write-exclusivity within any fork/join window: exactly one
  stream writes a shared buffer at a time.
- **MUST NOT** call any CUDA API from within a host callback.
- **Default to `exec_stream`** for H2D/D2H copies; use the auxiliary streams
  only when meaningful overlap justifies the fork/join machinery.

## Upstream imports

This crate has no upstream (`cs`/`prover`/`field`/`setups`) dependency at
all — `context.rs` and `transfer.rs` consume only `gpu_core`, `gpu_ntt`, and
`era_cudart*`/`log` directly. `src/upstream.rs` is still present and gates
the crate the same way as every other crate in the cluster: it is
intentionally empty today, documenting that fact; if a future change needs
an upstream item, add it there (`pub(crate) use …;`) rather than importing
directly from a consumer module.

## Widening convention

Several `ProverContext`/`Transfer` members are `pub` (not `pub(crate)`)
specifically so `gpu_circuit_prover`'s production code or test suites can
reach them across the crate boundary — each site carries a `// pub because
…` comment explaining the specific caller:

- Plain `pub` + why-pub comment = a production cross-crate API (e.g.
  `alloc_host_uninit_slice`, `Transfer::new`, `fork_join_exec_to_d2h`).
- `#[doc(hidden)] pub` = a test-reference seam only (e.g.
  `get_used_mem_peak`, `get_host_used_mem_current/peak`,
  `reset_host_used_mem_peak`, the `Transfer` struct fields' consumers) —
  the apex e2e test suite reaches these, but they are not part of the
  production surface.

## Build and Test

- Minimum validation for any code change: `cargo check -p gpu_prover_context`
- Build: `cargo build -p gpu_prover_context`
- Test: two safe harnesses — `cargo nextest run -p gpu_prover_context` for
  unattended/full-suite runs (the `gpu-serial` group in the workspace
  [`.config/nextest.toml`](../../.config/nextest.toml) serializes GPU tests,
  terminates hung tests, and isolates sticky CUDA errors per process), or
  plain `cargo test -p gpu_prover_context` as the zero-overhead attended path
  (the pre-main `gpu_core::force_serial_libtest!()` guard at the crate root
  forces `RUST_TEST_THREADS=1`). The crate carries no `#[serial]`
  annotations. CPU-only tests may be named or moduled `cpu_*` to run
  parallel under nextest.
- For compute-heavy GPU tests or prover flows, use `--release` by default.
- Compile first with `cargo nextest run --no-run`, then run under
  `.agents/bin/with_gpu_lock.sh cargo nextest run …` so only the execution
  step holds the GPU lock.

## Formatting

- Rust: `cargo fmt -p gpu_prover_context` only — never crate/workspace-wide
  `cargo fmt`.
- No native CUDA/C++ in this crate, so `clang-format` does not apply here.
