# AGENTS.md

`gpu_whir` owns the WHIR polynomial-commitment folding rounds (`fold/`) and
the PoW-verify/query-index scheduling (`pow.rs`), plus the recursive WHIR
extension oracle (`lib.rs`) and its LDE/Merkle commitment scheduler
(`oracle_commit.rs`). It carries the `gpu_whir_native` CUDA archive
(the WHIR/PoW protocol kernels that used to live under
`circuit_prover/native/whir/`).

## Layer position

`gpu_core < { gpu_ntt, gpu_ops, gpu_hash } < gpu_prover_context <
gpu_trace < gpu_gkr < gpu_whir < gpu_circuit_prover < gpu_execution_prover` — see [`../AGENTS.md`](../AGENTS.md) for the full cluster
DAG. Dependencies point only down: this crate depends on `gpu_core`,
`gpu_ntt`, `gpu_ops`, `gpu_hash`, `gpu_prover_context`, `gpu_trace`,
and `gpu_gkr`, plus the upstream crates below; `gpu_circuit_prover` depends on
it, never the reverse.

## GPU Scheduling Contract

`fold`, `pow`, and `oracle_commit` schedule kernels, copies and callbacks on
`exec_stream`. Before editing them or allocation lifetimes, read
[`../docs/gpu_scheduling_contract.md`](../docs/gpu_scheduling_contract.md) in full.

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

The crate's CPU-reference helpers and debug fold utilities are `#[cfg(test)]`.
`field::FieldExtension` is the production upstream item used by the kernels.

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
- **Kernel count**: 25 `__global__` kernels — `accumulate_eq.cu` 4,
  `columns.cu` 1, `fold.cu` 9, `leaves.cu` 1, `residue_commit.cu` 6,
  `in_domain.cu` 4. Count with
  `rg -c '__global__' gpu/whir/native/whir/*.cu`, or equivalently
  `rg -o 'ab_[a-z0-9_]*_kernel' gpu/whir/native/whir/*.cu | sort -u | wc -l`.
  Count `__global__` regardless of whether `void` appears on the same line.
  No `__constant__` symbols (all 8 cluster-wide ones live in `gpu_gkr`).
- **Namespace**: `airbender::whir`.
- **Header relationships**: `accumulate_eq.cu` includes `gpu_gkr`'s
  `gkr/support/{eq_inline,kernel_helpers}.cuh` via
  `DEP_GPU_GKR_NATIVE_INCLUDE` (forwarded because `gpu_gkr`'s build.rs sets
  `export_include(true)`); `leaves.cu`, `residue_commit.cu`, and `in_domain.cu` include `gpu_hash`'s `hash.cuh` via
  `DEP_GPU_HASH_NATIVE_INCLUDE`. `residue_commit.cu` and `in_domain.cu` also read
  gpu_ntt's `whir_leaf_transform.cuh` via `DEP_GPU_NTT_NATIVE_INCLUDE`. `in_domain.cu`
  also consumes the inline WHIR transcript update in `ops/gkr_ops_helpers.cuh`
  through `DEP_GPU_GKR_NATIVE_INCLUDE`. All three
  directories resolve automatically as CMake `-D` defines that
  `gpu_native_build` forwards. This crate also reads gpu_core's base headers.
  `deterministic_pow` is not a native `#define`
  here: the PoW search kernel itself lives in `gpu_hash`, so
  `gpu_whir/deterministic_pow` forwards to `gpu_hash/deterministic_pow`
  (and to `prover/deterministic_pow`, above) instead of defining
  `AB_DETERMINISTIC_POW` on this archive.
## Production commitment and query terms

Recursive oracles use coefficient leaves and partial Merkle trees. Small shapes
use the fused families in `fused_commit.rs`; retained residue LDEs cover
`(log_n, log_v) = (14..23, 5)`. Unsupported shapes and full-tree geometries fail
explicitly. There is no evaluation encoding, legacy interpolation path, or
auxiliary compute stream in the GPU prover.

Retained LDEs use all cosets in one launch when `log_ntt_len <=
MAX_LOG_N_FOR_SINGLE_KERNEL_LDE`. Larger transforms run depth-first LDE/hash
tiles, with `cosets_per_tile = pow2floor(max(1, (L2 / 2) / coset_bytes))`, capped
at the total coset count. This preserves the qualified residue tile geometry.

Every supported schedule uses symbolic in-domain query terms. Original/OOD terms
stay dense. Before each later fold group, including the final one, gather
natural-order coefficient leaves from the current oracle; add the symbolic
contribution to `[f0, f1, 4*f_half]` before the transcript update, then fold term
coefficients, weights and points on exec. Recomputed leaves are refreshed by
Horner evaluation directly from monomial coefficients.

The Sec100 trace-log 20/22/23/24 schedules were qualified with full-proof byte
parity and paired timings. Records: `.agents/audits/2026-09-29-whir-symbolic-results.md`,
`.agents/audits/2026-09-29-whir-kernel-followups.md`, and
`.agents/audits/2026-09-30-whir-rebase-yagni-results.md`. The subsequent removal
of nonproduction paths is recorded in the September 30 production-only plan.

## Widening convention

- `GpuWhirExtensionOracle` and its keepalive stay `pub(crate)`; they are
  internal fold-scheduler details.
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

## Small-kernel follow-up policy

M256/V32 commits skip unity twiddle multiplies in radix-4 stage zero. M128/V32
uses two shared-memory Merkle layers followed by a warp-0 shuffle tail. Other
fused shapes keep their measured reduction strategy. Symbolic terms refresh
recomputed leaves directly with interleaved Horner; proof queries keep the
subtree/path implementation. All use exec. The September 29 isolated matrix and
paired proof gate are recorded in `.agents/audits/2026-09-29-whir-kernel-followups.md`;
raw evidence is under `target/profiling/whir-kernel-followups/`.

A prepared-table 8/16-coset oracle-1 tiling experiment regressed every paired
proof despite removing repeated table fills. Its API was removed; untiled
batched DIT remains production.

The fused symbolic step runs correction, transcript update and term folding in
one CTA; the dense state fold follows on exec. Independent dense-reference tests
check its reductions and folded terms. The standalone GKR round-update body is
shared as an inline helper and retained instruction-identical code in the
pre-promotion comparison.
