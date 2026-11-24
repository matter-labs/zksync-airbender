# AGENTS.md

`gpu_whir` owns WHIR folding, PoW and query-index scheduling, and recursive WHIR
oracles. Field-specific Rust code lives in parallel `src/baby_bear/` and
`src/proth120/` folders. BabyBear folding is in `src/baby_bear/fold/`, its PoW and
query scheduling in `src/baby_bear/pow.rs`, its recursive extension oracle in
`src/baby_bear/mod.rs`, and its LDE/Merkle commitment scheduler in
`src/baby_bear/oracle_commit.rs`. Shared query-word sizing and generic
running-powers scheduling stay in `src/pow.rs`; `src/lib.rs` is the crate root.

The single `gpu_whir_native` CUDA archive (namespace `airbender::whir`) contains
`native/baby_bear/` and `native/proth120/` sources, registered by each field's
`CMakeLists.txt`. Shared `fold_shared.cuh` and `in_domain_shared.cuh` stay at
`native/`; the parent CMakeLists configures the target after adding both fields.
This crate does not export an include directory. Local shared headers use `../`
paths; dependency headers resolve through the owning crate's include root, such
as gpu_ntt's `baby_bear/whir_leaf_transform.cuh` and `proth120/context.cuh`.

## Layer position

`gpu_whir` sits above `gpu_gkr` and below `gpu_circuit_prover`; see
[`../AGENTS.md`](../AGENTS.md) for the cluster DAG. Dependencies point only down.

## Rules

- Kernels, copies and callbacks run on `exec_stream`. Before editing scheduling or
  allocation lifetimes, read
  [`../docs/gpu_scheduling_contract.md`](../docs/gpu_scheduling_contract.md).
- Production code imports `field` and `prover` items only through
  `crate::upstream`; test code is exempt.
- `deterministic_pow` forwards to `gpu_hash/deterministic_pow` and
  `prover/deterministic_pow`; it defines nothing in the native archive.
- `GpuWhirExtensionOracle` and its keepalive stay `pub(crate)`; plain `pub`
  items are the cross-crate API used by `gpu_circuit_prover`.

## Build and test

- Check: `cargo check -p gpu_whir`.
- Test: `cargo nextest run -p gpu_whir --release`, or `cargo test -p gpu_whir --release`
  (GPU tests run serially either way). Compile first with `--no-run`, then run
  under `.agents/bin/with_gpu_lock.sh` so only execution holds the GPU lock.
- Format: `cargo fmt -p gpu_whir`; native code with `clang-format` against
  [`../.clang-format`](../.clang-format).
