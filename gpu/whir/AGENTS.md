# AGENTS.md

`gpu_whir` owns the WHIR folding rounds (`fold/`), PoW and query-index scheduling
(`pow.rs`), the recursive WHIR extension oracle (`lib.rs`) and its LDE/Merkle
commitment scheduler (`oracle_commit.rs`), with the `gpu_whir_native` CUDA archive
(namespace `airbender::whir`).

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
