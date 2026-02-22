# gpu_prover

CUDA-backed proving crate for the `zksync-airbender` workspace.

## Test and Benchmark Commands

- Compile-check:
  - `cargo check -p gpu_prover`
- Run tests with field inlining disabled (faster compile times for large test sets):
  - `cargo test -p gpu_prover --features test_no_inline`
- Run benchmarks with default inlining behavior (for representative performance):
  - `cargo bench -p gpu_prover --bench field`
