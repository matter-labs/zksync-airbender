# GPU Work

Applies only to GPU-related code or commands that use the local GPU.

- Run from the repository root.
- If you touch a GPU crate, read that crate's `AGENTS.md`.
- Use `.agents/bin/with_gpu_lock.sh` only for commands that execute local GPU work.
- Do not lock CPU-only work such as `cargo build`, `cargo check`, `cargo test --no-run`, codegen, linting, dependency fetching, or log inspection.
- Split compile and run whenever possible so only the execution step holds the lock.
- For compute-heavy GPU tests or prover runs, prefer `--release` by default. Use debug builds only for quick smoke checks, compile-only validation, or when the task explicitly needs debug assertions/symbols.
- If a GPU command cannot be split cleanly, lock the whole command as a fallback.
- Treat profiling as GPU work.
- Keep the locked section short and report clearly when waiting on the GPU lock.

For Rust tests, build unlocked and have `.agents/bin/cargo_test_executables.py` print the locked command to run next:

```bash
cargo test -p gpu_prover some_gpu_test --no-run --message-format=json \
  | python3 .agents/bin/cargo_test_executables.py --print-run-command --test-name some_gpu_test
```

Example output:

```bash
.agents/bin/with_gpu_lock.sh target/debug/deps/<test-binary> --exact some_gpu_test --nocapture
```

For heavy tests, compile and run the release binary under the lock:

```bash
cargo test -p gpu_prover some_gpu_test --release --no-run --message-format=json \
  | python3 .agents/bin/cargo_test_executables.py --print-run-command --test-name some_gpu_test
```

Profile under the lock:

```bash
.agents/bin/with_gpu_lock.sh cargo flamegraph --root --unit-test -- tests::run_witness_get_test
```
