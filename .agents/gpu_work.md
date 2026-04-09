# GPU Work

Applies only to GPU-related code or commands that use the local GPU.

- Run from the repository root.
- If you touch a GPU crate, read that crate's `AGENTS.md`.
- Use `.agents/bin/with_gpu_lock.sh` only for commands that execute local GPU work.
- Do not lock CPU-only work such as `cargo build`, `cargo check`, `cargo test --no-run`, codegen, linting, dependency fetching, or log inspection.
- For Rust tests, always split compile and run with `cargo test --no-run` first unless the user explicitly asks for a different flow or the command truly cannot be split.
- Do not run `.agents/bin/with_gpu_lock.sh cargo test ...` directly for Rust tests when the test binary can be built first.
- Split compile and run whenever possible so only the execution step holds the lock.
- For compute-heavy GPU tests or prover runs, prefer `--release` by default. Use debug builds only for quick smoke checks, compile-only validation, or when the task explicitly needs debug assertions/symbols.
- If a GPU command cannot be split cleanly, lock the whole command as a fallback.
- Treat profiling as GPU work.
- Keep the locked section short and report clearly when waiting on the GPU lock.
- For local profiling output, default to ignored or temporary locations so the worktree stays clean.
- Prefer an ignored repo-local directory under `target/` for profiler reports and other generated diagnostics, or `/tmp/...` when the output is only needed for ad hoc inspection.

For Rust tests, build unlocked and have `.agents/bin/cargo_test_executables.py` print the locked command to run next. This is the default required workflow for Rust GPU tests:

```bash
cargo test -p <crate> <cargo_filter> --release --no-run --message-format=json \
  | python3 .agents/bin/cargo_test_executables.py \
      --print-run-command \
      --test-name module::submodule::some_gpu_test
```

When passing `--test-name`, use the full libtest name accepted by `--exact`. Do not pass a suffix such as just `some_gpu_test`; the helper validates the exact full test name against the built test binary and rejects partial matches.

For ignored tests, append the runner args explicitly:

```bash
cargo test -p <crate> <cargo_filter> --release --no-run --message-format=json \
  | python3 .agents/bin/cargo_test_executables.py \
      --print-run-command \
      --test-name module::submodule::some_gpu_test \
      --test-arg=--ignored
```

Example output:

```bash
.agents/bin/with_gpu_lock.sh target/release/deps/<test-binary> --exact module::submodule::some_gpu_test --nocapture
```
