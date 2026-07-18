# GPU Work

Applies only to GPU-related code or commands that use the local GPU.

- Run from the repository root.
- If you touch a GPU crate, read that crate's `AGENTS.md`.
- Use `.agents/bin/with_gpu_lock.sh` only for commands that execute local GPU work.
- Do not lock CPU-only work such as `cargo build`, `cargo check`, `cargo nextest run --no-run`, codegen, linting, dependency fetching, or log inspection.
- GPU-crate Rust tests run under **cargo-nextest**, not plain `cargo test`: the GPU crates carry no `#[serial]` annotations — their serialization lives in `.config/nextest.toml` (`gpu-serial` test group: one GPU test at a time, hung tests terminated after 5 min). Plain `cargo test -p <gpu crate>` stays safe via a pre-main guard at every GPU crate root (`gpu_core::force_serial_libtest!()` forces `RUST_TEST_THREADS=1`), but it lacks nextest's hung-test termination — prefer nextest.
- For Rust tests, always split compile and run with `cargo nextest run --no-run` first unless the user explicitly asks for a different flow or the command truly cannot be split.
- Split compile and run whenever possible so only the execution step holds the lock.
- For compute-heavy GPU tests or prover runs, prefer `--release` by default. Use debug builds only for quick smoke checks, compile-only validation, or when the task explicitly needs debug assertions/symbols.
- If a GPU command cannot be split cleanly, lock the whole command as a fallback.
- Treat profiling as GPU work.
- Keep the locked section short and report clearly when waiting on the GPU lock.
- For local profiling output, default to ignored or temporary locations so the worktree stays clean.
- Prefer an ignored repo-local directory under `target/` for profiler reports and other generated diagnostics, or `/tmp/...` when the output is only needed for ad hoc inspection.

This is the default required workflow for Rust GPU tests — build unlocked, then run under the lock (the no-op cargo re-check nextest does under the lock is fast):

```bash
# 1. Build (unlocked)
cargo nextest run -p <crate> --release --no-run

# 2. Run (locked)
.agents/bin/with_gpu_lock.sh cargo nextest run -p <crate> --release <filter>
```

Filtering:

- Substring, like libtest: positional args (`... --release proof_matrix`).
- Exact test: `-E 'test(=module::submodule::some_gpu_test)'`.
- Ignored/e2e tests: append `--run-ignored only` (or `all` to include normal tests too).
- Live stdout for one test: `--no-capture`.

`with_gpu_lock.sh` remains mandatory and unchanged: nextest's `gpu-serial` serialization covers tests within one invocation only — cross-session GPU exclusivity is still exclusively the lock's job. The only retired piece is the `cargo_test_executables.py` helper, which existed to locate the built test-binary path so the locked command could be the raw binary; with nextest the locked command is `with_gpu_lock.sh cargo nextest run ...` (after the unlocked `--no-run` prebuild, the cargo re-check it does under the lock is a ~1s no-op).
