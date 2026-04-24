# AGENTS.md

## Repo Rules

- Keep changes task-focused; avoid unrelated refactors.
- Avoid dependency or version churn unless explicitly requested.
- If a subdirectory has its own `AGENTS.md`, follow it for that area.

## Commits And PRs

- Use Conventional Commits for commit messages and PR titles, for example `fix(gpu_prover): shorten lock scope`.
- Keep the scope meaningful and specific to the area changed.
- Use `.github/pull_request_template.md` when preparing PR descriptions.
- Make sure the PR title matches the actual change, since PR titles feed changelog generation.

## GPU Work

- Only if the task touches GPU-related code or runs local GPU work, read `.agents/gpu_work.md`.

## Context Efficiency

- Prefer targeted reads over whole-file reads for large files: locate the relevant span first with `grep`/`rg`, then read only that range.
- Prefer `rg` (ripgrep) over recursive `grep` when available; fall back to `grep -r` otherwise.
- For chatty commands, trim output at the source rather than paging it into context: `cargo build 2>&1 | tail -50`, `cargo test ... 2>&1 | grep -E 'FAIL|error'`, `| wc -l` when only the count matters.
- For expensive-to-rerun commands (long release builds, full test suites, profiling runs), redirect to a file and query it afterwards, so you can re-inspect with different filters without re-running: `cargo test -p <crate> > /tmp/test.out 2>&1`, then `tail -40 /tmp/test.out` or `rg -n 'FAIL|error' /tmp/test.out`.
- When only errors matter from a Rust build/check, suppress warnings with `RUSTFLAGS="-Awarnings"` (e.g. `RUSTFLAGS="-Awarnings" cargo check -p <crate>`). This repo's crates produce substantial warning noise that is usually unrelated to the task.
- Run `cargo check -p <crate>` before a `cargo build --release` on that crate — much faster feedback loop, and release builds here can take multiple minutes.
- Scope cargo invocations with `-p <crate>` (and `--lib` / `--tests` / `--bin <name>` where possible) instead of building the whole workspace.
- Delegate broad codebase exploration or any task with large intermediate outputs to a subagent when your harness supports it, so the noise stays out of the main context and only the summary comes back.
