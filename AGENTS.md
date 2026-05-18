# AGENTS.md

## Repo Rules

- Keep changes task-focused; avoid unrelated refactors.
- Avoid dependency or version churn unless explicitly requested.
- If a subdirectory has its own `AGENTS.md`, follow it for that area.

## Nested Instructions

- `gpu_prover/` has crate-specific rules for CUDA build behavior, upstream-import policy, validation, formatting, and the GPU scheduling contract.
- `gpu_prover/native/` has additional native-only rules for `clang-format`, Rust↔CUDA interface stability, and upstream-constant drift guards.
- `gpu_prover/src/prover/` is a pointer scope that exists specifically to force a read of the full GPU scheduling contract before editing prover scheduling code.
- `gpu_prover_test/` and `gpu_witness_eval_generator/` each have their own `AGENTS.md`; read them when touching those crates.

## Worktrees

- Prefer external sibling worktrees under `../zksync-airbender-worktrees/` rather than nesting worktrees inside the repo tree.
- Name worktree directories by branch or task so they stay easy to map back to `git worktree list`.
- Do not create new worktrees under `.claude/`, `.codex/`, or any other tool-specific in-repo folder unless the user explicitly asks for that layout.

## Commits And PRs

- Use Conventional Commits for commit messages and PR titles, for example `fix(gpu_prover): shorten lock scope`.
- Keep the scope meaningful and specific to the area changed.
- Use `.github/pull_request_template.md` when preparing PR descriptions.
- Make sure the PR title matches the actual change, since PR titles feed changelog generation.

## GPU Work

- Only if the task touches GPU-related code or runs local GPU work, read `.agents/gpu_work.md`.

## Context Efficiency

This repo contains generated circuit code, large layout/proof JSON, and
pre-built `.elf` binaries. A single unscoped `rg` or `git show` can pull
hundreds of thousands of tokens into context. The rules below are not
preferences — follow them on every search and history inspection.

### Search Hygiene

- **A repo-root `.ignore` filters broad searches automatically.** Plain `rg <pattern>` already excludes generated code, compiled-circuit layouts, proof JSON, `.elf` binaries, and other artifacts that bloat context with no semantic value — see `.ignore` for the full list. Filtered files remain tracked in git and readable by direct path (`Read`, `cat`, `rg path/to/file`). When a task specifically needs to search filtered content, bypass with `rg --no-ignore <pattern>` or `rg -uu <pattern>`.
- **List before reading content.** First pass of a search uses `rg -l <pattern>` (file list) or `rg -c <pattern>` (per-file counts), not bare `rg <pattern>`. Decide which files are relevant from the list, then read content only from those. Don't dump full match output into context as a first step.
- **Cap match count when probing.** When you need content, use `rg -n -m 3 <pattern>` or `rg -n --max-columns 200 <pattern>` for the first look. Widen only if needed.
- **Targeted reads over whole-file reads.** For files >500 lines, locate the relevant span with `rg -n` first and read only that range. Never read a full file in `compiled_circuits/`, `test_proofs/`, or `**/generated/` — they are machine-generated and not meaningfully readable end-to-end.
- **Prefer `rg` over recursive `grep`.** Fall back to `grep -r` only if `rg` is unavailable.

### Output Trimming

- **Trim chatty commands at the source**, not by paging into context: `cargo build 2>&1 | tail -50`, `cargo test ... 2>&1 | grep -E 'FAIL|error'`, `| wc -l` when only the count matters.
- **Cache expensive runs.** For long builds, full test suites, or profiling, redirect to a file and query afterwards: `cargo test -p <crate> > /tmp/test.out 2>&1`, then `tail -40 /tmp/test.out` or `rg -n 'FAIL|error' /tmp/test.out`. Lets you re-inspect with different filters without re-running.
- **Suppress warnings** when only errors matter: `RUSTFLAGS="-Awarnings" cargo check -p <crate>`. This repo's crates produce substantial warning noise that is usually unrelated to the task.

### Cargo Scoping

- Run `cargo check -p <crate>` before `cargo build --release` — much faster feedback, and release builds here can take multiple minutes.
- Always scope with `-p <crate>` (and `--lib` / `--tests` / `--bin <name>` where possible) instead of building the workspace.

### Git History Hygiene

- **Preflight unfamiliar commits with `git diff-tree --no-commit-id --name-only -r <sha>`** (paths only, no diff or stat). For commits that may touch generated paths or have a wide blast radius, do this before any `--stat`/diff and decide which paths actually matter.
- **Cap `git show --stat`.** Use `git show --stat --stat-count=80 <sha>`; if the output reports files were omitted, decide whether the omitted paths matter before widening. Never run `git show <sha>` (full diff) on a commit you haven't sized.
- **Scope full diffs.** When you need diff content, scope it: `git show <sha> -- <path>` or `git log -p -- <path>`. Don't use `git log -p` without a path filter when generated files might be touched.

### Size-Aware Abort

- If a single tool result exceeds ~500 lines or is visibly very large, **stop**. Do not read further matches from it. Re-scope (narrower path, narrower pattern, lower `-m`) and retry. If narrowing isn't possible, fall back to subagent delegation (below) or summarize aggressively without ingesting the full output.

### Subagent Delegation

If subagents are available and permitted by the active runtime instructions, delegate the operations below so the bulk output stays out of the main conversation. If subagents are unavailable or restricted, narrow the operation locally and summarize aggressively instead — do not run the broad operation in-context as a fallback.

- An unscoped `rg` / `grep` across the workspace.
- Exploratory reads of files under `compiled_circuits/`, `test_proofs/`, or `**/generated/`. (Targeted single-file reads with a known path are fine.)
- `git show <sha>` or `git log -p` on commits known or suspected to touch generated files.
- Any task that will produce large intermediate output where you only need the summary.

### Research Termination

- **Stop once the question is answered.** For explanation-only tasks, stop collecting evidence as soon as you have enough source-backed support for your answer. Don't enumerate line anchors for every supporting detail unless the user asks for exhaustive references.
