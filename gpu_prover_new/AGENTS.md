# AGENTS.md

## Project Overview
`gpu_prover_new` is a Rust crate in the `zksync-airbender` workspace that builds CUDA-backed proving components. It uses a custom build script at `build/main.rs` and depends on `era_cudart`/`era_cudart_sys` for CUDA integration.

## Hard Constraints
- Do not modify CMake/CUDA flags.
- Do not change build configuration behavior unless explicitly requested.

## Working Agreements
- Prefer small, targeted changes with a clear rationale.
- Keep edits ASCII unless the file already uses Unicode.
- Avoid changing public APIs unless the request explicitly calls for it.

## Scope Control
- Keep changes task-focused; avoid unrelated refactors.
- Avoid dependency/version churn unless explicitly requested.

## Key Files and Structure
- `build/main.rs`: build script that wires cmake/CUDA integration.
- `native/`: native CUDA/C++ sources and build artifacts managed by the build script.
- `src/`: crate modules; follow existing layout and naming.
- `Cargo.toml`: dependency and feature definitions for this crate.

## Build and Test
- Minimum validation for any code change: `cargo check -p gpu_prover_new`
- Build: `cargo build -p gpu_prover_new`
- Test: `cargo test -p gpu_prover_new`
- Benches: `cargo bench -p gpu_prover_new`
- Some tests are compute-intensive and should not be run in debug mode; use release mode for those tests: `cargo test -p gpu_prover_new --release`.

## Build Script Boundaries
- `build/main.rs` is the only Rust entrypoint that wires CMake.
- Unless explicitly requested, changes in `build/main.rs` must be non-behavioral.

## Code Conventions
- Use `log` for diagnostic output rather than `println!`.
- Prefer `rayon` for CPU parallelism when applicable.
- Keep unsafe blocks minimal and justified; comment on non-obvious invariants.
- Add `// SAFETY:` comments for non-trivial unsafe blocks.

## CUDA Notes
- CUDA runtime dependencies are pinned via `era_cudart` and `era_cudart_sys`.
- Do not modify CMake/CUDA flags.

## Pull Requests
- Use `.github/pull_request_template.md` when preparing PR descriptions.
