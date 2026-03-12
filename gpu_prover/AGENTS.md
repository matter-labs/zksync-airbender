# AGENTS.md

`gpu_prover` is the CUDA-backed prover crate. It uses `build/main.rs` and depends on `era_cudart` and `era_cudart_sys`.

## Constraints
- Do not modify CMake/CUDA flags.
- Do not change build configuration behavior unless explicitly requested.

## Key Files and Structure
- `build/main.rs`: build script that wires cmake/CUDA integration.
- `native/`: native CUDA/C++ sources and build artifacts managed by the build script.
- `src/`: crate modules.

## Build and Test
- Minimum validation for any code change: `cargo check -p gpu_prover`
- Build: `cargo build -p gpu_prover`
- Test: `cargo test -p gpu_prover`
- Bench: `cargo bench -p gpu_prover`
- For compute-heavy GPU tests or prover flows, use `cargo test -p gpu_prover --release` by default. Use debug-mode execution only for quick smoke tests or when debug assertions/symbols are specifically needed.
- For Rust GPU tests, compile first with `cargo test --no-run`, then run the produced test binary under `.agents/bin/with_gpu_lock.sh`. Do not run locked `cargo test ...` directly when the binary can be built first.

## Build Script
- Unless explicitly requested, changes in `build/main.rs` must be non-behavioral.

## Code Notes
- Use `log` for diagnostic output rather than `println!`.
- Prefer `rayon` for CPU parallelism when applicable.
- Keep unsafe blocks minimal and justified; comment on non-obvious invariants.
- Add `// SAFETY:` comments for non-trivial unsafe blocks.
