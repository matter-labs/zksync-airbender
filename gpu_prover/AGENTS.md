# AGENTS.md

`gpu_prover` is the CUDA-backed prover crate. It uses `build/main.rs` and depends on `era_cudart` and `era_cudart_sys`.

## Constraints
- Do not modify CMake/CUDA flags.
- Do not change build configuration behavior unless explicitly requested.

## Key Files and Structure
- `build/main.rs`: build script that wires cmake/CUDA integration.
- `native/`: native CUDA/C++ sources and build artifacts managed by the build script.
- `src/`: crate modules.

## Legacy Reference
- `../gpu_prover_old/` is the old prover crate. It is kept only as a reference and must not be modified.
- `gpu_prover_old` is not an implementation target for new work; all active prover development belongs in `gpu_prover`.
- `gpu_prover` already overlaps heavily with `gpu_prover_old` across allocator, NTT, ops, witness generation, trace-holder logic, and many CUDA kernels, and more legacy behavior may continue to be reimplemented here.
- Before adding prover logic in `gpu_prover`, first check whether the needed behavior already exists here, then consult the corresponding code in `gpu_prover_old` for reference behavior and invariants.
- Use `gpu_prover_old` to understand behavior, not as a place to land fixes or feature work. Port behavior deliberately into `gpu_prover` rather than copying legacy structure mechanically.

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
