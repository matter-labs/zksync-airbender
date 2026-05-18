# AGENTS.md

This tree contains the native CUDA/C++ side of `gpu_prover`.

The parent [`../AGENTS.md`](../AGENTS.md) still applies. This file adds
native-specific rules for `native/`.

## Formatting

- Format touched native files with [`native/.clang-format`](.clang-format).
- `cargo fmt` does not format this tree; native changes need `clang-format`.

## Rust / CUDA Interface Stability

- Keep exported kernel symbol names, Rust launcher expectations, and other
  Rust↔CUDA interface contracts stable unless the task explicitly requires a
  coordinated change on both sides.
- If a native change requires a coordinated Rust-side interface update, make
  that dependency explicit and keep the two sides consistent in the same task.

## Upstream Constant Drift

- If native code hard-codes or duplicates a value owned by an upstream crate,
  add or update a Rust-side compile-time drift guard rather than relying on
  the duplicate staying in sync by convention.
- Follow the drift-guard pattern documented in [`../AGENTS.md`](../AGENTS.md)
  and place the assert in the established Rust-side guard location unless a
  more local guard site is clearly better.
