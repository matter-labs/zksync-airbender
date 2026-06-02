# AGENTS.md

This tree contains the native CUDA/C++ side of `circuit_prover`.

The **cluster-wide** native rules — `clang-format` (against
[`../../.clang-format`](../../.clang-format)) and Rust↔CUDA interface stability —
live in [`../../AGENTS.md`](../../AGENTS.md); the parent
[`../AGENTS.md`](../AGENTS.md) also applies. This file adds only what is specific
to `circuit_prover`'s native code.

## Upstream Constant Drift

- If native code hard-codes or duplicates a value owned by an upstream crate,
  add or update a Rust-side compile-time drift guard rather than relying on
  the duplicate staying in sync by convention.
- Follow the drift-guard pattern documented in [`../AGENTS.md`](../AGENTS.md)
  and place the assert in the established Rust-side guard location unless a
  more local guard site is clearly better.
