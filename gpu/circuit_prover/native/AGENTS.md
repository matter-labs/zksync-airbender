# AGENTS.md

This tree contains the native CUDA/C++ side of `circuit_prover`.

The **cluster-wide** native rules — `clang-format` (against
[`../../.clang-format`](../../.clang-format)) and Rust↔CUDA interface stability —
live in [`../../AGENTS.md`](../../AGENTS.md); the parent
[`../AGENTS.md`](../AGENTS.md) also applies. This file adds only what is specific
to `circuit_prover`'s native code.

## Runtime `assert` Is Documentation, Not A Guard

Native builds are **always** `-DNDEBUG`: `gpu_native_build` pins CMake
`Release` unconditionally (`gpu/native_build/src/lib.rs`, `config.profile("Release")`),
and nothing overrides the release flags. A `cargo build` without `--release`
still produces `-DNDEBUG` device code, so a runtime `assert` in a `.cu` never
executes in any build this repo produces.

- Do not write a comment claiming an `assert` protects anything, and do not
  hedge with "in builds that keep assertions enabled" — there are none.
- Keeping an `assert` as an executable statement of a precondition is fine.
  When you do, **name its real enforcer** in the comment (the host-side
  validator, a probe kernel, a compile-time drift guard) so the reader knows
  where the invariant is actually held.
- If no other enforcer exists, the `assert` is not one either. Move the check
  to the host encoder/validator, where this crate puts validation.

## Upstream Constant Drift

- If native code hard-codes or duplicates a value owned by an upstream crate,
  add or update a Rust-side compile-time drift guard rather than relying on
  the duplicate staying in sync by convention.
- Follow the drift-guard pattern documented in [`../AGENTS.md`](../AGENTS.md)
  and place the assert in the established Rust-side guard location unless a
  more local guard site is clearly better.
