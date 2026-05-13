# Backward `immediate_factor` encoding — perf design note

This note captures a deferred optimization opportunity for the
`CoefficientRecipe::immediate_factor` field in
[`prover/gkr/backward_flat.rs`](../src/prover/gkr/backward_flat.rs).

## Current shape

For each backward coefficient recipe we store:

- `batch_power: u32`
- `negate: bool`
- `immediate_factor: E` — known at build time
- `prefactors: Vec<Vec<…>>` — 0..2 challenge prefactors evaluated at runtime

The final per-term coefficient at runtime is

```
base^batch_power * immediate_factor * Π(prefactor_i)
```

negated if `negate` is true.

## Problem

For many gates `immediate_factor` is in fact a cs-side `u32` coefficient
promoted to `E` via `E::from_base(BF::from_u32_with_reduction(coeff))` (see
`build_single_max_quadratic_constraint_inputs_and_metadata` and the other
`*_inputs_and_metadata` helpers in `backward.rs`). Storing the value as `E`
forces every `c1_bf_bf` evaluation in round 0 (and the continuation
equivalents) to evaluate `E * BF * BF` — ~4 base multiplications on `Ext4`
per row — when the structurally correct shape is `BF * BF * BF` (~1 base
mul) accumulated in `BF` and lifted to `E` once per gate via the gate's
`batch_power = α^k` factor.

## Viable fixes (none change `c1_bf_bf` row counts)

1. **`ImmediateFactor` sum type.** Replace `immediate_factor: E` with
   `ImmediateFactor::Base(BF) | Ext(E)` and a parallel BF table the kernel
   reads when the BF variant is selected.
2. **Split `c1_bf_bf` into two term types.** `c1_bf_bf_bf` for pure-BF
   coefficients alongside the existing `c1_bf_bf` for mixed/E coefficients.
   Each BF row's coefficient shrinks from 16 B to 4 B — descriptor-bytes
   win on top of the compute win.
3. **Defer the BF→E lift entirely.** Keep `immediate_factor: BF` and have
   the kernel choose the multiplication width via a single discriminator
   bit; the result genuinely lives in `E` only after the `batch_power`
   multiplication.

## Out of scope here

This is a per-row cost optimization, not a row-count change. Deferred-form
templates that carry real verifier challenges via `prefactors` must remain
in `E`.
