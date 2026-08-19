# Sparse delegation layout emitted a tuple where an Option was required

## Classification

- Confirmed historical generated-verifier implementation bug
- Fixed by: [`9b955b6`](https://github.com/matter-labs/zksync-airbender/commit/9b955b649cfbd1ef04305ec15af344dc5a41354f)
- Vulnerable revision: `6327a202048659bd8afac3b65cf65bb7e2ed9fc3`

## Failure

The token generator for sparse read and write layouts emitted `variable_dependent: (c, v, i)` even though the field's type was `Option<(c, v, i)>`. The generated artifact therefore failed to preserve the compiler's `Some(...)` variant.

## Impact and fix

Regenerating a verifier for variable-dependent indirect accesses produced malformed Rust instead of a faithful layout, blocking that circuit from obtaining a valid verifier artifact. The fix emits `Some((c, v, i))` for both reads and writes while retaining `None` for constant-only addresses.

## Regression

Generate sparse read and write layouts with and without variable-dependent offsets, then compile the quoted artifact and round-trip its enum variants.

```sh
git diff 6327a202048659bd8afac3b65cf65bb7e2ed9fc3 9b955b649cfbd1ef04305ec15af344dc5a41354f -- cs/src/one_row_compiler/mod.rs
```
