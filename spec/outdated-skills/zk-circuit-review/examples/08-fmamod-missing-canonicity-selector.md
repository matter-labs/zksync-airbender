# FMAMOD was omitted from the modular-result canonicity selector

## Classification

- Confirmed historical soundness bug
- Component: GKR add/sub/LUI/AUIPC/modular-operations family
- Bug class: one opcode flag omitted from a shared manually aggregated constraint
- Fixed by: [`a16b6ec`](https://github.com/matter-labs/zksync-airbender/commit/a16b6ec1196f700798f7c3d802a9c07c8500e9ea), PR [#309](https://github.com/matter-labs/zksync-airbender/pull/309)
- Vulnerable revision for reproduction: `6e9cd7d594bf606b9dad26c8456a4f5e311d275a`

## Intended relation

ADDMOD, SUBMOD, MULMOD, and FMAMOD return the unique canonical 32-bit representative in `[0, p)`. Field equality alone proves only congruence modulo `p`, so all four flags must activate the limb recurrence and forced-borrow check that establish `out < p`.

The shared selector was intended to be:

```text
is_modular = is_addmod + is_submod + is_mulmod + is_fmamod
```

with mutually exclusive opcode flags.

## Vulnerable relation

`is_modular` omitted `is_fmamod`. A different selector, `is_mul_like`, did include FMAMOD and enforced field equality between the output and multiplication/FMA intermediate. Thus FMAMOD proved `out = result mod p` but did not prove that `out` was canonical.

## Security impact

FMAMOD proved only equality modulo `p`, not uniqueness of the returned 32-bit representative. Multiple range-valid word encodings of the same field element could satisfy its semantic equation, so the circuit did not enforce the machine's canonical-output rule for this opcode.

## Fix

The fix added `Expr::from(is_fmamod)` to `is_modular`, activating the same canonicity constraints used by the other modular operations.

## Audit lesson

Whenever flags are manually summed to share a constraint, derive the complete operation set from the decoder and compare it with every aggregate independently. A newer variant may be included in the semantic equation but omitted from range, canonicality, memory, or state constraints.

## Regression test

- Add a decoder-to-constraint coverage test that asserts each modular opcode flag appears in both the semantic selector and the canonicality selector.
- For FMAMOD boundary inputs, compare the returned word with a reference and assert it is strictly below `p`.
- Include the valid zero-result case and values near `p-1`, then prove and verify the full modular-op instruction binary from PR #309.

## Reproduction evidence

```sh
git diff 6e9cd7d594bf606b9dad26c8456a4f5e311d275a a16b6ec1196f700798f7c3d802a9c07c8500e9ea -- \
  cs/src/gkr_circuits/add_sub_family/circuit.rs
```
