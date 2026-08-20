# Timestamp boundary checks reused a legacy u16-limb parser

## Classification

- Confirmed historical state-layout correctness bug; previously overstated as silent truncation
- Invariant: verifier boundary checks interpret each field array according to its own algebraic limb layout
- Component: full-statement lazy-init/teardown continuity checks
- Security character: configuration fragility / overconstraint; the historical helper asserted high bits were zero rather than silently discarding them
- Fixed by: [`97dbacf`](https://github.com/matter-labs/zksync-airbender/commit/97dbacf8a3eec4dcb6621bc9965b1fa784efc6d5), PR [#81](https://github.com/matter-labs/zksync-airbender/pull/81)
- Vulnerable revision: `0b749ed60483e28712d89e0783552d78ea06b2cb`

## Composition context

The full-statement verifier compares lazy-initialization boundaries between consecutive chunks. Addresses, values, PCs, and timestamps may all be represented by two field elements, but that does not make their limb semantics identical. The legacy helper interpreted its input specifically as two 16-bit limbs forming one `u32`.

Timestamps had become configurable rather than hardcoded to the legacy 16-bit layout. The affected branch only needed to prove that a padding teardown value and timestamp were zero; reconstructing either through an unrelated integer encoding was unnecessary.

## Intended invariant

When adjacent sorted-memory boundaries do not advance, the prior row must be the canonical padding boundary:

```text
last_previous_address == 0             # address uses two u16 limbs
each teardown_value field limb == 0    # direct reduced-field zero checks
each teardown_timestamp field limb == 0
```

PC and address reconstruction can continue using an explicitly named two-u16-limb parser where that is their declared encoding.

## Failure

The verifier called generic-looking `parse_field_els_as_u32_checked` on the teardown timestamp. In reality the helper reduced both field elements, asserted each fit in 16 bits, and returned `low | high << 16`. It therefore embedded a legacy timestamp-width assumption into a global boundary check after timestamp representation became configurable.

The old example described this as higher bits being discarded. That was inaccurate: the helper rejected limbs with high bits set. Moreover, in the affected branch the required semantic value was zero, so the direct historical evidence is an inappropriate/overrestrictive representation check, not a demonstrated nonzero timestamp bypass.

## Failure flow

1. Evolve the timestamp limb allocation or field representation independently of address/PC encoding.
2. Reach the padding/lazy-init boundary path in the full-statement verifier.
3. Feed timestamp limbs into the legacy u16 parser even though the boundary property only requires field-wise zero.
4. Reject a representation that the timestamp circuit/layout permits, or create maintenance ambiguity about which high bits are meaningful.

The composition risk is that prover, circuit, and full-statement verifier cease agreeing on the state domain at chunk boundaries. This commit should be treated as correctness hardening unless a separate revision demonstrates an accepted noncanonical value.

## Impact and fix

The verifier carried a stale, hardcoded limb-width assumption into configurable timestamp handling. The fix renames the helper to `parse_field_els_as_u32_from_u16_limbs_checked`, retains it only for actual u16-limb values such as addresses and PC, and checks both teardown timestamp/value field elements directly for zero after reduction.

Audit semantic types rather than array shapes. Two `[Field; 2]` values can represent a u32, two independent limbs, a timestamp decomposition, or an extension-field element and require entirely different validation.

## Regression

- Unit-test the u16 parser separately at limb boundaries and verify it is called only for declared u16-limb encodings.
- Test timestamp configurations at and beyond the legacy width through actual chunk boundary values.
- Require each timestamp limb to be zero in the padding branch; mutate either limb independently and require rejection.
- Add type/layout-level wrappers or assertions so timestamp arrays cannot accidentally reuse address parsing.

## Reproduction evidence

The diff shows both the explicit helper rename and replacement of timestamp parsing with per-limb zero checks:

```sh
git diff 0b749ed60483e28712d89e0783552d78ea06b2cb 97dbacf8a3eec4dcb6621bc9965b1fa784efc6d5 -- verifier_common/src/lib.rs full_statement_verifier/src/lib.rs
```
