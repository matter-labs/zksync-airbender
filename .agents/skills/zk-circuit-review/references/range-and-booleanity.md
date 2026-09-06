# Range and Booleanity

## Invariant

Values interpreted as restricted-domain values must actually belong to that domain.

Examples:

- bits
- bytes
- u16/u32 limbs
- carries
- borrows
- opcodes
- counters
- indices
- enum tags

## Booleanity

For a boolean `b`, look for an equivalent of:

```text
b * (1 - b) = 0
```

or another constraint/lookup that restricts `b` to `{0,1}`.

## Limb Decomposition

For decomposed integers verify both:

1. each limb is range constrained
2. the limbs are recomposed and linked to the original semantic value when such a value exists

## Questions

- is a field element treated as an integer without a range check?
- is an enum tag allowed to take unintended values?
- are carry/borrow values constrained to the intended range?
- can overflow alter semantics?
- does a lookup actually constrain the exact width expected?
- is a supposedly 32-bit value represented by limbs that together admit values outside the intended domain?

## Example: 32-bit Addition

For 16-bit limbs:

```text
a_low + b_low = c_low + 2^16 * carry_low

a_high + b_high + carry_low = c_high + 2^16 * carry_high
```

Soundness additionally requires appropriate domain constraints such as:

- `a_low`, `a_high`, `b_low`, `b_high`, `c_low`, `c_high` are u16
- carry variables are boolean or otherwise restricted correctly

Arithmetic identities alone do not imply those ranges over a field.

## Normalized Multi-Limb Check

Range checks also do not establish that the limb recurrence is the intended
one. Recombine intended and enforced limb equations into a common radix
identity. Compare, for every activated operation, the coefficient and sign of
each input/output limb, carry or borrow input/output, operation-specific term,
and constant. Treat the first, recurrent, and final limbs separately; shared code
can implement different recurrence boundaries. Exercise both values of Boolean
auxiliaries with a nonzero boundary case rather than relying only on all-zero
witnesses.
