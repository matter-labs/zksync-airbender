# Lookup and LogUp Review

## Exact construction references

Use these as the paper baseline, then verify the checked-out implementation rather than assuming it is identical:

- Ulrich Haböck, [*Multivariate lookups based on logarithmic derivatives*](https://eprint.iacr.org/2022/1530), Cryptology ePrint Archive, Report 2022/1530 (2022). This is the original LogUp reference.
- Shahar Papini and Ulrich Haböck, [*Improving logarithmic derivative lookups using GKR*](https://eprint.iacr.org/2023/1284), Cryptology ePrint Archive, Paper 2023/1284 (2023). This is relevant when logarithmic-derivative claims are evaluated or compressed inside GKR.

The implementation, batching strategy, table layout, field, and GKR integration may change. The stable security goal does not: every enabled query must belong to the intended table or multiset of the specified size, encoding, and multiplicity rules, and no disabled or fabricated term may alter that claim.

## Paper-level invariant

At a high level, LogUp turns multiset inclusion into an equality of logarithmic-derivative sums. For a random challenge `beta` and an injective or randomly compressed encoding `enc`, the checked relation has the form

```text
sum over enabled queries q: 1 / (beta + enc(q))
  =
sum over table rows t: multiplicity(t) / (beta + enc(t)).
```

The exact signs, shifts, batching challenges, and numerator representation are implementation-specific. Recover them from code. Confirm that the final equality and every inverse relation are enforced, not merely computed by the witness generator.

## Airbender implementation profile

The current architecture describes three separate local LogUp arguments, split to avoid multiplicity-count overflow:

- `Generic`, including authenticated instruction-decoder and other fixed-table lookups;
- `RangeCheck16`, used for most 16-bit word limbs;
- `TimestampRangeCheck`, used for timestamp limbs that are commonly 19 bits.

Their terms are produced by circuit rows, compressed through GKR, and completed by verifier logic at the proving-chunk level. Therefore a per-circuit audit should assume the chunk-level completion mechanism is sound while checking that this circuit emits exactly the right local claims. Verify names, widths, table sizes, maximum multiplicities, setup commitments/caps, and completion logic in the branch under review.

## Local obligations

Inspect:

- the semantic query tuple and every encoded field;
- the table contents, dimensions, row count, setup commitment, and table identifier;
- deterministic tuple packing and random compression challenges;
- participation selectors, execution flags, multiplicities, and multiplicity bounds;
- inverse witnesses and constraints for each denominator;
- accumulator initialization, transitions, exposed outputs, and final equality;
- denominator-zero behavior and any exceptional challenge event;
- dummy rows, padding rows, and empty tables;
- GKR wiring from the originating row through compression to the verifier-visible claim.

Check key composition separately from table identity, gating, and multiplicity.
A query can be routed to the right table, correctly gated, and correctly counted
while still being keyed on the wrong value. For each lookup, enumerate the key's
component fields and, for every opcode or branch that activates it, confirm each
field carries the operand that branch's semantics require. Where one shared key
serves several branches, check every branch: a field that is right for the
register-register form is often wrong for the immediate form, and a field that
never appears in the key at all is the easiest omission to miss. Confirming that
a lookup is correctly gated says nothing about what it is asking.

For each activating branch, write the honest query-field expressions and the
exact enforced key-field expressions side by side after selection, conversion,
and packing, then compare them field by field. Witness construction is evidence
of intent, not enforcement. A downstream lookup against the expected table does
not close an earlier disagreement unless every semantic key field is the same
expression on that branch.

Ask:

- Is every key field the intended operand for every branch that activates this lookup?
- Does an operand the semantics require reach the key at all?
- Can an enabled query disappear or be routed into the wrong lookup argument?
- Can a fake table row, forged multiplicity, or wrong table size be accepted?
- Can distinct semantic tuples collide before a random challenge is applied?
- Can terms cancel because signs, numerators, or multiplicities are wrong?
- Is every claimed inverse constrained by `inverse * denominator = 1` on precisely the active domain?
- Can a selector exclude an invalid query or include a padding query?
- Is a fixed/preprocessed table cryptographically bound to the proof statement?

## Review boundary

Audit all local lookup machinery for the named circuit. If final equality is completed across a chunk or against shared setup, record that as an explicit assumption and verify the circuit-to-completion interface. Mark correctness of the external completion mechanism `REQUIRES_GLOBAL_AUDIT`; do not use that boundary to excuse a malformed local query, multiplicity, selector, or accumulator output.
