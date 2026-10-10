# Subword memory address decomposition was not locally canonical or aligned

## Classification

- Historical local-hardening change; not an independent soundness bug under a correct bound global RAM argument
- Evaluation status: non-scored hardening
- Component: `mem_subword_only` GKR circuit
- Bug class: underconstrained address/offset decomposition and missing range checks
- Fixed by: [`7eca15a`](https://github.com/matter-labs/zksync-airbender/commit/7eca15a5a3781e7b6143d1873f8a4c86ad80b527), PR [#334](https://github.com/matter-labs/zksync-airbender/pull/334)
- Vulnerable revision for reproduction: `7f0f5f63e0575daa8f01f1c1f21ade6906e65bc8`

## Intended relation

A byte or halfword address must split uniquely into a word-aligned cell address and the low two byte-offset bits. For base `B = 2^16`, the low-limb equation is:

```text
rs1_low + imm_low = cleanaddr_low + bit0 + 2*bit1 + B*carry
```

`cleanaddr_low` must be a canonical 16-bit limb divisible by four, and `bit0` and `bit1` must be Boolean.

## Pre-hardening relation

The circuit enforced the equation and Boolean carry/offset bits, but did not
locally range-check `cleanaddr_low` or prove it was word-aligned. Taken in
isolation, the row relation admitted several assignments that traded offset bits
against the address.

In the complete machine relation, however, the same raw address variables are
used in both the read and later write tuples. With bound tuple columns, strict
read-before-write timestamps, and deterministic aligned initialization and
teardown, a non-initialized address cannot form a finite closed RAM history.
That global induction forces the active address to be canonical and aligned,
which in turn fixes the offset bits.

Inactive rows require a separate control-flow argument. Their RAM and PC
products are masked to the grand-product identity, and their decoder lookup is
masked. They are not otherwise unconstrained: `cleanaddr_hi` still enters an
unconditional range-check lookup, the offset bits still enter the store-byte
helper lookup, and ordinary constraints still apply. The operation lookup has
its table ID multiplied by `execute`, so an inactive row is routed to the
all-zero `ZeroEntry` and its selected input and outputs must be zero. Thus a
noncanonical inactive address can participate in proof-internal constraints and
valid lookup multiplicities, but it does not reach RAM, ROM, PC, authenticated
machine state, or a public claim.

## Security assessment

There is no independent end-to-end soundness impact under the stated global RAM
assumptions. The local relation is fragile and non-self-contained, but the
global history rejects its alternative address representations.

The issue becomes security-relevant when tuple claims are not bound to their
base address columns, as in the separate memory-tuple cache bug recorded as
scored example 11. In that combined state, the global argument no longer authenticates
the variables on which the induction depends.

## Hardening change

The circuit now:

- commits a copy of `cleanaddr_low` and range-checks it to 16 bits;
- introduces a range-checked word index; and
- enforces `cleanaddr_low = 4 * cleanaddr_low_word`.

Together with the existing Boolean offset bits and carry, these constraints make the decomposition locally unique and remove the non-local dependency.

## Audit lesson

Distinguish a missing local invariant from an exploitable relation gap. A sound
global RAM induction can authenticate an unchanged address variable across read
and write tuples, but only when tuple claims are bound to those exact base
columns and initialization, ordering, closure, and activation masking are all
verified. Local checks may still be worthwhile to make that dependency explicit
and robust against later composition changes.

## Regression test

- Compare the circuit's decomposition with a native `address & !3` and `address & 3` reference across low-limb boundary values.
- Assert that the compiled relation contains both the 16-bit canonical copy and the factor-of-four alignment equation.
- Prove and verify valid byte and halfword accesses at all permitted offsets, including a carry from the low limb.
- As a system-level control, backport only the memory-tuple cache binding and
  confirm that the pre-hardening alias is rejected by full RAM closure even
  though it satisfies the family-local relation.

## Reproduction evidence

```sh
git diff 7f0f5f63e0575daa8f01f1c1f21ade6906e65bc8 7eca15a5a3781e7b6143d1873f8a4c86ad80b527 -- \
  cs/src/gkr_circuits/mem_subword_only/circuit.rs
```
