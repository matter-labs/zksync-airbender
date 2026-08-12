# Subword memory address decomposition was not locally canonical or aligned

## Classification

- Confirmed historical soundness bug
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

## Vulnerable relation

The circuit enforced the equation and Boolean carry/offset bits, but did not locally range-check `cleanaddr_low` or prove it was word-aligned. Several prover-chosen terms could trade off against each other while preserving the single field equation. Correctness was implicitly delegated to induction through the global memory argument, although this circuit needed the decomposition to select the accessed word and byte.

## Security impact

The same effective byte address could be represented with a different word cell and offset. The subword circuit could therefore bind a load or store to the wrong memory tuple while satisfying its local arithmetic. This is a real local underconstraint even if the surrounding audit assumes the global RAM permutation itself is consistent.

## Fix

The circuit now:

- commits a copy of `cleanaddr_low` and range-checks it to 16 bits;
- introduces a range-checked word index; and
- enforces `cleanaddr_low = 4 * cleanaddr_low_word`.

Together with the existing Boolean offset bits and carry, these constraints make the decomposition unique without relying on a non-local induction assumption.

## Audit lesson

Do not treat a globally consistent memory argument as proof that each circuit formed the intended address tuple. Audit local address construction separately: limb bounds, alignment, carries, address-space tags, and byte offsets must be pinned before the tuple enters RAM or ROM relations.

## Regression test

- Compare the circuit's decomposition with a native `address & !3` and `address & 3` reference across low-limb boundary values.
- Assert that the compiled relation contains both the 16-bit canonical copy and the factor-of-four alignment equation.
- Prove and verify valid byte and halfword accesses at all permitted offsets, including a carry from the low limb.

## Reproduction evidence

```sh
git diff 7f0f5f63e0575daa8f01f1c1f21ade6906e65bc8 7eca15a5a3781e7b6143d1873f8a4c86ad80b527 -- \
  cs/src/gkr_circuits/mem_subword_only/circuit.rs
```
