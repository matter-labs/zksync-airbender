# MULMOD constraints were selected by the SUBMOD flag

## Classification

- Confirmed historical soundness and completeness bug
- Component: unrolled add/sub/LUI/AUIPC/modular-operations circuit
- Bug class: execution selector copied from the wrong branch
- Fixed by: [`cb51e84`](https://github.com/matter-labs/zksync-airbender/commit/cb51e845228940003293aa9d17795f6589353873)
- Vulnerable revision for reproduction: `fd21f15f389e2c6ad2e65e4de01392e22a9a9ea5`

## Intended relation

Each modular branch must be gated by its own mutually exclusive decoder flag. In particular, the multiplication and reduction constraints for MULMOD must use `decoder.perform_mulmod()`, while subtraction constraints use `decoder.perform_submod()`.

## Vulnerable relation

The circuit assigned:

```text
is_mulmod = decoder.perform_submod()
```

All later MULMOD equations and witness selections referenced that alias. Actual MULMOD rows therefore had `is_mulmod = 0`, while SUBMOD rows activated both the subtraction and multiplication-labelled branches.

## Security impact

On a MULMOD instruction, the circuit omitted the branch-specific multiplication relation and did not bind the destination to the specified modular product. On SUBMOD, unrelated equations could overconstrain correct execution. This is the canonical missing-branch underconstraint caused by a selector copy/paste error.

## Fix

The selector now comes from `decoder.perform_mulmod()`. The remainder of the change keeps the existing MULMOD constraints and witness selection under that correct flag.

## Audit lesson

Build a selector-to-constraint coverage matrix and derive it independently from decoder definitions. Variable names and comments are not evidence that a selector has the matching source; compare the actual accessor or bit index for every branch.

## Regression test

- Introspect the circuit and assert that each modular opcode activates exactly one branch selector.
- For ADDMOD, SUBMOD, and MULMOD, compare emitted flag coefficients with the decoder bit allocation.
- Prove and verify valid MULMOD vectors whose result differs from both operands and from their subtraction, plus valid SUBMOD boundary cases.

## Reproduction evidence

```sh
git diff fd21f15f389e2c6ad2e65e4de01392e22a9a9ea5 cb51e845228940003293aa9d17795f6589353873 -- \
  cs/src/machine/ops/unrolled/add_sub_lui_auipc_mop.rs
```
