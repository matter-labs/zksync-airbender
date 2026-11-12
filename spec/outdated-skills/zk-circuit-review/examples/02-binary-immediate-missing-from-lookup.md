# Binary-immediate operations looked up `rs2` but omitted the immediate

## Classification

- Confirmed historical soundness bug
- Component: GKR binary/shift family circuit
- Bug class: one execution branch omitted from a manually aggregated lookup tuple
- Fixed by: [`b5021bc`](https://github.com/matter-labs/zksync-airbender/commit/b5021bcd4c68d4c691a7df1ce11ce49b9222e272)
- Vulnerable revision for reproduction: `725892f1727a7eaa411c8b2303cc8cecfa19410d`

## Intended relation

AND, OR, and XOR register and immediate forms shared one byte-wise lookup. Preprocessing represented an immediate form with `rs2 = x0` and placed the immediate bytes in decoder data. The second lookup operand therefore needed to be:

```text
rs2_byte + immediate_byte
```

under the binary-op selector. Exactly one contribution is nonzero after preprocessing. Bytes 0 and 1 come from decoder immediate limbs; bytes 2 and 3 use the separately constrained sign-extension byte.

## Vulnerable relation

The manually accumulated second lookup column contained only:

```text
is_binary_op * rs2_byte
```

The immediate contribution was absent. Immediate-form instructions consequently authenticated a lookup against zero, even though a separate lookup had correctly derived the immediate's sign extension.

This is a useful warning: constraining an auxiliary value somewhere in the circuit is insufficient if it is omitted at its semantic use site.

## Security impact

Immediate-form AND, OR, and XOR rows authenticated the second operand as zero rather than as the decoded immediate. The circuit's accepted state transition therefore disagreed with the instruction semantics whenever the immediate materially changed the result. The separately constrained sign-extension byte did not help because it was never consumed by the main operation lookup.

## Fix

For every byte, the fix added `is_binary_op * binary_op_imm` to lookup column 1, selecting the low decoder bytes or the sign-extension byte according to the byte index.

## Audit lesson

When several variants share a manually aggregated tuple, build a case matrix for every tuple column. Verify each selector's contribution independently. Then trace each previously constrained auxiliary value to the exact lookup or polynomial where its semantics must be consumed.

## Regression test

- Run AND-immediate, OR-immediate, and XOR-immediate with nonzero low bytes and with negative sign-extended immediates; compare all four output bytes with an independent bitwise reference.
- Assert the generated lookup tuple's second column equals the appropriate immediate byte on immediate forms and the `rs2` byte on register forms.
- Prove and verify the valid traces so the test covers the compiled GKR relation, not only witness generation.

## Reproduction evidence

```sh
git diff 725892f1727a7eaa411c8b2303cc8cecfa19410d b5021bcd4c68d4c691a7df1ce11ce49b9222e272 -- \
  cs/src/gkr_circuits/binary_shifts_family/circuit.rs
```
