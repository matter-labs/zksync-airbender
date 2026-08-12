# Signed SLTI used the register sign instead of the immediate sign

## Classification

- Confirmed historical soundness and completeness bug
- Components: standalone jump/branch/SLT GKR circuit and unified reduced-machine circuit
- Bug class: wrong operand selected for a signed-comparison lookup
- Fixed by: [`403b960`](https://github.com/matter-labs/zksync-airbender/commit/403b9609f1d092762462d1e7b0fa886727815f0f), PR [#326](https://github.com/matter-labs/zksync-airbender/pull/326)
- Vulnerable revision for reproduction: `1f967d68f5f22e6f5b33b1939291867e5f40ece8`

## Intended relation

The `ConditionalJmpBranchSlt` table resolves signed and unsigned comparisons from the subtraction borrow, equality bit, `funct3`, and both operands' signs. For register-register SLT and branches, the second sign is `sign(rs2)`. For SLTI, the decoder sets `rs2 = x0` and supplies the second operand through `imm`, so the table must receive `sign(imm)`.

## Vulnerable relation

Both circuits always packed `rs2_high` into the table key. On SLTI rows this supplied zero as the second-operand sign even when the immediate was negative. The arithmetic subtraction used the immediate, while the signed-resolution lookup classified the operands using a different value.

## Security impact

The circuit did not prove RISC-V's signed immediate comparison. Certain cross-sign SLTI inputs resolved to the unsigned result, so the proven destination register could disagree with the specified instruction semantics. Correct executions for those inputs were also rejected if the witness followed the ISA rather than the faulty table key.

## Fix

Each circuit now commits a dedicated sign-source variable bound to:

```text
slt_sign_source = rs2_high + is_slt * imm_high
```

Decoder mutual exclusion makes this a selection: branches retain `rs2_high`, while SLT/SLTI rows use the immediate high limb where applicable. The lookup key now uses this committed value. The unified circuit also reserves the additional scratch slot.

## Audit lesson

For every lookup key, trace each packed field back to the semantic operand for every opcode sharing the gadget. A subtraction relation can use the correct operand while a later sign, carry, or resolution table silently uses a sibling operand.

## Regression test

- Evaluate signed SLTI cases in which the register and immediate have opposite signs, including `0 < -1` and a negative register compared with a nonnegative immediate.
- Inspect the compiled standalone and unified relations and assert that the comparison-table sign input is value-bound to the immediate on SLTI rows.
- Retain register-register branch and SLT cases to prove the selector does not replace `rs2` there.

The fix includes `conditional_table_resolves_signed_slti_from_immediate_sign` and `jump_branch_slt_binds_immediate_sign_source` as direct guards.

## Reproduction evidence

```sh
git diff 1f967d68f5f22e6f5b33b1939291867e5f40ece8 403b9609f1d092762462d1e7b0fa886727815f0f -- \
  cs/src/gkr_circuits/jump_branch_slt_family/circuit.rs \
  cs/src/gkr_circuits/unified_reduced_machine/jump_branch_slt.rs \
  cs/src/gkr_circuits/unified_reduced_machine/circuit.rs
```
