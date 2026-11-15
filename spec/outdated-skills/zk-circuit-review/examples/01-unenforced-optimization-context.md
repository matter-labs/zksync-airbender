# Unenforced optimization context removed an opcode family's arithmetic

## Classification

- Confirmed historical soundness bug
- Component: unrolled `jump_branch_slt` circuit and constraint composer
- Bug class: constraints accumulated in an auxiliary object but never emitted
- Fixed by: [`77e979e`](https://github.com/matter-labs/zksync-airbender/commit/77e979edd7585d9de02cb2c6bdfef044afa8db44), PR [#212](https://github.com/matter-labs/zksync-airbender/pull/212)
- Vulnerable revision for reproduction: `33dacfe58d3315bf802dca66437ae7138453c9f1`

## Intended relation

`OptimizationContext` allocated shared output variables and collected masked add/sub, range, lookup, and zero-test relations for the JAL, JALR, branch, SLT, and SLTI cases. Calling `opt_ctx.enforce_all(cs)` was the step that converted those collected relations into circuit constraints.

For example, a JAL row must enforce both:

```text
rd = pc + 4
pc_next = pc + imm
```

and a branch row must bind the comparison flag to `rs1 - rs2` before using that flag to select `pc + 4` or `pc + imm`.

## Vulnerable relation

`apply_jump_branch_slt` constructed every relation through `opt_ctx.append_*`, used the resulting variables in later lookups and output-selection constraints, and then returned without calling `enforce_all`.

The later constraints only restricted properties of the shared result variables. They did not restore the missing equalities to the operands. For example, alignment cleanup constrained a chosen next PC's low bits, but did not prove that the chosen value equaled `pc + imm`.

## Security impact

The link register and next-PC variables remained subject to downstream range, cleanup, and output-copy constraints, but were not tied to the operands that define JAL/JALR/branch/SLT semantics. The proved relation could therefore admit state transitions that did not implement the decoded instruction. Branch comparison intermediates were affected by the same missing terminal enforcement.

## Fix

The fix added `opt_ctx.enforce_all(cs)` at the end of the circuit. It also added a `Drop` guard that asserts unless `enforce_all` was called exactly once, converting this silent omission class into a construction-time failure.

## Audit lesson

Treat every batching, optimization, builder, or deferred-enforcement object as a two-phase protocol. Trace both relation collection and the terminal flush/finalize call. Inspect early returns and every circuit entrypoint, and prefer an API that fails closed when a populated context is dropped.

## Regression test

- Keep a `#[should_panic]` construction test that drops a populated `OptimizationContext` without calling `enforce_all`, and assert the guard's specific failure message.
- For every opcode in the family, evaluate a valid trace with nontrivial operands and check the link register, comparison result, and next PC against an independent RV32 reference before proving and verifying it.
- Regenerate the serialized layout and assert that the expected add/sub relations are present, so a witness-only test cannot mask another missing flush.

## Reproduction evidence

```sh
git diff 33dacfe58d3315bf802dca66437ae7138453c9f1 77e979edd7585d9de02cb2c6bdfef044afa8db44 -- \
  cs/src/machine/ops/unrolled/jump_branch_slt.rs \
  cs/src/devices/optimization_context.rs
```
