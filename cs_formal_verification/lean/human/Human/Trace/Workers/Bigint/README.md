# Bigint worker execution

This directory states selected bigint operation effects on actual `RV.State` port
reads/writes within initialized native history. The claim connects limb
observations to the seven existing references and shared terminal matching. It
does not establish full caller-control validity, which the issued invalid-control
fixture leaves open.

## Checked results

[`rv_operation_execution`](../../../../../proven/Proven/Final/Trace/Workers/Bigint/RVTheorems.lean) proves all seven selected operation
effects on actual native RV reads/writes and terminal cells in a shared pool,
under public initialization/alignment, exact matching and the modeled bigint table.
Operand/pointer bounds are derived; this still admits the flagged x12 = 0 case
and does not prove the original caller's full control-mask ABI.

Read [Theorems](RVTheorems.lean) for the seven selected operation references
on actual native port observations. Follow
[the local circuit guide](../../../Circuits/Bigint/README.md) for addresses,
control decoding and named limb mappings.

[Shared operation inputs](../../../Helpers/Delegation/RVOperations.lean) and
[worker context](../../../Helpers/Delegation/WorkerContext.lean) bind initialized
history, actual reads/writes and public domain/table conditions.
The shared execution mapping reaches native terminal tokens.

The pinned reference rejects the control words of the [bigint control fixture](../../../../../test/Tests/UnifiedDelegation.lean)
(x12 = 0 with no control bit; x12 = 65537 with the ADD bit). Native operation observations do not close that full caller ABI.
Whole mixed caller retirement remains separate.
