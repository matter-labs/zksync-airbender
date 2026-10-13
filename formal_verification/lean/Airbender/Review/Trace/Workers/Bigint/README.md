# Bigint worker execution

This directory states selected bigint operation effects on actual Sail port
reads/writes within initialized native history. The claim connects limb
observations to the seven existing references and shared terminal matching. It
does not establish full caller-control validity, which the issued invalid-control
fixtures leave open.

## Checked results

[`operation_execution`](Theorems.lean) proves all seven selected operation
effects on actual native Sail reads/writes and terminal cells in a shared pool,
under public initialization/alignment, exact matching and the modeled bigint table.
Operand/pointer bounds are derived; this still admits the flagged no-opcode case
and does not prove the original caller's full control-mask ABI.

Read [Theorems](Theorems.lean) for the seven selected operation references
on actual native port observations. Follow
[the local circuit guide](../../../Circuits/Bigint/README.md) for addresses,
control decoding and named limb mappings.

[Shared operation inputs](../../../Helpers/Delegation/Operations.lean) and
[worker context](../../../Helpers/Delegation/WorkerContext.lean) bind initialized
history, actual reads/writes and public domain/table conditions.
The shared execution mapping reaches native terminal tokens.

The original reference rejects the checked issued controls 0 and 65537.
Native operation observations do not close that full caller ABI.
Worker ROM/public-byte transport and whole mixed caller retirement remain separate.
