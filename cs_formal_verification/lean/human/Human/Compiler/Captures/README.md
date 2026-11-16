# Cached circuit captures

Each family module states its cached circuit description, arithmetic preservation
claim and arithmetic witness claim. Start with [AddSub.lean](AddSub.lean), then read
the module for the circuit under review. The [compiler guide](../README.md) lists
the common interfaces and machine targets.

The description claim binds the constraint sections to the family artifact.
Arithmetic preservation takes native equations and placement agreement as premises.
Lookup, memory and worker arguments are separate premises of the machine targets.
The [import guide](../../Import/README.md) states the trusted transcription boundary.
