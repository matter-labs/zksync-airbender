# Imported setup tables

Table contents come from [native setup JSON](../../../../artifacts/setup/README.md).
Review keeps artifact paths, query layouts, native IDs/offsets and field casts.
The mathematical row relations and their proofs belong in `Proofs/`; consuming
instruction proofs reuse those relations through checked imported-data connections.

[Range](Range.lean), [Bytes](Bytes.lean), [Subword](Subword.lean) and
[Lookups](Lookups.lean) expose the shared tables. Circuit-specific tables and
controllers live in each circuit's `Tables/` directory. The checked connections
cover keys, outputs, padding, discriminators and disabled queries, with the
original field and inverse conditions.

For shift/binop data, [setup JSON](../../../../artifacts/setup/shift-binop.json)
feeds physical-column imports such as [Shift/Column0](../../../Data/Tables/Shift/Column0.lean).
[Region assembly](../../../Data/Tables/ShiftData.lean) retains the native regions and exported offsets;
[Bytes](Bytes.lean) selects their combined rows and wraps them in Clean's table
interface. That wrapper supplies field casts, table identity, index hints and
membership over the imported rows. The checked mathematical semantics live in
[ShiftCharacterization](../../../Proofs/Tables/ShiftCharacterization.lean) and its
imported-row proofs; the wrapper supplies no replacement table recipe.

Program-dependent setup quantifies over arbitrary public text and initial state.
The [public native setup](../../Compiler/NativePublicSetup.lean) supplies decoder
and full-word ROM rows; the [subword setup](../../Compiler/NativeSubwordSetup.lean)
also supplies halfword and byte ROM regions. The
[program decoder proofs](../../../Proofs/GKRProtocol/ProgramRows.lean) and
[native acceptance adapter](../../../Proofs/GKRProtocol/NativeMachineAcceptance.lean)
connect these inputs to the proved machine targets under exact lookup matching.
The theorem quantifies over public programs; retained programs are test fixtures.

Clean supplies logical membership. Parsing/emission fidelity, general Rust setup
refinement and cryptographic query/table authentication remain separate boundaries.
See [trust and provenance](../../../../TRUST_AND_REVIEW.md#modeled-tables-and-logical-arguments).
