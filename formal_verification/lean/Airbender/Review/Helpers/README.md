# Shared helper review

[Properties](Properties.lean) defines soundness, completeness and the observable
circuit model independently of any decoder/history claim. [Core](Core/README.md)
contains reused word and original Sail definitions; [tables](Tables/README.md)
states the current range-table boundary. [Context](Context/README.md) exposes
clock contracts and native logical matching; [decoder](Decoder/README.md) exposes
the native ten-column query; [memory](Memory/README.md) exposes
port interpretation and initialized history. Their definitions remain independent
of public whole-execution claims.

[Native mul/div arithmetic](../Circuits/MulDiv/README.md) reuses the unchanged
shared [integer byte-column theorem](../../Proofs/Arithmetic/Multiplication.lean).
Its v2 circuit connection derives all byte, carry and output bounds from actual
queries/assertions; the existing word and logical-history definitions are
unchanged. Original Sail execution is still a separate connection for this family.

## Unsigned MUL/DIV helpers

[Stateful public setup](Decoder/StatefulSetup.lean) retains actual extension-configuration reads. [The native context](Context/MulDiv.lean) and [full decoder membership](Decoder/MulDiv.lean) feed the [initialized trace claims](../Trace/Families/MulDiv/README.md).

## Subword native context

[The separate registry](Context/SubwordMemory.lean) selects actual native
subword state, decoder, mixed memory ports and ROM-dependent constraints.
[Native clock laws](../../Proofs/Trace/Families/SubwordMemory/History.lean)
discharge the unchanged shared contract; [public history](../Trace/Families/SubwordMemory/History.lean)
derives current/prior clock inputs and complete original Clean consistency from
actual Sail seeds and native matching. No shared semantic definitions or original
Sail clauses change. Canonical values/key binding and instruction execution remain
separate subword obligations.

## Subword initialized value preservation

[Full native decoder membership](Decoder/SubwordMemory.lean) now feeds the
[initialized payload-bound claim](../Trace/Families/SubwordMemory/Values.lean).
The unchanged shared value induction uses native local preservation from both
source and old-destination/RAM reads. Exact raw-key components and disjoint byte
contributions derive whole store-write bounds; actual original decoding derives
funct3/x0 ranges. [Same-state regressions](../../../Tests/SubwordWordBounds.lean)
retain actual public code/seed bytes. Shared Clean/Sail definitions, tables and
logical history semantics are unchanged; original instruction execution remains
separate.

## Subword native address geometry

[Original subword decoder membership](Decoder/SubwordMemory.lean) and the
unchanged initialized value induction now supply source/immediate/raw/x0 ranges
for [native address geometry](../Trace/Families/SubwordMemory/Address.lean).
The exact native offset relation and carry equations derive the containing
aligned word and actual mixed-port addresses. No helper table identity or
per-row expected address/read is supplied. Shared Clean/Sail semantics and
all original native fixed tables remain unchanged.
