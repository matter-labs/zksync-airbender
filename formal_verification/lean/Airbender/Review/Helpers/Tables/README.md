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

Program-dependent compatibility views retain arbitrary public programs.
[Imported word ROM](../../Circuits/WordMemory/ImportedROM.lean),
[imported subword setup](../../Circuits/SubwordMemory/ImportedSetup.lean) and
[unified execution](../../Trace/ImportedDecoder.lean) connect the complete selected
setup to those views under explicit public byte binding. The retained program
is a specialization, rather than a restriction on the earlier generalized claims.

Clean supplies logical membership. Parsing/emission fidelity, general Rust setup
refinement and cryptographic query/table authentication remain separate boundaries.
See [trust and provenance](../../../../TRUST_AND_REVIEW.md#modeled-tables-and-logical-arguments).
