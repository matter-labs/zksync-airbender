# Shared modeled tables

Shared 13-/16-/19-bit range rows now come from [native setup JSON](../../../../artifacts/setup/README.md),
with kernel-checked membership bounds. The other table definitions are still
being migrated from their reviewed models. The definitions state
which logical queries are members and how returned values are interpreted. Their
correspondence with the Rust setup generator and cryptographic lookup enforcement
are separate obligations.

## Checked connections

The [lookup lemmas](../../../Proofs/Lookups.lean) extract modeled pair/range-sign/
low-byte behavior from membership; [byte-table lemmas](../../../Proofs/ByteTables.lean)
characterize tagged binary rows and their lookup results under stated field bounds.
Consuming circuit proofs use these results to recover ranges and operation effects.
Range proofs concern the actual imported rows; byte/subword proofs still concern
their modeled rows. General Rust refinement and cryptographic enforcement remain separate.

[Range](Range.lean) defines limb-range rows; [Bytes](Bytes.lean) defines shared
byte constructions; [Subword](Subword.lean) defines subword/ROM rows;
[Lookups](Lookups.lean) supplies shared lookup encodings.

Review the row contents, query layout, field interpretation and disabled-query
behavior used by the consuming claim. Circuit-specific controllers and setup
belong in that circuit's Tables directory.

Clean supplies the lookup semantics. The imported ranges and remaining table models
have distinct provenance; the native table migration is in progress.
Membership and cryptographic enforcement are separate boundaries.
See [trust and provenance](../../../../TRUST_AND_REVIEW.md#modeled-tables-and-logical-arguments).
