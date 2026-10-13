# Shared modeled tables

This directory models shared lookup rows for limb ranges, bytes, subword memory
and common query encodings, using Clean's table semantics. The definitions state
which logical queries are members and how returned values are interpreted. Their
correspondence with the Rust setup generator and cryptographic lookup enforcement
are separate obligations.

## Checked connections

The [lookup lemmas](../../../Proofs/Lookups.lean) extract modeled pair/range-sign/
low-byte behavior from membership; [byte-table lemmas](../../../Proofs/ByteTables.lean)
characterize tagged binary rows and their lookup results under stated field bounds.
Consuming circuit proofs use these results to recover ranges and operation effects.
The proofs concern these modeled rows; they do not prove Rust setup correspondence.

[Range](Range.lean) defines limb-range rows; [Bytes](Bytes.lean) defines shared
byte constructions; [Subword](Subword.lean) defines subword/ROM rows;
[Lookups](Lookups.lean) supplies shared lookup encodings.

Review the row contents, query layout, field interpretation and disabled-query
behavior used by the consuming claim. Circuit-specific controllers and setup
belong in that circuit's Tables directory.

Clean supplies the lookup semantics. These are human-reviewed models of Rust setup,
not an extracted fixed-table artifact or proved generator correspondence.
Membership and cryptographic enforcement are separate boundaries.
See [trust and provenance](../../../../TRUST_AND_REVIEW.md#modeled-tables-and-logical-arguments).
