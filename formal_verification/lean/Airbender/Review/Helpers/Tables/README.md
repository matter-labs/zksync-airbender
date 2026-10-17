# Table review

[Range](Range.lean) uses native Clean static tables for 16-bit scalar and 19-bit
timestamp queries. Concrete enumeration proves their range semantics. Binding
these rows to actual v2 setup generation remains pending; imported query
expressions alone do not prove the cryptographic lookup argument.

[Word ROM](WordROM.lean) models the pinned native four-MiB separator/read tables:
all 65536 high-limb classifications and all 1048576 aligned word rows. Missing
words use native UNIMP padding. Membership derives alignment, classification and
exact public ROM data in [the table proofs](../../../Proofs/WordMemory/Tables.lean).
The native word-memory queries are unconditional, including RAM shadow lookups.
Public Sail-byte binding, physical Rust table export and cryptographic enforcement
remain separate. No table-equivalence or expected-read premise is used.
