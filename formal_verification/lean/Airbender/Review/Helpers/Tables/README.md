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
[Public ROM extraction](WordROMImage.lean) now reads actual original Sail bytes
into a bounded word vector and retains the complete native UNIMP tail. The
[read bridge](../../../Proofs/WordMemory/ROMImage.lean) recovers native ROM query
data as actual Sail reads inside the extracted prefix. Extracting all 1048576
words covers the entire ROM region. Missing padding bytes are not filled by the
constructor; boot/padding/shadow state, physical export and cryptographic
connections remain separate. No expected-read or table-equivalence premise is used.
