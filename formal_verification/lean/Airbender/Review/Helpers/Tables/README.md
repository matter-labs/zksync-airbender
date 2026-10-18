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
constructor. [Initialized projected histories](../../Trace/Families/WordMemory/CodeHistory.lean)
now preserve every actual byte entry below four MiB and every successful
extraction through changing RAM stores. Boot/padding/shadow state, physical export
and cryptographic connections remain separate. No expected-read or table-equivalence premise is used.

[Proving-loader padding](WordROMPadding.lean) separately retains the input words
and zero-extends them to the full native region. V2's raw table constructor uses
UNIMP only past the image it receives; passing a full padded image leaves no
in-region fallback. [Symbolic proofs](../../../Proofs/WordMemory/ROMPadding.lean)
check length, unchanged prefix and zero tail without evaluating the million-entry
list. This list model constructs no Sail bytes and proves no Rust refinement;
[regressions](../../../../Tests/WordMemoryNativeBoot.lean) preserve actual failure
on absent Sail padding.

[The explicit loader](PaddedROMImage.lean) now combines successful original prefix
extraction with actual Sail zero-byte inserts. [Symbolic extraction proofs](../../../Proofs/WordMemory/ROMBytePadding.lean)
derive a complete four-MiB ROM from those actual reads, without evaluating the
huge map/list or assuming table equivalence. [Padded boot execution](../../Trace/Families/WordMemory/NativeBoot.lean)
preserves original public decoding/configuration/profile and derives all ROM
coverage; missing or oversized prefixes fail. General Rust/export/argument
fidelity remains separate.

[Physical setup placement](SetupColumns.lean) records the guarded native 12/16
columns, scalar/decoder groups, four-column generic tuples and row capacities.
[The active tagged-row model](PhysicalSetup.lean) keeps the dummy row, native
separator/ROM tags 23/24 and all zero padding, excluding the final normalization
row. [Exact membership/read proofs](../../../Proofs/WordMemory/PhysicalSetup.lean)
recover both existing logical tables and actual padded Sail words without a
large evaluated trace or assumed table equivalence. [The public read claim](../../Trace/Families/WordMemory/Setup.lean)
exposes loader construction and tagged membership. Actual Rust/export/LDE and
argument correspondence remain separate; scalar-row binding is not claimed.

[Literal native v2 data](../../Circuits/WordMemory/Tables/NativeSetupData.lean) now
has [symbolic certificates](../../../Proofs/WordMemory/NativeSetup.lean) against the
existing complete ROM/separator/range models. The [lossless importer](../../../Import/Setup.lean)
keeps parsing/emission separate from kernel checks. Only the pinned fixture has
this actual exported-data connection; full trace assembly/LDE remains open.
