# Table review

[Range](Range.lean) uses native Clean static tables for 16-bit scalar and 19-bit
timestamp queries. Concrete enumeration proves their range semantics; actual native prefixes and
source-shaped full-row placement are certified below. Rust trace/LDE refinement
and cryptographic lookup enforcement remain separate.

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
argument correspondence remain separate; shared scalar data is checked below.

[Literal native v2 data](../../Circuits/WordMemory/Tables/NativeSetupData.lean) now
has [symbolic certificates](../../../Proofs/WordMemory/NativeSetup.lean) against the
existing complete ROM/separator/range models. The [lossless importer](../../../Import/Setup.lean)
keeps parsing/emission separate from kernel checks. Only the pinned fixture has
this actual exported-data connection; full trace assembly/LDE remains open.

[Actual shared scalar data](NativeScalarData.lean) imports complete native
range16/timestamp19 prefixes and models the native active zero filler. The
[short scalar claim](NativeScalars.lean) exposes exact bounds; [calculations](../../../Proofs/Tables/NativeScalars.lean)
certify every prefix/filler row and connect to unchanged original Clean helpers.
Both compiled column placements are checked. Zero filler remains valid range
data, and the reserved normalization row is excluded. No large trace is evaluated
or table-equivalence premise supplied. Rust physical trace/LDE/multiplicity and
argument enforcement remain separate.

[Active decoder rows](NativeDecoderData.lean) now retain three actual native
prefixes plus the direct native padding API output through all active setup rows.
[The short membership claim](NativeDecoder.lean) uses symbolic literal-data
certificates: minus-one filler is already in each prefix and adds no query.
The reserved normalization row is excluded. Native arithmetic/word-memory column
placements, supported rows and first/last active filler are checked; full Rust
trace/normalization/LDE refinement and physical argument enforcement remain open.
Physical lookup multiplicities remain a separate boundary.

[Complete active rows](NativeRowsData.lean) now combine all native groups at the
12/16-column compiled layouts. [Three short membership claims](NativeRows.lean)
expose scalar, decoder and tagged queries; [projections](../../../Proofs/Tables/NativeRows.lean)
recover existing Clean scalar/fixed meanings. Queries must fit in full; arithmetic
has no generic group. Decoder filler overlaps the still-active ROM region, and
final active rows retain distinct zero/minus-one fillers. [Regressions](../../../../Tests/NativeRows.lean)
check these boundaries and reject scalar overflow, truncated windows and wrong
tags. Rust construction/normalization/LDE and argument enforcement remain separate.

[Native control tables](Control.lean) now expose exact tagged membership for the
65,536 cleanup and 128 conditional rows. [Definitions](../../Circuits/JumpBranchSlt/Tables/Control.lean)
retain separate flags/funct3 keys and bit-one/cleaned-low outputs; [certificates](../../../Proofs/JumpBranchSlt/ControlTables.lean)
check every actual native value without enumerating the large cleanup domain.
Native tags 17/43 and offsets 0/65536 retain a profile without a dummy row.
[Full-row native effects](../../Circuits/JumpBranchSlt/Theorems.lean) consume actual
queries, while public decoding/initialized original Sail execution and terminal
PC assessment remain separate. Physical control setup padding and argument
refinement are not claimed by these regional certificates.
