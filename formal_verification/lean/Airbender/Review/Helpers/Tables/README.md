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

[Native paired byte ranges](SmallRange.lean) retain exact three-column queries
and odd-column zero padding for unsigned mul/div. [Exported literal rows](NativeSmallRangeData.lean)
include ID eight; [symbolic certificates](../../../Proofs/MulDiv/SmallRange.lean)
check all 65,536 actual pairs and identify exact Clean membership. Both byte
bounds follow from membership; nonzero third padding and wrong tags fail.
General physical setup/argument/compiler refinement remains separate.

## Actual native zero and binary prefix

[The mathematical three-column model](Binary.lean), [literal native data](NativeBinaryData.lean) and [tagged row observations](NativeBinaryRows.lean) feed [two short public membership/result claims](NativeBinary.lean). [Internal geometry](../../../Proofs/Tables/BinaryColumns.lean) checks actual keys/tags/extents structurally; [assembly](../../../Proofs/Tables/Binary.lean) uses complete source-shaped XOR/OR/AND output certificates. [Regressions](../../../../Tests/NativeBinary.lean) cover all rows, native zero/offsets, terminal keys and malformed queries. Dynamic selectors, large shifts, CSR/oracle behavior and family execution remain separate.

## Native shift scalar and sign-fill tables

[The short helper claims](./NativeShiftScalars.lean) now connect actual native truncation, zero-padded range and every sign-fill row to original Clean membership and exact results, including negative shift zero. [Internal assembly](../../../Proofs/Tables/ShiftScalars.lean) uses structural constant-block geometry across 64 symbolic domains and independent RV32 mask arithmetic. [Regressions](../../../../Tests/NativeShiftScalars.lean) check boundary cases and malformed queries. Native compiled offsets retain unexported regions. The four large logical-shift tables, dynamic constraint import and initialized family execution remain unfinished.

## Native low-input SRL rows

[Two short helper claims](./NativeSrlLow.lean) identify actual native SRL-low membership with original Clean semantics and derive bounds, zero high output and exact RV32 logical shift for all 2,097,152 rows. [Internal assembly](../../../Proofs/Tables/SrlLow.lean) reuses the source block checker with six symbolic actual-block certificates and independent bitvector arithmetic. [Regressions](../../../../Tests/NativeSrlLow.lean) cover shift/final-bit boundaries and malformed queries. The other three logical-shift tables, dynamic constraint import and initialized family execution remain unfinished.

## Native high-input SLL rows

[Two short helper claims](./NativeSllHigh.lean) connect original Clean membership to all 2,097,152 actual high-input SLL rows and derive bounds, zero low output and exact wrapped RV32 shift. [Internal assembly](../../../Proofs/Tables/SllHigh.lean) uses six symbolic actual-block partitions, ten checked stored templates and independent bitvector arithmetic. Generic size/output proofs avoid imported-data normalization under unchanged ceilings. [Regressions](../../../../Tests/NativeSllHigh.lean) cover discarded/final bits, shift boundaries and malformed queries. Low-input SLL, high-input SRL, dynamic constraint import and initialized family execution remain unfinished.

## Native low-input SLL rows

[Two short helper claims](./NativeSllLow.lean) connect original Clean membership to all 2,097,152 actual low-input SLL rows and derive both limb bounds and exact reconstructed RV32 shifts. [Internal assembly](../../../Proofs/Tables/SllLow.lean) reuses the complete native SLL-high low column and a checked 73-block high suffix, with six symbolic native carry partitions. [Regressions](../../../../Tests/NativeSllLow.lean) cover first carry, shifts sixteen/31, surviving/discarded bits and malformed queries. High-input SRL, dynamic constraint import and initialized family execution remain unfinished.

## Native high-input SRL rows

[Two short helper claims](./NativeSrlHigh.lean) connect original Clean membership to all 2,097,152 actual high-input SRL rows and derive both limb bounds and exact reconstructed RV32 shifts. [Internal assembly](../../../Proofs/Tables/SrlHigh.lean) reuses native SRL-low for the entire high column and a 73-block low suffix, retaining all 146 low blocks, ten rotated templates and five symbolic prefix certificates. [Regressions](../../../../Tests/NativeSrlHigh.lean) cover cross-shift/reset edges, shifts sixteen/31, final bits and malformed queries. All four native logical-shift limb tables now have helper membership/results; dynamic constraint import and initialized shift/binop execution remain unfinished.

## Tagged shift/binop composition

[The complete native tagged table](../../Circuits/ShiftBinop/Tables/Native.lean)
retains all twelve compiled regions and four-field queries. [Structural transport](../../../Proofs/ShiftBinop/NativeLookup.lean)
includes every stored helper row at its actual offset. Existing helper result
certificates are unchanged. The additional CSR data is the exact compilation
fixture, with runtime setup binding/custom execution explicitly separate.
Numerical shift/binop composition and initialized execution remain open.

## Native subword offset/trap table

[The public helper](SubwordOffsetTheorems.lean) and [source-shaped model](SubwordOffset.lean)
retain every 21-bit native key and the complete offset/width/limb/trap result.
[The literal-data certificate](../../../Proofs/SubwordMemory/Offset.lean) checks all
2,097,152 actual exported rows symbolically, with tag 44 and compiled offset 65,537.
[Regressions](../../../../Tests/SubwordOffset.lean) retain native misalignment,
x0-load waiver, invalid encoding and store behavior, and reject changed queries.
This table is a foundation for full subword constraint/decoder/history/execution
work; its isolated keys do not establish accepted circuit behavior or a defect.

## Native subword load-data table

[The public helper](SubwordLoadTheorems.lean) derives the exact signed/unsigned
byte/halfword outputs and canonical bounds from original Clean membership.
[The source-shaped model](SubwordLoad.lean) retains every native key, including
unused and odd-halfword zero outputs. [The literal certificate](../../../Proofs/SubwordMemory/Load.lean)
checks all 2,097,152 actual tagged rows at native ID 45 and compiled offset
2,162,689. Small template certificates run in separate bounded workers; symbolic
block assembly covers the complete table. [Regressions](../../../../Tests/SubwordLoad.lean)
exercise signs, all offsets, unsigned outputs and changed-query rejection.
The preselected limb is part of the table key. Full native constraints, limb
selection, initialized memory, decoder and original instruction execution remain
separate; table keys alone do not establish circuit acceptance or a defect.

## Native subword original-RAM clearing

[The public helper](SubwordStoreClearTheorems.lean) derives exact native clearing,
the unused zero output and canonical bounds. [The model](SubwordStoreClear.lean)
retains all 21-bit keys and all four offsets. [Internal assembly](../../../Proofs/SubwordMemory/StoreClear.lean)
checks all 2,097,152 literal native rows at ID 54 and compiled offset 5,308,417,
with symbolic block selection and the pinned periodic upper-byte proof.
[Regressions](../../../../Tests/SubwordStoreClear.lean) cover both byte masks,
all offsets, SH/SW/unused keys and changed-query rejection. Written-value
placement, actual limb selection, full accepted stores, initialized history and
original Sail execution remain separate. This certificate adds no defect finding.

## Native subword written-value placement

[The public helper](SubwordStorePlaceTheorems.lean) derives exact native SB/SH
placement, unused zero and canonical bounds. [The model](SubwordStorePlace.lean)
retains all 21-bit keys and offsets. [Internal assembly](../../../Proofs/SubwordMemory/StorePlace.lean)
checks all 2,097,152 literal rows at ID 55 and compiled offset 7,405,569 with
symbolic block selection and structural literal-array reads. The affine literal
emitter checks every actual parsed element before compact representation;
general emission fidelity remains an Import boundary.
[Regressions](../../../../Tests/SubwordStorePlace.lean) cover byte placement,
source high-byte removal, raw odd SH keys, SW/unused zeros and altered outputs.
Full native preselection, accepted store constraints, history and original Sail
execution remain separate; the isolated keys add no defect finding.

## Subword native lookup connection

[AlignedWordROM](AlignedWordROM.lean) shares WordROM values and UNIMP padding
with the actual v2 word-index key and native tag 46. [Symbolic proofs](../../../Proofs/Tables/AlignedWordROM.lean)
derive both limbs and canonical index and connect the byte-addressed row model.
[The circuit guide](../../Circuits/SubwordMemory/README.md) describes all seven
regions and accepted query extraction. Native export/compiler refinement,
subword routing and initialized original instruction execution remain separate.

## Subword accepted-tag resolution

[The native subword connections](../../Circuits/SubwordMemory/Lookups.lean)
now resolve each actual tag to these certified helpers, the separator or aligned
public ROM. The native zero region requires the exact all-zero tuple. Canonical
per-slot selector bounds follow from original Clean acceptance; table equivalence
is proved internally, not supplied as a premise. Operation-specific tag choices,
limb selection, native instruction effects and initialized execution remain open.
