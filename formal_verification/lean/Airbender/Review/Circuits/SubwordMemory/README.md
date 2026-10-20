# Native subword memory review

[The artifact](Artifact.lean) imports all 51 equations and fourteen queries from
the pinned native v2 layout: two scalar, eight timestamp, two constant fixed and
two dynamic fixed queries. [Internal checks](../../../Proofs/SubwordMemory/ArtifactChecks.lean)
retain actual state/decoder columns, three memory ports and clocks, and complete
setup placement. The explicit profile validates both witness selector columns,
every native table offset and the 9,502,721-row tagged extent.

[The short public claim](Lookups.lean) derives both actual three-field dynamic
queries and their evaluated fourth selector field from original Clean acceptance.
[Query assembly](../../../Proofs/SubwordMemory/NativeQueries.lean) stays under
Proofs; no expected result, routing or table-equivalence premise is supplied.

[The complete tagged table](Tables/Native.lean) retains zero (0), separator (23),
offset/trap (44), load-data (45), aligned word ROM (46), store-clear (54) and
store-place (55), in compiled offset order. [Structural inclusions](../../../Proofs/SubwordMemory/NativeLookup.lean)
cover every row in each region. Previously certified specialized fixed tables
retain their existing literal native data and scope.

V2 uses an aligned word ROM lookup followed by the existing load-data table;
there are no separate byte/halfword ROM regions here. [AlignedWordROM](../../Helpers/Tables/AlignedWordROM.lean)
shares the full public four-MiB image and native UNIMP tail, keyed by word index.
Ordinary RomRead instead has byte-address keys and native tag 24.
[Symbolic proofs](../../../Proofs/Tables/AlignedWordROM.lean) derive canonical
index and limbs and preserve word values between these two row models. General
Rust/JSON/compiler/setup correspondence and verifier enforcement remain separate.

[Kernel regressions](../../../../Tests/SubwordArtifact.lean) check counts,
evaluated selectors, placements, distinct ROM key units, UNIMP tail and changed
key/output rejection. Importer tests reject crossed profiles, altered selectors/
mappings/offsets, malformed widths, truncated extents and decoder setup overlap.

Next: accepted tag resolution, operation routing, actual limb preselection,
numerical load/store effects, public/native decoding, initialized history and
original Sail execution. This checkpoint adds no native defect or subword
execution/whole-machine theorem.

## Accepted tag resolution

[The public claims](Lookups.lean) now derive canonical selectors for both slots
and expose exact membership for all seven native tags. [Internal partition](../../../Proofs/SubwordMemory/NativeRegions.lean)
retains every region and proves tag uniqueness from actual literal columns and
public separator/ROM rows. Its symbolic affine getter is copied unchanged from
the checked v2 shift proof. [Resolution](../../../Proofs/SubwordMemory/NativeResolution.lean)
reuses complete fixed-table certificates; tag zero requires three zero fields.
The equivalences are proved, with no supplied table-equivalence or expected-result
premise. Original accepted-query extraction is unchanged.

[Thirty regressions](../../../../Tests/SubwordLookups.lean) cover all regions,
native value boundaries, malformed outputs/tags/unused fields, crossed store
regions, word-indexed ROM/UNIMP tail and canonical field tag wrap. Odd/raw x0
keys remain isolated table cases. These checks add no native defect finding.

Native equations must still derive operation-specific tags and limb preselection
before numerical subword effects and initialized original Sail execution.

## Accepted operation routing

[Four public claims](Routing.lean) now derive the exhaustive native modes and
connect actual ROM-load, RAM-load and store queries to certified helper membership.
[Observables](RoutingModel.lean) retain native limb selectors, offset/funct3 keys
and the v2 word ROM key. [Controls](../../../Proofs/SubwordMemory/Controls.lean)
derive Booleanity, separator bits, forbidden ROM stores, tags, mixed addresses
and all three limb muxes. [Field calculations](../../../Proofs/SubwordMemory/QueryFields.lean)
and [assembly](../../../Proofs/SubwordMemory/Routing.lean) remain internal.

No tag, intermediate read/result, expected query or table equivalence is assumed.
A RAM load disables its second slot with the actual zero tuple; a store clears
old RAM data and places the source low limb. [Six complete accepted rows](../../../../Tests/SubwordRouting.lean)
check every native equation and lookup, nonzero ROM word indexing, upper/lower
loads, signed data, x0 and stores. Eight native-equation mutations are rejected.

General numerical effects, native/public decoding, initialized memory/history,
original Sail execution and composition remain unfinished. These local accepted
rows add no initialized execution coverage and no confirmed native defect.

## Accepted values and actual writes

[Five public claims](Values.lean) now derive exact offset/mask values, absence
of the native trap bit and upper-limb selection; they connect certified load
values and candidate bounds to actual masked register writes, and clearing/
placement values to actual store writes. [Observables](ValuesModel.lean) keep
raw native keys and original x0 scaling. [Offset reductions](../../../Proofs/SubwordMemory/OffsetValues.lean),
[write equations](../../../Proofs/SubwordMemory/WriteValues.lean) and
[value assembly](../../../Proofs/SubwordMemory/Values.lean) remain internal.
The exact original x0 exception and all native table rows remain present.

[Tests](../../../../Tests/SubwordValues.lean) apply the results to the unchanged
six complete rows and reject nine mutations of candidates, actual writes,
offsets/selectors and a trap-bearing key. No desired result, read bound or
unchecked decoder interpretation is assumed. Decoded byte/halfword key
normalization, initialized source/old-RAM and whole-write bounds, original Sail
execution and composition remain unfinished. No confirmed defect is added.
