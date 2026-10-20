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
