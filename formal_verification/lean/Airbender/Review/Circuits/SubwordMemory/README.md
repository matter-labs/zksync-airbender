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

## Original public decoding

[Two public claims](Decoding.lean) derive actual native fields and decoded
load writes/bounds from the constructed original public image, complete logical
setup membership and native acceptance. [The interface](Decoder.lean) retains
all six original subword forms, signed immediates and x0. Native store Booleanity
excludes the entire unsupported/sentinel domain; no Boolean x0 or expected data
premise is added. [Recovery calculations](../../../Proofs/SubwordMemory/Decoder.lean)
remain internal. A source pin is separate from native exported decoder fidelity,
which is still open. Packed-key normalization, initialized reads/whole-store
bounds and original Sail execution remain next dependencies.

[Seven complete native fixtures](../../../../Tests/SubwordDecoderFixture.lean)
cover all six forms, actual public bytes, distinct unsigned-byte data and x0.
[Tests](../../../../Tests/SubwordDecoder.lean) apply both claims and reject five
wrong decoder memberships. Old local fixtures remain unchanged and accepted
locally; their incompatible unused-index/zero-flag metadata is rejected by
public decoding. Symbolic sparse-head membership avoids concrete-tail expansion
and preserves every proof/resource ceiling. No confirmed defect is added.

## Specific native decoder export fidelity

[Independent original public data](NativeData.lean) now has an actual native
[export](../../../../artifacts/setup/subword-decoder-native.json). [The short
fidelity claim](../../Trace/Families/SubwordMemory/NativeDecoder.lean) proves all
1,048,576 rows equal public original Sail setup: six forms, negative immediate
variants, original x0 loads, unused-index clearing, unsupported LW and full tail.
[Pure decoding](../../../Proofs/SubwordMemory/NativeDecode.lean) and
[byte/row proofs](../../../Proofs/SubwordMemory/NativeSetup.lean) remain internal,
with unchanged proof/resource limits. [Regressions](../../../../Tests/SubwordNativeDecoder.lean)
retain negative I/S metadata and complete row/text coverage. This is specific
export fidelity; initialized history/key binding and original execution remain
unfinished. General compiler and physical verifier bindings remain separate.

## Initialized native memory history

[The short history claim](../../Trace/Families/SubwordMemory/History.lean) now
derives complete original Clean history and newest reads from actual public Sail
seed reads/PC and native logical matching. The [native clock proof](../../../Proofs/SubwordMemory/Timestamp.lean)
checks all eight timestamp queries, three borrows and both carry equations.
[Eight initialized fixtures](../../../../Tests/SubwordHistoryFixture.lean)
retain ROM shadows, RAM, x0, actual SB/SH writes and a unique-seed rs1=rd alias.
Stale alias clocks pass local constraints and fail native matching; full clock
carry and malformed clock rejection pass under unchanged resource ceilings.
This is logical cell history. Source/old-RAM bounds, whole store-write bounds,
packed-key binding, instruction/data-ROM projection and original subword
execution remain separate; the earlier table/decoder claims are unchanged.

## Initialized native payload ranges

[The short value claim](../../Trace/Families/SubwordMemory/Values.lean) derives
every native read, write and terminal word bound from actual Sail seed reads,
native matching and full public original decoding in the same state.
[Packed fields](../../../Proofs/SubwordMemory/PackedKeys.lean) and
[disjoint store contributions](../../../Proofs/SubwordMemory/StoreBounds.lean)
preserve the native selected/other old limbs and actual SB/SH writes. Raw funct3,
x0 masking and offset/size/upper controls are derived; no bounded result or
packed-key equivalence is supplied. [Eight regressions](../../../../Tests/SubwordWordBounds.lean)
join original code bytes to initialization, including overlapping shadow bytes,
x0 and a source/destination alias. Boundary checks cover maximum keys/merges and
the raw-field range dependency. Effective addresses, width/sign/offset and
architectural ROM projection still need connection to original Sail execution.
