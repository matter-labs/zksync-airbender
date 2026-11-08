# V3 adaptation snapshot — 6 November 2026

## Natural native initialization sorting and global uniqueness (8 November 2026)

[Actual initialization addresses](Airbender/Review/Circuits/ReducedMachine/InitializationSorted.lean)
use canonical low/high field representatives as an unsigned radix32 Nat word.
[The calculations](Airbender/Proofs/ReducedMachine/NativeInitializationSorted.lean)
reuse the unchanged two-limb borrow theorem. The SAME complete source and full
actual-family logical lookup boundary derive both current/next address ranges;
the original complete BODY derives remainder ranges and Boolean borrows.
The actual adjacent polynomials then derive high-borrow1 exactly when the current
address is strictly smaller. No desired comparison bit or order is supplied.
No whole-word cast into M31 is used, including for addresses above its modulus.

The six native padding polynomials force all six current record fields to zero
when high-borrow is zero. Thus EVERY adjacent ordinary pair is weakly increasing,
and every nonpadding current record is strictly smaller than its successor.
An abstract finite-sequence induction derives weak order across the complete
8,388,607-row ordinary domain and strict order from any nonpadding record to ANY
later ordinary record. Global uniqueness of nonpadding actual token addresses
follows through the existing lossless address binding. Duplicate padding records
and tokens remain. All 8,388,606 source comparisons are used; the last ordinary
record is included and the reserved normalized last row is excluded.

[Two short roots](Airbender/Review/Circuits/ReducedMachine/InitializationSortedTheorems.lean)
retain the SAME existing acceptance relation. Full-family logical lookup and
full-token logical matching remain explicit cryptographic extraction boundaries;
this milestone introduces neither a new desired-result premise nor physical
proof extraction. Public first/one-before-last/chunk-window/image and seed rules,
combined chronological memory history, initialized worker reads/raw clocks,
active stage2 key refinement and caller-worker accounting remain open. Original
execution is unchanged and still excludes CSR/MOP; no Sail frame crosses an
unproved delegated action.

[Eleven controls](Tests/NativeInitializationSorted.lean) check low borrow,
radix carry, full RV32 words above M31, descending/wrap source slices rejected
by padding, the unchanged complete CSR BODY with its zero record, repeated
zero padding, nonadjacent finite growth, exact domains and conditional roots.
Source slices and finite references are NOT full positive nonempty main-aux,
global, worker or physical witnesses, attacks or native-defect evidence.
Four modules add 21 explicit roots with eight exact parent origins; all 5,539
prior ordered roots and source bytes remain. Native101 pins, dependencies,
artifacts, fixtures, production code, Sail and findings are unchanged. No native
generation or closed heavy replay. General refinement, cryptographic extraction,
completeness and checked parity remain separate and open.

Next: inspect and pin actual public first/one-before-last and chunk-window
sources before adapting their rules, then connect the sorted initialization
records to public seeds and combined memory history. Sorting alone supplies
neither public image coverage nor initialized worker semantics.


## Constructed native scalar setup and logical address bounds (8 November 2026)

[The constructed setup](Airbender/Review/Circuits/ReducedMachine/PhysicalScalar16Setup.lean)
copies the existing certified scalar16 literal prefix into the native reduced
2^23 domain, retaining every ordinary zero-tail row and excluding the reserved
last row from lookup membership. [The calculations](Airbender/Proofs/ReducedMachine/NativePhysicalScalar16Setup.lean)
reuse only the unchanged exported-prefix certificate. They derive the ordinary
field sum 2,147,450,880 and its Mersenne31 negative 32,767 symbolically, then prove
the closed normalization reference equals native negative-column-sum normalization
on every row. No million-row evaluation or table-equivalence premise is used.

The construction changes only physical setup0 on the SAME scalar16 proof.
All body, base/quartic, multiplicity, polynomial and other setup observations are
retained. Every constructed ordinary setup value is bound to its actual lookup
row. Existing complete normalized source acceptance is checked ON this constructed
setup; no arbitrary observed setup is identified with it by an equality premise.

[The logical lookup boundary](Airbender/Review/Circuits/ReducedMachine/Scalar16Lookups.lean)
checks ALL TEN actual queries of the four original pairs and the extra raw
initialization-address pair on ALL 8,388,607 ordinary rows. It supplies no expected
answer, address bound, read, clock, stream or execution flag. This is an explicit
Clean-style logical acceptance relation, following the pinned v3 trust boundary.
It is not extracted from fixed-challenge equations, auxiliary sums or a physical
proof. Setup commitment/authentication and cryptographic extraction stay open.

[The lookup calculations](Airbender/Proofs/ReducedMachine/NativeScalar16Lookups.lean)
derive all ten canonical 16-bit bounds from actual constructed table membership,
including BOTH initialization-address limbs and their 32-bit radix combination.
[Two short roots](Airbender/Review/Circuits/ReducedMachine/Scalar16LookupTheorems.lean)
retain the previous complete source/sum component on the SAME main proof and
expose these bounds under the named logical lookup boundary. This does not prove
natural sorting, public first/one-before-last/window/image rules, initialized
worker reads, combined memory history or caller-worker accounting.

[Eleven setup controls](Tests/NativePhysicalScalar16Setup.lean) and
[six lookup controls](Tests/NativeScalar16Lookups.lean) cover literal prefix/tail,
wide-value rejection, the derived last value and its source-normalization proof,
full symbolic column sum, unchanged observations and all ten actual query fields.
Existing complete CSR BODY plus logical lookups retains an inactive request at
that WEAKER interface; it is not complete new source/global/worker/physical
acceptance or a native defect. No full positive nonempty global witness is added.
Seven modules add 39 explicit roots, preserving all 5,500 prior roots/source bytes.
Fourteen exact parent origins, one manual source reference and one exact current-v3
logical-boundary reference are recorded. The unchanged native row-major zero
initializer was byte-compared and pinned BEFORE adaptation: 101 native pins,
with all previous 100 unchanged. Other native construction sources were rechecked.
No production/Sail/parser/exporter/artifact/dependency change or native generation/
closed heavy replay. General Rust/allocator/u64/field/FFT/LDE/quotient/JSON refinement
and completeness remain separate; findings and original execution are unchanged.

Next: natural sorted initialization, actual public first/one-before-last/chunk
window and image, then combined memory history, active worker bounds/key refinement
and real caller-worker accounting. Physical extraction, remaining decoder/request/
padding boundaries and checked parity remain open.


## Complete native scalar16 family consistency (7 November 2026)

[The scalar16 component](Airbender/Review/Circuits/ReducedMachine/Scalar16Arguments.lean)
retains the SAME complete native main, initialization-address and adjacent-ordering
proof. It checks the four original body pairs and the extra initialization pair
on every ordinary row. The actual body columns are 61/62, 69/70, 90/91 and 122/123;
their base auxiliaries are 0..3 and quartic auxiliaries are 12/16/20/24. The extra
pair keeps base4/quartic28. Physical multiplicity witness7, setup0 and quartic76
have separate types; witness7 is not body variable7.

[The strict intake](Airbender/Import/ReducedScalar16.lean) reuses the complete
unchanged body/all-stage2/init-pair parsing on the same 94,130 source bytes. It
binds all eight scalar query columns in native physical order and checks the
unmapped physical multiplicity and setup/auxiliary geometry. Existing parsers,
artifacts and native sources remain unchanged.

[The calculations](Airbender/Proofs/ReducedMachine/NativeScalar16Arguments.lean)
retain the exact table relation and all five terms of native sequential
subtraction. Actual difference-polynomial samples, degree, primitive domain and
zero/last divisibility derive equality of the ordinary table-auxiliary sum with
the sum of ALL five pair auxiliaries. The sum is not a premise. At the reserved
last row, table76 equals the sum of all five pair auxiliaries; none is assumed
individually zero. The reused generic zero-claim polynomial proof transfers no
decoder table semantics. [Two short roots](Airbender/Review/Circuits/ReducedMachine/Scalar16Theorems.lean)
expose these consequences on the same complete accepted component.

No multiplicity bit/count interpretation, zero-outside-capacity rule, expected
query/range/public seed, inverse or nonzero factor is supplied. Nonzero physical
multiplicity derives a nonpole; zero-multiplicity poles remain. Actual physical
setup observations have not been authenticated as the public scalar table.
Fixed-challenge equations and sums do not establish logical lookup extraction,
address bounds, initialized worker reads, chronological history or accounting.
Physical Rust/field/LDE/quotient/codec and cryptographic refinement remain separate.

[Fifteen theorem controls](Tests/NativeScalar16Arguments.lean) cover native
geometry, all five difference terms, source scaling, complete existing CSR BODY
plus original individual pairs, pure wide-multiplicity/pole/nonzero-last slices,
rejections and conditional sum/last roots. [Fifteen executable intake controls](Tests/NativeScalar16Import.lean)
retain strict query order, unrelated initialization validation and the changed
body-as-data distinction. They are not full positive nonempty auxiliary/global/
worker/physical proof witnesses or defects. Eight modules add 27 explicit audit
roots while preserving all 5,473 old roots and source bytes. Fourteen exact parent
origins and one manual source reference are recorded; all 100 native pins remain.
Findings and original execution are unchanged; no native generation or closed
heavy replay is needed.

Next: constructed native scalar16 setup and faithful logical lookup extraction,
then actual initialization-address bounds, public first/one-before-last/chunk
window and sorted initialization image, combined memory history, active worker
bounds/key refinement and real caller-worker accounting. General physical
refinement, cryptography, completeness and checked parity remain open.


## Native initialization-address pair oracles (7 November 2026)

[The extra address-pair component](Airbender/Review/Circuits/ReducedMachine/InitializationRange.lean)
retains the SAME complete native main proof and adjacent ordering component.
It adds the two actual source equations on every one of the 8,388,607 ordinary
rows, using raw initialization address columns 126/127. The separate base-field
auxiliary is column 4 and the quartic auxiliary is column 28; these are not body
variables 4/28. [The separate intake](Airbender/Import/ReducedInitializationRange.lean)
reuses unchanged complete body and all eighteen stage2-field validation on the
same 94,130 source bytes. No original parser or generated input changes.

[The calculations](Airbender/Proofs/ReducedMachine/NativeInitializationRange.lean)
preserve both product scalings and all rational-pair scalings before unit
normalization. They derive the actual base product and a division-free factored
pair equation. Distinct address limbs exclude poles; interpreting the pair as
a sum of inverses requires the stated nonpole conditions. At a duplicated pole,
this local relation permits an arbitrary pair accumulator. It must not be
replaced by two individually enforced inverse equations. No native defect or
accepted global witness follows from that local limit.

[Two short roots](Airbender/Review/Circuits/ReducedMachine/InitializationRangeTheorems.lean)
retain the pair equations and prior adjacent duplicate zero-padding exclusion
on the SAME proof. Address ranges, scalar16 table multiplicities/zero-last sum,
lookup extraction, public initialization image and chronological worker memory
history remain open. Debug range assertions are not an enforcement proof.
Source-reference normalization does not refine physical field/LDE/quotient/Rust
execution or establish cryptographic extraction.

[Twelve theorem controls](Tests/NativeInitializationRange.lean) include complete
existing CSR BODY plus the individual pair, an arbitrary local double pole,
base-versus-body separation, scaling and corruption controls, and a wide-address
PURE pair slice. [Twelve executable intake controls](Tests/NativeInitializationRangeImport.lean)
check strict geometry, unrelated group retention, historical rejection and
changed-body-as-data behavior. These are source/local/conditional controls, not
full positive nonempty auxiliary/global/worker/physical proof witnesses.
Eight modules add 24 explicit audit roots, preserving all 5,449 previous roots
and their source bytes. Twelve exact parent origins and one manual source
reference are recorded. The already pinned native function was byte-compared
against native67ee before adaptation; all 100 native source pins remain unchanged.
Findings, original execution, production code, artifacts and dependencies remain
unchanged. No native generation or unchanged heavy replay is needed.

Next: complete scalar16 table/sum and faithful lookup extraction, actual address
bounds, public first/one-before-last/chunk window and sorted initialization image,
combined memory history, active worker bounds/key refinement and caller-worker
accounting. Physical refinement, cryptography, completeness and checked parity
remain open.


## Native adjacent initialization ordering (7 November 2026)

[The ordering component](Airbender/Review/Circuits/ReducedMachine/InitializationOrdering.lean)
adds the actual low/high adjacent-row polynomials to the SAME existing complete
main acceptance. The comparison domain is8388606 positions: every physical row
except the last TWO. Actual address126/127, remainder122/123 and borrow124/125
metadata come from the unchanged strict native intake. Each linear polynomial
has one outer half-domain scaling and literal65536.

[The calculations](Airbender/Proofs/ReducedMachine/NativeInitializationOrdering.lean)
derive BOTH remainder16-bit bounds from actual full-body queries6/7 and borrow
Booleanity from equations25/26. No address bounds or expected comparison bit are
supplied. Repeated RAW field addresses force both borrows/remainders zero, so the
unchanged six padding polynomials force ALL address/teardown value/time fields
zero. [Short roots](Airbender/Review/Circuits/ReducedMachine/InitializationOrderingTheorems.lean)
retain this exclusion on actual losslessly encoded initialization token addresses.

This proves adjacent repeated-record exclusion, not global sorted uniqueness,
natural-number comparison, address range, public seed/image binding or initialized
worker reads. Init-address lookup extraction, first/one-before-last public
boundaries and chunk/window rules remain separate. Source-reference unit
normalization is not physical quotient/LDE/Rust-field/codec refinement.

[Nine controls](Tests/NativeInitializationOrdering.lean) cover native geometry,
scaling, complete existing CSR body controls/adjacent observations, sort-only
repeated17 accepted while the native padding slice rejects it, a wide-address
ordering SLICE with bounded remainders, the last-two boundary and conditional
actual-token exclusion. Slices are not complete accepted witnesses or defects.
No full positive NONEMPTY main/worker/global/physical verifier proof is added.
Four modules add17 audit roots, preserving all5432 old roots/source bytes.
Eleven exact parent origins plus one manual source-reference record are recorded.
The newly adopted4307-byte native ordering source was exact67ee byte-compared and
pinned BEFORE adaptation; native pins become100 with all previous99 unchanged.
No parser/exporter/artifact/fixture/production/Sail/dependency change, native
generation or unchanged heavy replay; findings and original execution stay unchanged.

Next: actual init-address lookup/range extraction, public boundaries/window/sorted
image, combined memory history and active old-read/value/address/worker-clock/key
bounds, decoder/request/padding enforcement and caller-worker accounting. General
physical/refinement/cryptography/completeness and checked parity remain open.


## Native full-domain main-state chronology (7 November 2026)

[The actual main-state view](Airbender/Review/Circuits/ReducedMachine/MainStateHistory.lean)
selects execute1 from ALL ordinary main observations across the proof list.
[Its calculations](Airbender/Proofs/ReducedMachine/NativeMainStateHistory.lean)
project the SAME full native logical ledger onto public initialPC0/time4,
public terminal PC/time and actual active main PC/time edges. Initialization and
worker memory tokens contribute no PC edges; they remain in memory matching.
No expected order, intermediate state, row clock or active-row count is supplied.

[The short theorem](Airbender/Review/Circuits/ReducedMachine/MainStateHistoryTheorems.lean)
reuses unchanged native clock laws and finite graph proofs to derive incoming,
outgoing and public terminal 19-bit clock ranges, alignment, four-tick increments,
public endpoint intervals, unique row clocks, terminaltime4+4*actualactivecount,
and a path containing exactly all active native state edges. The three actual
main write clocks have offsets0/1/2, bounded limbs and distinct global slots,
including readonly timestamp refreshes. No initialized old-read or worker-clock
bound is assumed or concluded. The private state-only proof view never asserts
an accepted memory trace using its empty placeholder fields.

Exact logical matching remains an explicit extraction boundary. These are native
PC/clock observations for all selected profiles, including CSR/MOP observations;
no original Sail CSR/MOP instruction semantics, worker memory effect, request
issuance/fulfillment or main frame across delegated actions is inferred.
[Twelve controls](Tests/NativeMainStateHistory.lean) cover actual CSR state fields,
inactive request retention, raw limbs, exact PC projections, a complete EMPTY
selected normalized component/history and wrong-terminal rejection. They are not
full positive NONEMPTY main/worker/physical verifier witnesses, attacks or defects.
Four modules add24 explicit audit roots while preserving all5408 old roots/source
bytes. Fourteen exact parent origins are recorded; all99 native pins, earlier
acceptance/proof/parser/exporter/artifact/fixture/source/dependency bytes and
findings remain unchanged. No native generation or unchanged heavy replay.

Next: public initialization and chronological COMBINED memory history, active
old-read/value/address/worker-clock bounds and stage2 key refinement, remaining
decoder/padding/request enforcement and actual caller-worker accounting. Original
CSR/MOP/worker execution, global init/teardown, physical/general refinement,
cryptography, completeness and checked parity remain open.


## Full-domain native token observations and logical filtering (7 November 2026)

[The native token ledger](Airbender/Review/Circuits/ReducedMachine/TokenLedger.lean)
constructs every ordinary main/worker contribution before compression: all32 public
registers including x0 timestamps, public PC, unmasked initialization/teardown,
three actual main ports and PC state, and all43 worker accesses. Native accepted
body Booleanity justifies the actual execute choice: inactive main port/state
contributions are the incoming tokens on BOTH sides. All8388607 ordinary main
rows and1048575 ordinary rows per selected worker proof remain represented.

[The calculations](Airbender/Proofs/ReducedMachine/NativeTokenLedger.lean) bind this
exact ledger to the unchanged full auxiliary/global product balance. Exact tagged
logical permutation is a separately named acceptance boundary, following pinned
v3 Clean's explicit state/RAM matching boundary. It is NOT inferred from a
single-challenge product, auxiliary sum, capacity bound or injective compression.
No expected read/value/range/clock or issued/fulfilled worker stream is supplied.

[Short public roots](Airbender/Review/Circuits/ReducedMachine/TokenLedgerTheorems.lean)
derive scalar product balance from native accepted components, and prove that
full logical matching is equivalent to matching after removing identical
incoming inactive port/state token MULTISETS. This preserves duplicates and uses
no division or nonzero-factor premise. Initialization/teardown and EVERY worker
access remain; no caller request is filtered. Memory and PC projections follow
from that same explicit logical relation. No initialized worker read, raw-clock
bound, chronological history, active stage2-key refinement or accounting follows
yet. Cryptographic extraction/physical codec/setup authentication remain separate.

[Twelve focused controls](Tests/NativeTokenLedger.lean) check actual domains,
port/public/worker token counts, active/inactive selection, unmasked init tokens,
retained inactive CSR request1, duplicate cancellation and retained zero compressed
factors. They are metadata/pure/reference/conditional controls; the CSR control
reuses complete BODY evidence only. They are not full positive nonempty global,
worker or physical proof witnesses, attacks, F02-F04 evidence or native defects.
Four modules add27 explicit roots, preserving all5381 old roots/source bytes.
Ten exact parent origins and one pinned-v3 boundary origin are recorded; all99
native pins and prior intake/exporter/artifact/fixture/source bytes remain unchanged.
No native generation or unchanged heavy replay was needed. Findings stay unchanged.

Next: public initialization and chronological history on the actual combined
logical ledger; active read/value/address/raw-clock bounds and worker key
refinement, remaining decoder/request/padding enforcement and actual caller-worker
issuance/fulfillment/accounting. Original CSR/MOP/worker execution, global
init/teardown, general physical/refinement/cryptography/completeness and checked
parity remain open.


## Constructed native physical decoder setup (7 November 2026)

[The source-reference construction](Airbender/Review/Circuits/ReducedMachine/PhysicalDecoderSetup.lean)
copies the full indexed public sparse decoder slice, including holes and its
configured tail, then pads every remaining ordinary physical row with minus-one.
Only the reserved last row becomes a negative column sum. The ordinary lookup
view has8388607 rows and excludes that normalized row. A complete original
stateful public image at log-capacity20 derives the exact1048576-row input slice.
Physical decoder columns6-through15 are constructed on the same proof; all other
observed setup fields, body rows, auxiliaries and claims are retained.

[The pure normalization proof](Airbender/Proofs/Tables/NormalizeLast.lean) proves
column sums zero symbolically over abstract groups/rows/width/domain BEFORE native
instantiation. [Native calculations](Airbender/Proofs/ReducedMachine/NativePhysicalDecoderSetup.lean)
derive exact prefix/tail/last observations and recover original seven-profile
Sail source evidence from membership in the constructed ordinary table. Actual
native mask equations exclude holes/tail; no expected per-row query or table-
equivalence premise is supplied. [Short roots](Airbender/Review/Circuits/ReducedMachine/PhysicalDecoderSetupTheorems.lean)
retain the existing complete same-main scalar/product/capacity/table-sum interface
when acceptance is checked ON these constructed setup observations.

Lookup membership/extraction is still an explicit trust boundary; it is NOT
inferred from single-challenge auxiliary sums. This explicit public construction
is not Rust execution, physical commitment/setup authentication, FFT/field/codec
refinement or identification of arbitrary public code with the fixed native
eight-word ROM. Original initialized execution interfaces and findings are unchanged.

Fifteen controls are split into [three base controls](Tests/NativePhysicalDecoderSetupBase.lean),
[eight slot/observation controls](Tests/NativePhysicalDecoderSetup.lean) and
[four normalization controls](Tests/NativePhysicalDecoderNormalization.lean).
A small two-slot hole fixture checks indexed holes; a separate exact-million-
capacity empty image checks the whole native physical tail. Its actual normalized
last value8388607 differs from padding and is excluded from lookup membership.
These are source/reference/metadata/conditional controls, not complete positive
nonempty table/global/worker/physical accepted witnesses or defect evidence.
Eight modules add39 explicit audit roots, preserving all5342 prior roots/source
bytes. Eleven exact parent origins plus two new manual native-source-reference
records retain99 unchanged native pins; no new intake, exporter/artifact/fixture/
production/Sail/dependency change, native generation or closed heavy replay.

Next: native decoder lookup extraction and remaining padding/global request
enforcement; full-domain main/43-worker token matching/public initialization;
active ranges/raw clocks/stage2-key refinement and real caller-worker accounting.
Original CSR/MOP and worker execution, global init/teardown, physical/general
refinement, cryptography, completeness and checked parity remain open.


## Native decoder table multiplicity and zero/last sum (7 November 2026)

[The decoder-table interface](Airbender/Review/Circuits/ReducedMachine/DecoderTableArguments.lean)
retains physical witness column9 separately from logical body variables: that
column has NO logical body-variable ID in this native artifact. Actual physical
setup columns6-through15 and quartic88 are separately typed; quartic72 remains
the decoder-access observation. [The same-read intake](Airbender/Import/ReducedDecoderTable.lean)
reuses unchanged complete body/stage2/access validation, checks exact multiplicity
geometry and unmappedness, and preserves all94130 source bytes. No body index is
invented for the physical multiplicity. Kernel geometry retains domain2^23,
witness width107, setup width16 and decoder capacity1048576.

The reviewed native per-row table relation is
tau*(setup-denominator*aux88-physical-multiplicity9). Every8388607 ordinary row
remains, with no assumed Boolean/count interpretation or zero-outside-capacity
rule. The normalized difference polynomial has actual aux88-minus-aux72 samples,
degree below the domain size, a primitive domain root and the native zero/last
divisor. [Proof calculations](Airbender/Proofs/ReducedMachine/NativeDecoderTableArguments.lean)
reuse the unchanged generic sum theorem with literal zero claim to DERIVE equality
of the two full ordinary auxiliary sums. The actual last auxiliary values are
equal; they are not each assumed zero. The sum is never an interface premise.

[Short roots](Airbender/Review/Circuits/ReducedMachine/DecoderTableTheorems.lean)
retain the existing decoder access and same-main scalar/product/capacity acceptance
on the EXACT SAME main rows/auxiliaries and configured worker batch. Separately
typed physical witness/setup values are observations; general body/physical codec,
public-code setup authentication and native Rust/field/FFT/LDE/quotient/transcript
refinement remain explicit open fidelity boundaries. Single-challenge auxiliary
sum equality supplies no table membership, compression injectivity, multiset
matching, initialized read, inactive request filter, issuance or accounting.
The prior complete-body/individual-decoder inactive CSR example is NOT promoted
to acceptance at this stronger table/global interface or a native defect.

[Thirteen regressions](Tests/NativeDecoderTable.lean) check physical/logical column
separation, actual setup/query/challenge roles, full domain retention, boundary
controls, pole slices and complete conditional sum/last results.
[Twelve executable intake controls](Tests/NativeDecoderTableImport.lean) check
changed/missing/extra physical groups, setup/auxiliary geometry, historical
rejection and canonical changed-body DATA without semantic transfer. Eight new
modules record13 exact parent origins and26 added audit roots, preserving every
prior5316 audit root/source byte. The unchanged native last-row/zero source was
exactly compared to67ee and pinned BEFORE adaptation, raising native source pins
to99. No old parser/proof/acceptance/exporter/artifact/fixture/dependency/production/
Sail change, native generation or closed heavy replay; FINDINGS unchanged.

Next: faithful public physical decoder setup/extraction and remaining native
padding/global request enforcement; full-domain main/43-worker token matching and
public initialization; active read/write/address/raw-clock ranges and stage2 key
refinement; caller-worker issuance/fulfillment/converse/accounting. Original
CSR/MOP and worker execution, global init/teardown, physical/general refinement,
cryptography, completeness and checked parity remain open.


## Native decoder access and faithful inactive-request boundary (7 November 2026)

[The decoder-access interface](Airbender/Review/Circuits/ReducedMachine/DecoderArguments.lean)
now retains the actual typed quartic slot72 and all ten original decoder fields.
[Its separate intake](Airbender/Import/ReducedDecoderAuxiliary.lean) reuses unchanged
complete body/stage2 validation on the same94130 source bytes; it transfers no
historical acceptance. The reviewed native denominator has PC-low coefficient1,
nine linearization challenges, witness scaling before gamma, and the source term
tau*(denominator*auxiliary-execute). The unit-normalized relation subtracts actual
execute, independently of the delegation request multiplicity. Physical field/
LDE/quotient extraction remains a separate fidelity boundary; unit normalization
is not a claim that all physical evaluation points have tau1.

[Short roots](Airbender/Review/Circuits/ReducedMachine/DecoderArgumentTheorems.lean)
extend the existing same-main scalar/product/capacity interface on the EXACT SAME
body rows and typed auxiliaries, preserving all8388607 ordinary rows and the same
configured worker batch/public observations. They derive the decoder row equation
and active pole exclusion, without table membership, expected query, active flag,
caller filter, initialized read, worker stream or result premises. Inactive poles
and auxiliary values are retained; no compression injectivity or matching follows.

[The local padding certificate](Airbender/Proofs/ReducedMachine/NativeDecoderPadding.lean)
checks the existing complete117-equation/22-lookup CSR1991/x0 body with execute0,
request1 and decoder auxiliary0 for EVERY decoder challenge. Thus this individual
decoder-access check also cannot justify inactive request filtering. This is a
precise LOCAL interface limit, not table-multiplicity/sum/last-row/global/worker/
physical acceptance, an accepted attack, F03 evidence, native defect or issue
assumption. FINDINGS and zero-established-native-defect status remain unchanged.

[Thirteen regressions](Tests/NativeDecoderArguments.lean) check complete local
active/inactive acceptance, all nine roles, PC-low scaling, inactive poles and
active-zero-auxiliary rejection. [Eight intake controls](Tests/NativeDecoderAuxiliaryImport.lean)
check actual source binding and changed/absent/overlapping slots, width and
historical-artifact rejection. Nine modules record13 exact parent origins and25
added explicit audit roots; all5291 previous audit roots/source bytes remain.
Already pinned aggregation/decoder native sources were byte-compared to67ee;
no new native pin, old parser/acceptance/proof/exporter/artifact/fixture/dependency/
production/Sail change, native generation or unchanged heavy replay was required.

Next: actual decoder table multiplicities/sum/last-row and remaining native
padding/global request enforcement, then faithful full-domain main/43-worker token
matching/extraction/public initialization and initialized active ranges/raw clocks/
stage2-key refinement and caller-worker accounting. The decoder-local result does
not settle any of these global obligations. Original CSR/MOP and worker execution,
physical/general refinement, cryptography, completeness and parity remain open.


## Exact sources

The current reference is [PR #585](https://github.com/matter-labs/zksync-airbender/pull/585)
at b29277dd895499574e317a994fd89243a72f06cb, based on
c1a662222cafcd96db4383dce737edb79fa62b09. The proof reference remains deliberately
pinned. The live source checkout advanced externally to 9bdfb988e0dd2ab83bf629d1e5c47f032f69030e,
parent964db88d3. Its reviewed cumulative five-path delta contains status/replay
timing changes plus a private Keccak slot-cache computation split into25 finite
blocks; original cache data, whole-cache statement and public normalization tail
are unchanged. Native/dependency inputs and public Review statements are unchanged.
Its status still leaves final full assurance pending. Those source-checkout
results are not v2 qualification or adoption of the newer proof implementation.
The native v2 target remains dev 67ee094449abaebc77e58435f130ce6ea27721e5.
No Rust, dependency version or original Sail standard clause changes are imported.

[Provenance](artifacts/provenance.json) distinguishes the original 805909325
source origins from the current reference and byte-identical current reuse.
Four shared arithmetic modules and the transparent field-capacity definitions
are copied unchanged from the new source. Capacity names preserve the exact
old inequalities; they do not identify a native field. Other reused modules
retain their historical hashes and origins. The eight current architecture,
importer, finding and trust references have independent source hashes.

## Migration map

| Current v3 component | V2 connection and remaining work |
| --- | --- |
| Unified CPU local import with an explicit fixed tagged table | The v2 combined reduced circuit follows this pattern, retaining its own four-field queries, eight scalar/eight timestamp queries, original x0 decoder and log-23 placement. The regenerated native target has 117 equations and a complete fourteen-region literal pool. Both actual sign/high-byte queries follow from original Clean acceptance; universal public/physical setup and other row semantics remain open. The historical 119-equation snapshot stays separate. |
| Reduced unrolled target | This is a different multi-family assembly. The name does not make it the target for the monolithic v2 reduced JSON. Existing standalone v2 families remain reusable components. |
| Unified row semantics and initialized execution | Port the calculations against actual v2 combined selectors/operands/writes and initialized memory/state history. Standalone proofs do not discharge these native connections. |
| Compiler certificates and native CPU acceptance | Not present in this backport. The local row importer does not establish GKR cached/uncached compiler preservation, exact decoder membership or the physical verifier's argument checks. Retained stage-two JSON is opaque. |
| Worker/caller and supported-use composition | Native v2 request and initialization coordinates are retained. Issue/fulfillment accounting, worker constraints and public custom-operation ABI remain to be connected. No v3 roster or temporary semantic assumption is inherited. |
| Initialization, terminal and padding boundaries | Current v3 covers one initialization/teardown instance, possibly with several windows, under explicit matching/public premises. V2 physical initialization/teardown and terminal/padding enforcement remain open; the descriptor alone supplies none of those results. |
| Exact lookup, state, RAM and request premises | Keep their boundaries visible. Sampled products or a table-equivalence premise cannot replace the missing v2 enforcement proof. General Rust/compiler refinement, cryptographic enforcement and completeness remain separately scoped. |

## Current reduced checkpoint

[The native artifact](Airbender/Review/Circuits/ReducedMachine/Artifact.lean)
retains the complete source bytes and emits the original Clean row operations.
[Structural checks](Airbender/Proofs/ReducedMachine/ArtifactChecks.lean) retain
all six three-value queries plus their actual constant/dynamic tags and the same
fixed setup table; no disabled row, gating change or witness-supplied table data
is introduced. Existing shift/CSR request coordinates are also retained, including
its absent ABI group; unsupported profiles cannot silently carry requests.
[Intake controls](Tests/ReducedMachineImport.lean) reject altered
setup geometry, selectors, initialization/request placement and unsupported
processor/batched/indirect metadata. [Emission controls](Tests/ReducedMachineEmission.lean)
reject omitted, wrong and crossed target profiles.

The complete serial bounded pass covers 777 source/test modules, including
139 test modules; 492 existing importer controls and 44 reduced/request
controls pass, as do all seven native CLI inputs, native exporter checks,
2,306 axiom roots and all 137 public Review claims. Dependency fingerprints
retain only unchanged verified modules. Peak charged footprint was
1387.39 MiB and peak resident usage 3601.03 MiB, below the unchanged
3072/4096 MiB ceilings. Every guard completed without a live owned process.

The independent bounded provenance audit also passes: 75 legacy and five
current byte-identical sources, seven native circuits, 56 native sources,
21 setup artifacts, four exporter files, 189 v3 adaptation identities and
693 earlier v2 reuse identities. Current architecture references and
historical reuse origins match their exact Git objects. The original
checkout and dependency versions are unchanged. The combined machine has no execution
soundness theorem yet. Next: bind actual v2 reduced fixed regions and public
ROM/CSR setup, then derive combined selectors, operands, writes and original
Sail row effects before assembling initialized history and caller boundaries.
A new hourly continuation task is active at the user's request; the old task
remains paused. The unchanged-circuit policy requires documented native evidence
and explicit narrow interface assumptions for any confirmed issue.

## Renewed continuation and first fixed-region certificate

The new hourly task continues this native reduced-machine dependency chain.
[The sign/high-byte region](Airbender/Review/Circuits/ReducedMachine/Tables/SignHigh.lean)
checks all actual native rows and their tag/placement; it is a regional certificate,
not whole-setup or execution coverage. The next step is the complete native pooled
fixed relation, including actual public ROM/CSR configuration and tag isolation,
then combined row semantics. The production circuit remains unchanged. See the
[issue-handling policy](FINDINGS.md#backport-issue-handling-policy).

## Regenerated source target

The unchanged native v2 compiler produces a different target from the historical
shipped reduced JSON: 117 equations/142 variables/fourteen fixed regions rather
than 119/141/thirteen. The [active native target](Airbender/Review/Circuits/ReducedMachine/NativeArtifact.lean)
and [full pool](Airbender/Review/Circuits/ReducedMachine/Tables/Native.lean) retain
that distinction and reproducible public inputs. No circuit code was fixed and
no coverage transfers through an equivalence premise. The full pool now yields
tag isolation and both actual sign/high-byte query results from Clean acceptance.
The next work is the other native operation tables, general public setup and
combined row/initialized execution, followed by workers and protocol boundaries.

The native Clean connection additionally derives all four dynamic selector
domains from exact pooled membership. Each tag comes from its actual fourth
expression and a certified stored region. The public theorem supplies no selector
answer; operation-specific identity and effects remain pending.

## Native selected shift connection

The [regenerated row claim](Airbender/Review/Circuits/ReducedMachine/Theorems.lean)
now derives shift operation flags and tags from actual native equations, and
routes the register/immediate operand into the literal tag-47 truncation query.
The six explicit native packed-mask cases retain v2 encodings. Kernel equality
of stored truncation columns permits reuse of the unchanged prior row lemma;
no v3 or standalone table-equivalence premise is supplied. The selected IDs are
47/37/37/20, distinct from the standalone split-shift tables and sign-fill ID 52.
The original public-decoder connection, table-37/sign-fill meanings, shift
results/writes/PC, combined history/execution and protocol boundaries remain
pending. This is further native reduced coverage, not parity or a finding.

## Native sign-fill result

The [same native row surface](Airbender/Review/Circuits/ReducedMachine/Theorems.lean)
now recovers all three minor flags and the actual tag-20 query. All 128 stored
rows yield exact filler limbs, with positive/logical and zero-shift cases
retained. The input sign and five-bit amount are derived from accepted native
queries; canonical packing derives the key bounds. This extends the regenerated
v2 combined row, with the decoded packed-mask input still explicit. It adds no
Sail retirement, full shift-result, physical setup or v3 parity claim.

The table-37 literal-column comparison requires a smaller evaluation design:
whole/sliced cross-artifact checks exceeded the existing resident or Lean
allocation limits and were terminated without survivors. The attempted draft
is excluded from coverage and committed source. No limit increase, table
assumption or circuit change was made to bypass that unfinished proof.

## Native contribution/port connection

The [native reduced claims](Airbender/Review/Circuits/ReducedMachine/Theorems.lean)
now derive both actual table-37 keys/output fields, directional contribution
assembly, the actual masked destination port/address and default-PC selection.
The existing native equation-extraction and metadata-check patterns are reused
with exact prior-backport source hashes in provenance. The decoded mask remains
explicit. No table meaning, desired write or numerical PC answer is supplied as
a premise. Eight conditional native regressions and all 2,420 axiom/148 public
Review roots pass. This advances the monolithic v2 target on the v3 Unified
migration path; it does not establish table-37 arithmetic, public decoding,
initialized source reads, original shift execution or coverage parity.

## Complete actual shift-column connection

[Native tag-37 output transport](Airbender/Proofs/ReducedMachine/NativeShiftColumns.lean)
now covers all 4,194,304 indices in both actual output columns. Twenty small
literal template certificates reuse exact prior size/read lemmas; block
congruence and symbolic resegmentation preserve the merged zero boundary and
reversed right-shift column order. No setup/circuit/importer change or table
assumption is used. All 2,459 axiom roots and 148 public Review roots pass.
Pooled canonical numerical query composition and actual shift/Sail execution
remain open. The second-output composition draft still hits the allocation cap
and stays outside committed coverage. This is native connection progress, not
checked v3 parity.

## Actual numerical row and contribution connection

The later [native numerical certificate](Airbender/Proofs/ReducedMachine/NativeShiftRows.lean)
closes the row/query composition gap above. It reuses exact certified getter
transport and unchanged arithmetic references through separate low/high proofs.
Generic projections prevent selecting a tuple limb from reducing its expanded
arithmetic; all proof/resource limits remain unchanged. Full actual pooled
membership now derives the canonical packed key, both exact outputs and bounds.
The [short row interface](Airbender/Review/Circuits/ReducedMachine/Theorems.lean)
derives all four numerical contribution fields/bounds from the actual queries.
Eleven native boundary/rejection/discarded-write regressions, all 2,482 standard-only
axiom roots, 150 public Review roots and exact provenance/guide gates pass. The
old second-output drafts remain excluded; the committed split proof supersedes
their resource gap. No circuit/importer/data/dependency change or new assumption
is used. Canonical architectural source-key binding, original public decoding,
initialized reads, complete shifted words, numerical PC and execution remain
open, followed by worker/protocol/terminal/init boundaries. This is not parity.

## Actual combined initialized clock and memory-history connection

The [regenerated reduced registry](Airbender/Review/Helpers/Context/ReducedMachine.lean)
now connects actual native metadata and explicit modeled setup to the shared
trace representation. Native equations 27..30/115/116 and timestamp lookups 8..15
prove the clock contract, independently of operation arithmetic. The
[short public history interface](Airbender/Review/Trace/Families/ReducedMachine/History.lean)
derives complete Clean logical consistency/newest reads, all local/prior clocks,
strict access order and terminal four-tick row accounting from original public
seed reads and accepted native matching. Four conditional regressions, all 2,497
standard-only axiom roots,152 public Review roots and exact provenance/guide gates
pass with unchanged limits. No production circuit/data/importer/dependency changed.
This is a checked native v2 connection using exact prior-backport proof origins,
not coverage transfer from the similarly named v3 reduced target. Derived word
ranges still require decoded native write preservation and initialized induction;
canonical source keys, original decoding/execution and machine/protocol/terminal
boundaries remain open. No defect, new restriction or parity claim is introduced.

## Original public shift decoding at the actual native reduced query

[The selected native reduced projection](Airbender/Review/Circuits/ReducedMachine/Decoder.lean)
adapts original RV32 shift constructors to checked reduced masks while retaining
x0 operands, funct3 and SRAI's encoded immediate. [Native packing proofs](Airbender/Proofs/ReducedMachine/NativeShiftDecoder.lean)
exclude holes/tail and recover every actual source/rd/x0/immediate field from
complete original-byte/stateful Sail decoder membership. The short
[public trace claim](Airbender/Review/Trace/Families/ReducedMachine/Decoder.lean)
therefore derives the existing explicit mask without assuming a selector answer.
Eight regressions include twelve ordinary/x0 forms and all 25 original public slots.
All 2,513 standard-only axiom roots, 153 public Review roots and exact provenance/guide
gates pass at unchanged limits. Only original public byte/decode lemmas are reused;
no old native decoder table is equated. This is not a new Rust preprocessing/export
certificate, universal fixed-ROM correspondence or execution/parity claim. Other
combined profiles, write preservation and initialized word ranges remain open.

## Initialized actual native shift word ranges and source keys

[Concrete native fixed-pool traces](Airbender/Review/Trace/Families/ReducedMachine/FixedData.lean)
now support proved masked-write preservation and unchanged shared initialized
range induction. The [short public range claim](Airbender/Review/Trace/Families/ReducedMachine/Values.lean)
derives every read/write/terminal word bound; [both source keys](Airbender/Review/Trace/Families/ReducedMachine/Sources.lean)
then have exact natural limb/amount/direction packing. Earlier-source bounds stay
internal and are discharged by public seeds, actual native matching and original
selected-shift decoding. No range, preservation, expected result or table-equivalence
answer is a public premise. Symbolic stride/gap/complement proofs replaced the
allocation-heavy arithmetic search without changing proof/resource limits.
Nine regressions, all 2,548 standard-only axiom roots, 155 public Review roots and exact
provenance/guide gates pass. Production/native data and dependencies are unchanged.
This is a checked native connection for the selected shift profile, not all combined
operations, original Sail GPR/cell/word execution, numerical PC, physical/preprocessing
fidelity, protocol/terminal closure or parity.

## Complete initialized native RV32 shift words

[The selected original-shift result](Airbender/Review/Trace/Families/ReducedMachine/Results.lean)
now derives exact canonical RV32 candidates and actual decoded x0-masked writes
from initialized native ranges and original public decoding. New symbolic native
word assembly reuses unchanged pure contribution/whole-RV32 lemmas after the
actual v2 table/query/candidate connection. No v3 or old split-family native
constraint/table/result is transferred by assumption. The public contract adds
no source range, expected read/write, table equivalence or intermediate state.
All 32 amounts, native right-output order, arithmetic zero shift and discarded
candidate participation remain intact. Eight new numerical/rejection/initialized
consequence regressions pass; they are not full positive 117-equation fixtures.

The bounded audit passes 2,569 standard-only axiom roots and 156 public Review
roots at unchanged limits. Native data/configuration and all importer/exporter
inputs are unchanged. Original Sail cell/GPR transport, native source-two address
and readonly binding, numerical PC/wraparound, instruction execution, other
combined profiles, workers/accounting and protocol/padding/terminal/init remain
required for parity. General preprocessing/ROM/physical/compiler fidelity stays
separate. No native defect or new issue-handling assumption is established.

## Original native reduced Sail register histories

[The selected original-shift register claim](Airbender/Review/Trace/Families/ReducedMachine/Registers.lean)
now derives actual original Sail GPR/cell states, all three pre-state reads,
masked writes, final matching, code/misa frames and decoder replay in constructed
row pre-states. Original public seed/decoder construction and native matching
supply all states/reads; no expected intermediate, address-space flag, x0 event
value or replay result is a public premise. Unlike the old split-family metadata,
actual v2 reduced source-two/destination ports are mixed: new native equations
prove register-space/indices before reusing unchanged shared history machinery.
Eight regressions retain aliases/x0, reject malformed native mixed-port fields
and include a positive three-port mechanics fixture, scoped below full native
117-equation acceptance. The bounded audit passes 2,592 standard-only axiom roots
and 157 public Review roots. Original selected-operand/clause and numerical PC/
fetched execution, other combined profiles and worker/protocol/terminal/init
remain open; general compiler/preprocessing/ROM/physical boundaries stay explicit.
No v3 native semantics, finding or circuit fix is inherited by assumption.

## Read-only source checkout observation

During the register-history checkpoint the original checkout advanced externally
to 964db88d323d7f04a258f38bce28eca1c6d31652. A scoped Git comparison with the
b29277dd895499574e317a994fd89243a72f06cb proof pin changes only verification
status and three replay/audit helper-control files. No Lean statement/proof,
production circuit, native input or dependency changes. The named ChiCharacters
replay time allowance is unrelated to these native reduced proofs, whose existing
resource ceilings stay unchanged. The v3 proof reference remains pinned; this
backport neither resets nor adopts the live checkout's changes. Independent
provenance checks every exact pinned Git object separately from the observed
live HEAD and verifies the original tracked checkout/unrelated files are retained.

## Original native reduced shift clauses

[The short original-clause history claim](Airbender/Review/Trace/Families/ReducedMachine/Clauses.lean)
now derives retained original Sail SLL/SRL/SRA/register/immediate execution at the
same actual GPR after-state. Native form/mask/routing proofs bind selected operands
without transferring old split masks/columns, while original readonly rs2/x0
accesses remain in the relation. Existing initialized ranges, numerical results
and original GPR histories discharge every internal bound/read/write/state premise.
No expected selected operand, result or intermediate state is a public input.

Eight regression roots include twelve concrete original Sail ordinary/x0 clause
executions, six whole-state x0 stutters, actual native SRAI 1055/readonly aliasing,
derived initialized-state composition and all illegal 32/63 immediate exclusions.
These local positive Sail fixtures do not establish complete 117-equation native
acceptance. The bounded audit passes 2,607 standard-only axiom roots and 158 public
Review roots. Numerical PC/wrap, preparation/retirement/fetched execution, other
combined profiles and worker/protocol/padding/terminal/init remain open. Native
preprocessing/ROM/physical and general compiler/crypto/completeness boundaries
remain unchanged; no native issue, circuit fix or new assumption is added.

## Actual native reduced numerical PC

[The public PC successor](Airbender/Review/Trace/Families/ReducedMachine/PC.lean)
now derives incoming canonical bounds/alignment and bounded actual final-PC+4
with complete RV32 wrap from original public decoding and accepted native rows.
The prior v2 arithmetic argument is reused only after checking new native Boolean,
carry, inverse, default candidate and selected final-PC coordinates; no split
constraint or table-equivalence premise is transferred. The polynomial proof keeps
generic modeled setup explicit and adds no physical/preprocessing/ROM claim.
Eight regressions check exact native increment slices, corruption rejection,
original decoded wrap/query agreement, oversized successors and x0 advancement.
The positive slice fixtures are scoped below complete117-equation acceptance.
All 2,621 standard-only axiom and 159 public Review roots pass at unchanged caps.
Normal PC preparation/retirement/fetched execution, other combined profiles and
worker/protocol/padding/terminal/init remain open; this is not parity or a native
finding/fix. General compiler/physical/cryptographic/completeness boundaries remain.

## Selected native reduced original fetched execution

[The public retired-history](Airbender/Review/Trace/Families/ReducedMachine/Execution.lean)
and [fetched-execution claims](Airbender/Review/Trace/Families/ReducedMachine/FetchedExecution.lean)
now derive original normal nextPC/clause/tick_pc execution and finite successful
four-byte Sail stepping to actual native terminal PC/cell reads for initialized
selected shifts. Actual native ports/clauses/numerical PC and derived ranges
justify reuse of shared control-frame/chronological composition; original public
stateful decoder replay and all intermediate states/order are conclusions.
The fixedData/public initialization/full decoding/aligned-domain boundaries stay
explicit; no source range/result/state/table-equivalence answer is added.
All twelve original forms and x0/wrap retirement, initialized segment extraction,
terminal-bound rejection and concrete empty actual-native execution pass. The
positive fixtures are local Sail or zero-row native paths, not complete nonempty
117-equation acceptance. All 2,634 standard-only axiom and 161 public Review roots
pass. Other combined operations, workers/accounting/protocol/padding/terminal/init,
native public/fixed-ROM/physical setup, general compiler/crypto/completeness and
original interrupt/exception paths remain separate. Selected-profile execution
is not full reduced-machine coverage or v3 parity. No native fix/issue/assumption.

## Complete nonempty native reduced execution examples

[The actual SLL/x0 witnesses](Tests/NativeReducedWitness.lean) check all117native
equations and22lookups at the complete unchanged native pool. [Public fixtures](Tests/NativeReducedFixture.lean)
then prove activity,state/memory matching,original Sail seed/PC reads,complete
13-word sparse/stateful decoding with holes/padding and actual query membership.
[The positive execution checks](Tests/NativeReducedPositive.lean) derive actual
PC4/x3=2 or PC52/x3=0,x0=0 from original fetched execution while candidate2 remains
present on both rows. No desired read/result/state or old split native table
identity is supplied. These are complete modeled nonempty accepted traces;
other profiles and native public/preprocessing/ROM/physical correspondence remain
separate,including the distinction between13public words and8native fixed words.
All 2,643 standard-only axiom and 161 public Review roots pass. Native inputs are
unchanged;small transparent certificates replace deep reduction without raising
limits. This fixture checkpoint is not new general coverage,full machine/parity,
a native defect/fix or a new issue-handling assumption.

## Native reduced arithmetic profile connection

[Actual native arithmetic routing/writes](Airbender/Review/Circuits/ReducedMachine/ArithmeticTheorems.lean)
now cover ADD/ADDI/SUB/LUI/AUIPC under their five explicit reduced masks. All
native flags,scalar/carry equations,candidate assembly,readonly rs2 participation,
zero dynamic tags and default-PC selection are derived independently of the
standalone family. Unchanged pure RV32 lemmas are used only after these actual
connections. Numerical calculations keep input bounds INTERNAL until original
public arithmetic decoding and initialized preservation/history discharge them.
[Nine conditional regressions](Tests/NativeReducedArithmetic.lean) retain RV32
wrap/borrow,LUI words above Mersenne31 and x0 participation. This is local native
coverage,not initialized arithmetic execution,physical setup or v3 parity. Native
production inputs are unchanged and no issue-handling assumption is added.
All 2,666 standard-only axiom roots and 163 public Review roots pass, with exact
189/863 origin identities and the unchanged memory ceilings. The next native
connection is original arithmetic public decoding and initialized preservation,
ranges, GPR history and retained Sail execution across combined profiles.

## Original decoded and initialized arithmetic values

[Three short native trace claims](Airbender/Review/Trace/Families/ReducedMachine/ArithmeticResults.lean)
now recover original arithmetic metadata, all initialized word bounds and
canonical RV32 candidates/actual x0-masked writes. Original byte/stateful decoding
retains raw U-type funct3 and sign-extended ADDI; native constraints exclude
holes/tail. Actual scalar checks and decoded immediate fields prove preservation,
then unchanged shared induction discharges every local read-range prerequisite.
The generic modeled setup stays explicit because these arithmetic proofs require
no dynamic-table numerical semantics; no native table-equivalence premise is
added. [Decoder/source checks](Tests/NativeReducedArithmeticDecoder.lean) and
[initialized consequences](Tests/NativeReducedArithmeticValues.lean) are not full
positive arithmetic execution fixtures. Original GPR/cell/retained Sail execution
and mixed shift/arithmetic traces remain next. No native defect/fix/assumption or
parity is claimed; production/data/dependency inputs remain unchanged.
All 2,694 standard-only axiom roots and 166 public Review roots pass, with exact
189/882 origin identities, unchanged limits and no owned surviving processes.

## Original native arithmetic GPR histories

[The short original history claim](Airbender/Review/Trace/Families/ReducedMachine/ArithmeticRegisters.lean)
now derives chronological original GPR/cell states, all three actual reads in one
pre-state, masked writes, terminal matching, code/misa frames and decoder replay
from public initialization/decoding, native acceptance and aligned tracked cells.
New native arithmetic address/x0 proofs justify unchanged shared history reuse;
shift masks/constraints are not transferred. [Eight regressions](Tests/NativeReducedArithmeticRegisters.lean)
retain mixed-port rejection, aliases, x0 stutters and initialized zero events.
No complete accepted arithmetic execution fixture or retained clause/PC retirement
is inferred; AUIPC's incoming architectural PC still needs explicit derived row
state preparation. No native defect/fix/assumption or parity is claimed.
All 2,717 standard-only axiom roots and 167 public Review roots pass, with exact
189/892 origin identities and unchanged resource limits; every worker terminated.

## Original arithmetic fetched-execution checkpoint

[Arithmetic execution](Airbender/Review/Trace/Families/ReducedMachine/ArithmeticFetchedExecution.lean)
now composes actual reduced ADD/ADDI/SUB/LUI/AUIPC constraints, public original
decoding, initialized GPR/range history, selected operands, numerical results and
PC preparation/retirement into finite fetched Sail execution. AUIPC's architectural
PC observation is derived from actual incoming native PC in constructed states.
The two short public roots supply no per-row read/range/result/PC/state answer.
Generic native modeled setup stays explicit; mixed shifts still require exact
fixedData/NativeFixed.table semantics. [Retirement regressions](Tests/NativeReducedArithmeticExecution.lean)
cover all ten ordinary/x0 forms, carry/borrow/sign/upper immediates, nonzero-PC
AUIPC and RV32 wrap; [empty executions](Tests/NativeReducedArithmeticFetched.lean)
cover every RV32 terminal PC. These do not certify positive nonempty arithmetic
117-equation fixtures. Separate selected-shift and arithmetic execution does not
prove mixed-profile execution, other combined operations, worker/protocol spans,
padding/terminal/init, native public setup/compiler/physical fidelity or parity.
No production/native/literal/dependency input changes or native findings are added.
The continuation remains active every thirty minutes.

## Mixed selected shift/arithmetic execution checkpoint

[Common original decoding](Airbender/Review/Circuits/ReducedMachine/SupportedDecoder.lean)
now preserves checked native fields while admitting both selected shifts and
ADD/ADDI/SUB/LUI/AUIPC. [Mixed initialized execution](Airbender/Review/Trace/Families/ReducedMachine/SupportedExecution.lean)
derives actual native-clock order/original Sail states, all source ranges,
original decoder replay and finite successful fetched execution with actual
terminal PC/cell reads. Profile/query transport and common write/x0/range/history
proofs justify reuse of the checked local native executions; separate-profile
public theorems alone are not used to assume mixed history. Exact fixedData pool
acceptance stays explicit; no table-equivalence or local read/result/state/PC
answer is supplied. [New image tests](Tests/NativeReducedSupportedDecoder.lean)
construct one original 25-word mixed public decoder with holes/seven padding rows;
[initialized/empty tests](Tests/NativeReducedSupportedExecution.lean) retain source/
x0/terminal rejection. These are not positive nonempty arithmetic/mixed native
117-equation fixtures. Remaining ordinary combined profiles, workers/accounting,
protocol/padding/terminal/init and public/compiler/physical/completeness boundaries
remain open. No native finding/fix/issue assumption or parity claim is added.

## Native bitwise local numerical checkpoint

[Actual reduced bitwise proofs](Airbender/Review/Circuits/ReducedMachine/BitwiseTheorems.lean)
now derive all18native flags at33/35, actual four byte queries/decompositions,
full canonical RV32 candidates and both operand ranges without range answers.
[Actual pool semantics](Airbender/Review/Circuits/ReducedMachine/Tables/NativeBitwiseTheorems.lean)
use exact independently emitted data identities, checked in Lean, before reusing
unchanged byte arithmetic. Old split masks/constraints are not transferred. Actual
masked destination/register-space and default-PC selection are checked; original
public bitwise decoding/rd/x0/GPR/operand/clause/PC/fetched execution remain next.
The common supported execution still covers shifts and five arithmetic profiles.
[Regressions](Tests/NativeReducedBitwise.lean) retain actual byte-row offsets,
corruption/domain rejection, immediate readonly/x0 participation and sign-bit RV32
values above M31, without claiming complete positive native bitwise execution.
No native/imported/generated data or production/Sail/dependency input changed;
no native finding, issue assumption, fix or parity claim is added.

## Original native bitwise execution checkpoint (7 November 2026)

[Original bitwise projection](Airbender/Review/Circuits/ReducedMachine/BitwiseDecoder.lean)
adapts the exact pinned native arithmetic public-decoder pattern while preserving
all six original constructors/x0/raw operands/sign extension and actual33/35mask,
4/6/7rawfunct3. [New native effects](Airbender/Proofs/ReducedMachine/NativeBitwiseExecution.lean)
prove all actual ports, selected operands, decoded masked writes, original clauses
and PC preparation/retirement with RV32 wrap. Previously checked byte numerics
supply all ranges; no source-bound or desired result/state/PC premise is introduced.
[The common supported execution](Airbender/Review/Trace/Families/ReducedMachine/SupportedExecution.lean)
now derives initialized interleaved shift/arithmetic/bitwise fetched execution via
common native range/x0/history/code/misa/replay proofs and exact fixedData acceptance.
All 25 original public image slots now have SourceWith evidence. [New regressions](Tests/NativeReducedBitwiseExecution.lean)
check all twelve ordinary/x0 forms and original retirement, sign bits/negative
immediates, wrong tags and masked writes. Original local Sail positives are separate
from full nonempty native witnesses. Exact parent-revision template hashes are in
[provenance](artifacts/provenance.json); old split masks/constraints/tables are not
assumed equivalent. Other combined profiles and public/export/preprocessing/ROM/
physical/protocol/terminal/init/cryptographic/completeness/interrupt scopes remain
open. No production/native/Sail/data/dependency change, finding or parity claim.

## Native comparison decoding and initialized numerics (7 November 2026)

[New actual reduced comparisons](Airbender/Review/Circuits/ReducedMachine/ComparisonTheorems.lean)
derive masks65/67/all18flags, actual routing/subtraction/candidate/write/PC fields,
and complete tag22packed-key lookup semantics. Every128row is checked independently;
old split tag43and inconsistent-flag behavior are not inherited. Native signed
resolution flips unsigned borrow when signs differ; valid bounded operands prove
its exact RV32 meaning through unchanged pure borrow/signed-order lemmas.
[Original decoding](Airbender/Review/Trace/Families/ReducedMachine/ComparisonDecoder.lean)
retains SLT/SLTU/SLTI/SLTIU/x0/raw operands/sign extension. [Initialized word ranges](Airbender/Review/Trace/Families/ReducedMachine/ComparisonValues.lean)
and [complete numerical candidates/writes](Airbender/Review/Trace/Families/ReducedMachine/ComparisonResults.lean)
derive every internal source bound from public seeds/matching and proved local
preservation at exact fixedData. No desired local range/read/result/state or table
identity premise. Original GPR/Sail/PC/fetched/common mixed comparison execution
remains next; other combined/protocol/setup/completeness boundaries remain open.
[Regressions](Tests/NativeReducedComparison.lean) include every actual resolver row,
inconsistent-flag distinctions, original SLTIU bytes/stateful slot and initialized
oversized-source rejection; no complete positive nonempty comparison witness is
claimed. Native conditional.rs is newly pinned unchanged; no native/Sail/data/
dependency change, finding/fix/issue assumption or parity claim is added.

## Native comparisons in common original execution (7 November 2026)

[New actual native ports](Airbender/Proofs/ReducedMachine/NativeComparisonPorts.lean)
justify original GPR observations before shared history reuse. [Original signed/unsigned primitives](Airbender/Proofs/ReducedMachine/NativeComparisonClauseReference.lean),
[retained clauses](Airbender/Proofs/ReducedMachine/NativeComparisonClause.lean),
[actual bounded PC+4/wrap](Airbender/Proofs/ReducedMachine/NativeComparisonPC.lean)
and [normal retirement](Airbender/Proofs/ReducedMachine/NativeComparisonExecution.lean)
close the original comparison row connection. [Common initialized execution](Airbender/Review/Trace/Families/ReducedMachine/SupportedExecution.lean)
now admits comparisons after derived original profile/query transport and new native
range/x0/address/PC/execution rules. Both readonly source bounds and alignment,
all states/order/code/misa/decoder replay and terminal observations are derived
from the same explicit public interfaces and exact fixedData acceptance.
Readonly rs2/x0 participation, original sign extension and AUIPC's prepared actual
PC remain unchanged. No desired local answer or arbitrary-table identity is used.

[Six regressions](Tests/NativeReducedComparisonExecution.lean) retain ordinary/x0,
signed/unsigned/negative-immediate and RV32-wrap behavior; a common original public
SLTIU slot is checked too. These are not new full nonempty native comparison/mixed
witnesses or physical setup fidelity. Exact parent962 template hashes are recorded
in [provenance](artifacts/provenance.json). Earlier numerical-only comparison scope
is superseded here. Other ordinary/protocol/setup/terminal/init/completeness and
original interrupt/exception boundaries remain open. No production/Sail/native/
data/dependency change, defect, issue assumption or parity claim.

## Native branch local routing foundation (7 November 2026)

[Actual branch mask70](Airbender/Review/Circuits/ReducedMachine/Branch.lean) and
[all18native flags](Airbender/Proofs/ReducedMachine/NativeBranchSelectors.lean) now
justify [actual readonly/dummy/query/PC fields](Airbender/Proofs/ReducedMachine/NativeBranchFields.lean).
[Shared remainder-zero semantics](Airbender/Proofs/ReducedMachine/NativeConditionalEquality.lean)
follows from actual78..81 and scalar checks without source bounds/zero answers.
[One short local root](Airbender/Review/Circuits/ReducedMachine/BranchTheorems.lean)
retains the decoded mask and explicit generic modeled setup. Complete resolver128
rows remain unchanged. No old split mask/constraint/table identity transfers.

[Regressions](Tests/NativeReducedBranchRouting.lean) include exact five-assertion
zero/nonzero slices; these are not complete accepted117-equation branches.
Original public branch decoding, conditions/targets/alignment/GPR/Sail execution
and common integration remain open. Current common support remains shifts/
arithmetic/bitwise/comparisons. Six exact parentc6a992 template origins record
this foundation; native/Sail/data/dependencies and physical/trust boundaries are
unchanged. No defect, issue assumption, production fix or parity claim.

## Native branch conditions and PC numerics (7 November 2026)

[New actual branch conditions](Airbender/Proofs/ReducedMachine/NativeBranchCondition.lean)
derive full RV32 equality/order from actual bounded subtraction/signs and packed
resolver membership; native inconsistent-flag behavior is not copied from split
control tables. [Actual tag17 semantics](Airbender/Review/Circuits/ReducedMachine/Tables/NativeBranchTheorems.lean)
now cover all65,536native rows with symbolic column proofs and complete-pool
isolation. [Numerical PC effects](Airbender/Proofs/ReducedMachine/NativeBranchPC.lean)
derive canonical target/final bounds, actual PC+offset/full wrap, taken-only bit1
exclusion and selected aligned target/default successor. Canonical source/PC/
offset inputs, incoming alignment and offset parity remain internal obligations
for original public decoding/history; chosen condition/target is never supplied.

[Eight regressions](Tests/NativeReducedBranchResults.lean) include complete cleanup
membership and four-assertion target edge slices. They do not certify full native
accepted branches or original Sail execution. Original public decoder/GPR/clause/
normal/fetched branch effects and common support remain next. Ten exact parent8563
origins record unchanged pure condition/column/arithmetic and adapted proof patterns.
Native/Sail/data/dependencies, physical/trust boundaries and zero findings remain
unchanged; no issue assumption or parity claim.

## Original public branch numerics (7 November 2026)

[Original BTYPE fields](Airbender/Review/Circuits/ReducedMachine/BranchDecoder.lean)
now recover actual native70mask/operands/dummy-rd/x0/offset/raw funct3 from complete
public byte/stateful sparse membership. Original Sail decoding derives offset
parity; constructors remain unfiltered. [Initialized ranges](Airbender/Review/Trace/Families/ReducedMachine/BranchValues.lean)
use proved actual readonly/dummy-zero preservation and unchanged time induction.
[Short public numerical result](Airbender/Review/Trace/Families/ReducedMachine/BranchResults.lean)
discharges every source/PC/offset/range/alignment/parity input internally, deriving
actual branch condition/target/final PC bounds/RV32 wrap/alignment from exact
fixedData acceptance. No local answer or arbitrary-table identity is public.

[Eight regressions](Tests/NativeReducedBranchDecoder.lean) retain all six original
sources/full six-slot setup/parity/negative x0 aliases and initialized bounds.
Only original bytes/stateful decoding are reused from the old fixture, not native
masks/tables/constraints/acceptance. Six modeled words plus two padding are not the
native fixed configuration or physical ROM/export enforcement. Original GPR/Sail
branch clauses/normal/fetched execution and common operation-specific PC integration
remain next. Sixteen exact parent0f1188 origins record twelve new modules/tests.
No native/Sail/data/dependency change, defect, issue assumption or parity claim.

## Native branch original fetched execution (7 November 2026)

[New actual port bindings](Airbender/Proofs/ReducedMachine/NativeBranchPorts.lean)
justify shared history transport for original rs1/rs2 and the present x0 dummy
read/zero write. [Public original history](Airbender/Review/Trace/Families/ReducedMachine/BranchRegisters.lean)
constructs all states/reads/writes/stutters/code/misa/replay. [Local execution](Airbender/Proofs/ReducedMachine/NativeBranchExecution.lean)
uses retained BTYPE clauses only after new native condition/PC effects and actual
incoming-PC preparation; pure retirement and control-CSR lemmas are reused unchanged.
[Public fetched execution](Airbender/Review/Trace/Families/ReducedMachine/BranchFetchedExecution.lean)
discharges both source bounds/alignment/decoder parity internally. Initial public
misa readability is explicit, its value unrestricted; each local read is derived.
No standalone native mask/table/constraint identity or desired state/read/result/PC
answer is transferred. Nineteen exact parent889 origins cover thirteen modules/tests,
including unchanged pure clause/control/retirement/group/reference reuse.

[Port/history](Tests/NativeReducedBranchRegisters.lean), [retained-clause](Tests/NativeReducedBranchExecution.lean)
and [empty native](Tests/NativeReducedBranchFetched.lean) regressions do not certify
full nonempty117-equation branch acceptance. Branch-only execution is checked;
common mixed branch integration and other ordinary/protocol/setup/terminal/init
boundaries remain open. Native/Sail/data/dependencies are unchanged; no native
defect, issue assumption, production fix, axiom or parity claim.

## Mixed native branch integration (7 November 2026)

[Common original projection](Airbender/Review/Circuits/ReducedMachine/SupportedDecoder.lean)
now admits branches without changing any actual query field. [Five-way original
entry transport](Airbender/Proofs/ReducedMachine/NativeSupportedDecoder.lean) supplies
checked branch preservation/x0/addresses before one common initialized range/Sail/
code/misa/replay chain. [Common local execution](Airbender/Proofs/ReducedMachine/NativeSupportedLocal.lean)
discharges branch source bounds/parity/PC inputs and invokes the previously checked
actual retained branch interface. Operation-specific final bounds replace universal
common PC+4; unchanged ordinary per-profile PC proofs remain available.
[Public execution](Airbender/Review/Trace/Families/ReducedMachine/SupportedExecution.lean)
requires initial readable misa only for public programs containing BTYPE. Value is
unrestricted and every local read is derived; empty/ordinary CSR-free scopes remain.

[Independent mixed source/configuration regressions](Tests/NativeReducedSupportedBranches.lean)
do not imply full nonempty117-equation native acceptance. Fifteen exact parentc814
origins record nine changed/new modules/tests, preserving older provenance. Remaining
ordinary/protocol/setup/terminal/init/completeness boundaries and zero findings remain;
no production/native/Sail/data/dependency change, issue assumption or parity claim.

## Actual native jump routing/output bounds (7 November 2026)

[Native jump masks257/33025](Airbender/Review/Circuits/ReducedMachine/Jump.lean) and
[all18actual bits](Airbender/Proofs/ReducedMachine/NativeJumpSelectors.lean) precede
[new exact field connections](Airbender/Proofs/ReducedMachine/NativeJumpFields.lean):
base81/82 from PC/rs1, actual shared addition74/75, tag17 query, rejected bit1,
default return candidate, masked rd and cleaned final PC. [Numerical proof](Airbender/Proofs/ReducedMachine/NativeJumpNumerics.lean)
reuses unchanged actual scalar/carry helpers and certified actual cleanup region
only after those bindings. Output bounds/alignment require no source-range answer;
raw addition input bounds remain internal pending original initialization.
[Local roots](Airbender/Review/Circuits/ReducedMachine/JumpTheorems.lean) keep masks
explicit. Original decoded GPR/operands/PC return/target/clauses/execution remain next.

[Eight regressions](Tests/NativeReducedJump.lean) include six-assertion positives,
not complete117equation accepted native jumps. Ten exact parenta4a origins record
six new modules/tests; jump.rs is newly hash-pinned to unchanged v2 base,66native
sources. No old split masks/tables/acceptance transferred, no heavy certificate
replay/data regeneration, finding, production/Sail/dependency change or parity claim.

## Original decoded/initialized native jump results (7 November 2026)

[New original jump fields](Airbender/Review/Circuits/ReducedMachine/JumpDecoder.lean)
retain raw operands/x0/sign extension/JALfunct3 at actual33025/257masks. [Full
source recovery](Airbender/Proofs/ReducedMachine/NativeJumpDecoder.lean) derives
native fields and original JAL parity. [Return preservation](Airbender/Proofs/ReducedMachine/NativeJumpReturn.lean)
uses original public PC bounds/alignment before shared initialized ranges, avoiding
a source-range cycle. [Numerical assembly](Airbender/Proofs/ReducedMachine/NativeJumpDecodedResult.lean)
discharges every raw base/immediate prerequisite from actual initialized reads/
public inputs, then proves canonical return/write/target, wrap and low-bit cleanup.
[Short public results](Airbender/Review/Trace/Families/ReducedMachine/JumpResults.lean)
keep no source/range/parity/PC/result/state/table identity answer premise.

[Ten regressions](Tests/NativeReducedJumpDecoder.lean) reuse only old original
byte/stateful decoder evidence, not old native masks/tables/acceptance. They do not
certify complete nonempty117-equation accepted native jumps. Twenty-two exact
parent56origins record fourteen modules/tests. Native GPR/clauses/fetched execution,
common jump integration and physical/export/compiler/completeness stay open. No
production/native/Sail/data/dependency change, finding, issue assumption or parity.

## Original initialized native jump GPR history (7 November 2026)

[New jump port bindings](Airbender/Proofs/ReducedMachine/NativeJumpPorts.lean)
prove every original rs1/rs2/rd address from actual jump equations/decoded fields
before unchanged native history lemmas. JAL x0 inputs and JALR aliases remain.
[Initialized zero/code/register history](Airbender/Proofs/Trace/Families/ReducedMachine/JumpRegisterHistory.lean)
derives every Sail segment/read/write/final match/code/misa/decoder replay;
[one short root](Airbender/Review/Trace/Families/ReducedMachine/JumpRegisters.lean)
keeps public image/native acceptance/full decoding/aligned cells explicit with no
state/read/result/replay or initial CSR-read answer. No old split mask/constraint/
table/acceptance transfer. [Eight tests](Tests/NativeReducedJumpRegisters.lean)
include unchanged exact three-port/x0 mechanics, not complete positive native jumps.
Retained clauses/actual incoming PC preparation/fetched/common jump execution are next.
Ten exact parent0aaa origins record seven modules/tests; no native/data/dependency change.

## Local retained native jump retirement (7 November 2026)

[New assembly](Airbender/Proofs/ReducedMachine/NativeJumpExecution.lean) applies the
unchanged pure original retire_jump after actual regenerated native numerical/port
bindings. Incoming architectural PC is derived from preparation, source reads precede
aliased writes, and retirement projects to actual native after-state. Source bounds,
alignment and original CSR/landing-pad configuration remain internal initialized-trace
obligations; no public answer or whole/mixed jump execution claim. Six exact parentd80
origins preserve native/Sail/data/dependency pins, with no split native identity transfer.

## Initialized original native jump execution (7 November 2026)

[Public jump fetched execution](Airbender/Review/Trace/Families/ReducedMachine/JumpFetchedExecution.lean)
now derives source/alignment/local CSR prerequisites from original public image and actual
initialized history before the new native local retirement binding. Original replay,
native clock/PC chain, terminal PC/cell reads and finite successful stepping are conclusions.
[JumpISA](Airbender/Review/Helpers/Decoder/ReducedMachineJump.lean) restricts initial reads
to nonempty program misa and original-JALR Machine/mseccfg/MLPE-clear configuration;
every local CSR read is derived, empty/direct-only/GPR scopes stay narrow. [Regressions](Tests/NativeReducedJumpConfiguration.lean)
plus [empty paths](Tests/NativeReducedJumpFetched.lean) do not add complete positive native
jump acceptance. Eleven exact parent40 origins record six affected modules/tests. Common
mixed jump integration and physical/general fidelity/completeness remain open; no production/
Sail/data/dependency change, defect, issue assumption, axiom or parity claim.

## Mixed native JAL/JALR integration (7 November 2026)

[Supported original projection](Airbender/Review/Circuits/ReducedMachine/SupportedDecoder.lean)
now admits six profiles including jumps. [Exact profile PC/byte/query transport](Airbender/Proofs/ReducedMachine/NativeSupportedDecoder.lean)
precedes new actual jump preservation/addresses/PC/clause reuse. Original common public
membership derives return alignment before shared range induction, then common x0/
native-clock Sail/code/CSR/replay history derives all states and [fetched execution](Airbender/Review/Trace/Families/ReducedMachine/SupportedExecution.lean).
Initial misa applies only to BTYPE/JAL/JALR; initial Machine/mseccfg/MLPE-clear only to
JALR. All local reads follow history; ordinary/empty and branch-only scopes preserved.
[Six regressions](Tests/NativeReducedSupportedJumps.lean) add logical original JAL/ADD/
JALR sources/configuration, not full positive native mixed witnesses. Twenty-two exact
parent127 origins record ten affected Lean paths. No production/Sail/native/data/dependency
change, native defect, issue assumption, axiom or whole-machine/parity claim.

## Actual native word-only memory foundation (7 November 2026)

[New native references](Airbender/Review/Circuits/ReducedMachine/WordMemory.lean) keep
LW1025/SW16386 explicit. [All18native flags](Airbender/Proofs/ReducedMachine/NativeWordMemorySelectors.lean)
and actual32/33/113/114operand/port spaces are checked without standalone mask/table/
constraint transfer. Native base load.rs/store.rs are newly pinned unchanged. [Regressions](Tests/NativeReducedWordMemoryRouting.lean)
are conditional routing consequences, not complete native memory witnesses. Original
decoding/addresses/values/ROM/shadow/code-frame/initialized Sail/common support remain
open; no defect/issue assumption/new axiom/general fidelity or parity claim.

## Actual native word-memory address/table adaptation (7 November 2026)

[Fresh native access equations](Airbender/Proofs/ReducedMachine/NativeWordMemoryAccess.lean)
bind effective LW shadow/SW memory addresses, candidate/field mask versus unmasked
store write, actual queries18/23/24 and default/final PC selection. Unchanged pure
addition/shared native scalar/carry facts are reused only AFTER new74/75 memory
bindings; source/immediate bounds stay internal pending original public history.
[Complete new table certificates](Airbender/Proofs/ReducedMachine/NativeWordMemoryTables.lean)
prove every actual18/23/24row, including all1,048,576ROM rows and padding, using
symbolic stored blocks. No standalone masks/constraints/table identity is transferred.
Exact full-pool meanings derive native alignment, RAM-only stores and LW's active
ROM shadow even on RAM loads. All8retained public ROM words match the reference;
arbitrary original image/physical/Rust-public-export fidelity is still separate.
Seventeen exact parenta117origins record twelve affected Lean modules/tests, with
unchanged Word/periodic/pool helpers. [Regressions](Tests/NativeReducedWordMemoryAccess.lean)
are complete-region members, fixture/corruption checks and four-assertion positive
address slices, NOT full accepted native LW/SW. Original public decoding/initialized
memory/code-frame/Sail/common execution remain open; no defect/issue/new axiom/parity.

## Original native LW/SW public decoder adaptation (7 November 2026)

[New reduced projection](Airbender/Review/Circuits/ReducedMachine/WordMemoryDecoder.lean)
retains original LOAD(false,4)/STORE(4), raw/x0/negative immediates, actual reduced
1025/16386/tag2 and constructor-derived unused indices. [Native recovery](Airbender/Proofs/ReducedMachine/NativeWordMemoryDecoder.lean)
adapts checked original comparison full-sparse decoder machinery only after these
fresh query bindings; unchanged accepted18bit mask packing excludes holes/tail.
Eight exact parent5360origins record six new modules/tests, including original pure
word-memory constructor reference and independent public-byte fixture template.
No old standalone native masks/constraints/tables/acceptance is transferred. Public
logical image/decoder scope remains separate from native8word ROM/physical export,
initialized memory/code frames/Sail/common execution. No defect/issue/axiom/parity.

## Initialized actual native LW/SW numerical adaptation (7 November 2026)

[Fresh port bindings](Airbender/Proofs/ReducedMachine/NativeWordMemoryPorts.lean) derive
all3register/memory cell identities and native ROM-prefix word-cell store exclusion.
[Preservation](Airbender/Proofs/ReducedMachine/NativeWordMemoryPreservation.lean) reuses
only unchanged readonly metadata/shared time induction AFTER actual new LW ROM/RAM
and SW unmasked source-copy bindings. Original decoded rd/x0 masks only LW. Native
initialized read/write/terminal ranges now discharge all address addition/source/
immediate inputs. Fresh actual final-PC selection precedes unchanged PC+4/wrap proof.
[Public numerical effects](Airbender/Review/Trace/Families/ReducedMachine/WordMemoryResults.lean)
remain separate from original pre-row Sail memory/GPR state realization. Eighteen
exact parent648template/pure-helper origins record eleven new modules/tests, including
unchanged value induction/cell-address injection/Word arithmetic patterns; no old
standalone compiled masks/tables/acceptance is transferred. Independent shadow/
fixed-ROM byte construction, code-byte frames/Sail/common execution remain open.
No defect, issue assumption, new axiom, production fix or parity claim.

## Actual reduced independent-shadow initialization (7 November 2026)

[New actual reduced initializer](Airbender/Review/Helpers/Memory/ReducedMachineShadowImage.lean)
reuses unchanged PURE shadow classification/typed public seed/token/image definitions
from old word-memory helpers in NativeReducedFamily. [Pure seed proofs](Airbender/Proofs/Trace/Families/ReducedMachine/ShadowImage.lean)
derive projection/uniqueness/clocks/ranges. No old compiled masks/constraints/table/
acceptance is reused. Actual reduced preservation and shared time induction derive
all native numerical bounds/effects with independent shadow seeds. Ten exact parenteecb
origins record seven new modules/tests. Fixed native ROM/original byte construction,
projected row/Sail states/code-byte frames/retained clauses/common integration remain
open; logical public shadow seeds are not physical boot enforcement. Missing-byte/
independent-value/empty-boundary regressions are not nonempty native execution. No
native finding, issue assumption, axiom, production fix or parity is claimed.

## Actual native fixed-ROM byte construction (7 November 2026)

[New reduced ROM constructor](Airbender/Review/Helpers/Memory/ReducedMachineROMImage.lean)
extracts actual dataImage entries into unchanged PURE WordROM/UNIMP semantics and
constructs every original little-endian byte in four MiB. [Symbolic proofs](Airbender/Proofs/ReducedMachine/NativeROMImage.lean)
copy unchanged PURE read_rom_words_of_reads recursion and adapt the pure finite
insertion pattern; original read_word_of_bytes is reused after fresh native
fixture/padding binding. Eight-slot exact kernel and symbolic tail bridges avoid
native-table equivalence and broad definitional evaluation. Full original public
extraction/every aligned byte read/register/outside-byte preservation are derived.
[New actual LW connection](Airbender/Proofs/ReducedMachine/NativeWordMemoryROMRead.lean)
uses only freshly checked native address/lookup meanings, not old standalone masks,
columns/tables/acceptance. Ignored shadow values stay independent. Thirteen exact
parent0fe origins record six new modules/tests; no literal/native data is regenerated.
[Nine tests](Tests/NativeReducedROMImage.lean) cover original fixture/padding/frames,
independent shadow values/missing RAM bytes/corrupt native output. No complete
positive NONEMPTY117-equation accepted memory witness or retained LOAD/STORE/common
execution is claimed. Projected initialized memory/Sail states/byte-code frames and
general Rust/public-export/physical-ROM fidelity remain separate. No native finding,
issue assumption, production fix, new axiom, dependency change or parity claim.

## Actual reduced projected word-memory history (7 November 2026)

[Fresh native x0 law](Airbender/Proofs/Trace/Families/ReducedMachine/WordMemoryZeroRegister.lean)
uses actual mixed-port bindings and canonical native masked LW writes, retaining
SW memory writes. [Shadow projection](Airbender/Proofs/Trace/Families/ReducedMachine/ShadowHistory.lean)
copies unchanged PURE initial-zero/event-seed-origin arguments and instantiates
unchanged shared accepted matching/time induction/projected realization/row order
only AFTER this new actual law. [Actual port domains](Airbender/Proofs/ReducedMachine/NativeWordMemoryDomains.lean)
and effective-address roots follow new native canonical addresses, not old masks/
columns/tables/acceptance. ALLnative shadow events remain matched.

[Code frames/replay](Airbender/Proofs/Trace/Families/ReducedMachine/WordMemoryCodeHistory.lean)
reuse pure byte-frame/control-CSR/stateful indexed-construction lemmas after the
architectural public cell domain and code capacity derive full original windows.
Every projected state/segment/order/final matching/code frame/decoder replay is
constructed, never supplied. Twenty-one exact parent2917 origins record ten new
modules/tests. No old positive accepted native fixture is copied; original pure
RAM-write and actual-native empty regressions have their separate stated scopes.
Retained LOAD/STORE/configuration/normal/fetched/common memory execution and general
Rust/public/physical/compiler/crypto/completeness remain open. No native finding,
issue assumption, production fix, new axiom, dependency change or parity claim.

## Actual reduced original word-memory transfers (7 November 2026)

[Fresh projected ports](Airbender/Proofs/ReducedMachine/NativeWordMemoryProjectedPorts.lean)
instantiate unchanged PURE projected_native_read/write with NEWactual reduced
addresses/domains/readonly metadata. All kept reads and final write share one
original pre-state, including aliases/RAM refresh/OLDREAD. [Original transfers](Airbender/Proofs/ReducedMachine/NativeWordMemoryTransfers.lean)
reuse pure original word-write/read and x0 accessors after these bindings. Actual
ROM reads follow exact constructed native bytes transported through actual past
history, independently of ignored shadow values. Unmasked original load-to-x0
writes preserve the read; SW retains unmasked memory writes. No old standalone
compiled masks/columns/tables/acceptance or accepted positive fixture is transferred.

[Initialized assembly](Airbender/Proofs/Trace/Families/ReducedMachine/WordMemoryTransfers.lean)
reuses closed actual projected history/ranges/numerical proofs and derives every
local obligation from public construction. Fifteen exact parente6d4942 origins
record six new modules/tests. Eight regressions are conditional-native/original
accessor/complete-empty evidence, not full positive NONEMPTY117-equation accepted
LW/SW or retained instruction execution. Original LOAD/STORE virtual-memory/platform/
privilege/configuration/exception clauses, normal/fetched/common memory integration
and general Rust/public/physical/compiler/crypto/completeness remain open. No native
finding, issue assumption, production fix, new axiom, dependency change or parity.

## Actual reduced retained memory clauses (7 November 2026)

[Fresh actual platform bindings](Airbender/Proofs/Trace/Families/ReducedMachine/WordMemoryPlatform.lean)
combine actual native ROM bounds/initialized RAM address origins with meaningful
public ordinary-cell domains. Initial original CSR/PMP/PMA/HTIF configuration is
conditional on nonempty public memory programs; unchanged PURE history configuration
transport derives every local read/permission. [Retained clauses](Airbender/Proofs/ReducedMachine/NativeWordMemoryClauses.lean)
instantiate unchanged PURE virtual_word_read/virtual_memory_write/load_word/store_word
with the new actual numerical/transfer bindings, preserving original unmasked
load-to-x0 and unmasked SW. The reference-only dispatch retains original operands.
No old standalone native masks/columns/tables/acceptance/positive witness transfers.

Nineteen exact parent2c84a82 origins record seven new modules/tests. [Nine regressions](Tests/NativeReducedWordMemoryClauses.lean)
cover configuration/domain rejection, positive original ROM LW-to-x0/RAM SW and
complete empty native clauses without CSR inputs. They are not full positive
NONEMPTY117-equation accepted memory witnesses. Reference initial configuration/
ordinary domain are explicit inputs, not native enforcement/issue assumptions.
PC preparation/normal/fetched/common memory and general Rust/public/physical/
compiler/crypto/completeness remain separate. No native defect, production fix,
new axiom, dependency change or parity claim.

## Actual reduced original memory retirement and fetched execution (7 November 2026)

[Fresh native normal retirement](Airbender/Proofs/ReducedMachine/NativeWordMemoryRetirement.lean)
uses unchanged PURE cell read/write control frames on already checked actual
transfers. Original unmasked LW-to-x0 reads and actual SW RAM writes survive
preparation; original clause/normal_step_native/tick_pc reaches actual final state/
PC. [New stateful projected induction](Airbender/Proofs/Trace/ProjectedStatefulComposition.lean)
adapts unchanged PURE filtered composition and stateful first-step removal, with
no pure-decoder/replay answer premise. [Actual initialized composition](Airbender/Proofs/Trace/Families/ReducedMachine/WordMemoryComposition.lean)
derives all local obligations/order/PC chain/replay and architectural terminal
readers from exact public construction/native matching. All shadow tokens remain.

Twenty exact parent9306b53 origins record seven new modules/tests. Five regression
roots cover positive original normal LW/SW at every RV32 PC and complete empty
native fetched/terminal checks, not full positive nonempty117-equation memory
acceptance. Concrete reference CSR/source/ROM calculations are split from abstract
sequencing at default proof limits. No old standalone compiled native identity/
acceptance/positive witness transfers. Common mixed memory and general Rust/public/
physical/compiler/crypto/completeness/protocol/init/teardown remain separate.
No native finding, issue assumption, production fix, new axiom or parity claim.

## Seven-profile native initialized history (7 November 2026)

[UnifiedMode](Airbender/Review/Circuits/ReducedMachine/UnifiedDecoder.lean) wraps
unchanged SupportedMode plus LW/SW without narrowing existing ordinary public
source/execution scopes. Exact original entry/instruction/PC/data/ten-query
transport derives the selected checked native profile. New actual common
write/x0/domain rules feed ONE unchanged range induction and common initialized
projected Sail history; no old all-events-GPR memory frame is transferred.
The [public roots](Airbender/Review/Trace/Families/ReducedMachine/UnifiedHistory.lean)
derive every row state/segment, chronological order/final architectural matching,
ROM-byte/misa frames and stateful source replay while full native matching retains
all independent shadow tokens. No CSR or desired local answer is required.

Fifteen modules/tests record26 exact parent2cc4535 origins in
[provenance](artifacts/provenance.json), reusing PURE mapping/shadow/clock/history/
code helpers and checked actual native per-profile laws. Eighteen independent
original-source/conditional-native/complete-EMPTY regressions do not establish
NONEMPTY native memory/mixed acceptance. Common retained/normal/fetched execution
is NEXT, with narrowly constructor-activated memory reference configuration and
local CSR/ordinary-address/ROM bindings derived at actual common states. Arbitrary
logical public images remain distinct from exact NativeROM input construction.
No native/Sail/fixture/dependency change, defect/new axiom or parity is claimed;
worker/protocol/padding/terminal/init/teardown and physical/general refinement
boundaries remain open.

## Common original seven-profile execution (7 November 2026)

[The new common fetched root](Airbender/Review/Trace/Families/ReducedMachine/UnifiedFetchedExecution.lean)
closes original normal/fetched execution at the shared initialized projected
states, with actual terminal PC/architectural-cell readers. Fresh supported-row
filter identity and actual selected memory address origins precede reuse of
unchanged per-profile native execution/transfer/retirement laws. Constructor-
conditional initial reference configuration preserves ordinary/empty CSR freedom,
branch/JAL unrestricted misa and JALR-only security distinctions; actual mixed
past/control frames derive every local CSR/permission. Explicit exact NativeROM
mixed-memory input scope leaves older arbitrary ordinary public-code roots
unchanged; no arbitrary/native ROM identity is assumed.

Eight new modules/tests record17 exact parentf8df source origins. Eleven
configuration/domain/native-filter/complete-EMPTY regressions are not NONEMPTY
native memory/mixed witnesses. No production/native/Sail/fixture/dependency change,
native finding/issue assumption/new axiom or parity. Next inspect actual remaining
MOP/CSR/delegation paths and exact native special-CSR semantics before workers/
callers/accounting/protocol and padding/terminal/init/teardown. General Rust/public/
physical/cryptographic/completeness boundaries remain explicit.

The original checkout advanced externally to9bdfb988e0dd2ab83bf629d1e5c47f032f69030e
(parent964db88d3) during this checkpoint. Its exact two-path commit changes only
status and the private Keccak SplitSlotReduction cache proof (361-case computation
split into25 finite blocks, public whole-cache/slots contract unchanged). Exact
parent/path/blob/prefix/public-tail checks were read-only; the change is preserved,
not imported or adopted. The independent audit records observed liveHEAD9bdf and
its cumulative five-path delta separately from pinned b292 Git-object proofs,
native inputs and dependencies. Original checkout is tracked-clean with the same
five unrelated untracked paths; this task changed no original source/cache files.

## Actual reduced MOP arithmetic adaptation (7 November 2026)

[The new local root](Airbender/Review/Circuits/ReducedMachine/MOPTheorems.lean)
checks actual native MOP masks34819/133123/67587 and ADD/MUL/SUB minor order,
field relation including65536 squared=2 modulo Mersenne31, canonical output from
native subtraction underflow/range-checked remainder/Boolean carries, second GPR
routing and candidate/rdmask/default-PC bindings. Six new modules/tests record ten
exact parentb727 origins, reusing PURE field/borrow/projection patterns only after
fresh actual native bindings. Active mop.rs is byte-identical to nativebase67ee
and independently hashed in provenance; production/native/Sail/literal/fixture/
dependency inputs are unchanged.

Eleven reference/conditional-native/partial-positive regressions include fullRV32
source reduction and three seven-equation actual native slices, not full accepted
MOP witnesses or original execution. Native source words are not yet architectural
Sail pre-state reads. The upstream Zimop zero-result fallback is not adopted as
custom field arithmetic semantics; original public MOP decoding/custom reference/
initialized/common execution remain open. No defect/issue assumption/new axiom,
physical/completeness or parity follows. Next certify native special-CSR table
meaning and actual CSR/delegation bindings before fulfillment/accounting/protocol.
The deliberate v3 proofpinb292 remains unchanged; observed original checkout
9bdf/private Keccak proof activity is audited separately and not adopted.

## Actual reduced CSR fixture/request adaptation (7 November 2026)

[Complete actual special-CSR meaning](Airbender/Review/Circuits/ReducedMachine/Tables/CSRTheorems.lean)
now derives from stored affine intervals and six/two exceptional slots, followed
by full native-pool tag isolation. [Actual local CSR effects](Airbender/Review/Circuits/ReducedMachine/CSRTheorems.lean)
derive mask129/query/flags, supported keys, readonly GPR routing, bounded oracle/
candidate/rdmask/default-PC and imported request multiplicity/kind/ABI high offset.
Delegation returns zero; nondeterminism remains a bounded native oracle without
an identified original value/stream. Actual source-high lookup derives the masked
ABI bound, with no supplied source/read/result/request answer. In-cycle index3
is metadata, not fulfillment or global accounting.

Nine modules/tests record 18 exact parent-9bc PURE/helper/template origins. Fresh
actual bindings precede reuse; no old standalone compiled/acceptance identity or
arbitrary/native table equality is transferred. Active csr_with_delegation.rs is
byte-identical to base67ee and independently hashed. Thirteen fixture/table/
conditional-native/partial-positive tests are not full nonempty accepted CSR rows
or original public CSR/MOP decoding/custom/nondeterminism/privilege execution.
Those reference/initialized/common connections and workers/callers/accounting/
protocol/init/physical/completeness/parity remain open. Production/native/Sail/
artifact/public fixture/dependencies and prior seven-profile roots stay unchanged;
no native finding/issue assumption/new axiom. Deliberate v3 proofpinb292 stays
separate from observed original checkout9bdf/private Keccak proof activity.

The next worker adaptation must distinguish explicit fixture keys1988/1989 from
native source ABI constants Blake2=1991 and bigint=1994. Read-only byte comparison
of the three delegation-constant source files against base67ee passed. This is
source planning, not a Lean worker/runtime setup certificate or a finding; preserve
the imported fixture and assess actual native configuration before composition.

## Separate native runtime CSR regional certificate (7 November 2026)

Pinned unified reduced runtime allow-lists contain nondeterminism1984/Blake2CSR1991;
bigint1994 is a separate target. A new FV-only exporter mode calls unchanged native
CSR construction, materializes ONLY the4,096-row region and retains actual tag25/
offset1507585/public configuration. The existing5,771,521-row pool/8word/1988-1989
fixture and native circuit artifacts remain unchanged. No dependency/production
Rust/Sail/codec change or heavy unchanged region regeneration.

[Separate intake](Airbender/Import/RuntimeCSRSetup.lean) checks exact JSON/profile/
configuration/geometry/canonical literals and emits same-read bytes. [The regional
kernel certificate](Airbender/Proofs/ReducedMachine/NativeRuntimeCSR.lean) checks
all rows symbolically, and the short root derives exact key/support/delegate
meaning without any table equivalence or desired row output premise. Eight theorem
regressions, strict importer controls and the scoped native reproduction/negative
gate retain separate fidelity and semantics boundaries. Twelve exact parent-e05
origins and four pinned native ABI/runtime sources record the adaptation.

Runtime pool/query/accepted-trace/public original CSR/MOP decoding/reference/
issuance/worker fulfillment/accounting and physical/general refinement/completeness/
parity remain open. No old local CSR/seven-profile claim is transferred to the new
region. No native defect/issue assumption/new axiom. Deliberate v3pinb292 and the
separate originalcheckout9bdf/private Keccak audit remain unchanged.


## Runtime CSR full-pool and local query connection (7 November 2026)

[The explicit complete pool](Airbender/Review/Circuits/ReducedMachine/Tables/RuntimePool.lean)
keeps native5,771,521-row geometry, all thirteen original non-CSR literal regions
and the eight-word ROM/UNIMP tail, inserting separately exported runtime1984/1991
CSR data. The original1988/1989 pool remains unchanged. Fresh partition/tag proofs
recover this table's actual membership; unchanged regional identities reuse only
literal data results, never an old accepted-circuit or arbitrary-table equivalence.
Both native sign queries, all four dynamic queries/domains and [selected CSR effects](Airbender/Review/Circuits/ReducedMachine/RuntimeCSRTheorems.lean)
are now derived on this construction. Generic117-equation field proofs are reused
after fresh actual pooled query/support binding. Source-high lookup derives ABI
bounds; oracle/zero/rdmask/default-PC and all imported request fields stay explicit.

Eight new modules/tests record eleven exact parent195 origins. Sixteen regressions
include all CSR pool rows and narrow actual selected-constraint exclusions; they
are not full positive nonempty native CSR witnesses. There is no original public
CSR source/decoder/rd-x0, initialized Sail read/retirement, request clock/issuance,
nondeterminism stream/custom reference, worker/converse/accounting/protocol claim.
The retained ROM scope is a logical construction, not universal runtime program/
Rust/public/physical setup refinement. Bigint1994 remains a separate target. Existing
seven-profile roots and all prior native/Sail/import/export/artifact/fixture/dependency
inputs remain unchanged. No native defect/issue assumption/new axiom or parity.


## Original CSR public decoding and runtime composition (7 November 2026)

[The native CSR projection](Airbender/Review/Circuits/ReducedMachine/CSRDecoder.lean)
retains original CSRReg CSRRW with raw rs1/rd, readonly rs2=x0, unsigned 12-bit
index/mask129/funct3=1. Fresh source/field proofs use complete stateful sparse/padded
public construction and actual native packing to recover all ten fields, original
constructor and canonical index/high-zero. No standalone shift/CSR operand restriction
is transferred to the reduced target. The unchanged CSR operation definition is
byte-pinned to base67ee; general Rust decoder-export refinement stays open.

[The short source/runtime roots](Airbender/Review/Trace/Families/ReducedMachine/CSRDecoder.lean)
derive the local mask from original public decoding, then apply the checked runtime
CSR effect theorem through an explicit setup-only trace constructor. All rows,
public boundaries and tokens remain. No desired mask/source/read/range/result/
request/state/PC/worker answer or table equivalence is supplied. Seven modules/tests
record eleven exact parent3d25 origins. Fourteen original-byte/conditional-native
regressions include both nonzero raw operands, unsigned4095 and a CSRRS hole; narrow
original Zicsr rewrites keep all default limits and original generated code unchanged.

This CSR-only source connection does not add initialized/common seven-profile CSR
execution, original privilege/custom/nondeterminism semantics, native request clock/
issuance, worker/converse/accounting/protocol or universal runtime public/physical
setup. Arbitrary original public bytes are not identified with the retained ROM.
No complete positive nonempty accepted CSR witness, native defect, issue assumption,
new axiom, production/dependency change or parity is claimed.


## Initialized native CSR GPR history (7 November 2026)

[Fresh CSR port bindings](Airbender/Proofs/ReducedMachine/NativeCSRPorts.lean)
derive all three original GPR cells from actual native CSR equations and full
source/query identities before PURE read/write/history lemmas apply. Actual oracle
scalar bounds, candidate/rdmask and original rd-zero flag derive write preservation;
then unchanged single time induction bounds all actual reads/writes/terminal tokens.
The actual x0 law retains both readonly refreshes and OLDREAD/alias participation.
Fresh GPR event-space laws derive every byte/misa frame and source replay, followed
by complete chronological GPR transfer states/segments/final matching. Public generic
and concrete runtime-pool roots provide no desired per-row answers or table identity.

Eleven modules/tests record eighteen exact parentde55 origins, copying unchanged
PURE/template portions and using fresh actual bindings before reuse. Seventeen
regressions retain port/alias/initialized/x0 bounds, CSR-shaped positive three-port
mechanics and complete EMPTY native runtime history at every RV32 PC with terminal
x0/empty original bytes/no CSR availability. They are not full positive nonempty
117-equation/22-lookup accepted CSR witnesses, original CSR execution or worker
composition. Runtime setup construction retains every row/token/public boundary.

GPR realization memory frames do not describe unproved delegated worker RAM effects.
Original CSR/custom/nondeterminism/privilege semantics, PC retirement, request clock/
issuance, fulfillment/converse/accounting/protocol/terminal/init, independent ROM-
shadow/general public/physical setup/refinement/crypto/completeness remain separate.
No native source/artifact/import/export/Sail/fixture/dependency change, native defect,
issue assumption, new axiom or parity. Existing mixed seven-profile scopes unchanged.


## Original CSR source/request observations (7 November 2026)

Five new modules/tests record eleven exact parentbff728 source origins. Checked
pure Word canonicality and existing CSR initialized GPR history/ranges compose
with actual native runtime request equations and original unsigned CSR query
identities. [CSRRequestHistory](Airbender/Review/Helpers/Memory/ReducedMachineCSRRequests.lean)
retains full native history and the same segment states while attaching original
rs1 full RV32 value/limbs/request ABI observations. No new native input/artifact,
whole-table equivalence, old accepted-circuit transfer or desired local answer.
Natural high-half division precedes M31 cast. Eight boundary/reference/conditional
native tests pass; no full positive nonempty CSR witness or original CSR execution.
Imported offset3 is not issuance/accounting. Original CSR/reference/PC, actual
caller/compiler/protocol clock binding and Blake2 workers remain separate. No v3
finding/assumption/fix is copied; zero established native defects and no parity.


## CSR row-local caller projection (7 November 2026)

Five new modules/one extended test record eleven exact parent4baa source origins.
Actual imported request92/94/some93/offset3 and clock2/3 bind row-local caller tuple
(w2+3,w3); unchanged pure write_time is reused only after actual initialized native
bounds/alignment. Native advancement/port metadata and real chronological history
derive bounded nonzero strict local clocks and the multiplicity-selected projection
with original row origin/request kind1991/ABI bounds. No caller stream, desired
per-row answer, whole-table equivalence or old accepted-circuit transfer.

Five unchanged compiler/prover files newly byte-pinned67ee document actual native
stage2 tuple and stage3 sequence-HIGH contribution. General Rust/protocol timestamp
normalization/enforcement remains unproved, distinct from logical local projection.
Eight boundary/filter/order/zero-clock tests and one complete accepted EMPTY runtime
projection retain all tokens/no CSR premise; no full positive NONEMPTYCSR witness,
original CSR execution, worker converse/fulfillment/accounting or v3 F03 finding.
No production/native/Sail/artifact/import/export/fixture/dependency modification,
native defect/issue assumption/fix/new axiom/whole-machine/parity claim.


## Selected unrolled caller argument normalization (7 November 2026)

Five modules/tests record six exact parent76847 origins, using prior actual caller
interfaces/tuple metadata and regression patterns. Fresh source review found the
unrolled prover passes literal sequence0 to the generic cache; both constructor
and cache are newly byte-pinned67ee. Aggregation/constants already pinned/rechecked.
Imported geometry and zero contribution are kernel-checked as reviewed references,
not general Rust refinement or a change to production behavior.

[Argument identities](Airbender/Proofs/ReducedMachine/NativeCSRArgument.lean) preserve
native witness scaling versus gamma/literal additions for every tau in any
commutative target ring/base-field embedding. Unit specialization identifies exact
pre-compression keys; public trace assembly retains actual caller row origins/full
original source/native history and no desired per-row answers. Nine independent
scalar/reference tests include arbitrary-challenge collisions; no injectivity or
physical evaluation assumption. Stage2 auxiliary/global worker ledger, native
worker artifacts/constraints/fulfillment/converse/accounting, original CSR execution,
Rust/field/LDE/physical/crypto/completeness/parity remain open. No native defect,
issue assumption/fix/new axiom/production/artifact/import/export/dependency change.

## Native Blake2 worker intake and local control checkpoint (7 November 2026)

The [fresh native worker](Airbender/Review/Circuits/Blake2Worker/NativeArtifact.lean)
is now independently generated from the unchanged selected extended-control
constructor at trace2^20, runtime CSR1991. Its352 equations/871 variables and296
lookups (2 scalar,86 timestamp,208 fixed queries) are all emitted into original
Clean, in small blocks. The [reproduction gate](scripts/check_native_blake2.py)
checks source/configuration, all old exporter branches, repeat bytes and the
separately preserved historical worker JSON: parsed layouts are exactly equal.
No historical worker acceptance or arbitrary table equivalence is transferred.

[Same-read ABI intake](Airbender/Import/Blake2Worker.lean) retains processing
multiplicity/ABIhigh/write timestamp, registers10/11/12,24 state writes and16
message reads, all43 old reads/timestamps, and the full raw stage2/indirect-clock
source. Existing main-circuit intake still rejects active workers. Complete local
Clean constraints use an explicit four-field modeled setup; native worker fixed
pool semantics and memory/protocol acceptance are separate obligations.

[The control root](Airbender/Review/Circuits/Blake2Worker/ControlTheorems.lean)
derives all13 actualBoolean flags, input/output high-half bounds<8192 and x12
written low-half zero from accepted local constraints, without a desired result,
range, read, processing flag, schedule or worker-success premise. Exact native
linear packing equations and imported coordinates are kernel checked. Twelve
[regression roots](Tests/NativeBlake2Worker.lean) include five positive16-equation
control slices;24 [intake controls](Tests/NativeBlake2WorkerImport.lean) preserve
native redundant Mersenne31 modulus-as-zero encoding and reject residues above it.
These are not complete positive352-equation/296-lookup worker witnesses. In
particular, zero/multiple round flags in a partial slice are not v2 defect evidence.

NEXT certify actual worker fixed tables and native memory/processor constraints,
ABI alignment/address/ranges, processing multiplicity, clock/control schedules,
state/terminal and issued/unissued acceptance, then connect caller/worker
auxiliary/accumulators, fulfillment/converse/accounting and unified protocol.
Do not repeat closed caller argument/source/history or worker intake/control
results. Valid round masks, original/delegated reference effects, F02/F03/F04
retests, original CSR/MOP/common execution, physical/general Rust/compiler/JSON/
field/LDE refinement, cryptography/completeness and parity remain open. Bigint1994
is outside this selected runtime. Zero established native defects; no production
fix, new issue assumption, axiom or whole-machine claim.

## Native Blake2 complete fixed-pool checkpoint (7 November 2026)

The selected worker now has a separate [actual native fixed export](artifacts/setup/blake2-fixed-native.json),
with all344384 stored rows and native offsets0/65536/65600/65856/82240 for tags4/26/27/28/29.
The [scoped reproduction gate](scripts/check_blake2_fixed.py) calls the unchanged native driver,
checks every row independently, repeats exact bytes, preserves all prior exporter branches
and rejects five malformed CLI/layout inputs. Production code, previous artifacts/fixtures,
dependencies and the original checkout remain unchanged.

[Strict literal intake](Airbender/Import/Blake2Fixed.lean) validates the complete selected profile,
geometry and canonical blocks, emitting same-read bytes and five separate literal units.
The [constructed native-shaped pool](Airbender/Review/Circuits/Blake2Worker/Tables.lean)
retains actual region order. [Short public roots](Airbender/Review/Circuits/Blake2Worker/TablesTheorems.lean)
derive tag/operand domains and XOR semantics for all five regions from actual membership.
Byte semantics reuse existing proofs only after exact newly exported literal-column binding;
the worker byte offset0 is distinct from the old main pool offset1. No whole-table equivalence
or old accepted-worker semantics is supplied.

All64 XOR3,256 XOR4,16384 XOR7 and262144 XOR9 outputs are kernel checked against actual literals.
The [generic window checker](Airbender/Proofs/Blake2Worker/BlockCertificates.lean) is proved sound
for the unchanged finite block checker. Calculations use small units, symbolic dense-array
geometry and transparent data; allocation failures led to splitting calculations, with no
raised heartbeat, recursion, memory or watchdog limits. [Theorem regressions](Tests/NativeBlake2Fixed.lean)
cover every actual row's participation, native geometry, positive small regions, absent tags,
operand bounds and forged outputs. Nineteen [import controls](Tests/NativeBlake2FixedImport.lean)
check complete same-read bytes and malformed geometry/canonical literals; altered valid data
is accepted as data, without certifying its semantics.

This closes the worker's fixed-pool foundation. It does not yet project the208 compiled fixed
queries into those roots or establish full352-equation/296-lookup positive worker witnesses.
NEXT derive actual compiled query, ABI address/alignment/range, processing multiplicity,
all43 memory/clock, initialized control/schedule/state/terminal and request-worker acceptance
connections, then auxiliary/accumulator, fulfillment/converse/accounting and unified protocol.
Main Trace.Accepted still has no global worker ledger. Caller observations and reference
argument algebra are not enforcement; derived main GPR frames cannot cross unproved worker actions.
F02/F03/F04 require complete accepted native evidence, and no defect follows from these gaps.
Original CSR/MOP execution, general Rust/compiler/JSON/physical/field/LDE refinement,
cryptography, completeness, padding/terminal/init/teardown and parity remain open.
Bigint1994 remains outside this selected runtime. Zero established native defects;
no production fix, issue assumption, new axiom or whole-machine claim.

## Native Blake2 complete lookup-effects checkpoint (7 November 2026)

The [short concrete-pool theorem](Airbender/Review/Circuits/Blake2Worker/QueriesTheorems.lean)
now derives all296 local lookup observations from complete352-equation/296-lookup
original Clean acceptance on the actual344384-row worker pool. No expected query,
tag/profile, input/read, bound, result, process flag, clock, state, schedule,
request, worker answer or table identity is a premise.

[Separate same-read query intake](Airbender/Import/Blake2Queries.lean) reuses the
unchanged complete worker parser and copies the unchanged coefficient/expression
emitters. [Query references](Airbender/Review/Circuits/Blake2Worker/QueryArtifact.lean)
retain every actual2 scalar,86 timestamp and208 fixed expression plus the complete
source bytes. A kernel equality binds those bytes to the original worker intake;
all existing importers/artifacts/exporters/native sources and data are unchanged.
[Projection calculations](Airbender/Proofs/Blake2Worker/NativeQueryProjection.lean)
extract native sublists, and independent kernel syntax equalities bind the new
observables to actual accepted operations. No previous accepted-worker semantics
or arbitrary table equivalence is transferred.

The [observable model](Airbender/Review/Circuits/Blake2Worker/Queries.lean) retains
native fixed order: eight18-query groups,32 extended-control queries and32
finalization queries. Actual tag binding derives80 byte XOR,16 XOR3,16 XOR4,
40 XOR7 and56 XOR9 queries, with both canonical operand bounds, canonical output
bounds and exact natural XOR results, using only already certified actual pool
membership. These static compiled-query counts are not worker issuance counts.
The2 scalar bounds apply to actual scaled-pointer expressions, and86 bounds
apply to actual timestamp-difference expressions. They are not raw pointer/read
or old/processing timestamp bounds; those require separate native relations.

Thirteen [regression roots](Tests/NativeBlake2Queries.lean) check same source,
complete geometry/static tag counts, original query/scalar/clock coordinates,
wrong-result/oversized-query/unit-pointer rejection under complete local native
acceptance, and positive scalar/difference slices. The difference slice explicitly
retains raw time600000 with zero differences; it is not a complete accepted worker
or native defect. Six [query-intake controls](Tests/NativeBlake2QueriesImport.lean)
check same-read data, complete counts, physical/logical source mapping, changed
canonical data retained without certifying semantics, missing queries and invalid
columns. No full positive nonempty352-equation/296-lookup worker witness is claimed.

NEXT derive actual ABI alignment/address/read ranges, processor multiplicity,
all43 memory/clock read/write/readonly-refresh relations, initialized control/
round schedules/reference/state/terminal, and accepted caller/worker/auxiliary/
accumulator connections before fulfillment/converse/accounting/unified protocol.
Main Trace.Accepted still has no global worker ledger, and main GPR byte/RAM
frames cannot cross unproved worker actions. Original CSR/MOP execution and
F02/F03/F04 broader-path retests remain open. Native Rust/compiler/JSON/physical/
field/LDE refinement, cryptography, completeness, terminal/padding/init/teardown
and parity remain separate. No new defect, issue assumption, axiom or production
fix; FINDINGS and all earlier selected execution scopes remain unchanged.

## Native Blake2 ABI-local memory laws (7 November 2026)

The [short actual-pool root](Airbender/Review/Circuits/Blake2Worker/MemoryTheorems.lean)
derives canonical pointer alignment and all43 ABI-bound Boolean borrow/difference
laws from complete352-equation/296-lookup original Clean acceptance. There is no
supplied raw read bound, pointer value, process flag, timestamp, order, state,
schedule, request, worker answer or table identity.

[Memory observables](Airbender/Review/Circuits/Blake2Worker/Memory.lean) flatten the
actual imported descriptors in native order, retaining all43 old reads, both
readonly register descriptors and25 written accesses. [Kernel bindings](Airbender/Proofs/Blake2Worker/NativeMemoryProjection.lean)
identify every read-time pair and all43 Boolean borrows with actual equations125..167
and the original86 compiled difference expressions. Each old timestamp is compared
with the actual imported processor time740/741 and multiplicity0. These are field
difference laws and bounds; raw-clock ranges, chronological matching and Boolean
processing multiplicity are not inferred.

[Canonical inverse arithmetic](Airbender/Proofs/Blake2Worker/NativeMemory.lean)
derives actual state-pointer low2=128 times its scaled-query canonical value,
and message-pointer low100=64 times its scaled-query canonical value. Thus the
canonical lows are aligned by128/64 and below8388608/4194304 respectively. The
native scaled-query bounds alone do not establish16bit initialized read ranges,
16bit address-carry behavior, allowed architectural pointers or worker ROM/RAM
semantics. The public theorem discharges all pure inverse/capacity calculations;
no expected bound or architectural read value is an input.

Twelve [regressions](Tests/NativeBlake2Memory.lean) preserve descriptor/read-only/
old-read geometry, last-clock coordinates, reject misalignment, oversized pointers,
non-Boolean borrows and oversized differences under full local native acceptance,
and check maximum scalar slices. A positive scalar slice explicitly admits65536,
above a16bit limb; it is not a complete accepted worker row or native defect.
All earlier query/table/intake/source/native artifacts remain unchanged.

NEXT establish initialized worker read/write/address ranges and full43-access
memory matching, raw clocks/processing multiplicity, input/control/round schedules,
reference/state/terminal and actual caller-worker auxiliary/accumulator acceptance
before issuance, fulfillment/converse/accounting/unified protocol. Allreadonly
refreshes/oldreads/tokens must survive that connection. Main Trace.Accepted has no
worker ledger, and main GPR byte/RAM frames cannot cross unproved delegated actions.
Full positive nonempty worker witnesses, original CSR/MOP execution, F02/F03/F04
broader-path retests, padding/init/teardown and general Rust/compiler/JSON/physical/
field/LDE/crypto/completeness/parity remain open. Zero established native defects;
no production fix, issue assumption, axiom or whole-machine claim.

## Native Blake2 normalized processing conventions (7 November 2026)

The [short processing root](Airbender/Review/Circuits/Blake2Worker/ProcessingTheorems.lean)
now derives Boolean multiplicity and inactive memory zeroing at a separate,
explicit logical acceptance boundary. [The contract](Airbender/Review/Circuits/Blake2Worker/Processing.lean)
requires the complete unchanged352-equation/296-lookup native body on the actual
pool AND the individual normalized processing-convention polynomials. It supplies
no active flag, expected read/value/bound/result/clock/state/order/schedule/request,
worker success or issued stream. These extra polynomials are not claimed to follow
from the352 JSON equations alone.

The [pinned native quotient function](../../prover/src/prover_stages/unrolled_prover/quotient_parts/every_row_except_last.rs)
uses half-domain factor tau: Boolean term(tau*m)*(tau*m-1), and mask term
(tau*m-1)*tau*value. [Source references](Airbender/Review/Circuits/Blake2Worker/Processing.lean)
retain both scale factors. [Proof calculations](Airbender/Proofs/Blake2Worker/NativeProcessing.lean)
bind original Clean acceptance exactly to the individual source-reference terms
at unit normalization. This is a reviewed source/algebra contract for ordinary
rows, not formal Rust/M31Complex/LDE refinement, challenge separation, physical
quotient acceptance or last-row enforcement. No physical evaluation point is
assumed to have unit scaling.

[A separate descriptor intake](Airbender/Import/Blake2Processing.lean) reuses the
unchanged strict worker parser. [Same-read observables](Airbender/Review/Circuits/Blake2Worker/ProcessingArtifact.lean)
retain all source bytes, actual processor multiplicity,225 masked columns and
all226 physical-memory logical variables. The walk follows native register/
indirect order: ABIhigh, processing time, every oldtime/readvalue and actual
written value. Selected geometry has no nontrivial address-carry fields. Kernel
source equality, unique coverage and an exact memory-column permutation prove
that no selected memory field is omitted. All43 oldreads, both readonly register
refreshes and25 written accesses remain; multiplicity zero derives all226 memory
columns zero. Processing multiplicity is now derived at this stronger logical
interface, while its physical enforcement remains open.

Twelve [regression roots](Tests/NativeBlake2Processing.lean) cover exact source/
geometry/partition, normalized-contract rejection of non-Boolean multiplicity and
nonzero inactive clocks/reads/oldtimes/writes, positive convention-only slices
and scaling boundaries. Multiplicity one permits arbitrary convention-masked
values; non-unit scaled coordinates need not themselves be Boolean. Neither
slice asserts complete accepted worker/body matching or a native defect.
Six [intake controls](Tests/NativeBlake2ProcessingImport.lean) check identical
source, complete unique mask/physical maps, changed canonical ABI data retained
without its coverage certificate, and invalid memory columns. The new intake
gate is serial; unchanged native/importer/heavy certificates are not replayed.

NEXT bind actual worker memory keys/tokens and full43-access matching, initialized
active read/write/address ranges, raw clocks, padding-token cancellation and real
caller-worker auxiliary/accumulator acceptance before issuance/fulfillment/
converse/accounting/unified protocol. Multiplicity-one zero-clock exclusion is
not proved. Main Trace.Accepted still has no worker ledger; main GPR byte/RAM
frames cannot cross unproved delegated actions. Control/round/reference/state/
terminal, full positive worker witnesses, F02/F03/F04 broader-path retests,
original CSR/MOP execution, global padding/init/teardown/general Rust/compiler/
JSON/publicexport/preprocessing/physicalROM/field/LDE/crypto/completeness/parity
remain open. This is a new logical native-convention acceptance boundary, not an
issue-handling restriction, fix, new axiom or whole-machine claim; FINDINGS and
zero-established-defect status are unchanged.

## Native Blake2 unused memory-key agreement (7 November 2026)

[Short key/product roots](Airbender/Review/Circuits/Blake2Worker/MemoryKeysTheorems.lean)
now derive unused-row reference-key agreement and equality of every memory factor
from the existing stronger normalized processing contract. No expected address,
key/read/value/bound/result/clock/order/state/schedule/request/worker answer,
table identity, inverse, nonzero denominator or compression injectivity is supplied.
This is not full logical memory matching or physical permutation enforcement.

[Key observables](Airbender/Review/Circuits/Blake2Worker/MemoryKeys.lean) construct
all43 actual register/indirect descriptors. Kernel [source bindings and proofs](Airbender/Proofs/Blake2Worker/NativeMemoryKeys.lean)
retain native descriptor order, every old read and25 explicit written values.
Both readonly register accesses and16 readonly message accesses still have write-side
timestamp refreshes. ALL43 write sides use the same imported processor clock740/741;
no per-port offset, temporal order, deduplication or alias rewrite is invented.
The native key register indicator is literal1 for registers and0 for indirect RAM,
with six challenge roles address low/high,time low/high,value low/high. Its conversion
to the existing main history's different address-space coding remains separate.

Reviewed stage-two address references preserve canonical-to-u16 truncation,
offset carry into high and explicit high-overflow failure. Selected quotient
unit references retain raw field low+offset/high for actual empty-carry metadata.
They are not silently equated on active rows. The three unchanged native source
files [stage2 helpers](../../prover/src/prover_stages/stage2_utils.rs),
[43-access walk](../../prover/src/prover_stages/unrolled_prover/stage_2_ram_shared.rs)
and [worker timestamp driver](../../prover/src/prover_stages/stage2.rs) were byte-compared
to nativebase67ee and separately pinned. Existing quotient/constants pins are unchanged.
These are reviewed source references, not general Rust/M31 representation/compiler/
LDE/physical verifier refinement; no physical point is assumed unit-normalized.

Derived inactive memory zeros imply actual base/time/read/write fields zero.
Every selected offset is kernel-bound below128. Thus all43 stage-two address
references succeed and agree with the quotient unit addresses; their read/write
precompression tuples are equal. The complete43-factor write/read products are
equal in any target ring/embedding/challenges, before division. Zero factors are
allowed; this alone proves no accumulator transition, ratio1, global matching,
worker issuance/converse/accounting or multiplicity-one zero-clock exclusion.

Twelve [regressions](Tests/NativeBlake2MemoryKeys.lean) retain actual register/base/
offset/OLDREAD/readonly clock coordinates, check all43 keys and products, source
u16 carry/high-overflow boundaries and a wide-pointer reference mismatch. The
wide-pointer65536 case and unaligned carry case are not complete accepted worker
witnesses or native defects; active agreement still needs initialized16bit reads
and source-derived alignment/no-carry. A zero-factor check prevents treating
product equality as an invertible ratio. No importer/exporter/native artifact,
literal, fixture, dependency, production or original-checkout source changed.

NEXT derive actual worker auxiliary/accumulator acceptance and full43-access
memory matching/initialization, active read/write/address ranges/raw clocks,
active key normalization, reference/control/round/state/terminal effects and
caller-worker issuance/fulfillment/converse/accounting/unified protocol. Preserve
every readonly refresh/OLDREAD/alias/token and the actual common worker clock.
Do not carry main GPR byte/RAM frames across unproved delegated actions. Full
positive accepted worker witnesses, original CSR/MOP execution, v3F02/F03/F04
broader-path retests, global padding/init/teardown/general Rust/compiler/JSON/
publicexport/preprocessing/physicalROM/field/LDE/crypto/completeness/parity remain
open. FINDINGS and zero-established-defect status are unchanged; no issue
assumption, production fix, new axiom or whole-machine claim.

## Native Blake2 auxiliary acceptance and memory balance (7 November 2026)

[Short row and trace roots](Airbender/Review/Circuits/Blake2Worker/AuxiliaryTheorems.lean)
now derive a division-free memory product balance from explicitly modeled native
auxiliary polynomials. This closes the selected worker's normalized auxiliary
relations and domain boundaries; it does not establish full memory matching or
a caller-worker ledger. The old body-only and processing-only interfaces remain
unchanged.

A [separate strict intake](Airbender/Import/Blake2Auxiliary.lean) validates every
selected stage2 key, group, pair count, inactive family and width after the unchanged
complete worker parser. [Typed quartic columns](Airbender/Review/Circuits/Blake2Worker/AuxiliaryColumns.lean)
keep these slots separate from the871 body logical variables. The complete
same-read artifact binds processor1064, all43 memory slots1068..1236 at stride4,
grand-product1240, extension offset44 and width1244. Kernel [bindings and calculations](Airbender/Proofs/Blake2Worker/NativeAuxiliary.lean)
retain complete source-byte identity and every memory slot. No auxiliary column
is silently mapped to a body variable; existing artifacts/literals/intakes are unchanged.

The newly byte-pinned unchanged [global worker quotient](../../prover/src/prover_stages/stage3.rs)
provides reviewed source references for the processor relation, all43 memory steps,
adjacent-row grand-product update and first/last boundaries. Worker literal1991
and gamma remain outside witness scaling. The source initializes the within-row
chain from the inverse half-domain factor; its unit-normalized value is literal1,
not a supplied previous-row accumulator. Every old read, readonly refresh,
explicit write, alias and the common worker write clock remains in the43 factors.

[The explicit logical acceptance](Airbender/Review/Circuits/Blake2Worker/Auxiliary.lean)
contains complete body/processing acceptance plus individual unit-normalized
native auxiliary polynomials. The full domain has1048575 ordinary rows and a last
row carrying the claimed grand product. Adjacent grand values come from the same
auxiliary trace; initial value1 and terminal equality to the public proof claim
are separate native boundary polynomials. The already pinned prover driver commits
that claim and returns it in the proof. No terminal claim1, expected worker stream,
per-row source/read/value/bound/key/result/state/clock/order/schedule/count/request/
worker answer, inverse, nonzero factor or compression injectivity is supplied.

A pure telescope derives the actual processor denominator equation, the complete
43-factor row balance and the complete-domain product balance against the claimed
terminal accumulator. Zero factors are allowed: these equations alone do not imply
multiset equality, invertible ratios, initialized reads, active key refinement,
raw-clock bounds, zero-clock exclusion, issuance, fulfillment, converse or accounting.
This is a reviewed source/algebra and normalized logical-acceptance boundary,
not general Rust/M31Quartic/compiler/LDE/physical verifier/challenge-separation
refinement or a claim that physical points have unit normalization.

Fourteen [theorem regressions](Tests/NativeBlake2Auxiliary.lean) preserve all43 slots,
full source/domain, worker literal scaling, public boundary and zero-factor limits.
Fourteen [executable controls](Tests/NativeBlake2AuxiliaryImport.lean) reject changed,
overlapping, incomplete or unsupported auxiliary geometry; canonical changed body
equations remain data without proof transfer. Pure/reference/conditional cases
are not complete positive nonempty accepted worker witnesses or native defects.
The new intake gate is serial and bounded; unchanged heavy certificates are not replayed.

NEXT connect the actual delegation sum/public accumulator and global caller-worker
acceptance, full43-token matching/initialization and active read/write/address/raw-clock
bounds before active stage2/quotient key refinement, worker reference/round/state/terminal
execution or accounting/unified protocol. Do not carry main GPR byte/RAM frames
across unproved delegated actions. Full positive worker witnesses, v3F02/F03/F04
broader-path retests, original CSR/MOP execution, padding/init/teardown, general
Rust/compiler/JSON/publicexport/preprocessing/physicalROM/field/LDE/crypto/
completeness/parity remain open. FINDINGS and zero-established-defect status are
unchanged; no production fix, issue assumption or project axiom is introduced.

## Native delegation sum and public claim component (7 November 2026)

[The worker sum and statement-component roots](Airbender/Review/Circuits/Blake2Worker/DelegationTheorems.lean)
now derive the selected worker's ordinary-row auxiliary sum from its native
polynomial boundary relation, then connect it to the unified statement's additive
claim component. Main proof claims remain opaque returned observables. No caller
stream, issued ledger, fulfillment, converse or accounting claim follows yet.

[The generic sum interface](Airbender/Review/Helpers/Memory/DelegationSum.lean)
models the reviewed native zero/last-point divisor: the auxiliary polynomial plus
claimed-sum times domain-generator times X is divisible by X times X-minus-last-point.
The primitive domain, actual sampled auxiliary values and polynomial degree below
the domain size remain explicit representation inputs. The ordinary-row sum is
not an acceptance premise. [The calculation](Airbender/Proofs/Memory/DelegationSum.lean)
derives value0 at zero, negative claimed sum at the last point, and zero total
sum by exchanging the finite polynomial-support/domain sums and cancelling
nonconstant geometric sums. It then derives the ordinary-row sum equals the
claimed scalar. [The short helper root](Airbender/Review/Helpers/Memory/DelegationSumTheorems.lean)
uses this calculation without evaluating a million domain points.

[Worker proof observables and acceptance](Airbender/Review/Circuits/Blake2Worker/Delegation.lean)
retain the complete previous body/processing/43-memory-auxiliary/full-domain
acceptance. The sum polynomial samples the actual separate quartic processor
slot1064 over the imported1048576-point domain. [Native worker proofs](Airbender/Proofs/Blake2Worker/NativeDelegation.lean)
connect the derived sum to that proof's returned delegation claim. The native
multiplicity-one auxiliary equation also derives a nonzero denominator and its
inverse value; inactive poles are not excluded and no inactive auxiliary is
silently dropped from the sum. Every old read, readonly refresh, write factor,
alias and common worker clock remains in the unchanged underlying acceptance.

Three unchanged nativebase sources were byte-compared and separately pinned:
[Divisor construction](../../prover/src/quotient_evaluator.rs),
[Verifier claim/quotient boundary](../../verifier/src/lib.rs), and
[Unified statement](../../full_statement_verifier/src/unified_circuit_statement.rs).
The already pinned global/unrolled quotient drivers use the same linear sum
interpolant. The unified scalar component starts at0, adds each returned main
claim, subtracts each returned worker claim and checks0. The explicit component
interface retains that source fold plus accepted selected-worker proofs; generic
fold normalization and derived worker sums yield equality of the main-claim sum
and all worker-row auxiliary sums. It does not identify main claims with actual
caller rows, enforce dispatch/setup/challenge correspondence physically, or
model the separate configured-capacity bound. Bigint1994 remains outside this
selected worker scope.

These are reviewed source/polynomial and normalized logical-acceptance boundaries.
FFT/interpolation, native M31Quartic/domain construction, degree/physical LDE,
quotient/challenge separation and general Rust/compiler/verifier refinement remain
separate. No physical evaluation is assumed unit-normalized, desired row sum,
expected stream/per-row source/read/value/range/result/clock/state/schedule/count/
request/worker answer, table identity or compression injectivity is supplied.
Scalar equality alone is not multiset equality or a native defect.

Eight [generic sum regressions](Tests/NativeDelegationSum.lean) include a positive
two-slot polynomial, endpoint values, wrong-claim/constant/degree-bound rejection
and an endpoint-only high-degree alias boundary. Ten [worker/component regressions](Tests/NativeBlake2Delegation.lean)
retain actual slot/domain, exact scalar folding, a nonmatching scalar cancellation,
inactive-pole limits and complete conditional worker/component roots. Pure/reference
and conditional cases are not full positive nonempty accepted352-equation/296-lookup
worker witnesses, physical attacks, v3F02/F03/F04 evidence or native defects.
No intake/exporter/artifact/literal/fixture/dependency/production source changed;
unchanged native/intake controls and heavy certificates are not replayed.

NEXT bind the actual main caller auxiliary slot92 and native sum polynomial to
complete caller-row acceptance, then connect initialized callers and native global
capacity/dispatch/challenge/public boundaries before fulfillment/converse/accounting.
Main auxiliary92 is a separate quartic slot, not body logical variable92. Full43-token
matching/initialization, active read/write/address/raw-clock bounds and key refinement,
worker control/round/reference/state/terminal effects and complete positive witnesses
remain open. Main GPR byte/RAM frames cannot cross unproved delegated actions.
Original CSR/MOP execution, global padding/init/teardown, broader-path findings
retests, physical/general refinement/cryptography/completeness/parity remain open.
FINDINGS and zero-established-defect status are unchanged; no production fix,
issue-handling assumption or project axiom is introduced.

## Native caller auxiliary sums and row balance (7 November 2026)

[The main caller sum and caller-worker row roots](Airbender/Review/Circuits/ReducedMachine/DelegationTheorems.lean)
now connect the native main proof's returned delegation claim to all ordinary
caller-row auxiliary values. The stronger normalized scalar component consequently
equates actual full main-row and selected worker-row auxiliary sums. It is not a
caller/worker matching, issued-stream, fulfillment, converse or accounting result.

[The separate selected main intake](Airbender/Import/ReducedAuxiliary.lean) reuses
unchanged full main parsing and validates all18 stage2 keys, every group/pair,
active initialization/state/masking families, fresh117-equation/142-variable body
geometry, extension offset12 and width124. Historical119-equation intake rejects
without any equivalence or coverage transfer. [Typed main columns](Airbender/Review/Circuits/ReducedMachine/AuxiliaryColumns.lean)
retain request92, memory96/100/104, state108, masking112, initialization116 and
grand-product120. Reusing the unchanged quartic-column type transfers no worker
acceptance or semantics. Request auxiliary92 is a different type and row space
from body logical variable92, the actual request multiplicity.

[The same-read artifact](Airbender/Review/Circuits/ReducedMachine/AuxiliaryArtifact.lean)
and [kernel bindings/calculations](Airbender/Proofs/ReducedMachine/NativeCallerDelegation.lean)
identify the complete unchanged main source bytes, all selected geometry and the
native8388608-point domain. No native artifact, literal, fixture, old intake,
exporter, dependency or production source changed. All native source pins remain
unchanged; no native generation or closed heavy certificate is replayed.

[The explicit caller interface](Airbender/Review/Circuits/ReducedMachine/Delegation.lean)
checks the complete original Clean body on the actual constructed runtime-CSR pool
for every8388607 ordinary row, the individual normalized native caller auxiliary
relation and the native sum-polynomial divisor with actual slot92 samples. It does
not supply execute-one flags, a CSR profile, initialized reads, desired sum or
per-row source/value/range/result/key/state/clock/order/schedule/count/request/worker
answers. The existing logical execution trace requires every listed row active;
it is deliberately not substituted for this full native domain. Active history,
padding and filtering connections remain separate. Every ordinary auxiliary
value stays in the sum, including multiplicity-zero rows.

The denominator reuses the already checked selected-constructor sequence-zero
caller normal form and actual precompression request/time observations. No public
chunk sequence is added again, and no other constructor/chunk is assumed zero.
Source-reference auxiliary equations derive the actual observation-key denominator
relation and exclude poles when the observed multiplicity is one. Inactive poles
are not excluded and their auxiliary contributions are not silently discarded.
The unchanged polynomial calculation derives the main claim from all row values;
the sum is not a premise. Shared gamma/ABI/low-time/high-time roles map directly
to the selected worker challenge structure. The exact native add-main/subtract-worker
claim component then derives full caller-row sum equals full worker-row sum.

This is an additional reviewed normalized polynomial/logical component interface.
Physical Rust/FFT/M31Quartic/domain/LDE/quotient/challenge-separation and global
sequence/dispatch/setup/capacity/public-proof correspondence remain open. The full
native state/memory permutation and initialization auxiliaries are retained as
geometry, not newly interpreted as enforced matching. Scalar equality is not
multiset equality or a cardinality bound. No physical point is assumed unit-scaled,
no desired worker stream or table-equivalence premise is introduced, and no main
GPR byte/RAM frame crosses an unproved delegated action.

Twelve [theorem regressions](Tests/NativeCallerDelegation.lean) retain complete source,
all auxiliary families/roles, shared challenge positions, active/inactive pole
limits and complete conditional row/sum/component roots. Eighteen [executable intake controls](Tests/NativeReducedAuxiliaryImport.lean)
check native source/geometry, historical rejection, changed/overlapping/missing
active groups, width/offset/unknown/remainder failure, and canonical changed-body
data without semantic proof transfer. These are conditional/reference checks,
not full positive nonempty accepted main/worker witnesses, physical attacks,
v3F02/F03/F04 evidence or native defects. The new intake gate is serial and bounded.

NEXT connect initialized actual caller observations to this full-domain auxiliary
component with faithful padding/filter/history and native global capacity/dispatch/
sequence/challenge/public boundaries before stream matching, fulfillment, converse
or accounting. Full43-token worker matching/initialization, active read/write/address/
raw-clock ranges and key refinement, worker control/round/reference/state/terminal
effects and complete positive witnesses remain open. Original CSR/MOP execution,
global padding/init/teardown, broader-path findings retests, physical/general
refinement/cryptography/completeness/parity remain open. FINDINGS and zero-established-
defect status are unchanged; no production fix, issue assumption or project axiom.

## Configured native worker capacity and caller component (7 November 2026)

[The selected capacity roots](Airbender/Review/Circuits/Blake2Worker/CapacityTheorems.lean)
derive the actual number of multiplicity-one worker rows below Mersenne31's
modulus, with at most2048 selected worker proofs. The native counter adds
configured1048575-row slots for each returned proof. It is a capacity counter;
no issued-request count or expected worker stream is supplied. The public32-bit
stream count and actual output-list length also derive u64 counter headroom.

[The explicit source-reference interface](Airbender/Review/Circuits/Blake2Worker/Capacity.lean)
retains every returned worker observation: sequence0, type1991, equality to
configured setup caps, shared memory/delegation challenges, and complete existing
normalized worker acceptance. Both security dispatch labels remain explicit.
[Unchanged native dispatch](../../full_statement_verifier/src/imports.rs),
[its constants include](../../full_statement_verifier/src/constants.rs), and
[the generated parameter bytes](../../circuit_defs/setups/generated/all_delegation_circuits_params.rs)
are newly independently compared with exact nativebase Git objects and pinned.
The first configured tuple has type1991/capacity1048575, matching the already
pinned constructor's domain2^20 minus its last row. Setup caps remain opaque
configured data checked for equality; no physical setup derivation, dispatch
execution, ProofOutput serialization or Rust refinement is inferred.

[The calculations](Airbender/Proofs/Blake2Worker/NativeCapacity.lean) first derive
all Boolean multiplicities from the existing individual processing polynomials.
An abstract finite-indicator proof then identifies the actual body multiplicity
sum with the natural active count. The aggregate sum's canonical field value
is exactly that count because the configured counter is below2147483647.
The arithmetic is symbolic; no million-row evaluation or limit increase occurs.
The capacity and count cover the selected one-family loop component. Other
configured families and the full transcript/security/setup statement remain
separate, as do active clock/initialized-read bounds and physical enforcement
of the normalized worker acceptance contract.

[The configured caller/worker interface](Airbender/Review/Circuits/ReducedMachine/ConfiguredDelegation.lean)
uses the SAME returned worker list for these checks and the native additive
claim fold. [The short composition root](Airbender/Review/Circuits/ReducedMachine/ConfiguredDelegationTheorems.lean)
reuses the closed full caller-row/worker-row scalar-sum proof and combines it
with the derived capacity and exact multiplicity count. Every ordinary auxiliary
value remains, including inactive poles. There is no inactive-auxiliary filter,
new ledger, table-equivalence premise or per-row read/value/range/result/key/
clock/state/schedule/count/request/worker-success answer. A bounded scalar
identity still does not establish multiset equality, issuance, fulfillment,
converse or accounting. No main GPR byte/RAM frame crosses unproved worker actions.

Fourteen [regressions](Tests/NativeBlake2Capacity.lean) check selected geometry,
exact2048/2049 field boundaries, distinct security labels, u64 headroom, an empty
counter, finite positive/nonboolean indicator boundaries, retained metadata and
complete conditional capacity/multiplicity/caller-component roots. These are
pure/reference/conditional checks, not complete positive nonempty native worker
or main witnesses, physical attacks, v3F02/F03/F04 retests or defect evidence.
Seven new modules record eleven exact parent origins; three unchanged native
source pins bring the total to96. Prior intake/exporter/artifact/literal/fixture/
production/dependency/original-checkout/cache bytes remain unchanged; no new
intake gate, native generation or closed heavy-certificate replay is needed.

NEXT connect initialized actual caller observations to the full-domain component
through faithful padding/filter/history and establish full43-worker-token native
matching/initialization. Derive active read/write/address/raw-clock ranges and
stage2/quotient key refinement from that matching before issuance or accounting.
Worker control/round/reference/state/terminal effects, full positive witnesses,
original CSR/MOP execution, global padding/init/teardown and general physical/
cryptographic refinement/completeness/parity remain open. The field bound does
not make scalar compression injective. FINDINGS and zero-established-defect
status are unchanged; no production fix, issue assumption or project axiom.

## Native public memory boundary and worker products (7 November 2026)

[The public boundary root](Airbender/Review/Circuits/ReducedMachine/MemoryBoundaryTheorems.lean)
connects every returned selected worker's complete ordinary-row memory products
to the native unified statement's returned main grand claims and public register/
PC contributions. This is a reviewed source-reference multiplicative component;
it does not establish full token matching or initialized worker reads.

[The interface](Airbender/Review/Circuits/ReducedMachine/MemoryBoundary.lean)
retains all32 initial and final register keys, including x0. The native register
helper uses initial value0/time0 for every register and literal register-indicator
coefficient1; all six shared memory-challenge roles remain. Public final values
and PC are full32-bit words split by natural16-bit limbs before casting to the
field. Public timestamps remain observed base-field limbs: no19-bit range or
raw-u32/native Mersenne31 representation refinement is assumed. The public x0
check concerns its value; its timestamp is retained and is not forced zero.

The separate PC-state factor uses PC low with coefficient1, PC high and both
timestamp challenges, plus gamma. The pinned native initial PC is0 and its
initial timestamp is4, split at19bits. This source boundary is distinct from
arbitrary initial-PC logical execution roots and does not change their scope.

[The native helpers](../../prover/src/definitions/mod.rs) compute initial-product
multiplied by the successful inverse of each final boundary product. The explicit
accepted-operation relations retain both inverse results; their equations derive
boundary denominator nonzeroness. Individual worker factors are not assumed
nonzero. [The unchanged constants re-export](../../common_constants/src/lib.rs)
and the helper source are newly compared with exact nativebase Git objects and
pinned, bringing native-source pins to98. Existing register-count, challenge-index,
initial-PC/timestamp and unified-statement pins remain unchanged. These source
pins are not a general Rust/M31Quartic/raw-word codec proof.

[Calculations](Airbender/Proofs/ReducedMachine/NativeMemoryBoundary.lean) normalize
the actual native fold of main grand claims, worker grand claims, register
contribution and PC contribution, checked equal to1. Successful inverse equations
clear the two boundary denominators. The unchanged worker43-chain/full-domain
proof then derives each worker claim times all read factors equals all write
factors. Pure list transport combines every returned proof and all43 accesses on
all1048575 ordinary rows without evaluating that domain, dividing by worker
factors, cancelling zero factors or assuming compression injectivity.

Main claims remain opaque FULL returned grand-product observables, including the
state/masking/initialization families; they are not relabeled RAM-only ratios or
identified with actual main-row memory constraints. Configured worker metadata,
shared challenges, complete normalized worker acceptance and all readonly/OLDREAD/
write factors remain. The accepted global component supplies no desired worker
stream, token matching or per-row read/value/range/key/clock/state/schedule/count/
request/result answer. Scalar product balance remains weaker than precompression
multiset equality, initialization, active ranges, issuance or accounting. Native
Rust/ProofOutput/FFT/LDE/quotient/transcript/cryptographic extraction and other
statement configurations/checks remain separate. No main GPR/RAM frame crosses
an unproved delegated action.

Fourteen [regressions](Tests/NativeMemoryBoundary.lean) cover all32 factors,
full-RV32 splitting before field reduction, initial PC time4, retained x0 time7,
a positive BOUNDARY-HELPER-only case, both pole rejections, factor roles, a scalar
product collision, and complete conditional worker/global product roots. They are
pure/reference/conditional checks, not complete positive native main/worker
witnesses, physical attacks, v3F02/F03/F04 retests or defects. Four new modules
record nine exact parent origins and27 new explicit roots. All prior intake,
exporter, artifact, literal, fixture, dependency and production bytes remain;
no new importer gate, native generation or closed heavy-certificate replay.

NEXT bind actual main memory/state/masking/initialization auxiliary relations and
public grand boundaries to these returned main claims before full main/worker
token matching and initialized histories. Faithful full-domain caller padding/
filter/history, full43-token worker matching, active read/write/address/raw-clock
bounds and stage2/quotient key refinement remain open. Worker round/reference/
terminal effects, complete positive witnesses, original CSR/MOP execution,
global initialization/teardown, physical/general refinement/cryptography/
completeness/parity remain open. FINDINGS and zero-established-defect status
are unchanged; no production fix, issue assumption or project axiom.

## Native main auxiliary chain and joint memory products (7 November 2026)

[The main and joint product roots](Airbender/Review/Circuits/ReducedMachine/MainAuxiliaryTheorems.lean)
now derive returned main grand claims from the actual selected full-domain
memory/state/masking/initialization chain. The stronger source-reference
component consequently combines actual main and worker row products with the
public32-register/PC boundary. The earlier boundary-only root remains unchanged;
its main claims are opaque until this additional main contract is supplied.

[The interface](Airbender/Review/Circuits/ReducedMachine/MainAuxiliary.lean) uses
unchanged imported main port, state, initialization and typed auxiliary metadata.
[Kernel bindings and calculations](Airbender/Proofs/ReducedMachine/NativeMainAuxiliary.lean)
retain all three accesses, both readonly refreshes, third-port OLDREAD and actual
write, register/RAM indicator polarity, address limbs and clock offsets0/1/2.
The selected native chain is memory96/100/104, state108, masking112,
initialization116, then adjacent-row grand120. Its per-row chain starts from
literal1 at unit normalization, not the previous row's grand accumulator.
Quartic slots remain separate from body logical variables; request quartic92 is
not body92. No fallback port or dropped address is used.

This order follows the already pinned [main driver](../../prover/src/prover_stages/unrolled_prover/stage3.rs)
and [native helper functions](../../prover/src/prover_stages/unrolled_prover/quotient_parts/every_row_except_last.rs).
The existing importer already validates and emits all required descriptors,
including initialization address126/127, teardown value128/129, time130/131 and
padding borrow125. No parser, exporter, artifact, literal, dependency or native
source changes; all98 source pins remain. Generic polynomial helpers and product
telescopes are reused unchanged. No worker acceptance or whole-table semantics
are transferred to main rows by an equivalence assumption.

The explicit accepted-row component checks complete original Clean117-equation/
22-lookup body acceptance on the actual constructed runtime pool, all three
memory auxiliary equations, PC-state equation, actual execute-masking equation,
six native initialization-padding equations, unmasked initialization/teardown
accumulation and the adjacent grand equation. The trace retains every8388607
ordinary row and native first-grand1/last-public-claim equations. It supplies no
execute-one/Boolean-execute premise, desired read/value/range/key/clock/state/
schedule/count/request/result or expected product. Existing initialized active
logical execution interfaces are not substituted for this physical row domain.

Let D denote the three memory read factors times the incoming PC-state factor,
and N the three writes times the outgoing PC-state factor. The source masking
relation derives masked-accumulator times D equals e*N+(1-e)*D for the actual
field execute e. The polynomial identity remains valid as pure field algebra, without
cancelling factors or inserting an active-row filter. Original body equation31
derives execute0-or1 from full native acceptance and gives actual N-versus-D
mask selection; Booleanity is a conclusion, not a premise. Initialization and teardown
remain unmasked, with zero initial RAM value/time and actual teardown value/time
at the SAME imported address. The resulting row read factor is teardown*D;
the write factor is initialization*(e*N+(1-e)*D). The observed zero padding-borrow
branch derives all six initialization/teardown fields zero from its real native
padding equations, not from supplied per-row field values.

A symbolic full-domain telescope derives main-grand-claim times all row read
factors equals all row write factors. The same returned main list now feeds the
unchanged global worker/public-boundary component. Pure product transport gives
joint main/worker/public product balance without dividing by or cancelling any
worker/main factor and without inverse/nonzero/injectivity premises. Every
inactive row and auxiliary contribution remains. This does not establish
precompression token matching, initialized history, active-row history filtering,
active bounds/clocks, stage2 key refinement, issuance or accounting.

Sixteen [regressions](Tests/NativeMainAuxiliary.lean) check chain/initialization
geometry, readonly timestamps, actual third write, raw indicator/state fields,
unmasked initialization, active/inactive mask slices, a nonboolean MASK-ONLY
slice, a nonunit scaling boundary, and complete conditional padding/main/joint
roots. These are metadata/pure/reference/conditional checks, not complete positive
native main/worker witnesses, physical attacks, F02/F03/F04 evidence or defects.
Four modules record ten exact parent origins and31 explicit roots. No new
importer gate, native generation or closed heavy-certificate replay is needed.

The new interface remains an explicit source-reference normalized polynomial
component. Physical Rust/M31Quartic/FFT/LDE/quotient/challenge separation,
ProofOutput/dispatch/setup fidelity and full initialization range/sorting/window
checks remain separate. No physical point is assumed unit-scaled. Faithful
full-domain caller padding/filter/history, coupling additive and multiplicative
proof observations, full main/worker token matching and initialized active
read/write/address/raw-clock bounds remain open. Original CSR/MOP execution,
worker round/reference/terminal effects, complete positive witnesses, physical
initialization/teardown, general refinement/cryptography/completeness/parity remain
open. FINDINGS and zero-established-defect status are unchanged; no production
fix, issue assumption or project axiom. Main GPR/RAM frames still cannot cross
unproved delegated actions.

## Lossless native memory-key/token bridge (7 November 2026)

[The short bridge roots](Airbender/Review/Circuits/ReducedMachine/MemoryTokenTheorems.lean)
connect reviewed native precompression keys to the unchanged original Clean
memory-token encoding. Native register indicator1/RAM0 becomes Clean space0/1
through FIELD complement1-minus-indicator before canonical Nat pair coding.
Separate raw address/value limbs and both timestamp fields remain. A decoder
left inverse proves address/key injectivity without Boolean selectors,16-bit
values/addresses or19-bit clock premises. Arbitrary Nat tokens need not lie in
the encoder image. Pure two-way list-permutation transport preserves duplicates;
it asserts no native matching relation and extracts none from a scalar identity.

[The proof](Airbender/Proofs/ReducedMachine/NativeMemoryTokens.lean) binds ALL
three actual imported main read/write tokens to these keys. Both readonly
refreshes, third OLDREAD, raw mixed indicators and unmasked third write remain;
there is no execute/CSR filter or per-row expected key/value/range/time premise.
All43 worker raw quotient keys retain the same lossless representation and exact
challenge-factor products, including inactive rows. Their stage2 u16-truncated
addresses are still separate from raw quotient addresses. Main and worker
factor transport introduces no cancellation or compression-injectivity premise.

Seventeen [regressions](Tests/NativeMemoryTokens.lean) check raw nonboolean
indicators, wide field limbs, the restricted encoded image, radix-packing aliases,
duplicate multiplicity, actual main OLDREAD/readonly timestamps, all43 worker
slots, public x0 timestamps and scalar collisions. These are pure/reference/
metadata/conditional checks, not complete positive native witnesses, attacks,
F02/F03/F04 evidence or defects. Four modules record eleven exact parent origins
and37 explicit audit roots. All prior5227 audit roots and source bytes remain.
No parser/exporter/artifact/literal/fixture/native pin or dependency changes;
no native generation or closed heavy replay is needed.

The affine address-space coding gap is closed. Actual native precompression
matching/extraction, initialized main/worker history, faithful full-domain padding/
active filtering, active read/write/address/raw-clock ranges, stage2 refinement,
same-main-proof additive/multiplicative coupling and issuance/accounting remain
open. Single-challenge sums/products plus capacity still do not imply matching.
No new accepted-matching or issue-handling assumption is introduced. Physical
Rust/field/LDE/quotient/compiler/JSON/crypto refinement, worker reference/terminal
effects, original CSR/MOP execution, initialization/teardown and parity remain
separate. FINDINGS and zero-established-native-defect status are unchanged.

## Same-main-proof argument coupling (7 November 2026)

[The joint root](Airbender/Review/Circuits/ReducedMachine/MainArgumentTheorems.lean)
now derives delegation scalar balance, full main/worker/public memory-product
balance and worker capacity/no-wrap conclusions from the SAME main observations
and configured worker list. [One observation record](Airbender/Review/Circuits/ReducedMachine/MainArguments.lean)
holds one actual body-row function, one typed auxiliary trace and distinct returned
grand/delegation claims. Its caller view reuses those exact functions by definition;
there is no supplied equality between independently chosen row traces or claims.
Every ordinary main/worker row and inactive factor/auxiliary contribution remains.

[Projection proofs](Airbender/Proofs/ReducedMachine/NativeMainArguments.lean)
derive the two unchanged complete parent accepted components and reuse their
checked conclusions. Shared memory/delegation challenges, native global accumulator
checks, configured metadata/capacity and public boundary remain explicit. No
expected read/key/range/clock/state/result, issued stream, active filter or token
matching premise is added. The already pinned [selected main driver](../../prover/src/prover_stages/unrolled_prover/mod.rs)
returns both fields from the same stage-two output; its native67ee bytes were
freshly compared. No new native source pin or production change is required.

Seven [regressions](Tests/NativeMainArguments.lean) check identical body/auxiliary
projections, retained claim/full-domain fields, distinct observed accumulator
values, the actual shared auxiliary sum and complete conditional joint effects.
The distinct-claim record is observation data only, not an accepted main/worker
witness. Four modules record ten exact parent origins and eleven explicit roots.
No old acceptance interface or proof is weakened; no intake/artifact/exporter/
literal/dependency change, native generation or heavy replay.

This closes observation coupling at the selected delegation-present normalized
source-reference interface. Rust Option/ProofOutput parsing, physical commitments/
transcript extraction, dispatch and quotient/refinement remain separate. Concurrent
scalar/product balances and capacity still do not imply precompression matching,
initialized reads, issuance, fulfillment or accounting. Next: faithful full-domain
main/43-worker key/token matching/extraction and public initialization, then
padding/active history filtering, active ranges/raw clocks and stage2 key agreement.
Original CSR/MOP and worker reference execution, initialization/teardown, physical/
general refinement/crypto/completeness/parity remain open. No findings, issue
assumptions, production fixes or project axioms; main frames cannot cross unproved
delegated actions.

## Complete native CSR caller fixture and body-padding limit (7 November 2026)

[The body-scope roots](Airbender/Review/Circuits/ReducedMachine/BodyPaddingTheorems.lean)
now provide independently constructed CSR1991/x0 witnesses satisfying ALL117
actual equations and ALL22 lookups on the complete constructed runtime pool.
[The transparent witness certificate](Airbender/Proofs/ReducedMachine/NativeCSRPositiveWitness.lean)
uses four small polynomial blocks and each individual lookup; no partial slice,
old fixture acceptance or table equivalence is substituted. Both execute1 and
execute0 observations pass this complete BODY, retaining request multiplicity1,
kind1991, ABI-high0 and imported offset3. Consequently inactive-request filtering
is NOT derivable from body acceptance alone. This is a precise proof-interface
limit, not an accepted global attack, native defect or issue-handling assumption.
Decoder/auxiliary/full-domain/global enforcement still require separate analysis.

[The complete nonempty active fixture](Tests/NativeCSRPositive.lean) additionally
checks original Clean active/state/memory acceptance with all three x0 aliases:
OLDREAD clocks0/4/5 and readonly/write refreshes4/5/6, PC0-to4 and time4-to8.
Independent original public bytes encode CSRRW x0,1991,x0. Full sparse/padded
stateful decoding and actual Sail zero-x0/PC initialization feed the unchanged
initialized caller theorem, deriving original source/GPR/request history and
caller projection at clock7. No expected source, range, key, order, state or
worker answer is a public theorem premise. The existing active logical trace
interface rejects execute0; it is not substituted for the full physical domain.
Changing the actual request multiplicity alone rejects native body acceptance.

This is a complete positive native BODY and initialized logical caller example;
it does NOT execute the original CSR clause, privilege/nondeterminism/custom
semantics, delegated worker or full physical proof. Its one-word public program
is independent of the retained eight-word native ROM fixture. The inactive
example establishes ONLY the stated complete-body limitation, not decoder,
auxiliary, global or worker acceptance. It supplies no F02/F03/F04 evidence or
confirmed defect. FINDINGS and zero-established-native-defect status are unchanged.

Four modules record ten exact parent origins and16 explicit roots, including ten
regression roots. All prior5275 audit roots/source bytes remain. No parser,
exporter, artifact, old fixture, native source pin, dependency, production Rust/
circuit or original Sail change; no native generation or closed heavy replay.
Faithful full-domain padding/active filtering, actual main/43-worker token matching/
extraction/public initialization, active bounds/raw clocks/stage2 refinement and
issuance/accounting remain open. Never drop inactive auxiliary poles or factors,
assume execute1 for every physical row, or replace these obligations with a desired
ledger. Original CSR/MOP and worker execution, physical/general refinement,
initialization/teardown, cryptography/completeness/parity remain separate.
