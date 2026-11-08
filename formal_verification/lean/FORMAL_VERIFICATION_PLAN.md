# Circuit formal verification plan

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


Backport the current formalization to Airbender v2 on dev while preserving its
small review surface, directory roles, pinned references and explicit trust
boundaries. This document is a snapshot of pending work; checked coverage lives
in [Verification status](VERIFICATION_STATUS.md), and accepted counterexamples
and unresolved connections live in [Findings](FINDINGS.md).

## User priority: native reduced machine (2026-10-21)

Work directly on the [regenerated combined reduced circuit](Airbender/Review/Circuits/ReducedMachine/NativeArtifact.lean)
and its original Sail execution connection now. The six standalone-family
checkpoints are reusable components; they do not establish reduced-machine
coverage. Do not complete remaining standalone/subword work first. The
[native reduced path](../../cs/src/machine/ops/unrolled/reduced_machine_ops.rs)
uses LoadOp with SUPPORT_LESS_THAN_WORD=false and StoreOp with the same flag
false. Subword retirement is therefore not a prerequisite for this machine.
This explicit user priority supersedes the older ordinary-family-first order
in the historical checkpoints below.

**The reduced machine now has conditional fetched-execution soundness for mixed
selected original shifts, ADD/ADDI/SUB/LUI/AUIPC, XOR/OR/AND register/immediate,
SLT/SLTU/SLTI/SLTIU, all six conditional branches and JAL/JALR rows. Full combined-operation
coverage remains open.** The active
[regenerated native target](Airbender/Review/Circuits/ReducedMachine/NativeArtifact.lean)
is independently reproducible from unchanged pinned Rust: 117 equations,
142 variables and 14 fixed regions. The original [historical artifact](Airbender/Review/Circuits/ReducedMachine/Artifact.lean)
retains 119 equations, 141 variables and 13 regions; no equivalence is assumed.
The complete current native fixed pool and explicit public fixture are imported,
and original Clean acceptance now derives both actual sign/high-byte queries.
Full combined row effects and execution remain pending. See the
[current adaptation snapshot](V3_ADAPTATION.md). Selected main/worker auxiliary geometry is separately typed and checked; unmodeled protocol semantics remain open.

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

## Current selected-unrolled caller argument checkpoint (7 November 2026)

[The argument root](Airbender/Review/Trace/Families/ReducedMachine/CSRArgument.lean)
now preserves initialized caller/source history while connecting actual row origins
to reviewed native stage2 and quotient key/denominator formulas. The selected
unrolled prover passes literal sequence0; actual trace2^23/three-port cache shift6
is checked and its sequence-high contribution is zero. Quotient witness terms
scale by tau; gamma/literal offset stay outside. Polynomial normal form holds for
all tau; unit specialization gives exact pre-compression caller-key agreement,
not an assertion that all physical protocol points have tau=1. Nine reference/
scalar regressions include non-injective arbitrary challenge compression.

This closes the selected constructor-sequence calculation and per-row algebra NEXT
below. General Rust/field/LDE/physical enforcement remains separately scoped;
do not repeat closed caller/source/clock/key algebra. NEXT actual native Blake2
worker artifact/configuration/ABI/constraints, request-worker acceptance, stage2
auxiliary/accumulator connections and fulfillment/converse/accounting/unified
protocol. Main Trace.Accepted has no worker ledger; do not invent issued-request/
worker-success/count/schedule/state premises. Bigint remains outside this selected
runtime. Original CSR/custom/nondeterminism/privilege/PC/common execution, delegated
RAM/terminal/padding/init/physical/general refinement/crypto/completeness/parity
remain open; all existing fixtures/execution/input scopes stay unchanged.

## Current CSR local caller projection checkpoint (7 November 2026)

[Row-local caller projection](Airbender/Review/Trace/Families/ReducedMachine/CSRCallers.lean)
is now checked from full original CSR source membership, public logical seeds,
accepted runtime constraints/matching and tracked alignment. Exact request metadata
and clock2/3 produce (w2+3,w3); initialized ranges/alignment derive bounded nonzero
slot3 clocks, strictly after native GPR slots0/1/2 and before next machine clock.
Actual multiplicity filters chronological rows; selected kind1991/ABI-high bounds
and strict caller-clock order are derived. Full source/request/native history keeps
ALL rows/tokens/segments. Eight new regressions plus complete EMPTY runtime caller
projection pass, not nonempty accepted CSR witnesses or original CSR execution.
This closes row-local tuple/order/projection work; do not repeat it.

NEXT bind actual native protocol key/sequence normalization and request/worker
acceptance before enforced issuance or worker-ledger claims. Pinned native stage2
reads the intermediate-state clock plus metadata offset; quotient stage3 also has
a circuit-sequence HIGH contribution. Its representation/normalization is not
proved by this local model; neither blindly append it nor infer a defect from
source-shape differences. Then actual Blake2 ABI/worker constraints/issued-unissued
behavior/fulfillment/converse/accounting/unified protocol. Main Trace.Accepted has
no worker ledger. Original CSR/custom/nondeterminism/privilege/PC retirement and
common integration, delegated RAM/physical/general refinement/crypto/completeness/
terminal/init/parity remain open. Bigint stays outside this selected runtime.

## Current CSR source/request observation checkpoint (7 November 2026)

[Original-source request observations](Airbender/Review/Trace/Families/ReducedMachine/CSRRequests.lean)
now strengthen the same initialized chronological GPR history. Actual native
source35/36 is the canonical full RV32 original pre-state rs1 word; actual imported
request multiplicity/kind/optional ABI-high follow the original unsigned CSR index
and natural high half, with division before field cast. Full history/tokens/states/
segments/order/source replay/byte-misa frames are retained, no local source/range/
read/request/state answer is public. Eight boundary/reference/conditional-native
regressions pass, not full positive nonempty accepted CSR witnesses or execution.
This closes the source-to-request observation NEXT below; do not repeat it.

NEXT inspect actual native compiler/protocol request-clock and caller projection
boundaries. Main Trace.Accepted has row activity/constraints/state/memory matching,
not a worker request ledger; metadata offset3 is not actual issuance/scheduling.
Derive observations honestly and bind real request enforcement before calling them
issued or composing workers. Original CSR/custom/nondeterminism/privilege/PC
retirement, delegated RAM actions, actual Blake2 fulfillment/converse/accounting,
protocol/terminal/init/general public/physical/refinement/crypto/completeness/parity
remain open. Keep the existing runtime versus old-fixture and memory/shadow scopes.

## Current initialized CSR GPR history checkpoint (7 November 2026)

[CSR value bounds](Airbender/Review/Trace/Families/ReducedMachine/CSRValues.lean)
and [chronological GPR history](Airbender/Review/Trace/Families/ReducedMachine/CSRRegisters.lean)
are now derived from fresh actual CSR port/write/x0 laws, full original public
CSR setup/membership, public Sail seed reads and native matching. One unchanged
time induction bounds all actual reads/writes/terminal tokens. Both readonly
refreshes/OLDREAD/aliases/raw x0 survive, and every original GPR read observes one
derived pre-state. Actual selected CSR addresses establish GPR space before all
byte/misa frames and original source replay at constructed rowBefore states.
Generic modeled-setup and explicit runtime-pool roots retain every row/boundary/token.
Seventeen regressions include complete empty runtime history with x0 and no CSR
availability; no full nonempty accepted CSR witness or original CSR execution.

This closes the port/x0/range/GPR-history NEXT item below. Do not repeat these
proofs or earlier decoding/pool/local CSR/MOP/seven-profile milestones. NEXT combine
the derived original pre-state GPR reads/ranges with actual CSR request fields to
recover source-word/ABI observations, then check actual native caller clock/issuance
before streams/workers. Metadata index3 is not issuance. GPR realization states do
not execute original CSR/custom/nondeterminism/privilege effects or delegated RAM
updates; their memory frame cannot be assumed through a worker action. Original
CSR PC/retained/normal/fetched/common integration, actual Blake2 fulfillment/
converse/accounting/protocol/terminal/init and general public/physical/refinement/
crypto/completeness/parity remain open. Preserve all existing scopes and inputs.

## Current original CSR decoding connection (7 November 2026)

[Original public CSR decoding](Airbender/Review/Trace/Families/ReducedMachine/CSRDecoder.lean)
now recovers original register CSRRW, all ten query fields, raw operands/rd/x0,
unsigned 12-bit CSR index/mask129/funct3=1 and canonical key/high-zero facts from
full sparse/padded membership and accepted native constraints. A separate explicit
runtime trace constructor selects the checked pool while retaining all rows and
boundaries; the public runtime-effect root derives its local mask from original
sources before applying the existing local native CSR certificate. No per-row mask,
profile/read/result/request/PC/state/worker answer or table identity is supplied.
Fourteen original-byte/conditional-native regressions retain scope. Generic original
public code is not equated with the retained native ROM; no CSR execution is proved.

This supersedes the public CSR decoding NEXT item below. Do not repeat closed
source/field/pool/local CSR proofs, MOP arithmetic or seven-profile execution.
NEXT derive actual CSR GPR port/write/x0 laws and initialized history/ranges/rs1
values; derive request clock/issuance from the actual native relation before caller
streams. Metadata index3 alone is not issuance/schedule. Establish meaningful
original CSR/custom/nondeterminism/privilege reference semantics before normal/
fetched/common execution, then actual Blake2 worker ABI/constraints/fulfillment/
converse/accounting/protocol. Bigint remains outside this target. Keep ordinary/
empty and existing execution scopes unchanged; physical setup, terminal/padding/
init/teardown/general refinement/crypto/completeness/parity remain open.

## Current runtime CSR full-pool connection (7 November 2026)

[The complete constructed runtime-CSR pool](Airbender/Review/Circuits/ReducedMachine/Tables/RuntimePool.lean)
now shares thirteen actual stored regions and the retained eight-word ROM with
the old fixture, selecting the independently exported1984/1991 CSR region.
Fresh tag isolation and actual native lookup projection derive both sign queries,
all four dynamic selector domains and [selected local CSR return/request effects](Airbender/Review/Circuits/ReducedMachine/RuntimeCSRTheorems.lean).
Every request field, delegated zero and ABI-high bound follows from this pool's
accepted constraints; no table equivalence, desired per-row answer or old accepted-
circuit transfer is used. The explicit local mask remains separate from original
public decoding. Sixteen regressions and exact parent provenance retain input scope.

Do not repeat the closed regional/pool/query/local CSR/MOP or seven-profile
certificates. This checkpoint supersedes the pool-construction NEXT item in the
earlier regional snapshot below. NEXT derive original public CSR decoding/source/
rd-x0 plus actual native request clock/issuance and initialized reads before caller
streams. Establish meaningful original/custom/nondeterminism reference inputs,
then native Blake2 worker ABI/constraints/fulfillment/converse/accounting/protocol.
Keep the constructed pool's retained ROM scope explicit; general runtime public/
Rust/physical setup refinement is open. Preserve the original1988/1989 fixture and
bigint's separate target, all tokens and initial/reference domains. Other operation/
execution, terminal/padding/init/teardown/cryptographic/completeness obligations
remain open; zero established native defects and no parity claim.

## Current separate runtime CSR-region checkpoint (7 November 2026)

[Actual unified reduced runtime CSR data](Airbender/Review/Circuits/ReducedMachine/Tables/RuntimeCSRTheorems.lean)
is now independently exported and kernel-certified for every4,096 rows:
nondeterminism1984 and Blake2 CSR1991 supported, only1991 delegated. Pinned native
runtime u32/u16 allow-lists contain these two values; bigint1994 is outside this
selected target. The original full pool/1988-1989/eight-word fixture is preserved.
A new FV-only CSR exporter mode, separate strict importer, eight theorem regressions,
scoped native row/reproduction/negative controls and importer controls retain
explicit source/configuration/geometry/literal/semantics boundaries. No production
Rust, dependencies, original Sail or existing artifacts change.

Do not repeat closed regional row/configuration checks or old local CSR/MOP/seven-
profile certificates. The new regional root is NOT a complete runtime pool,
accepted-trace query connection, original CSR decoding/execution or worker link.
NEXT certify a runtime pool using actual stored regions and this independently
exported CSR region, deriving selected native CSR membership/requests without
an arbitrary-table equivalence premise; also derive original public CSR source/
clock issuance before caller streams. Then assess native Blake2 worker ABI,
constraints, fulfillment/converse/accounting and protocol boundaries. Preserve
bigint's separate target/configuration, all native tokens and public inputs.
General Rust/public/physical/cryptographic/completeness and machine terminal/init/
teardown remain open. No defect/parity inference from scope gaps or counts.

## Current native CSR local checkpoint (7 November 2026)

[The exact native special-CSR table](Airbender/Review/Circuits/ReducedMachine/Tables/CSRTheorems.lean)
and [local CSR request/return root](Airbender/Review/Circuits/ReducedMachine/CSRTheorems.lean)
now derive the configured supported/delegated keys, actual mask/query/ports,
bounded oracle, delegation zero and masked native request fields. The source-high
lookup derives the ABI high-offset bound. No desired request, source/read/output/
range or worker result is a public premise. All 4,096 table rows are checked
symbolically from stored blocks; no native table equivalence is assumed.

Do not repeat these local table/selector/query/return/request checks, closed MOP
field/canonical/port proofs or the seven-profile common execution. Thirteen table/
conditional-native/partial-positive CSR tests are not complete nonempty accepted
CSR rows. Exact imported request coordinates/in-cycle index identify observables,
not global issuance/fulfillment/accounting. Original public CSR/MOP decoding,
custom/nondeterminism/privilege reference semantics, initialized reads/x0/history/
PC and retained/normal/fetched/common integration remain open.

First assess the explicit setup difference: imported fixture keys1988/1989 are
not the native Blake2/bigint ABI constants1991/1994 (read-only source comparison,
not a checked worker composition). Review the actual runtime generator/configuration
and native artifacts before selecting a worker target or adding a separate pinned
setup scope. Preserve the existing fixture; do not relabel its keys, assume table
equivalence or treat this unfinished binding as a defect.

NEXT inspect and connect actual native delegation callers/workers, fulfillment
and accounting, retaining exact v2 ABI/source/reference boundaries and independently
retesting v3 findings. Derive worker/request/schedule/state/terminal relations from
accepted native constraints/public inputs; do not supply desired answers. Continue
unified protocol spans, padding/terminal/init/teardown and the explicit general
Rust/public preprocessing/physical/cryptographic/completeness checklist. No
production fixes, standalone/subword expansion or parity inference from counts.

## Current native MOP local checkpoint (7 November 2026)

[Actual reduced MOP arithmetic](Airbender/Review/Circuits/ReducedMachine/MOPTheorems.lean)
now derives selected native field ADD/SUB/MUL, canonical output below Mersenne31,
readonly second GPR routing, candidate/rdmask and default-PC selection. Actual
subtraction underflow/remainder bounds and Boolean carries discharge output
canonicality, rather than a desired result premise. Native words may span RV32;
no source<modulus shortcut or original Sail source-read claim is made.

Do not repeat these local selector/field/canonical/port checks. Original public
MOP decoding, pinned custom-operation reference semantics/input-output, actual
initialized source/history/PC and retained/normal/fetched/common integration are
still open. The upstream Zimop zero-result fallback must not be treated as this
custom field arithmetic. Eleven conditional-native/reference/partial-positive
regressions are not full positive accepted MOP rows. The existing seven-profile
original execution interfaces remain unchanged.

NEXT derive exact native SpecialCSRProperties table semantics and actual CSR
selectors/operands/returns/delegation requests, reviewing original custom/CSR/
nondeterminism interfaces independently of v3. Continue caller/worker fulfillment/
accounting and unified protocol spans, then machine padding/terminal/init/teardown.
Keep general Rust/public export/preprocessing/physical ROM/cryptographic/
completeness boundaries explicit. No production fixes or defect/parity inference
from source inspection, coverage gaps or theorem counts.

## Current common fetched-execution checkpoint (7 November 2026)

[Common seven-profile original fetched execution](Airbender/Review/Trace/Families/ReducedMachine/UnifiedFetchedExecution.lean)
is now checked at the actual initialized projected states, with actual terminal
PC/architectural-cell readers. The explicit exact NativeROM mixed-memory scope
preserves all older arbitrary ordinary public-code and separate memory roots.
Original constructor-sensitive initial reference configuration/RAM-domain inputs
activate only on the public operations that need them. Actual mixed past/control
frames derive every local CSR/permission; selected accepted memory port origins
root RAM addresses in public cells. Supported GPR-row filtering is proved locally
before old execution is reused. No all-events-GPR memory frame is assumed.
AUIPC preparation, x0/aliases/readonly/OLDREADs/unmasked SW and native PC wrap remain.

Do not repeat closed seven-profile decoding/profile/query transport/shared ranges/
x0/projected histories/code/misa frames/source replay/local normal retirement/
stateful finite composition/terminal observations. Eleven input-domain/conditional-
native/complete-EMPTY regressions are not full positive NONEMPTY memory/mixed
native witnesses or physical/completeness certificates.

NEXT inspect actual remaining MOP and CSR/delegation selector/operand/write/PC/
request paths against the unchanged native117-equation artifact. Derive exact
special-CSR table semantics and meaningful original input/output interfaces
before native callers/workers/accounting and unified protocol spans. Retest v3
findings against actual v2 enforcement; no defect follows from an unfinished
connection. Then address padding/terminal machine boundaries and initialization/
teardown, preserving explicit general Rust/public preprocessing/physical ROM/
cryptographic/completeness scopes. No standalone/subword expansion or parity
inference from counts.

1. Generalize the actual native pool beyond its explicit public image/CSR fixture,
   prove the remaining regions' operation semantics and connect physical setup.
   All 14 literal regions, exact tags and sign/high-byte recovery are checked.
   Do not inherit standalone fixture configuration, supplied row answers or v3 encodings.
2. Derive operation-specific native selector identities and flags, operand routing,
   actual masked writes, PC/clock effects and original Sail clauses. The domains
   of all four dynamic table selectors and both sign/high-byte queries are now
   derived from the regenerated constraints and complete pool. Shift masks now
   recover the operation flags, all four selected tags, actual register/immediate
   source-two routing and exact five-bit truncation. The explicit decoded mask
   now follows for the selected original shift profile from stateful public Sail
   decoding and complete sparse/padded membership at the actual native query.
   Native equations exclude holes/tail; source/rd/x0/immediate fields are recovered.
   Native preprocessing/fixed-ROM fidelity and other profiles remain separate.
   Actual sign-fill outputs
   are now derived, including minor flags and positive/logical/zero-shift cases.
   Both actual table-37 queries, contribution assembly, destination address, masked
   port write and default-PC candidate selection are now derived from native
   equations. All 4,194,304 actual table-37 rows now have checked numerical
   meanings, including the merged boundary and reversed right outputs. Complete
   native-pool membership derives canonical keys, exact arithmetic outputs and
   bounds; the selected native row derives all four contribution values/bounds
   at its actual field-packed keys. Initialized selected-shift traces now derive
   every read/write/terminal word bound and both canonical source keys from public
   seeds, original public decoding and actual fixed-pool native acceptance. Internal
   natural candidate values/bounds and masked-write preservation are proved for
   all 32 amounts, including x0 and arithmetic zero shift. Complete canonical RV32
   candidate/write results now follow from those initialized ranges, actual native
   equations and original decoded rd/x0. Actual mixed-port register bindings,
   original Sail cell/GPR histories and decoder replay now follow for selected
   shifts. Original selected register/immediate operands and retained Sail shift
   clauses now follow from actual native routing/results and initialized GPR
   history, including x0. Canonical numerical PC+4 and RV32 rollover now follow
   from original public decoding and actual native carry/inverse/select equations.
   Original normal preparation/retirement and finite fetched execution now follow
   for initialized selected-shift traces from actual native matching and public
   decoding. Native ADD/ADDI/SUB/LUI/AUIPC local routing/flags, actual scalar/carry
   equations, candidate/masked-write assembly and default-PC selection are now
   checked under five native masks. Original public arithmetic decoding now
   derives those masks and actual rd/x0/immediate/raw funct3 fields. Proved native
   preservation feeds initialized induction and derives all read/write/terminal
   bounds, including the prior LUI immediate gap. Canonical RV32 arithmetic
   candidates and actual masked writes now follow with every internal range
   premise discharged. Original arithmetic Sail GPR/cell histories now follow
   with all three reads in one pre-state, actual masked writes, code/misa frames
   and original decoder replay. Original selected arithmetic operands, retained
   clauses, numerical PC+4/RV32 wrap, normal preparation/retirement and finite
   fetched execution now follow for initialized arithmetic-profile traces.
   AUIPC's original get_arch_pc is derived from the actual incoming native PC
   placed into constructed row states before preparation. Both internal read
   ranges, alignment and every state/control answer are discharged. One original
   supported projection now admits mixed shift/arithmetic rows. Derived profile/
   query transport supplies proved local range/x0/register-space/PC/execution
   rules; common initialized induction derives every read/write/terminal bound,
   original Sail state and code/misa/decoder frame. Finite mixed fetched execution
   now follows under exact fixedData acceptance without local answer premises or
   arbitrary-table equivalence. Native bitwise33/35selector bits, all four byte
   queries/decompositions, actual literal/full-pool table arithmetic and canonical
   full RV32 candidates/source/operand bounds are now checked without source-range
   premises. Actual masked port/address/default-PC selection are checked locally.
   Original public bitwise register/immediate masks/tags/rs/rd/x0/sign extension,
   actual GPR/operand/clause/PC execution and common supported preservation/history/
   fetched execution are now checked. Common initialization derives all ranges,
   states and replay across shifts, arithmetic and bitwise rows at exact fixedData.
   Actual comparison masks65/67, all18flags, native tag22 packed resolver rows,
   subtraction/borrow/sign meaning, original SLT/SLTU/SLTI/SLTIU public decoding,
   write preservation and initialized all-word ranges/canonical numerical results
   are now checked separately. Internal source bounds are discharged by public
   history. Actual comparison GPR addresses/read/write transport, selected operands,
   retained original signed/unsigned Sail clauses and bounded PC+4/full RV32 wrap
   now derive normal preparation/retirement. Common initialized execution now
   includes comparisons through derived profile/query transport, write/x0/address/
   PC rules and both actual readonly bounds. All states/order/code/misa/replay and
   terminal observations follow from public initialization and exact fixedData
   acceptance. Native branch mask70/all18flags, actual readonly operands and
   present x0 dummy port, subtraction/lookup routing and conditional PC field
   selection now follow from accepted native constraints. Shared actual zero-test
   equations78..81 plus scalar checks derive remainder-zero semantics without
   source bounds. Actual bounded subtraction now proves operand equality and
   unsigned borrow; native sign queries and the actual packed resolver derive all
   six branch conditions. All65,536actual tag17cleanup rows and full-pool membership
   now have exact meanings. Native target bounds/carries/addition, PC+offset/full
   RV32 wrap, taken-only bit1 exclusion and bounded/aligned final PC selection are
   checked internally. Source/PC/offset bounds, initial alignment and offset parity
   now follow from original public BTYPE decoding and initialized native history.
   Full sparse/padded membership derives all ten fields, canonical sign-extended
   offset and parity from the retained Sail decoder. Proved readonly/dummy-zero
   preservation feeds shared time induction; both actual read bounds, PC/offset
   bounds/alignment/parity are discharged before the short public numerical result.
   Original branch GPR/cell history now binds both readonly sources and present
   x0 dummy old-read/zero-write in one pre-state, deriving whole-data stutters.
   Retained original BTYPE clauses, actual incoming PC preparation and numerical
   conditional PC effects now derive normal/fetched branch-only execution. Both
   source bounds/alignment/parity and every local CSR read are derived internally;
   the public initial Sail state explicitly makes misa readable, value unrestricted.
   Common mixed integration now includes branches after deriving exact profile/query
   transport and local preservation/x0/register-space prerequisites. The common PC
   interface derives incoming bounds/alignment and operation-specific final bounds;
   ordinary per-profile PC+4 proofs remain unchanged. Common initialization derives
   both branch source bounds/parity and every state/control/replay answer. Initial
   misa readability is required only if the public program contains BTYPE, value
   unrestricted; ordinary/empty CSR-free scopes remain. Actual JALR257/JAL33025
   masks/all18bits, immediate/readonly routing, PC-vs-rs1 base selection, shared
   addition/cleanup query, return candidate/masked destination and final-PC fields
   are now checked locally. Exact native cleanup derives output PC bounds/alignment
   and raw bit1 rejection without source-range premises. Raw addition input bounds
   remain internal until original public decoding/initialization discharges them.
   Original JAL/JALR full public decoding now derives all fields/zero flags,
   canonical sign-extended offset/raw JALfunct3 and direct parity. Actual PC+4
   return/masked-write preservation follows public PC bounds/alignment before
   initialized range induction. All actual read/write/terminal ranges then discharge
   raw base/immediate bounds, deriving canonical return/raw/selected target/full
   RV32 wrap and JALR low-bit clearing without public local answers.
   Original jump GPR/cell history is now derived after fresh all3port bindings:
   one pre-state for source/readonly/old-destination aliases, masked write/x0
   preservation, chronological Sail states/final matching/code/misa/decoder replay.
   No initial CSR-read premise at this GPR-only boundary.
   Local native jump execution now derives original source/architectural-PC observations,
   retained JAL/JALR clauses and normal retirement at the actual native after-state.
   Initialized jump-only fetched execution now discharges all local source/alignment/
   CSR reads through public ranges/original membership/past history, deriving replay,
   native clock/PC chain and terminal observations. Initial misa is readable only for
   nonempty jump programs; original JALR additionally uses Machine/readable mseccfg/
   MLPE-clear configuration. Empty/direct-only CSR scopes remain narrow. Next extend
   Common original projection/profile transport and mixed initialized execution now
   include JAL/JALR. Six original profiles derive exact PC/byte/query identities,
   common jump return-alignment before range induction, x0/register-space/PC/CSR
   rules and all states/replay/terminal observations. Initial misa applies only to
   original branch/jump constructors, security configuration only to original JALR;
   ordinary/empty and branch-only scopes stay narrow. Next inspect remaining actual
   ordinary combined operations before delegation/protocol/padding/terminal/init.
   Word-only LW1025/SW16386 now derive all18flags, operand/port spaces, actual
   effective-address/addition/default-PC equations, load shadow/selection/masked
   destination and unmasked store memory address/write. Complete native18/23/24
   table certificates cover all offset/separator/ROM rows and padding, with no
   standalone table identity. Canonical aligned load addresses/ROM shadow and
   RAM-only aligned stores need no supplied address bounds. Internal RV32 addition
   still awaits initialized source bounds. Original full public LW/SW decoding is
   now checked: retained constructors/x0/sign extension/unused indices and allten
   actual query fields derive from complete original sparse/padded membership;
   native packing excludes holes/tail. Fresh ALL3mixed register/memory port cells,
   load ROM/earlier-memory-read and unmasked store-source write preservation now
   feed unchanged shared initialized induction. ALLactualread/write/terminal bounds,
   canonical effective address/write/PC+4/fullRV32wrap derive publicly; no local
   range/read/result/PC answer supplied. SW excludes native ROM-prefix WORD CELLS,
   not yet an original byte-code frame. Independent public ROM-shadow initializer
   now constructs native seeds separately from original architectural byte reads;
   uniqueness/clocks/ranges/architectural seed projection and all native numerical
   bounds/results derive under that boundary. Exact native fixed-ROM/original
   byte-image construction is now checked: actual8publicwords plus complete UNIMP
   tail construct all4MiB original Sail bytes, derive every aligned ROM read/full
   public extraction and preserve registers/outside bytes. Actual accepted LW ROM
   output now gives that byte read in the constructed state, independently of
   ignored shadow values. Actual architectural/shadow port domains and effective
   address origins now derive from fresh native bindings/accepted matching. Actual
   LW x0 preservation and SW memory-port exclusion feed full projected Sail state
   realization/chronological segments/final matching while every native shadow
   token remains matched. Architectural public cell domains and meaningful public
   code capacity derive EVERYROMbyte frame/stateful decoder replay; no supplied
   code/read/write/state/frame answer. Fresh projected native port proofs now derive
   ALL retained reads/OLDREADs and final write at ONE original pre-state, including
   aliases and RAM refreshes. Actual ROM candidates bind to constructed bytes through
   past projected history; ignored shadow values stay independent. Original unmasked
   load-to-x0 writes discard only after the memory read; SW writes actual RAM from
   original rs2, never dummy rd masking. The public transfer root discharges every
   source/range/address/PC/result/state/order/replay obligation from exact NativeROM
   input construction and full original public initialization/decoding. Retained
   original LOAD/STORE virtual/physical accesses and clauses now execute at actual
   row states. Meaningful initial reference configuration applies only to nonempty
   public memory programs; actual past history derives every local CSR/permission.
   Public tracked-RAM ordinary domain plus actual initialized origins, or native ROM
   bounds, derives every local exclusion of pinned CLINT/signature windows. These
   are reference input boundaries, not native enforcement or per-row success answers.
   Original PC/nextPC transport now preserves every actual transfer/OLDREAD/alias,
   unmasked x0 load and SW RAM write through prepared states. Retained original
   normal_base_next_pc/clause/tick_pc execution reaches actual native final PC,
   including RV32 wrap. Stateful projected composition derives finite original
   fetched LW/SW execution and all architectural terminal readers, without pure
   decoder or supplied replay/state/order/PC premises. Empty programs remain CSR-free.
   NEXT common retained instruction/normal/fetched execution at the initialized
   mixed states now derived above, preserving ordinary scopes/AUIPC PC.
   General Rust/public/physical fidelity stays separate.
   Common supported execution excludes
   LW/SW; no all-events-GPR frame reuse.
   Other combined
   profiles, workers/protocol/padding/terminal/init and positive nonempty arithmetic/
   mixed/bitwise/comparison fixtures remain distinct open coverage.
   The former projection allocation gap is closed by generic projections and separate proof units,
   without increasing limits or adding result/equivalence premises.
3. Compose initialized combined histories, public decoding and original execution.
   Actual regenerated reduced timestamp equations and all eight timestamp queries
   now discharge the unchanged shared clock contract. Public seed construction
   plus accepted native state/memory matching derive full logical memory history,
   newest preceding reads, all local/prior clock bounds and terminal four-tick
   row accounting. Proved selected-shift write preservation now feeds shared
   range induction and derives the formerly unchecked low source limb, all other
   native word ranges and both canonical source keys. Concrete fixedData selects
   the actual certified native pool without an equivalence premise. Extend proved
   local preservation/public decoding to other combined operations. Selected-shift
   canonical RV32 words and original Sail cell/GPR histories now follow, including
   actual readonly aliases, masked writes, code/misa frames and decoder replay in
   constructed pre-states. Original shift operand transport and clause execution
   are now checked at the same derived after-states. Numerical PC+4/wrap and
   incoming bounds/alignment are now derived without per-row PC answers. Original
   preparation/retirement and finite fetched execution now compose for selected
   shifts, including actual terminal PC bounds/reads and empty traces. A complete
   nonempty ordinary/x0 SLL fixtures now check all117equations,22lookups and full
   modeled public execution boundaries. Common initialized mixed shift/arithmetic
   execution is now checked with one original public decoder and shared derived
   range/x0/history/code frames. Other combined profiles, nonempty arithmetic/mixed
   fixtures and physical setup/protocol/terminal/init correspondence remain unfinished.
4. Connect native delegation workers/callers and supported public use.
5. Close combined protocol, terminal/padding and initialization/teardown boundaries.

The new v3 reference is PR #585 at b29277dd895499574e317a994fd89243a72f06cb.
Its unified and reduced unrolled targets are distinct; the monolithic v2 reduced
artifact maps to the unified migration path. Its newer compiler certificates and
initialization contracts are dependencies to adapt, not established v2 coverage.
Preserve original Clean/Sail semantics and existing resource caps. Do not replace
missing obligations with desired outputs, table equivalence or intermediate states.

## Unchanged-circuit policy (6 November 2026)

Continue to checked parity with the current v3 formalization without fixing
production circuit or machine code. A confirmed native v2 issue must retain its
pinned evidence and exact acceptance scope in the findings register, and any
required restriction must appear as a narrow, explicit Review interface
assumption. Such an assumption is a conditional theorem boundary, not a fix or
an enforcement proof; it must not be implemented as a project axiom or a
premise that supplies the desired result. Coverage gaps and importer limitations
remain open obligations, not findings. No native v2 defect is currently established.

## Integrated review contract

Keep the same ownership boundaries as the source formalization:

- Review/Circuits owns selected references, artifacts, observable mappings and short public claims.
- Review/Helpers owns common properties, word representations, tables and local context.
- Review/Trace owns whole-execution and terminal-state contracts.
- Proofs owns calculations, selector recovery, native-equation checks and composition.
- Import owns the separate artifact-fidelity boundary.

Use original Clean constraint semantics and original pinned Sail standard clauses.
Reuse shared proofs unchanged when possible; record adaptations explicitly.
Derive local selectors, bounds and actual reads before promoting a row claim to
an initialized trace claim. Never hide a result or desired intermediate state in
an interface. Keep public assumptions visible and v2 findings independent.

## Continuing execution

The user authorized continuation and regular commits on 17 October, stopped the
scheduled task on 21 October, and resumed foreground work on 6 November against
the latest PR #585. A continuation task, Continue v2 FV to v3 parity,
is active every 30 minutes at the user's request; the old task remains paused. Keep working
in the isolated dev-based worktree and make small verified unsigned Conventional
Commits, with Git signing disabled per invocation rather than configuration.
Do not push without authorization. Use the
[serial bounded verification runner](scripts/check_all.py) and its
[validated watchdog](scripts/bounded_fv.py): one Lean worker, Lean memory cap
3072 MiB, total footprint at most 3072 MiB, resident at most 4096 MiB and finite
wall budgets. Confirm termination after limits and redesign instead of raising caps.
This sampled guard and Lean allocation cap are not an OS hard physical-memory limit.

## Pending integration work

Native direct shuffle-RAM/state metadata, ADD/SUB clock extraction and initialized
logical memory histories are checked. Accepted state/memory matching and initial
clock boundaries now derive all row/prior clock inputs, complete Clean memory
consistency and newest preceding reads. Public Sail image construction now binds
seed tokens and initial PC to actual reads, deriving initial bounds/clocks and
unique addresses. Ten-column native decoder placement/query order is checked,
including the separate zero flag. Selected-profile public Sail setup construction,
full padded logical membership, native padding exclusion and recovered zero flags
are checked. Initialized history now derives native read/write/terminal bounds;
canonical decoder PC/immediate and register-index bounds are checked. Native history
now constructs actual Sail reads/writes and intermediate states, including x0
preservation from v2 masked writes. Derived clock order groups complete rows;
readonly refreshes preserve the instruction pre-state even with aliases. Public
indexed PCs now derive every incoming PC alignment, including RV32 truncation.
Native equations derive bounded outgoing successors, and state matching bounds the
terminal PC. The proof layer now assembles all five arithmetic row interfaces
and original Sail preparation/execution/retirement from these derived facts and
actual native history. Rebased control transport derives PC reads and reaches the
actual masked write. Complete initialized five-opcode execution now composes
original Sail byte reads/decoding and normal steps to exact terminal PC/cells,
including empty traces. Native GPR metadata preserves all code bytes; actual pure
decoder evidence is retained from construction. A reversed two-row ADD/ADDI
witness derives PC 8 and x2=247 with no intermediate/result premise.

1. Finish binding native word-memory alongside checked arithmetic execution.
   All v2 equations/queries/metadata and native-shaped ROM tables now support
   checked transfer laws, alignment, exact ROM values and RAM-only stores.
   Native address arithmetic, modular PC successors and clock/port laws are also
   checked under explicit source/immediate/initial-PC and clock inputs.
   Public LW/SW decoding is now checked in a separate native registry: complete
   padded membership recovers actual original Sail source evidence, exact zero
   flags and PC/immediate bounds/alignment, including original x0 loads.
   Actual Sail byte extraction now binds native ROM data inside the public
   prefix; a complete four-MiB extraction covers every native ROM address.
   Initialized logical word-memory history now reuses shared matching, native
   clock recovery and decreasing-time range induction. Public seed construction
   derives all initial/per-row/prior clock inputs and all read/write/terminal
   word bounds, including discarded ROM-shadow reads; full decoder membership
   supplies the zero flag. Nonempty LW/SW/x0 fixtures and omitted-shadow rejection
   are checked. Initialized native-row assembly now derives effective-address
   addition, bounded aligned PCs, modular successors and clock/port order using
   existing native calculations unchanged, with no per-row numerical premises.
   Actual Sail cell realization and native row grouping are now checked with
   mixed-port x0 preservation, source-GPR transport and actual register/RAM writes.
   Reversed dependent store/load rows derive the intermediate RAM state and later
   read without a supplied state/read result. This realizes the full supplied
   native image, including shadow cells tracked as RAM. Native shadow accesses
   below four MiB now provably preserve their exact read value; native matching
   still retains every refresh token. Whole-address projection now preserves
   Clean consistency/latest writes and realizes only architectural cells in Sail.
   A separate public initializer reads architectural cells and retains canonical
   native shadow seeds independently; clocks, unique addresses, x0 preservation
   and complete row grouping are derived. The same constructor now supplies
   canonical seed bounds to the unchanged shared range induction, deriving all
   full native read/write/terminal ranges, including erased shadows. Ordinary/x0 ROM-load regressions retain
   full matching and actual masked Sail writes with unreadable shadow locations
   and distinct native shadow/ROM values. Projected initialization and public
   decoding now derive effective-address addition, bounded aligned PCs, modular
   successors and native clock/port effects through the existing calculations.
   Shared readonly-prefix transport recovers every retained port read in the
   instruction pre-state and the final actual masked write; native constraints
   prove that the final port always survives projection. Ordinary/x0 ROM loads
   and reversed dependent RAM store/load rows exercise these interfaces without
   supplied reads/intermediate states. Projected transfers now preserve every
   byte below four MiB, including missing bytes and code outside the tracked
   domain. Actual RAM writes remain outside that region. Successful public ROM
   extractions survive every projected prefix; public setup construction derives
   complete code-byte windows for programs fitting the native ROM region, and
   original Sail source/decoding evidence survives. A reversed dependent SW/LW
   regression simultaneously derives a real RAM change, retained ROM extraction
   and original code evidence without a later-read/result premise. Eight unchanged
   pinned Sail platform modules now discharge Machine translation, PMP/PMA and
   ordinary-memory helpers under public configuration. Actual projected native
   histories preserve that configuration. Native RAM reads/writes and alignment
   now feed original virtual-memory calls; the same reversed dependent SW/LW
   fixture derives a real virtual store and subsequent load without expected
   intermediate/read/state premises. Actual public ROM extraction and preserved
   prefixes now feed original Sail virtual ROM loads. Native address bounds derive
   their ordinary-address domain. Native masked writes now match the original LW
   destination effect, including x0 without NOP projection; the proof layer reaches
   the original ROM LW clause result in the actual native after-state. Ordinary/x0
   initialized fixtures construct actual ROM/decoder bytes and configuration while
   retaining shadow value 123 distinct from the loaded ROM word 0xc0001073.
   Original RAM LW/SW clauses now reach the actual native cell-transfer states.
   Native decoder fields derive opcode selectors, original registers and sign
   extension; retained native ports derive rs2 and RAM reads, including masked
   load writes/x0. The same reversed dependent fixture reaches original SW then
   LW clause results with actual read 123 and the actual destination write,
   without a supplied intermediate state/read or desired result. Original Sail
   nextPC preparation and PC retirement now compose all three RAM/ROM clause
   paths through unchanged control/history/configuration lemmas. Actual decoding
   selects original LW/SW; initialized effects derive the effective address and
   exact modular native PC successor. The small original Sail dispatcher is
   reused without v3's discarded-load profile. Ordinary/x0 ROM fixtures retire
   to native PC 4, and the same reversed SW/LW fixture reaches actual PC 8 and
   terminal RAM/x3 values 123 without intermediate/read/PC/result premises.
   [General initialized word-memory execution](Airbender/Review/Trace/Families/WordMemory/Theorems.lean)
   now composes every derived row through actual code reads, original decoding
   and normal preparation/clause/retirement. Public cell and shadow-seed domains
   discharge all local ordinary-RAM and actual ROM-prefix coverage conditions.
   Projected composition retains every native shadow token in matching and
   concludes the exact terminal PC and architectural cells, without equating
   shadow values with actual ROM bytes. The reversed dependent SW/LW fixture
   reaches PC 8 and RAM/x3=123 through this general relation; ordinary/x0 ROM
   loads and empty traces also pass. Configuration, public program size in ROM,
   ordinary public RAM and actual ROM extraction/seed coverage remain visible.
   [Fixed native zero boot](Airbender/Review/Trace/Families/WordMemory/NativeBoot.lean)
   now uses the unchanged original Sail initial profile and boot-image proof.
   Public domain geometry and native zero GPR/RAM/shadow seeds derive the general
   initialized execution boundary. Complete native paths keep terminal shadow
   values zero independently of actual ROM bytes. Ordinary/x0 boot fixtures reach
   native PC four and actual destination values; invented native seeds and
   nonzero public GPRs are rejected. The native proving-loader padding path was
   retested: it zero-extends the input words to four MiB, while the raw table
   constructor uses UNIMP only outside the image it receives. The separate
   [padding model](Airbender/Review/Helpers/Tables/WordROMPadding.lean) now proves
   full extent, unchanged prefix and zero tail symbolically. The explicit
   [loader constructor](Airbender/Review/Helpers/Tables/PaddedROMImage.lean) now
   pads actual Sail byte memory and derives complete four-MiB ROM extraction.
   Symbolic lookup/word-vector proofs avoid evaluating a huge map or list.
   Prefix bytes, ordinary RAM, registers, the original zero profile and public
   Machine/PMP/PMA configuration are preserved. Actual public decoder setup
   survives when its code lies in the supplied prefix. The small padded-boot
   claim now derives every shadow coverage condition from construction and the
   existing public ROM domain. Ordinary/x0 native fixtures pass complete original
   execution from that padded state; missing/oversized prefixes reject padding.
   Physical setup geometry is now imported and guarded for both artifacts:
   exact 12/16-column placement, ten-wide decoder groups, four-wide tagged tuples,
   complete table offsets, decoder capacity and the reserved normalization row.
   The [active setup-row model](Airbender/Review/Helpers/Tables/PhysicalSetup.lean)
   retains native dummy/zero-padding tuples and tags 23/24. Symbolic proofs derive
   exactly the existing logical ROM/separator membership from these tuples;
   tagged ROM membership then derives actual Sail reads after the public loader.
   Nonempty real-byte fixtures check original/padded reads and altered-word/tag
   rejection. The [standalone native exporter](../native_setup_exporter/README.md)
   now emits actual regional generic/decoder/range16 values and public image/text
   data without building a full trace. The pinned LW/SW/x0/UNIMP fixture has exact
   reproduction, exhaustive lossless compression checks and symbolic certificates
   for every ROM/separator/range row, unsupported decoder slot and image zero tail.
   Its actual tagged ROM rows feed original Sail reads through the existing loader.
   [Sparse public construction](Airbender/Review/Helpers/Decoder/SparseSetup.lean)
   now retains unsupported pure words at indexed PCs and rejects missing/effectful
   inputs. Native mask equations exclude holes/tail before source recovery and
   derive canonical words/alignment and the exact zero flag. A second actual native
   export has an interior UNIMP slot: supported PCs stay 0/8/12. Actual original
   Sail reads/decoding construct its sparse setup, and every exported decoder row
   is certified against it. A complete native x0-load row at PC 12 satisfies all
   original equations/lookups and recovers its actual public source. No table
   equivalence is a premise. [Sparse initialized execution](Airbender/Review/Trace/Families/WordMemory/SparseExecution.lean)
   now shares the existing native history, numerical, code-frame, original Sail
   clause/retirement and terminal assembly. Actual strict/sparse constructors
   derive proof-internal indexed source evidence; the strict public claim is
   unchanged. A nonempty fully initialized x0-load fixture selects actual exported
   slot three and derives original execution from public PC 12 to PC 16, RAM 123
   and x0 zero. The PC-four hole remains in actual public bytes; no step through
   an unsupported instruction or control-flow skip is claimed. No per-row read,
   intermediate state/result or table-equivalence premise is supplied.
   [Shared native scalar export](Airbender/Review/Helpers/Tables/NativeScalars.lean)
   now certifies every range16/timestamp19 prefix value and source-shaped active
   zero filler. The timestamp generation clause is copied unchanged from pinned
   native source with its existing constant; no full prover build is needed.
   Exact lookup meanings connect to the unchanged Clean helpers. Both compiled
   scalar placements, endpoints/padding and fourteen strict importer checks pass;
   the reserved normalization row and physical multiplicity enforcement remain
   outside this model. The [actual arithmetic export](Airbender/Review/Trace/Families/AddSub/NativeDecoder.lean)
   now certifies all 1,048,576 native ten-column slots against independent public
   bytes and original Sail sparse construction. The seven-word fixture covers
   all five arithmetic opcodes, signed ADDI, original SUB-to-x0, raw U-type funct3,
   an interior UNIMP hole and ADD at original PC 24. Native packed-mask equations
   exclude holes/tail; a complete post-hole ADD row recovers its actual source.
   Exact fixture/binary reproduction and nineteen strict importer checks pass.
   No table-equivalence premise or custom MOP coverage is added.
   [Sparse initialized arithmetic execution](Airbender/Review/Trace/Families/AddSub/SparseExecution.lean)
   now shares the existing numerical/native history/original Sail/terminal
   assembly through proof-internal indexed evidence derived from either builder.
   The strict public theorem statement is unchanged; complete sparse membership
   excludes holes/tail before source selection. A fully initialized nonempty ADD
   fixture uses actual exported slot six at original PC 24 and derives fetched
   execution to PC 28 and x1=246. Full alias matching derives every refresh/read;
   no indexed-source, per-row bound/read, intermediate state/result or table
   equivalence is a public premise. The PC-20 UNIMP hole remains public bytes;
   initial PC 24 is supplied, with no control-flow skip asserted.
   [Active decoder rows](Airbender/Review/Helpers/Tables/NativeDecoder.lean)
   now retain each of the three actual native prefixes and the direct native
   padding API output throughout the remaining 15,728,639 active rows. Literal
   minus-one padding is already present in every prefix, so symbolic proofs
   derive exact membership without a table-equivalence premise. Compiled column
   positions 2/6, native capacity and active boundaries are checked. The short
   [arithmetic bridge](Airbender/Review/Trace/Families/AddSub/ActiveSetup.lean)
   derives initialized execution from this full active decoder domain; the same
   real alias fixture reaches PC 28/x1=246. No huge trace allocation or finite
   domain enumeration is used. Native source comments mentioning zeros do not
   replace actual sentinel data. Reserved c0 normalization and Rust full-trace/
   LDE/argument refinement remain separate. Next generalize exported-data
   certificates to arbitrary public programs and bind full physical trace
   assembly/initialization.
   [Complete active setup rows](Airbender/Review/Helpers/Tables/NativeRowsData.lean)
   now assemble all scalar/generic/decoder columns, with exact imported placement
   and unchanged Clean scalar/fixed-table membership derived in Proofs. Full
   windows reject truncation; arithmetic has no generic group. Decoder filler can
   overlap still-active tagged ROM data, and last active rows retain distinct
   scalar/generic zero and decoder minus-one fillers. The initialized arithmetic
   alias regression now consumes complete-row decoder columns and derives the
   same PC 28/x1=246. Next refine this row model against Rust trace construction
   and generalize native decoder certificates; normalization/LDE, multiplicities
   and cryptographic enforcement stay separate.
   The fixture certificates are not general Rust/export/LDE/compiler refinement.
   Rust refinement and cryptographic enforcement remain separate.
   Preserve v2 PC rollover and native timestamp offsets;
   keep physical setup generation/export and mixed/custom expansion explicit.
2. Add native jump/branch/SLT and extend the shared execution relation with checked
   control-flow interfaces. Preserve full native setup padding and actual public
   code-byte/decoder evidence; do not add per-row result or PC premises.
   [The concrete native artifact](Airbender/Review/Circuits/JumpBranchSlt/Artifact.lean)
   and both fixed tables are now checked: all 36 equations, 16 lookups and exact
   typed metadata; [actual native export](artifacts/setup/jump-control-native.json)
   has cleanup/conditional tags 17/43 and offsets 0/65536 without a dummy row.
   Symbolic/small finite certificates derive exact membership and fixed effects.
   The full active JAL witness, wrong targets/profiles, signed/unsigned flags,
   changed outputs and actual JAL alignment rejection pass. The v2 conditional
   table keeps flags and funct3 separate. [Native PC bounds](Airbender/Proofs/JumpBranchSlt/PC.lean)
   now follow from all constraints and supported masks: outgoing high equals
   scalar-ranged variable 43, and outgoing low is the raw or cleaned ranged key.
   The JAL -4 field-minus-one variant passes all polynomials and the other 15
   queries but fails actual scalar query index 5; the canonical target passes.
   Do not copy the v3 F01 closure premise into this local claim.
   [Public control decoding](Airbender/Review/Circuits/JumpBranchSlt/Decoder.lean)
   now constructs actual original Sail bytes/metadata and full sparse padding;
   native packed-mask bounds exclude sentinels and recover the supported mask,
   canonical words/alignment and exact x0 flag. The public claim derives PC
   bounds without a supplied mask. Retain v2 SLTI mask 8, branch mask 16, original
   x0 operations and raw JAL funct3 (tag 7 for -4). The full public JAL witness
   passes; wrong tag-zero membership and the malformed high PC reject.
   [The actual native control decoder export](artifacts/setup/jump-decoder-native.json)
   is now certified against independently constructed public Sail data, preserving
   raw JAL tag 7, the interior hole and original SLTIU-to-x0 at PC 8. Every prefix/
   tail row is proved equal using the arithmetic certificate structure, and the
   short exported-decoder claim derives source evidence/PC bounds from actual
   membership plus all native constraints. Both binary/fixture modes reproduce;
   crossed/unsigned-only profiles, malformed inputs and tag-zero membership fail.
   [Native control clocks/ports](Airbender/Review/Helpers/Context/JumpBranchSlt.lean)
   now discharge the unchanged shared clock/history contract, using actual native
   carry/borrow equations and all eight timestamp queries. [The short public history
   claim](Airbender/Review/Trace/Families/JumpBranchSlt/History.lean) derives complete
   Clean history and newest reads from actual public Sail seeds/PC plus full native
   matching. The accepted JAL -4 fixture retains both aliased x0 refreshes and the
   actual link write; stale local reads fail matching. Missing register data,
   19-bit lower-clock carry, derived port effects and terminal clocks are checked.
   [Control word bounds](Airbender/Review/Trace/Families/JumpBranchSlt/Values.lean)
   now follow from actual public sparse decoding, native write equations and
   unchanged initialized range induction, including all readonly aliases and
   terminal tokens. [Hardwired-x0 preservation and Sail cell history](Airbender/Review/Trace/Families/JumpBranchSlt/SailHistory.lean)
   reuse native destination masks, shared zero-value induction and row grouping
   to derive actual cell transfers/intermediate states. The exported JAL fixture
   checks old x1=123 to actual link four with both x0 refreshes retained.
   [Original control register accesses](Airbender/Review/Trace/Families/JumpBranchSlt/Registers.lean)
   are now connected to the derived native history: unchanged readonly-prefix
   transport and decoded indices recover both source reads, the old destination
   read and actual masked write in one cell-history pre-state. Shared append/split
   proofs derive every row's actual segment states and original public source
   entry, without a per-row state/read/schedule premise. The exported JAL fixture
   derives both x0 reads, old x1=123 and link write four through the public claim.
   [Saved JAL/JALR links](Airbender/Review/Circuits/JumpBranchSlt/Theorems.lean)
   now follow from native carry equations 29/30, actual scalar ranges and shared
   modular word addition. Full public decoding supplies PC bounds and the x0 flag;
   native packed masks one/two recover all selectors before actual masked writes.
   The exported JAL, new logical JALR/x0 cases, full local native PC+4 wrap and
   altered-link rejection are checked. The wrap row is not a public-decoder or
   initialized execution certificate, and the new logical fixture has no new
   native arbitrary-program export certificate.
   [Native jump targets](Airbender/Review/Trace/Families/JumpBranchSlt/Targets.lean)
   now derive actual JAL/JALR PC sums, JALR bit-zero clearing and four-byte
   alignment from initialized matching and original public byte decoding. Shared
   history supplies indirect-source ranges; unchanged original Sail decoder lemmas
   and native metadata supply JAL parity. Actual native high-candidate range
   queries eliminate the v3 final-high closure interface. The exported negative
   JAL and a new initialized aliasing JALR (public x1=257, odd sum 265, target 264)
   pass, with local x0/wrap and bit-one rejection cases. Logical-fixture native
   export and initialized wrap execution are not claimed.
   [Initialized comparison results](Airbender/Review/Trace/Families/JumpBranchSlt/Comparisons.lean)
   now derive actual SLT/SLTU/SLTI/SLTIU masked writes from native subtraction,
   positive high-limb flags, actual scalar/fixed queries and initialized matching.
   Public original decoding derives register/immediate identity, signedness and
   x0; no sign/borrow bit, operand bound, expected read or result is supplied.
   Unchanged original signed word-ordering lemmas are reused. Four separately
   initialized cases cover signed/unsigned disagreement, sign-extended -1,
   discarded true SLTIU-to-x0 and its readonly alias refresh. Its query also occurs
   in the prior native export; new logical-program export is not claimed.
   [Comparison PC advancement](Airbender/Review/Trace/Families/JumpBranchSlt/ComparisonPC.lean)
   now follows from actual native candidate/routing equations, Boolean carries
   and both scalar bounds, retaining RV32 wrap. Public decoding derives incoming
   ranges/alignment and exact comparison selection; no register-image boundary
   or per-row PC/carry/result is required. All four initialized fixtures pass;
   full native wrap and altered-PC rejection are local regressions, not a new
   initialized wrap execution or native export certificate.
   [Initialized branch conditions](Airbender/Review/Trace/Families/JumpBranchSlt/Branches.lean)
   now derive all six predicates, taken/complement bits and actual zero writes.
   Original subtraction, signed ordering and the unchanged positive-high proof
   are reused; actual inverse equations identify equality, while scalar/fixed
   queries resolve signs and borrow. Public original metadata derives mask/tag
   identity and complete matching supplies both operand ranges. Eighteen
   initialized cases cover both outcomes per opcode, opposite signed/unsigned
   orderings and equality. A false equality/table answer fails the native inverse
   equation; no new defect or native program-export certificate is claimed.
   [Initialized branch targets](Airbender/Review/Trace/Families/JumpBranchSlt/BranchTargets.lean)
   now follow the checked decisions to PC+offset or PC+4, retaining RV32 wrap and
   four-byte alignment. Original decoder/sign-extension lemmas derive offset
   parity; public metadata derives PC/offset ranges, alignment and selectors.
   Native carries, both scalar candidate queries and taken-only bit-one checks
   derive exact outgoing words, with no final-high closure premise. All eighteen
   initialized cases pass; local taken -4, taken/untaken wrap and misalignment
   rejection are separately checked without claiming initialized wrap execution
   or a new native export certificate.
   [Original comparison clauses and retirement](Airbender/Review/Trace/Families/JumpBranchSlt/ComparisonExecution.lean)
   now execute SLT/SLTU/SLTI/SLTIU in constructed initialized-history segments.
   All operand/result/immediate/PC inputs come from native matching and original
   public decoding. Unchanged Sail clause, preparation, history-frame and
   retirement proofs are reused; native x0 handling and both candidate bounds
   remove the source nonzero-destination/final-high interfaces. The four existing
   original-byte fixtures execute from actual public states; true SLTIU-to-x0
   retains x1=123 and data stuttering while retiring PC eight to twelve.
   [Original branch clauses and retirement](Airbender/Review/Trace/Families/JumpBranchSlt/BranchExecution.lean)
   now connect all six predicates/targets to original BTYPE clauses in constructed
   segments. Native matching and public decoding derive all reads, bounds,
   offsets, conditions and PCs. An actual initial misa entry is explicit, with
   unrestricted value; unchanged original CSR frame lemmas transport it through
   history. All eighteen native fixtures are reused unchanged and execute both
   outcomes per opcode with that public CSR entry, deriving full data stuttering.
   Missing-entry/accessor regressions retain this original-state boundary.
   [Original JAL/JALR clauses and retirement](Airbender/Review/Trace/Families/JumpBranchSlt/JumpExecution.lean)
   now reuse unchanged pure definitions and the complete original retirement
   declaration. Native links, targets, actual reads/writes and public constructors
   derive all row interfaces. Initial misa is readable; only traces containing
   JALR need actual Machine privilege and MLPE-clear mseccfg. Unchanged history
   transports the profile. Existing negative JAL and aliasing JALR fixtures
   execute original retirement and the exact native link write in the same
   constructed after-state; JAL has no privilege/security entries.
   [Complete fetched control execution](Airbender/Review/Trace/Families/JumpBranchSlt/Execution.lean)
   now reuses the unchanged shared composer and all twelve original control
   constructors. Actual native history preserves public bytes; state/memory
   matching derives row order, intermediate states and terminal PC/GPR reads.
   Scalar candidate queries also bound raw terminal PC limbs, including empty
   traces. Existing jump/branch fixtures and a reversed two-row JAL/JALR program
   pass; stale source data passes local constraints/decoding/state matching but
   fails memory matching. Keep the explicit initial CSR profile. This closes
   standalone checked control-family fetched composition, without adding a
   source closure premise. Continue with the remaining ordinary families below;
   new native program exports, whole-machine/protocol spans, general
   Rust/compiler and cryptographic refinement remain separate. No per-row
   result/PC or table-equivalence premise is added.

3. Port unsigned mul/div, shift/binop and subword memory into the same shared
   context; retain their family-specific assumptions and supported ISA profile.
   [Unsigned mul/div artifact import](Airbender/Review/Circuits/MulDiv/README.md)
   now retains all native equations and six paired-byte queries covering eleven
   8-bit columns. Actual table-driver rows and exact tagged Clean membership
   have symbolic certificates; native constraints derive every byte bound.
   Optimized-out scratch variables remain unconsumable. Importer mutation
   checks cover pairing/padding, scratch uses and native profile geometry.
   Native MUL/MULHU/DIVU/REMU numerical results now follow from every accepted
   equation/query, including zero divisors and actual masked x0 writes. The
   unchanged shared integer product theorem has its native v2 byte/carry
   connection; remainder comparison uses checked inverse 32768 and the native
   packed mask. Forty full local assignments apply the public numerical claim.
   Actual stateful original Sail decoding now derives packed operation and
   destination-zero metadata. Initialized native matching/public seeds derive
   every read/write/terminal bound and newest-read history; the short public
   trace claim obtains all four numerical results without local interfaces.
   Sixteen complete initialized traces and disabled-M/wrong-tag/bad-flag checks
   pass. The unchanged source decoder-frame proof retains actual misa reads.
   Actual Sail operand/old-destination reads, masked writes and every segment
   state now follow from initialized native history, including aliases and x0.
   Original three-port declarations are copied unchanged and bound to native
   v2 metadata. Actual native GPR histories preserve code/misa and replay the
   stateful original decoder after real updates. Sixteen cases and a reversed
   aliasing two-MUL program pass; stale old-destination metadata passes local
   constraints/decoding/state matching but fails native memory matching.
   Original MUL/MULHU/DIVU/REMU clauses and local nextPC preparation/PC
   retirement now follow from those constructed histories. Native PC gates
   derive bounded modular RV32 successors, including a full imported-row wrap
   regression. Sixteen initialized cases and actual second-MUL alias retirement
   pass. Complete fetched MUL/DIV execution now derives every original
   fetch/decode/preparation/retirement step, the actual native PC chain and
   terminal register reads. Stateful composition reuses the unchanged original
   misa-frame theorem and derives replay through actual native history/PC
   updates, without pure-decoder, extra ISA, row-step, intermediate-state or
   terminal-bound premises. Sixteen complete cases, concrete arithmetic final
   values, a newest-first two-MUL alias program reaching PC eight/x1=x3=861,
   and empty execution pass. Shift/binop now has an actual native decoder export
   and an independent public-byte/original-Sail certificate for all twelve
   ordinary forms, their original x0 variants, an unsupported ADD hole and all
   1,048,576 rows. Native v2 masks, full immediate limbs and SRAI encoded funct7
   differ from v3 and are checked directly. Empty CSR allow-list filtering and
   unsupported REV8/rotate/shift words are reproduced through the actual Rust
   API. Continue with native dynamic selectors/table import and exact membership,
   then numerical soundness, initialized execution and subword memory. Keep
   custom CSR/oracle semantics separate; dynamic compiled lookups still reject. The
   actual native zero/XOR/OR/AND low-ID prefix is now reproduced, with checked
   compiled offsets, all 196,608 binary outputs, actual zero row and exact
   original Clean/native membership. Native membership derives byte bounds and
   bitwise results; malformed keys/results reject. Geometry is structural and
   all output calculations reuse the source literal-block certificates within
   unchanged memory caps. Native truncation, zero-padded range and all 2,097,152 sign-fill rows now have checked
   actual-data/Clean membership, derived key/limb bounds and exact RV32 masks.
   Symbolic 64-domain block proofs retain native shift-zero behavior and original
   compiled noncontiguous offsets. Negative/positive sign boundaries and malformed
   queries pass. The actual low-input SRL table now has complete original
   Clean/native membership and exact zero-extended RV32 logical-shift semantics
   for all 2,097,152 rows, with derived key/output bounds and zero high output.
   Six symbolic certificates retain all 74 native blocks and compiled offset
   4460545 without row enumeration. Shift/final-bit boundaries and malformed
   queries pass. The actual high-input SLL table now also has complete original
   Clean/native membership and exact wrapped RV32 semantics for all 2,097,152
   rows, with derived bounds and zero low output. Six symbolic partitions and
   ten stored-template certificates retain all 74 native blocks, original
   offset 2363393 and actual shift/discard boundaries. Generic size/output
   assembly keeps imported arrays out of metadata normalization, under the same
   caps. Low-input SLL now also has exact actual-data/Clean membership and
   reconstructed RV32 results for all 2,097,152 rows, deriving both limb bounds.
   Its low column is identified with checked native SLL-high; all 145 high-output
   blocks retain native carry/truncation, with six symbolic prefix certificates
   and a 73-block suffix transported from that existing proof. First-carry,
   shift-sixteen and final-bit/discard boundaries pass under unchanged caps.
   High-input SRL now also has exact actual-data/Clean membership and RV32
   results for all 2,097,152 rows. The full high column reuses checked SRL-low;
   all 146 low-output blocks retain rotated/cross-shift templates, the 65,537-row
   initial zero block and the shortened shift-eleven affine block. Ten bounded
   template certificates, five symbolic partitions and a transported 73-block
   native SRL-low suffix derive every value and both limb bounds. All four native
   logical-shift limb tables now have checked helper membership/results.
   The complete shift/binop local projection now retains all fifty equations,
   eight timestamp queries and four dynamic table selectors as fourth Clean
   lookup fields. Twelve structural region proofs retain all 10,817,537 tagged
   rows with original offsets, including the exact compilation fixture CSR
   profile (nondeterminism enabled, empty delegation CSR list). Explicit-target, arity,
   mapping, placement and crossed-profile regressions pass. Runtime CSR setup
   binding remains separate; no custom CSR execution claim is inferred.
   All four actual tagged queries and their exact canonical selector domains now
   follow from native constraint acceptance. An exhaustive partition of every
   stored region proves unique tags and resolves native membership to the checked
   helper results; the actual zero row permits only three zero fields. Combined
   table regressions reject incorrect results/selectors and crossed SLL regions.
   Original public construction and native decoder membership now derive the
   six operation/immediate bits, all four native lookup tags, selected operand
   limbs and disabled ordinary delegation multiplicity. The six-bit bound rejects
   the complete sentinel tail. Full native fixtures cover all twelve forms and
   their x0 variants; all 96 tagged queries and public routing applications pass.
   Native XOR/OR/AND now derive all four accepted byte queries, both source-word
   bounds and exact selected RV32 results, including immediate forms. Native
   inverse-256 equations reconstruct all input/output limbs; original decoded x0
   flags derive the actual masked writes. Twelve complete binary fixtures retain
   sign-extended immediates and word values above Mersenne31; corrupted bytes,
   selected results and x0 writes reject under unchanged caps.
   Native SLL/SRL/SRA contributions now follow from original public decoding,
   all four accepted queries and native equations. The low operand is bounded
   and truncated modulo 32; each canonical packed key has exact bounded native
   contribution semantics. Both actual selected-limb sums and RV32 contribution
   addition are derived without input-range or desired-output premises. Twelve
   complete shift fixtures retain SRAI encoded funct7, native sign-fill order,
   shift-31/x0 boundaries and malformed key/inactive/sign-fill rejection.
   Native clocks/ports and complete initialized Clean history now follow from
   actual public Sail seeds/PC and accepted native matching. All twenty-four
   ordinary/x0 fixtures retain actual masked writes and readonly refreshes;
   six immediate/x0 stale-clock alternatives pass local equations but fail full
   memory matching. Native two-carry equations and eight timestamp queries derive
   all row/prior bounds, alignment and port order without local clock premises.
   Initialized word bounds and canonical packed-key source binding are now
   derived from actual public code, Sail seeds/PC and accepted native matching.
   Separate bounded SLL/SRL/SRA half calculations cover all shift amounts/signs;
   shared time induction supplies read bounds, exact masking bounds actual writes
   and natural key lifting recovers source/amount quotient and remainder.
   All twenty-four ordinary/x0 fixtures and twelve concrete shifts pass these
   public claims without local range, source/key or desired-output premises.
   Whole ordinary SLL/SRL/SRA/XOR/OR/AND numerical results and canonical actual
   selected/write limbs now follow from public decoding and initialized native
   history, with no local source/range or desired-result premise. Separate whole
   SLL/SRL/SRA calculations cover all 32 amounts and both sign domains; low-limb
   truncation equals the whole selected operand's architectural low-five bits.
   All twenty-four ordinary/x0 traces apply the short public numerical claim and
   derive concrete results. SRA sign calculations remain split under default
   heartbeat and fixed memory caps. Actual original Sail cell/GPR transport is
   now constructed from initialized matching and original public decoding: all
   native-clock-ordered segment states, common pre-state source/old-destination
   reads, actual masked writes, final cell matching and code/misa preservation
   are conclusions. The three original pinned register-port transport declarations
   are reused unchanged with checked v2 metadata; stateful original decoding
   replays after actual GPR updates. Twenty-four complete fixtures derive actual
   transfers/numerical writes; all twelve x0 variants preserve the entire Sail
   data state, including the six immediate/x0 readonly aliases. Original clauses are now
   checked for all six ordinary operations and twelve register/immediate forms:
   actual native routing/public immediate columns derive the selected operand,
   SRAI's encoded funct7 bits provably leave its low-five-bit shift count unchanged,
   and native numerical results/masked writes execute the retained original Sail
   instruction into the same actual history after-state. The short public
   clause-history claim derives source bounds and all row states from initialized
   native matching and original public decoding. Twenty-four complete fixtures
   reach actual original clause execution; all twelve x0 variants preserve the
   whole data state. The RV32 profile continues to reject amounts 32 and 63.
   Original preparation/retirement and complete fetched execution are now checked
   for this selected ordinary profile. Actual native carry gates derive outgoing
   PC bounds and modular +4; public original setup derives incoming PC bounds and
   alignment. Complete native rows check low carry and full RV32 wrap. Actual GPR
   history supplies every state/read and preserves code/misa, so original stateful
   decoding replays in each real pre-state. Native PC matching composes finite
   original fetched steps to exact terminal PC/cells, including empty traces.
   Twenty-four complete fixtures derive original retirement, actual terminal PCs
   and GPR values; all twelve x0 forms advance PC while preserving data. Continue
   with remaining ordinary/subword-memory coverage and runtime CSR setup binding
   before delegation workers/callers and unified protocol boundaries below.
4. Rebind bigint/BLAKE/Keccak workers and callers. Retest control validity,
   unissued workers, ROM behavior and request participation on v2 before reusing
   any source finding or temporary premise.
5. Port unified execution, protocol spans, terminal boundaries, padding and
   initialization/teardown under their actual v2 argument interfaces.

Expand importer support only when a concrete circuit requires it. The two native
word-memory and two native control fixed tables are now supported with exact
three-column queries and explicit profiles. The unsigned mul/div paired-byte profile is also supported with exact tagged
native data and checked odd-column zero padding. The exact four-witness shift/binop
profile now has complete tagged import. Other fixed tables, unsupported dynamic
selector profiles, unpaired byte columns and state linkage continue to fail closed.
Do not copy unused v3 Review theorems into the v2 build.

## Deferred milestones

Faithful Rust/JSON/Lean generation, full compiled argument correspondence,
cryptographic lookup/memory/statement enforcement and completeness remain
separate milestones. Every promoted public theorem needs a nonvacuous regression,
an explicit axiom root and resolved review-guide links.

## Findings discipline

Use the [same finding-status bar as the pinned v3 review](FINDINGS.md#assessment-standard):
retain accepted native/reference discrepancies and concrete source defects at their
exact scope without requiring a full forged proof. An assumption or narrower
conditional theorem is not a fix. Keep unresolved bindings and supported profiles
explicit, retest v3 candidates on actual v2 paths, and put coverage/milestone notes
in verification status rather than inflating the findings register.

## Native subword offset/trap table checkpoint (2026-10-20)

The native v2 offset/trap table now has an actual export and a complete kernel
certificate for all 2,097,152 rows. Its native tag is 44 and its compiled offset
is 65,537. [Literal data](Airbender/Review/Helpers/Tables/NativeSubwordOffsetData.lean)
comes from the unchanged pinned table generator and lossless shared codec;
[strict import](Airbender/Import/Setup.lean) rejects changed field, profile, tag,
placement, extent, shape and noncanonical values. The standard native gate
reproduces the JSON byte for byte under the existing shared-lock watchdog.

[The small public helper](Airbender/Review/Helpers/Tables/SubwordOffsetTheorems.lean)
derives a canonical 21-bit key, its exact low-two-bit offset and the complete
native width/limb/trap mask. [Internal calculations](Airbender/Proofs/SubwordMemory/Offset.lean)
check all stored blocks symbolically over 32 control groups and every low-address
pattern, and prove exact original Clean/native tagged membership without a table
equivalence premise. The original affine getter and membership transport are
reused from verified v2 certificates. No proof or resource ceilings were raised.

[Regressions](Tests/SubwordOffset.lean) retain ordinary misaligned halfword/word
loads, the explicit native misaligned-load-to-x0 exception, high-half selection,
invalid encoding and store controls, and reject altered offset/trap queries.
The table alone admits some keys that the full decoder/circuit must assess.
No accepted subword row, Sail execution or native defect is claimed here. The
remaining load/store/ROM regions, full native constraint import, public decoding,
initialized reads and original subword instruction execution remain unfinished.
The findings standard and historical findings/coverage archive are unchanged.

## Native subword load-data table checkpoint (2026-10-20)

The native v2 signed/unsigned load-data table now has a complete certificate for
all 2,097,152 actual exported rows, with native tag 45 and compiled offset
2,162,689. [Literal data](Airbender/Review/Helpers/Tables/NativeSubwordLoadData.lean)
comes from the unchanged pinned native generator and shared lossless codec.
The strict importer checks field, profile, tag, placement, extent, shape and
canonicality; the standard native gate reproduces the JSON byte for byte.

[The public helper](Airbender/Review/Helpers/Tables/SubwordLoadTheorems.lean)
derives the canonical 21-bit key, exact signed/unsigned low and high outputs,
and both 16-bit bounds directly from original Clean lookup membership. The key
retains its preselected 16-bit limb, two offset bits and funct3. Odd-halfword and
unused/invalid keys retain the native zero outputs; their isolated presence is
not an accepted-row or architectural defect claim.

[Internal assembly](Airbender/Proofs/SubwordMemory/Load.lean) proves exact tagged
native/Clean membership. Symbolic getters and 32 control groups cover every
stored affine/periodic block. The pinned v3 block-selection lemmas are copied
unchanged. Four actual 256-entry templates use 64 separate 16-entry kernel
certificates, each in a fresh bounded worker. Literal constants share data without
changing values or codec semantics. This replaces an allocation-heavy draft;
no memory, recursion or heartbeat limits were raised.

[Nineteen kernel regression roots](Tests/SubwordLoad.lean) cover byte sign
boundaries, signed halfword boundaries, all four offsets, unsigned outputs,
odd-halfword and unused keys, and rejection of altered low/high values. Fourteen
additional importer checks reject malformed native load-data artifacts.
Full subword constraints, remaining store/ROM regions, public decoding,
initialized native memory/history, original instruction execution and physical
argument binding remain unfinished. The findings standard and historical
findings/coverage archive are unchanged.

## Native subword original-RAM clearing table checkpoint (2026-10-20)

The native v2 original-RAM-limb clearing table now has a complete certificate for
all 2,097,152 actual exported rows. Its native ID is 54 and compiled offset is
5,308,417, obtained from the actual generator and compiled layout. [Literal data](Airbender/Review/Helpers/Tables/NativeSubwordStoreClearData.lean)
uses the unchanged pinned native generator and lossless shared codec. Strict
import checks field, profile, tag, placement, extent, shape and canonicality;
the standard native gate reproduces the JSON byte for byte.

[The short public helper](Airbender/Review/Helpers/Tables/SubwordStoreClearTheorems.lean)
derives the canonical key, exact retained original RAM byte, unused zero output
and 16-bit bound from original Clean lookup membership. The key retains the
preselected limb, both offset bits and raw funct3. SB preserves the byte outside
the selected write position. SH, SW and all unused funct3 keys retain the native
zero outputs. These isolated keys do not establish accepted full store behavior.

[Internal proof assembly](Airbender/Proofs/SubwordMemory/StoreClear.lean) covers
all actual affine/periodic blocks symbolically over 32 control groups, reusing
the verified native block helpers and pinned v3 periodic upper-byte proof.
Exact tagged native/Clean membership is proved; no table-equivalence premise,
expected output, new axiom or increased proof/resource limit is used.
[Fourteen kernel regression roots](Tests/SubwordStoreClear.lean) cover all four
offsets, retained/cleared byte boundaries, SH/SW/unused zero outputs and rejection
of changed clearing or unused fields. Fourteen new importer checks retain strict
malformed-artifact rejection and crossed native-region checks.

The written-value placement table, subword ROM regions, full native constraints,
limb preselection, public decoding, initialized memory/history, original subword
instruction execution and physical argument binding remain unfinished. No native
defect is established; the findings bar and historical coverage archive are unchanged.

## Native subword written-value placement checkpoint (2026-10-20)

The native v2 written-value placement table now has a complete certificate for
all 2,097,152 actual exported rows, native ID 55 and compiled offset 7,405,569.
[Literal data](Airbender/Review/Helpers/Tables/NativeSubwordStorePlaceData.lean)
comes from the unchanged pinned generator and shared lossless codec. Strict
import retains exact field, profile, tag, placement, extent, shape and canonical
values; the standard native gate reproduces the JSON byte for byte.

[The public helper](Airbender/Review/Helpers/Tables/SubwordStorePlaceTheorems.lean)
derives canonical key, exact SB/SH contribution, unused zero and 16-bit output
bound from original Clean lookup membership. SB selects the source low byte and
places it by offset parity; SH retains the whole preselected limb at every raw
offset. SW and unused funct3 keys retain zero outputs. The presence of odd SH
keys in this isolated table does not establish full circuit acceptance.

[Internal assembly](Airbender/Proofs/SubwordMemory/StorePlace.lean) checks all
native affine/periodic blocks across 32 control groups, adapting the pinned v3
placement proof and reusing the verified v2 block helpers. The nondependent
periodic getter is copied unchanged. Affine literal arrays compare every parsed
element against the actual first/step/length before compact emission; prior
emitter modes remain unchanged. Sample and size lemmas are structural. General
Rust/JSON/elaborator fidelity remains the separate Import boundary; no theorem
assumes table equivalence, expected results or new axioms, and no limits are raised.

[Fifteen kernel regression roots](Tests/SubwordStorePlace.lean) cover all offsets,
source high-byte removal, SH full/odd raw keys, SW/unused zeros and changed-query
rejection. Fourteen new importer checks retain malformed-artifact rejection and
crossed native-region tests. Remaining subword ROM regions, full native constraints,
limb preselection, public decoding, initialized memory/history, original instruction
execution and physical argument binding remain unfinished. No native defect is
established; the findings standard and historical coverage archive are unchanged.

## Complete native subword lookup import checkpoint (2026-10-20)

[The artifact](Airbender/Review/Circuits/SubwordMemory/Artifact.lean) retains all
51 native equations, two scalar queries, eight timestamp queries, two constant
fixed queries and both multiplexed witness-selected queries. [Structural checks](Airbender/Proofs/SubwordMemory/ArtifactChecks.lean)
retain actual state/decoder columns, all three memory ports and clocks, and
complete setup geometry. The importer requires the exact selector profile, all
62 table offsets and the 9,502,721-row tagged extent. Prior validation remains;
the CLI gate now covers all six native compiled layouts.

[The complete table](Airbender/Review/Circuits/SubwordMemory/Tables/Native.lean)
keeps all seven native regions: zero, separator, offset/trap, load-data, aligned
word ROM, original-RAM clearing and written-value placement. Previously checked
literal fixed data is unchanged. [Internal structural proofs](Airbender/Proofs/SubwordMemory/NativeLookup.lean)
include every row in each region. [The short public claim](Airbender/Review/Circuits/SubwordMemory/Lookups.lean)
derives both actual queries and evaluated selectors from original Clean native
acceptance, with no expected result, selector bound, intermediate state or
table-equivalence premise.

Earlier references to remaining subword ROM regions were a planning expectation.
Actual v2 has one AlignedRomRead region, tag 46, keyed by aligned word index;
v3's separate byte/halfword ROM regions do not apply. [The aligned model](Airbender/Review/Helpers/Tables/AlignedWordROM.lean)
shares the full public WordROM image and native UNIMP tail. Ordinary RomRead has
a byte-address key and tag 24. [Symbolic proofs](Airbender/Proofs/Tables/AlignedWordROM.lean)
derive the canonical index and both limbs and connect the two row models' word
values. General Rust/JSON/compiler/setup correspondence and physical verifier
enforcement remain separate boundaries; this adds no general native ROM-export
refinement claim.

[Thirteen kernel regressions](Tests/SubwordArtifact.lean) cover evaluated
selectors, native placements, distinct ROM key units, the complete UNIMP tail
and altered key/output rejection. Explicit macro guards reject missing/crossed/
duplicate profiles. Thirty-one new importer checks cover selectors/mappings,
tuple widths, all region offsets, extents and overlapping decoder placement.

Next are subword tag resolution, operation routing, actual limb preselection,
numerical load/store effects, public/native decoding, initialized memory/history,
original Sail execution and whole-machine composition. No native defect is
established. FINDINGS and its historical archive, original Clean/Sail semantics,
native source/exporter/codec and resource ceilings are unchanged.

## Native subword tagged-query resolution checkpoint (2026-10-20)

[Internal partition](Airbender/Proofs/SubwordMemory/NativeRegions.lean) now proves
the exact seven-region decomposition of the complete native subword table.
Literal fourth-column reads and public separator/ROM tags derive tag uniqueness
and the canonical selector set 0, 23, 44, 45, 46, 54, 55. No region is omitted
because it is expected to be unused by a later routing proof. The existing
affine tag getter is copied unchanged from the checked v2 shift-region proof.

[Exact resolution](Airbender/Proofs/SubwordMemory/NativeResolution.lean) connects
each selected tag to the already certified helper membership: offset/trap,
signed/unsigned load data, original-RAM clearing and written-value placement,
alongside the public separator and aligned word ROM. Tag zero requires the
actual all-zero query. These are proved equivalences, not assumed table-equivalence
premises. All native literal data, region offsets, import semantics and the
public ROM model are unchanged.

[The short public claims](Airbender/Review/Circuits/SubwordMemory/Lookups.lean)
expose these seven connections and canonical selector bounds. Both per-slot
bounds follow from original Clean native acceptance through the existing
accepted-query extraction theorem, which is retained unchanged. They require
no witness-supplied selector bound, expected result, routing or intermediate
state. Operation-specific tag choices still require the native routing equations.

[Thirty kernel regression roots](Tests/SubwordLookups.lean) cover every region,
separator boundaries, native trap and x0 raw keys, signed/unsigned loads, both
store byte positions, altered outputs/unused fields, crossed store regions,
unsupported tags, ROM word/byte key distinction, UNIMP tail and canonical field
tag wrap. Previous helper rejection proofs are reused. These malformed-input
rejections and isolated raw keys add no confirmed native defect.

Next: derive the ROM/RAM/load/store routing and actual limb preselection, then
numerical operation effects, public/native decoding, initialized memory/history,
original Sail execution and whole-machine composition. General native export/
compiler refinement, runtime CSR binding and physical verifier enforcement
remain separate boundaries. FINDINGS and its historical archive, native sources,
original Clean/Sail, exporter/codec and all resource ceilings remain unchanged.

## Native subword operation-routing checkpoint (2026-10-20)

[Controls](Airbender/Proofs/SubwordMemory/Controls.lean) derive store, size and
upper-limb Booleanity from native equations. The actual fixed separator derives
RAM/ROM selection and the low six high-address bits. Native acceptance excludes
stores into ROM. The two optimized equations determine tags 46/45 for ROM loads,
45/0 for RAM loads and 54/55 for stores. Native mixed-port modes/addresses and
three separate ROM/load-RAM/old-store-RAM limb muxes are also derived.

[Field selection](Airbender/Proofs/SubwordMemory/QueryFields.lean) derives all
three fields of both native dynamic queries in each accepted mode. V2 ROM keeps
its field inverse of four and word-index key. Load/clear/place keys retain the
actual offset and raw funct3 encoding. The inverse-coefficient proof pattern is
adapted from checked v2 binary-query proofs with small kernel-checked Mersenne31
characteristic identities; resource/proof limits and native coefficients are
unchanged. Selected limbs, query keys and results are conclusions, not premises.

[Four short public claims](Airbender/Review/Circuits/SubwordMemory/Routing.lean)
expose exhaustive accepted modes and the exact ROM-load, RAM-load and store
connections. [Observables](Airbender/Review/Circuits/SubwordMemory/RoutingModel.lean)
name selected native limbs and keys. [Internal assembly](Airbender/Proofs/SubwordMemory/Routing.lean)
uses original Clean acceptance and the existing proved tagged-table resolution.
A RAM load has an actual all-zero second slot. Stores query old RAM data for
clearing and the source register's low limb for placement. No result, table
equivalence, selector-bound or intermediate-state premise is added.

[Six complete native fixtures](Tests/SubwordRouting.lean) satisfy all 51 original
equations and fourteen lookups, with two-row proof partitions. They cover lower
and upper ROM loads, a nonzero ROM word index, signed odd-byte/upper-half RAM
loads, x0, an odd-byte store and a halfword store. Public routing claims are
applied to these accepted rows. Concrete writes and eight mutations check crossed
store tags, byte-address ROM keys, wrong RAM/store limbs, nonzero disabled fields,
ROM stores, non-Boolean upper selectors and mixed addresses. These local fixtures
do not assert public decoding, initialized history or original instruction execution.

Next: derive general numerical subword effects, decoder/control connections,
initialized reads and history, original Sail execution and whole-machine composition.
Five other ordinary families already have initialized fetched execution; the sixth
subword family, delegation/custom/CSR and unified/terminal/padding/initialization
boundaries remain unfinished. General export/compiler refinement and physical
verifier/cryptographic enforcement remain separate. No new confirmed native defect
is established. FINDINGS and its historical archive, native sources/artifacts,
original Clean/Sail, exporter/codec and all resource ceilings remain unchanged.

## Native subword value/write checkpoint (2026-10-20)

[Offset controls](Airbender/Proofs/SubwordMemory/OffsetValues.lean) now derive the
actual fixed offset query, its canonical key bound and exact offset/mask values.
Native Boolean size/upper controls and the packed-mask equation force the retained
mask below four, so a native trap bit cannot occur in an accepted row. The size
bit is the mask's low bit and the upper-limb selector is exactly offset / 2.
The original table, all trap rows and explicit misaligned-load-to-x0 exception
remain unchanged; this is native control reasoning, not an architectural alignment
or x0 correctness claim. A generic original Clean lookup bridge and three separate
field reductions avoid a recursion-limit failure without raising proof limits.

[Actual writes](Airbender/Proofs/SubwordMemory/WriteValues.lean) now connect native
ROM/RAM data outputs to both load-candidate columns and the actual written register
columns. The original (1 - rd_is_x0) scaling remains exact. For either supported
flag value, writes equal the candidate or zero; Boolean decoding itself is still
a public-decoder dependency, not a new local premise. Native store equations
assemble certified clearing/placement outputs, preserve the opposite old limb
in subword mode and retain the full-word source mux in the raw native relation.

[Value assembly](Airbender/Proofs/SubwordMemory/Values.lean) derives actual canonical
load candidate values and both candidate bounds, public word-indexed ROM contents,
cleared/placed values, their bounds and unused zeros. The v3 data/merge proof
approaches are adapted with exact source identities, alongside checked v2 reuse.
No v3 native result is assumed: actual v2 tables, field, query keys, columns and
write equations supply the connections. No expected result, selected read, table
equivalence, alignment or read bound is supplied as a premise.

[Five short public claims](Airbender/Review/Circuits/SubwordMemory/Values.lean)
use the small [observable interface](Airbender/Review/Circuits/SubwordMemory/ValuesModel.lean).
[Test applications](Tests/SubwordValues.lean) reuse all six complete native fixtures
unchanged, preserving signed data, upper/lower loads, nonzero ROM word indexing,
x0 and stores. The original nonzero x0 candidate is retained before its zero
write. Nine rejections cover changed ROM/RAM candidates, actual writes, nonzero
x0 writes, wrong offsets/upper selectors and a native trap-bearing key. Rejected
mutations are coverage evidence and add no confirmed native defect.

Next: connect actual native/public decoding to supported byte/halfword operations,
normalize packed raw keys over that domain, derive source/old-RAM read and whole
write bounds from initialized history, then reach original Sail execution and
whole-machine composition. Canonical lookup values and field write assembly do
not claim these remaining connections. The sixth ordinary family, delegation/
custom/CSR and unified/terminal/padding/initialization boundaries remain unfinished.
General export/compiler refinement and physical verifier/cryptographic enforcement
remain separate. FINDINGS and its historical archive, native sources/artifacts,
original Clean/Sail, exporter/codec and resource/proof ceilings are unchanged.

## Public subword decoding checkpoint (2026-10-20)

[Original public decoding](Airbender/Review/Circuits/SubwordMemory/Decoder.lean)
now projects all six supported original Sail forms: LB, LH, LBU, LHU, SB and SH.
The actual v2 decoder source is pinned. Its one-bit store mask and raw funct3
are retained, unused load rs2 and store rd clear, and original x0 loads remain
present. Signed immediate limbs are preserved. The v3 projection/proof approach
is adapted with exact provenance; its three-bit masks, x0 exclusions and native
connections are not copied into v2 coverage.

[Internal recovery](Airbender/Proofs/SubwordMemory/Decoder.lean) uses actual
public sparse-image construction, complete logical setup membership and original
native acceptance. Native store Booleanity excludes every unsupported slot and
the complete sentinel tail. The selected original public instruction supplies
all ten native query fields: PC, register indices, x0 flag, immediate, raw funct3
and store mask. No selector meaning or Boolean x0 flag is supplied separately.
Certified native candidate bounds plus the derived x0 flag give actual decoded
load writes and both written-limb bounds, including discarded x0 writes.

[Two short public claims](Airbender/Review/Circuits/SubwordMemory/Decoding.lean)
expose these connections without supplying expected reads/results or a table
equivalence. Calculations and proof assembly remain internal. This is logical
public-image membership; correspondence to an actual native exported subword
decoder table remains an explicit Import fidelity boundary. The source pin is
not an exported-table certificate or general Rust/compiler refinement claim.

[Seven complete native rows](Tests/SubwordDecoderFixture.lean) cover all six
forms, lower/upper ROM and RAM cases, signed/unsigned data, original x0 loads
and SB/SH. Existing six local fixtures remain unchanged. New rows clear their
unused load index and correct store rd/x0 metadata; an added LBU case has its
own native key, unsigned candidate and actual write. All 357 original equations
and 98 lookup memberships pass. Independent original instruction bytes construct
public one-word images with the full 1,048,576-row capacity; original decoding is
checked separately as small pure reductions. [Applications](Tests/SubwordDecoder.lean)
exercise both claims nonvacuously, signed immediate extremes, unsupported word
forms and five decoder-membership rejections. Old local rows remain accepted
locally and their incompatible decoder metadata is correctly rejected.

Concrete membership expansion initially reached Lean's allocation cap. Reusing
the existing symbolic sparse-head membership lemma avoids that expansion; query
metadata is reduced explicitly and original decoding is split from state replay.
No allocation, footprint, resident, recursion or proof ceiling is increased.
Every failed owned worker is confirmed terminated before retrying.

Next: certify actual native decoder exports, normalize packed subword keys over
the decoded domain and derive source/old-RAM reads and whole store-write bounds
from initialized history. Original subword Sail execution and composition remain
unfinished. The sixth ordinary family, delegation/custom/CSR, unified execution,
initialization/teardown and terminal/padding boundaries remain open. General
Rust/compiler refinement and physical verifier/cryptographic enforcement remain
separate. No confirmed native defect is added; FINDINGS and its historical
archive, original Clean/Sail, native circuit/helper artifacts and source checkout
are unchanged.

## Native subword decoder export checkpoint (2026-10-21)

[The actual native export](artifacts/setup/subword-decoder-native.json) now
retains thirteen original words: all six subword forms, their negative-immediate
variants with original x0 load destinations, and an unsupported LW slot. The
exporter calls the pinned original native subword family and shared preprocessor/
flattening functions; its codec, dependencies and other profile behavior remain
unchanged. The independent strict [parser](Airbender/Import/Setup.lean) and
[literal emitter](Airbender/Import/SetupEmbed.lean) retain the exact subword family,
Mersenne31 field, text bounds and full ten-column 1,048,576-row extent.

[Independent public data](Airbender/Review/Circuits/SubwordMemory/NativeData.lean)
spells original instruction bytes and Sail constructors separately from exported
metadata. [Small pure original reductions](Airbender/Proofs/SubwordMemory/NativeDecode.lean)
retain signed immediates and original x0 forms before replay in the public state.
[Byte reads and internal certificates](Airbender/Proofs/SubwordMemory/NativeSetup.lean)
construct the exact public indexed setup and prove equality with every actual
exported row. Four small byte-read partitions and symbolic compressed-column tail
getters preserve all default proof/resource ceilings; no million-row expansion,
expected result or table-equivalence premise is introduced.

[One short public claim](Airbender/Review/Trace/Families/SubwordMemory/NativeDecoder.lean)
checks this specific export's fidelity. Native I-type unused rs2 is zero, original
x0 destinations retain zero flag one, and negative immediates use 65535/65535.
Native S-type raw bits contain apparent rd=31 for immediate -1; the actual decoder
clears that unused index, retains rs2 and sets zero flag one. The unsupported LW
keeps its physical slot and the entire sentinel tail is retained.

[Kernel regressions](Tests/SubwordNativeDecoder.lean) cover original text and
Sail decoding, full row equality, tail, signed x0 loads and negative stores.
Nineteen added importer checks reject bad/crossed profiles, altered fields,
noncanonical words, incomplete columns/extents and unknown fields. Native Rust
runs reproduce the fixture and independent little-endian text input; actual
word/doubleword/ADD/CSR filtering and malformed/oversized text rejection pass.
All previous native exports and importer checks remain covered.

This closes the specific decoder-data fidelity dependency, not arbitrary Rust/
JSON/compiler refinement or subword instruction execution. Native constraints,
initialized matching, public state/ROM bindings and packed-key normalization must
still derive source/old-RAM reads, whole store-write bounds and original subword
Sail execution. Five other ordinary families remain at their existing checked
execution checkpoints; delegation/custom/CSR, unified execution, initialization/
teardown and terminal/padding boundaries remain unfinished. Physical verifier
and cryptographic enforcement remain separate. No confirmed defect is added;
FINDINGS and its historical archive, original Clean/Sail and native sources/
circuit/helper artifacts are unchanged. The original checkout is preserved.

## Initialized native subword history checkpoint (2026-10-21)

The separate [native registry](Airbender/Review/Helpers/Context/SubwordMemory.lean)
retains the actual imported subword constraints, state, decoder and three mixed
register/RAM port descriptors. [Native clock extraction](Airbender/Proofs/SubwordMemory/Timestamp.lean)
checks the three Boolean comparison borrows, Boolean carry, both clock equations
and all eight timestamp queries against the subword artifact. These discharge
the unchanged [shared clock contract](Airbender/Proofs/Trace/Families/SubwordMemory/History.lean).
No v3 column identity or assumed table equivalence is used.

[One short public claim](Airbender/Review/Trace/Families/SubwordMemory/History.lean)
now derives complete original Clean online memory history and every newest
preceding read from actual original Sail seed reads/PC and accepted native
state/memory matching. Row bounds, prior-clock bounds, alignment, port order,
history and read values are derived. Readonly ROM-shadow accesses and their
timestamp refreshes stay in matching, as do actual masked destination writes.

[Eight complete initialized traces](Tests/SubwordHistoryFixture.lean) cover
signed/unsigned byte and halfword loads, ROM shadows, RAM, x0 and actual SB/SH
writes. Their independent public registers and little-endian data bytes construct
the seed image. The eighth load aliases rs1=rd=1 and consumes the source port's
readonly refresh at clock four, using a unique seed domain. [The stale version](Tests/SubwordHistoryStale.lean)
still satisfies every local native constraint, but [logical matching rejects it](Tests/SubwordHistory.lean).
This is a regression for the intended matching boundary, not a confirmed defect.
Projecting to timestamp multiplicities makes rejection small without reducing
word/address payloads. Splitting local acceptance from history checks preserves
the existing Lean allocation/resource ceilings after an initial check hit the cap.

[Clock regressions](Tests/SubwordClock.lean) verify a full native row at low clock
524284: the actual carry advances to low/high 0/1 and clock value 524288, with all
three ports strictly after their prior clocks. Nonboolean carry and high-limb
overflow are rejected. All earlier decoder, table, routing, value and execution
checks remain unchanged. Calculations and assembly stay under Proofs; Import
keeps its separate data-fidelity boundary.

This closes initialized logical history for subword rows. Canonical source/old-RAM
word bounds, whole store-write bounds, packed byte/halfword key binding, public
instruction/data-ROM projection and original subword Sail execution remain next
dependencies. The fixtures do not yet identify their ROM-shadow data bytes with
architectural instruction bytes. Delegation/custom/CSR, unified execution,
initialization/teardown and terminal/padding boundaries remain unfinished.
General Rust/JSON/compiler refinement and physical verifier/cryptographic
enforcement remain separate. No confirmed defect is added; FINDINGS and its
historical archive are unchanged. Original Clean/Sail, native sources/artifacts,
exporter, earlier fixtures and the original checkout are preserved.

## Initialized native subword word bounds checkpoint (2026-10-21)

[Exact packed-key calculations](Airbender/Proofs/SubwordMemory/PackedKeys.lean)
now recover the native 16-bit limb, two-bit offset and three-bit raw funct3
without Mersenne31 wrap. Native offset/upper controls, canonical reads and
original public metadata supply the ranges. [Store preservation](Airbender/Proofs/SubwordMemory/StoreBounds.lean)
uses the already certified literal native clear/place relations and actual
write muxes. SB's complementary bytes bound their sum; SH replaces the selected
limb and unused raw rows contribute zero. The opposite old limb and native
full-word mux branch are retained. Separate contribution bounds alone are not
used to justify a bounded sum.

[The initialized assembly](Airbender/Proofs/Trace/Families/SubwordMemory/Values.lean)
derives original raw funct3 and x0 masking from actual public decoding. Readonly
ports preserve their read words. The last store write uses both the earlier
source read and its old destination/RAM read. The unchanged shared time induction
then derives every native read, write and terminal payload range from actual
public Sail seeds and native matching. [One short public claim](Airbender/Review/Trace/Families/SubwordMemory/Values.lean)
uses the same actual public state for initialization and full sparse decoder
construction. No per-row bound, clock, expected read, result, intermediate state
or table-equivalence premise is introduced.

[Eight complete initialized decoded traces](Tests/SubwordWordBounds.lean)
exercise all six forms, RAM/ROM-shadow loads, actual SB/SH writes, x0 and an
rs1=rd alias consuming the source refresh at clock four. Independent actual
instruction bytes and register/data bytes now share one public Sail state.
Three new row copies change only shadow read/selection columns when the shadow
overlaps instruction address zero; earlier fixtures remain unchanged. Every
native equation and lookup is checked. This joins decoding and logical memory
initialization; architectural data-ROM lookup contents remain a separate binding.

[Boundary regressions](Tests/SubwordPackedBounds.lean) retain the largest native
key, maximal byte merges, halfword/unused rows and the insufficiency of separate
contribution bounds. A Mersenne31 packed-field alias explains why raw funct3
ranges matter; the integrated claim derives those ranges from actual original
public decoding. These regressions do not establish a confirmed defect.

Draft combined fixture/closed-relation assembly checks hit Lean's allocation
cap and terminated with no surviving owned workers. Three native certificates
are now split, and one generic assignment-transport lemma precedes finite
specialization. The final checks preserve all default/resource ceilings; no
memory increase, semantic restriction, truncated table or expected-result
assumption was introduced. The disjoint-merge and two-read history arguments
adapt the pinned v3 source with accurate provenance; shared Clean/Sail/value
semantics and native v2 sources/artifacts/exporter are unchanged.

Next work binds bounded source/old-RAM words and native effective addresses,
size/sign/offset selectors and load/store packed fields to original Sail byte/
halfword effects, then prepares/retires and composes full subword execution.
Architectural instruction/data-ROM projection remains explicit. Delegation/
custom/CSR, unified execution, initialization/teardown and terminal/padding
boundaries remain unfinished. General Rust/JSON/compiler refinement and physical
verifier/cryptographic enforcement remain separate. FINDINGS and its historical
archive are unchanged; no confirmed defect is added. The original checkout is
preserved and no push/publication is authorized.

## Initialized native subword address checkpoint (2026-10-21)

[Native Mersenne31 addition](Airbender/Proofs/SubwordMemory/AddressArithmetic.lean)
now derives the effective RV32 byte address from the actual source and decoded
immediate limbs. The existing word-memory carry calculation is reused with the
checked native subword equation indices. Both scalar address queries supply
canonical limbs; low and high carries retain native RV32 wraparound.

[Offset and port geometry](Airbender/Proofs/SubwordMemory/Address.lean) derives
canonical native offset-key packing from the ranged address, original raw
funct3/x0 fields and native store Booleanity. Accepted fixed-table membership
then yields the byte offset. Native subtraction recovers the containing aligned
word without field wrap or natural underflow. Its address is exactly byte-address
floor division by four, including the top RV32 word, and adding the derived
offset recovers the byte address. The actual mixed load/store port address is
that containing word; no cell, address, alignment or expected-result premise is
supplied.

[Initialized assembly](Airbender/Proofs/Trace/Families/SubwordMemory/Address.lean)
uses the same original public Sail state for seed reads and full sparse decoding.
The established history supplies the actual first-port source range; original
decoding supplies the immediate and raw/x0 ranges. [One short public claim](Airbender/Review/Trace/Families/SubwordMemory/Address.lean)
derives actual public source evidence, decoded metadata and every native address
property. No caller-supplied row read, bound, clock, flag or intermediate state is
added. The observables remain in Review and all arithmetic/assembly remains in
Proofs.

[Eight unchanged complete initialized traces](Tests/SubwordAddresses.lean) now
exercise address and port geometry for all six forms, actual SB/SH writes, x0,
ROM-shadow/RAM data and a source/destination alias. [Two split complete-native
boundary certificates](Tests/SubwordAddressBoundaries.lean) retain all 51 native
equations and 14 lookups each: 0xffffffff plus one wraps to zero with both native
carry levels, and zero plus original sign-extended minus three yields byte
address 0xfffffffd and containing word 0xfffffffc. Actual original instruction
decoding and native metadata/query fields are checked. The boundary certificates
are address regressions; they do not claim original instruction execution.

Next work binds width/sign/offset selectors and the bounded source/old-memory
words to original Sail byte/halfword load/store effects, then prepares/retires
and composes full subword execution. Architectural instruction/data-ROM
projection remains explicit. Delegation/custom/CSR, unified execution,
initialization/teardown and terminal/padding boundaries remain unfinished.
General Rust/JSON/compiler refinement and physical verifier/cryptographic
enforcement remain separate. FINDINGS and its historical archive are unchanged;
no confirmed native defect is added. Resource ceilings are unchanged, the
original checkout is preserved and no push/publication is authorized.

## Initialized native subword load-value checkpoint (2026-10-21)

[Two shared mathematical lemmas](Airbender/Proofs/SubwordMemory/ByteMath.lean)
copy the pinned v3 statements and proof bodies unchanged: bounded limb sign/
zero extension and byte/halfword extraction. [The v2 connection](Airbender/Proofs/SubwordMemory/LoadExtension.lean)
uses the actual raw-funct3/two-bit-offset keys and the already certified complete
literal native load tables. It retains odd-halfword zero rows and unused keys;
no native v3 field, inverse, key, table or selector identity is imported.

[Native data controls](Airbender/Proofs/SubwordMemory/DataControls.lean) recover
raw funct3, load and x0 key bits without Mersenne31 wrap. Original decoded fields
and actual fixed-offset membership derive the subword mux and upper selector.
Retained halfword loads and stores align through absence of the native trap bit.
Discarded loads retain the native waiver; unconditional alignment is not assumed.
[Exact ROM indexing](Airbender/Proofs/SubwordMemory/ROMAddress.lean) proves that
the native inverse-of-four query names the actual containing word index, then
recovers both complete ROM limbs, including native UNIMP padding. Architectural
instruction/data-ROM byte binding remains separate.

[Actual native load data](Airbender/Proofs/SubwordMemory/LoadData.lean) derives
both offset bits, the selected limb and the packed key from accepted controls
and actual bounded words. Native RAM/ROM candidates then equal the original
Sail extension of the selected byte/halfword slice. The actual x0 flag controls
the actual masked write. [Initialized assembly](Airbender/Proofs/Trace/Families/SubwordMemory/LoadData.lean)
and [one short public claim](Airbender/Review/Trace/Families/SubwordMemory/Loads.lean)
use one original public state for seed reads and full sparse decoding. Existing
history supplies actual read bounds; no row read/range, sign, size, alignment,
expected result, table equivalence or intermediate state is supplied.

[Eight unchanged complete initialized traces](Tests/SubwordLoadData.lean) retain
all six forms, actual stores, x0, aliases and distinct native ROM versus logical
instruction-shadow data. [Independent boundary checks](Tests/SubwordLoadExtension.lean)
exercise signedness thresholds, all byte positions and odd-halfword helper rows.
[A ninth complete initialized decoded trace](Tests/SubwordOddX0.lean) retains
odd LH-to-x0 with every native equation, lookup, state/memory match and actual
public byte/seed read. Its offset is three, both candidate limbs are zero and
the actual masked write is zero. This prevents treating unconditional halfword
alignment as a consequence of the accepted logical relation. Original Sail
access/exception/retirement comparison for this case remains unproved; neither
an original instruction success nor a defect or repair is claimed here.

Next work connects store byte-window effects, actual architectural read/write
history and ROM bytes, native subword PC/prepare/retire behavior and full original
instruction execution. Delegation/custom/CSR, unified execution, initialization/
teardown and terminal/padding boundaries remain unfinished. General Rust/JSON/
compiler refinement and physical verifier/cryptographic enforcement remain
separate. FINDINGS and its exact historical archive are unchanged; no confirmed
native defect is added. Resource ceilings are unchanged, the original checkout
is preserved and no push/publication is authorized.

## Initialized native subword store-byte checkpoint (2026-10-21)

[Pure byte arithmetic](Airbender/Proofs/SubwordMemory/StoreBytes.lean) adapts the
pinned v3 natural-merge/BitVec argument, using native v2 clearing arithmetic and
separate whole-word bounds at default recursion and heartbeat limits. No native
v3 field, column, table, key, selector or mapping premise is copied.
[The native connection](Airbender/Proofs/SubwordMemory/StoreData.lean) reconstructs
both actual packed keys and clearing/placement outputs from bounded actual reads.
Disjoint contributions cannot wrap Mersenne31 or carry beyond the selected limb.
The accepted native size/upper muxes and actual write equations then give the
complete merged word and each changed/preserved byte. SB selects exactly the
low source byte at any of four positions; SH selects the low source halfword at
either aligned position. Original decoding and the native offset mask derive
SH alignment. Complete literal table domains, including unused/odd rows, remain
unchanged; no aligned-domain table replacement is used.

[Initialized assembly](Airbender/Proofs/Trace/Families/SubwordMemory/StoreData.lean)
extracts both actual data-port and old-word-port read bounds from accepted history.
[One short public claim](Airbender/Review/Trace/Families/SubwordMemory/Stores.lean)
uses the same original public state for initialization and full sparse decoding.
No expected source/old word, range, alignment, selector, packed-key identity,
written value, table equivalence or intermediate state is supplied. Review adds
only the actual old-word observable, byte-window result and short theorem;
calculation and proof assembly remain under Proofs.

[Eight unchanged complete native traces](Tests/SubwordStoreData.lean) pass the new
claim, preserving all original memory/state matches and public code/seed reads.
Concrete accepted SB at offset three changes 0x89cd4567 to 0xabcd4567 from source
0xdead12ab; accepted SH changes it to 0x89cd12ab. Nonzero high source bits are
discarded and unselected old bytes are preserved. All-input byte correctness is
kernel proved, rather than inferred from these examples.

Next work connects these derived load/store values and addresses to actual
architectural memory/ROM read-write history, original Sail access/exception
behavior, native PC/prepare/retire behavior and full original subword execution.
The accepted odd LH-to-x0 case still has an open original exception comparison;
this store-byte checkpoint does not resolve or reclassify it. Delegation/custom/
CSR, unified execution, initialization/teardown and terminal/padding boundaries
remain unfinished. General Rust/JSON/compiler refinement and physical verifier/
cryptographic enforcement remain separate. FINDINGS and its exact historical
archive are unchanged, with zero confirmed native defects. Resource ceilings
are unchanged, the original checkout is preserved and nothing is pushed.
