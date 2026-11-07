# V3 adaptation snapshot — 6 November 2026

## Exact sources

The current reference is [PR #585](https://github.com/matter-labs/zksync-airbender/pull/585)
at b29277dd895499574e317a994fd89243a72f06cb, based on
c1a662222cafcd96db4383dce737edb79fa62b09. The proof reference remains deliberately
pinned. The live source checkout advanced externally to 964db88d323d7f04a258f38bce28eca1c6d31652;
its reviewed four-path delta contains only status/replay timing changes, no Lean
statement/proof, native input or dependency change. Its status reports a successful parent warm run and
explicitly leaves final full assurance pending. That is not a v2 test result.
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
