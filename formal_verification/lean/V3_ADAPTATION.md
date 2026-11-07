# V3 adaptation snapshot — 6 November 2026

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
