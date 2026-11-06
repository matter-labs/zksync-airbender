# V3 adaptation snapshot — 6 November 2026

## Exact sources

The current reference is [PR #585](https://github.com/matter-labs/zksync-airbender/pull/585)
at b29277dd895499574e317a994fd89243a72f06cb, based on
c1a662222cafcd96db4383dce737edb79fa62b09. GitHub head metadata and the read-only
source checkout agree. Its status reports a successful parent warm run and
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
