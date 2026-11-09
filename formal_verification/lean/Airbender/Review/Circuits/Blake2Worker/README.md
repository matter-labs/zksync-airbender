# Native Blake2 worker review guide

[Fresh native artifact](NativeArtifact.lean), [Native source](../../../../../../cs/src/delegation/blake2_round_with_extended_control/mod.rs), [Local control root](ControlTheorems.lean), [Proof calculations](../../../Proofs/Blake2Worker/NativeControl.lean), [Import fidelity](../../../Import/Blake2Worker.lean), [Reproduction gate](../../../../scripts/check_native_blake2.py), [Theorem regressions](../../../../Tests/NativeBlake2Worker.lean), [Intake controls](../../../../Tests/NativeBlake2WorkerImport.lean).

The selected runtime worker has CSR1991 and trace2^20. Fresh352-equation,
871-variable native compilation and all296 local lookups are retained separately
from historical generated files. Its parsed layout matches the pinned historical
JSON exactly; no historical Lean worker acceptance is reused by an assumption.

The ABI exposes processor multiplicity0,ABIhigh1 and time740/741; register10
reads a state pointer with24 read/write indirects, register11 reads a message
pointer with16 readonly indirects, register12 retains its old control read and
write. All43 access descriptors and old timestamps remain. This observes
coordinates, not initialized memory values, permission/alignment or issued work.

Review owns observables and the short control theorem. Proofs derive all13 actual
Boolean flags, both high-half13bit bounds and x12 low clearing using the native
packing equations. Import consumes every local equation and scalar/timestamp/
fixed lookup; full same-read raw protocol/clock metadata stays explicit and
uninterpreted. The local control root remains generic in the explicit four-field setup; the separately certified native fixed pool is now available below. Existing main-circuit intake remains fail closed.

Positive control slices cover only16 actual equations, including zero and
multiple round flags. They do not establish complete native acceptance, valid
round scheduling, v3F02/F03/F04 reproduction or a defect. ABI alignment/addresses/ranges, processing flags/clocks, full memory matching,
reference state/round effects, issued/unissued request/auxiliary/accumulator
connections, fulfillment/converse/accounting/terminal/protocol remain open.
General compiler/Rust/JSON/physical/field/LDE/crypto/completeness boundaries and
main CSR/MOP execution are unchanged. No native production code is modified.

## Actual native fixed pool

[Native literal pool](../../../../artifacts/setup/blake2-fixed-native.json), [Table model](Tables.lean), [Membership/output roots](TablesTheorems.lean), [XOR7 certificate](../../../Proofs/Blake2Worker/Xor7Certificate.lean), [XOR9 certificate](../../../Proofs/Blake2Worker/Xor9Certificate.lean), [Literal importer](../../../Import/Blake2Fixed.lean), [Native reproduction](../../../../scripts/check_blake2_fixed.py), [Regressions](../../../../Tests/NativeBlake2Fixed.lean), [Intake controls](../../../../Tests/NativeBlake2FixedImport.lean).

The complete344384row pool has tag4 byte XOR at0, tag26 XOR3 at65536,
tag27 XOR4 at65600, tag28 XOR7 at65856 and tag29 XOR9 at82240. Every
stored row participates, and actual membership derives both operand domains,
tag isolation and exact XOR semantics. Byte literal columns equal the retained
main certificate's columns, with a different native pool offset. Only those
literal bindings reuse old results; neither whole-table identity nor worker
acceptance is assumed. Other output regions are checked over every stored row.

The strict importer retains all source bytes and validates all five regions;
calculation units preserve transparent literals. Generic finite16-element
windows are proved sound for the original block checker, with symbolic dense
array-size proofs. This split is necessary for the unchanged resource limits.
Native exporter/independent every-row/repeat-byte controls and Lean importer
controls remain separate fidelity checks from kernel semantics.

The208 actual compiled fixed queries now connect to these table roots through
the separate complete lookup-effects theorem below. No complete positive accepted worker row, initialized worker
memory/history, valid control schedule, native processing/auxiliary relation,
request-worker fulfillment/converse/accounting or unified protocol is inferred.
No main GPR/RAM frame is transported across unproved delegated actions.

## Complete local lookup effects

[Public lookup root](QueriesTheorems.lean), [Observables](Queries.lean), [Same-read query artifact](QueryArtifact.lean), [Separate intake](../../../Import/Blake2Queries.lean), [Native projection](../../../Proofs/Blake2Worker/NativeQueryProjection.lean), [Result assembly](../../../Proofs/Blake2Worker/NativeQueryResults.lean), [Regressions](../../../../Tests/NativeBlake2Queries.lean), [Intake controls](../../../../Tests/NativeBlake2QueriesImport.lean).

Complete local native acceptance on the actual fixed pool derives the exact
native tags, both operand/output domains and XOR results for every208 fixed
query, plus the2 scaled-pointer and86 timestamp-difference expression bounds.
The reference tag order is kernel-bound to the actual compiled source, never a
per-row premise. Native scalar/timestamp modeled-table scopes are unchanged.

The original worker importer is unchanged. A separate same-read observer uses
its strict parser and unchanged expression emitters. Kernel source-byte equality
and actual sublist/lookup syntax bindings connect both intakes. Pure syntax
calculations and small query units avoid evaluating witness expressions while
binding the source; generic typed getters handle assembly at default limits.
No heartbeat, recursion, memory or wall ceiling is raised.

Static native lookup counts do not measure worker issuance. Timestamp bounds
apply to differences, not raw old or processing clocks; scaled-pointer bounds
do not supply initialized read ranges. Raw ABI reads, alignment/addresses,
processing multiplicity, all43 memory/clock histories, round/reference/state/
terminal, accepted auxiliary/accumulator/caller-worker and fulfillment/converse/
accounting/protocol connections remain open. Query/scalar/clock slices are not
complete native worker witnesses, F02/F03/F04 reproductions or native defects.

## ABI-local memory laws

[Public root](MemoryTheorems.lean), [Observables](Memory.lean), [Actual descriptor/equation/query bindings](../../../Proofs/Blake2Worker/NativeMemoryProjection.lean), [Canonical arithmetic and assembly](../../../Proofs/Blake2Worker/NativeMemory.lean), [Regressions](../../../../Tests/NativeBlake2Memory.lean).

Complete local native acceptance derives canonical state/message low-pointer
alignment128/64 and scalar-implied bounds8388608/4194304, without supplied raw
read bounds. Every one of43 ABI old timestamps is bound to its actual compiled
low/high difference expressions and Boolean borrow equation. Both readonly
register descriptors, every old read and25 written accesses stay visible.
These results do not supply16bit initialized reads, address-carry/ROM/RAM
semantics, raw-clock ranges/order, processing multiplicity, native matching,
worker execution/issuance or protocol accounting. Allscalar slices are explicitly
partial; no complete positive worker witness, F03/F04 evidence or defect follows.
The next connection must derive ranges/states/clocks from real initialized
worker memory and accepted native/protocol matching, retaining every token.

## Normalized native processing conventions

[Logical contract](Processing.lean), [Short root](ProcessingTheorems.lean), [Descriptor artifact](ProcessingArtifact.lean), [Separate intake](../../../Import/Blake2Processing.lean), [Proof calculations](../../../Proofs/Blake2Worker/NativeProcessing.lean), [Regressions](../../../../Tests/NativeBlake2Processing.lean), [Intake controls](../../../../Tests/NativeBlake2ProcessingImport.lean), [Pinned native quotient](../../../../../../prover/src/prover_stages/unrolled_prover/quotient_parts/every_row_except_last.rs).

The native quotient's processing conventions are separate from the352 JSON body
equations. Their reviewed source references retain half-domain scaling:
(tau*m)*(tau*m-1) and(tau*m-1)*tau*value. Individual unit-normalized polynomials
form an explicit logical acceptance input alongside the complete original body.
Kernel calculations bind those polynomials to the reference terms; no physical
point is assumed unit-normalized, and LDE/quotient/challenge/last-row enforcement
remains separate. The parser/old artifact stay unchanged.

The same-read descriptor walk retains225 masked columns, unique and exactly
covering all226 physical memory fields together with multiplicity. Under this
stronger logical interface, multiplicity is Boolean; when zero, ABI/time/all43
oldread/readonly-refresh/all25 written fields are zero. No active flag or desired
read/result/clock/state/request/worker answer is supplied. Active raw clocks,
memory keys/matching/initialized ranges, unused-token cancellation, issuance/
auxiliary/accumulator/accounting/converse and complete reference execution remain
open. In particular this does not exclude multiplicity-one zero-clock workers.
Convention-only positive/scaling slices are not full accepted worker witnesses,
F03 evidence or native defects. No production fix or issue assumption is added.

## Unused memory keys and products

[Native key references](MemoryKeys.lean), [Short roots](MemoryKeysTheorems.lean), [Kernel bindings/calculations](../../../Proofs/Blake2Worker/NativeMemoryKeys.lean), [Regressions](../../../../Tests/NativeBlake2MemoryKeys.lean).

All43 descriptors keep actual register/indirect order and every read/write side,
including18 readonly timestamp refreshes and25 explicit writes/OLDREADs. Worker
write time is the same imported processor740/741 for all43 accesses; no invented
in-cycle offsets/order or alias deduplication. Native register indicator1/RAM0
is distinct from main history address-space coding and needs a separate bridge.

Stage-two references explicitly truncate base limbs to16bits, carry low offset
overflow and return failure on high overflow. Quotient unit references use
rawfield low+offset/high with the actual empty-carry metadata. Source pins cover
unchanged helpers/driver/walk. These reviewed definitions are not general Rust/
field representation/LDE/physical verifier refinement. Active keys are not equated
without initialized bounds/alignment/no-carry. The stronger normalized processing
contract derives memory zeros for unused rows, hence every address/key succeeds
and both reference read/write keys agree. All43 affine factor products equal in
arbitrary rings/challenges before division. No inverse/nonzero/compression
injectivity, native auxiliary, global matching/issuance/converse/accounting or
multiplicity-one zero-clock exclusion follows. Reference carry/wide-pointer/zero
factor slices are not full accepted worker witnesses or native defects.

## Auxiliary acceptance and complete-domain memory balance

[Typed slots](AuxiliaryColumns.lean), [Same-read intake](AuxiliaryArtifact.lean),
[Logical source-reference interface](Auxiliary.lean), [Short roots](AuxiliaryTheorems.lean),
[Calculations](../../../Proofs/Blake2Worker/NativeAuxiliary.lean),
[Regressions](../../../../Tests/NativeBlake2Auxiliary.lean),
[Intake controls](../../../../Tests/NativeBlake2AuxiliaryImport.lean).

Separate quartic slots1064/1068..1236/1240 never become body logical variables.
The explicit normalized source polynomials retain all43 factors, literal initial
chain1, actual adjacent grand values, first boundary1 and terminal public claim.
A division-free telescope derives row and1048575-row memory product balance;
no terminal claim1 or nonzero/injective compression assumption. Source normalization
is not a physical quotient/LDE/challenge-separation or general Rust refinement.
Memory matching/initialization, active bounds/keys/raw clocks and delegation sum/
issuance/converse/accounting remain open. Full accepted positive worker witnesses
and reference/round/state/terminal effects are still required; no main frames
cross unproved worker actions. Zero-factor/reference slices are not defects.

## Delegation sum and unified claim component

[Acceptance and observables](Delegation.lean), [Short roots](DelegationTheorems.lean),
[Worker calculations](../../../Proofs/Blake2Worker/NativeDelegation.lean),
[Polynomial sum interface](../../Helpers/Memory/DelegationSum.lean),
[Generic sum calculations](../../../Proofs/Memory/DelegationSum.lean),
[Regressions](../../../../Tests/NativeBlake2Delegation.lean).

The ordinary-row auxiliary sum is derived from the native zero/last-point divisor,
actual slot1064 samples, primitive domain and degree bound; it is not supplied as
an answer. Exact native unified add-main/subtract-worker claim folding connects
returned main claims to derived worker sums. Main claims are still opaque, not
identified caller rows or an issued ledger. Native multiplicity-one auxiliary
relations derive nonzero denominators; inactive poles are not excluded. Physical
FFT/M31Quartic/LDE/quotient and global dispatch/capacity/challenge boundaries remain
separate. Scalar sums do not imply matching/converse/accounting. Pure degree-alias/
scalar-collision tests are not complete worker witnesses or native defects.

The stronger [main caller/component roots](../ReducedMachine/DelegationTheorems.lean)
now replace opaque main claims with derived full main-row auxiliary sums under
an explicit main-body/auxiliary/polynomial contract. This still supplies no
initialized caller stream, inactive-row filtering, matching, fulfillment/converse/
accounting or physical/global capacity/sequence/dispatch/challenge enforcement.

## Configured worker capacity component

[Capacity and exact multiplicity roots](CapacityTheorems.lean),
[observations/native component](Capacity.lean),
[calculations](../../../Proofs/Blake2Worker/NativeCapacity.lean),
[configured caller composition](../ReducedMachine/ConfiguredDelegationTheorems.lean),
[regressions](../../../../Tests/NativeBlake2Capacity.lean).

The selected native source loop adds1048575 configured slots per returned
Blake2 proof and checks the total below2147483647. Metadata retains sequence0,
type1991, configured setup-cap equality and shared memory/delegation challenges;
the public32-bit proof count is tied to the full returned list. Both security
labels remain explicit source-reference dispatch observations, not Rust execution
certificates. Existing normalized worker acceptance derives Boolean processing
multiplicities; symbolic indicator arithmetic gives the actual multiplicity sum's
canonical value equal to the active-row count, bounded by capacity, and at most2048
selected proofs. Source bytes/constructor bindings are pinned separately from
physical setup/dispatch/ProofOutput/transcript refinement.

The same returned list participates in the existing full caller/worker scalar
sum component. All ordinary auxiliary values and inactive poles remain. Bounds
and scalar balance do not prove issued-stream matching, fulfillment, converse,
accounting or active initialized reads/clocks/addresses. Full43-token matching,
initialization and active key refinement are next; no main frame crosses an
unproved delegated action. Fourteen pure/reference/conditional regressions are
not full positive native witnesses or defect/F02-F04 evidence. No production,
artifact, old intake, exporter, dependency or literal data changes.

The [native public memory-boundary component](../ReducedMachine/MemoryBoundaryTheorems.lean)
now combines the unchanged full43-chain/full-domain worker products with actual
returned-claim and32-register/PC source boundary factors. All returned workers,
readonly refreshes, OLDREADs, writes and inactive rows remain; no worker factor
is cancelled or assumed nonzero. Main grand claims remain full opaque protocol
outputs. This is not token matching/initialized memory, active key/clock bounds,
issuance/accounting or physical Rust/field/quotient/refinement evidence.

The stronger [main auxiliary component](../ReducedMachine/MainAuxiliaryTheorems.lean)
now identifies actual returned main claims with their full source chain products
before composing with all worker factors and public boundaries. Execute masking
remains a field polynomial; initialization is unmasked and every ordinary row
remains. No factor cancellation, token matching/initialized-read/active-clock/
issuance/accounting or physical/refinement claim is inferred.

[Lossless native token transport](../ReducedMachine/MemoryTokenTheorems.lean)
retains all43 raw quotient keys on each side, including inactive rows, readonly
refreshes and the common processor timestamp. Exact decode and challenge-factor
transport preserve separate field limbs without16-bit/raw-clock premises. This
closes the native indicator/Clean space encoding gap, not stage2 truncation
refinement, actual matching, initialized reads, worker effects or accounting.

[Same-main-proof composition](../ReducedMachine/MainArgumentTheorems.lean) now
feeds both checked global components from identical main body/auxiliary fields
and the same configured worker batch/challenges. All worker rows remain. Scalar/
product/capacity conclusions still do not establish matching or initialized reads.

[The complete native CSR caller fixture](../../../../Tests/NativeCSRPositive.lean)
now exercises initialized original-source/request observations and clock7 with
all117 main equations/22 lookups and aliased GPR matching. It executes no worker.
A separate execute0 BODY witness still requests; full-domain padding/global
accounting must be checked before filtering. No F03 defect or worker acceptance
is inferred from this weaker boundary.

## Complete local active-worker fixture

[The explicit positive worker row](PositiveRowTheorems.lean) satisfies all 352 native equations,
296 actual lookups and 226 normalized processing conventions. Its source retains
all ports and aliases. This local fixture supplies no source/global/worker-trace
acceptance, initialized memory history, issued request or Sail effects; those
combined obligations and parity remain open.

## Native worker message schedule

[Worker schedule](../../Trace/Families/ReducedMachine/WorkerScheduleTheorems.lean) derives all13 control bits, compression inputs,
all32 selected-message limbs and exact x12 update from FULL native BODY. The same
counted source retains initialized replay/word bounds and covers every ordinary
worker including inactive rows. Zero/multiple round bits stay visible. Standard
hash results, physical round schedules, converse accounting and worker Sail remain open.

## Native worker state initialization

[Worker initialization](../../Trace/Families/ReducedMachine/WorkerInitialTheorems.lean) derives all32 pre-mixing limbs and all16
final-XOR base limbs from actual original reads/control bits. Same counted source
retains exact replay, word bounds and prior schedule for every ordinary worker.
G mixing, rotations/XOR, hash results, physical schedules and converse accounting remain open.

## First native G A/D steps

[First G steps](../../Trace/Families/ReducedMachine/WorkerFirstGTheorems.lean) derive weighted Boolean carries, field sum/D bounds
and exact XOR/rotate16 for all four column calls from FULL native BODY/fixed pool.
Same counted source retains prior initialization/schedule/replay/word bounds.
Whole-word addition, remaining G steps, hash results and physical schedules remain open.

## Initialized first G wrapping additions

[Initialized additions](../../Trace/Families/ReducedMachine/WorkerAdditionTheorems.lean) derive all four first A wrapping sums from
the SAME counted source and initialized raw read-token bounds. Natural weighted
messages retain zero/multiple round bits and wide limbs; prior exact D rotation,
initialization, replay and word bounds stay. Full G/hash and physical schedules remain open.

## First native column C/B steps

[First C/B steps](../../Trace/Families/ReducedMachine/WorkerCBTheorems.lean) derive actual Boolean carries, C/B limb bounds and
exact XOR/rotate12 from FULL native BODY/fixed pool. The SAME counted initialized
source derives four C wrapping additions, retaining prior A/D, weighted messages,
replay and word bounds. Second G steps, full hash and physical schedules remain open.

## Second native column A/D steps

[Second A/D steps](../../Trace/Families/ReducedMachine/WorkerSecondADTheorems.lean) derive second A wrapping additions and D XOR/rotate8
from FULL native BODY and the SAME initialized counted source. Actual B bounds,
native carry bits and prior weighted messages supply inputs; all prior effects stay.
Second C/B, diagonal calls, full hash and physical schedules remain open.

## Complete native column G arithmetic

[Column G](../../Trace/Families/ReducedMachine/WorkerColumnGTheorems.lean) derives second C wrapping additions/B XORrotate7 and assembles
all four COLUMN intermediate output vectors into pure G with derived pre-G inputs
and weighted messages from the SAME counted source. Prior effects stay. Diagonal
calls, finalization/full worker hash and physical schedules remain open.

## Native diagonal G entry steps

[Diagonal entry](../../Trace/Families/ReducedMachine/WorkerDiagonalFirstTheorems.lean) derives canonical routed post-column inputs and all
four first diagonal wrapping A additions/D XORrotate16 results from the SAME
counted source. Prior column G/replay effects stay. Remaining diagonal steps,
finalization/write-result/full hash and physical schedules remain open.

## First-half native diagonal G arithmetic

[Diagonal first half](../../Trace/Families/ReducedMachine/WorkerDiagonalCBTheorems.lean) derives C wrapping additions/B XORrotate12 and
assembles all four first-half G vectors on derived routed inputs/weighted messages
from the SAME counted source. Prior column G/replay effects stay. Second diagonal
steps, finalization/write-result/full hash and physical schedules remain open.

## Second native diagonal A/D steps

[Second diagonal A/D](../../Trace/Families/ReducedMachine/WorkerDiagonalADTheorems.lean) derives wrapping A additions and chained D
XORrotate8 from the SAME counted source and derived first-half inputs/weighted
messages. Prior column G/diagonal first-half/replay effects stay. Second C/B,
finalization/write-result/full hash and physical schedules remain open.

## Complete native diagonal G arithmetic

[Diagonal G](../../Trace/Families/ReducedMachine/WorkerDiagonalGTheorems.lean) derives final C/B steps and all four complete diagonal G
results, retaining all four column G and initialized replay effects from the SAME
counted source. These are intermediate results; native final writes, full worker
reference round/hash and physical schedules remain open.

## Actual native extended-state write results

[Extended outputs](../../Trace/Families/ReducedMachine/WorkerExtendedOutputTheorems.lean) binds all32 actual write limbs and16 words to the
checked diagonal G results, retaining all eight G calls and initialized replay on
the SAME counted source. First8-state finalization, full worker reference hash
and physical round schedules remain open.

## Actual native state-write finalization

[Finalization](../../Trace/Families/ReducedMachine/WorkerFinalizationTheorems.lean) derives all8 actual state words as selected base/extended
XOR or exact previous-read copies, retaining all G/extended-write/replay effects
on the SAME counted source. Full reference worker round/hash assembly and physical
round schedules remain open.

## Complete native weighted worker transition

[Transition](../../Trace/Families/ReducedMachine/WorkerTransitionTheorems.lean) derives all25actual writable ABI outputs from read inputs
only, retaining zero/multiple masks, eight G calls and prior initialized replay.
This closes pointwise reference assembly; physical round sequencing, standard
scheduled full hash and protocol/Sail/accounting boundaries remain open.

## Common initialized worker pre-state

[Snapshot](../../Trace/Families/ReducedMachine/WorkerSnapshotTheorems.lean) derives ALL43exact reads from one initialized pre-state
and all25writable reference outputs from those samples, retaining prior replay.
MAIN partial dependencies remain. Grouped post-state/frame, physical scheduling,
standard scheduled hash and protocol/Sail/accounting boundaries remain open.

## Grouped native worker post-state

[Grouped block](../../Trace/Families/ReducedMachine/WorkerGroupTheorems.lean) derives ALL43post-write tokens, unaffected-address
frame and complete residual replay for each active worker, with all25reference
outputs sampled from pre/post states. One jointly grouped trace for ALL workers,
physical scheduling and protocol/Sail/accounting boundaries remain open.

## One shared native block execution

[Joint replay](../../Trace/Families/ReducedMachine/JointReplayTheorems.lean) places ALL active worker43-port blocks and MAIN
port singletons in ONE complete initialized raw-token execution. Each worker
has exact pre/post samples, all25reference outputs and an unaffected-address
frame within that same order. Physical round scheduling, standard scheduled
hash, caller activity/converse accounting and the prior Sail/physical boundaries
remain open.

## Exact aggregate worker-key accounting

[Key accounting](../../Trace/Families/ReducedMachine/DelegationKeyAccountingTheorems.lean) derives active-worker raw clock/key uniqueness
from actual x12 writes and proves every raw-key caller aggregate is the exact
0/1 worker indicator, retaining all caller rows. This is aggregate accounting;
individual caller Booleanity/activity and per-call issuance bijection remain
open alongside physical scheduling/Sail/cryptographic boundaries.

## Complete mixed caller queries

[Mixed queries](../../Trace/Families/ReducedMachine/CallerMixedQueriesTheorems.lean) derive all four actual tuples and runtime-pool
memberships on every ordinary caller row, including inactive rows, without a
valid-mask or activity premise. All sixteen query equations are kernel-bound
before evaluation. Individual caller Booleanity/activity and per-call accounting
remain open; prior aggregate accounting and joint execution are retained.

## Individual caller validity

[Caller validity](../../Trace/Families/ReducedMachine/CallerValidityTheorems.lean) derives Boolean weights and exact zero-or-one
request shape on all ordinary rows, including inactive rows, with raw key1991
and bounded ABI for nonzero requests. Full mixed queries and actual table outputs
exclude the competing pattern. Activity and per-call accounting remain open;
no full mask, activity, expected key/range or Boolean weight is supplied.

## Natural caller counts

[Caller counts](../../Trace/Families/ReducedMachine/CallerCountTheorems.lean) derive count=workerIndicator+p*q with q<=31
over every original caller occurrence. Any deviation requires at least257 MAIN
proofs; up-to256 batches have exact per-key counts. No no-wrap/count/activity
premise is added. Universal activity/per-call matching remains open.

## Request-position matching

[Original-index matching](../../Trace/Families/ReducedMachine/CallerPositionTheorems.lean) derives unique partners in both
directions OR at least 257 MAIN proofs. Request-positive inactive callers remain
included. No count/activity/matching premise is added; physical activity and
larger-batch matching remain open.

## Initialized x12 control history

[Actual control chain](../../Trace/Families/ReducedMachine/ControlHistoryTheorems.lean) derives the complete zero-seed-to-public
raw-token path, every actual MAIN control edge and every active worker port42
update. No path/reset/round/schedule premise; zero/multiple masks and both raw
times stay. Physical enforcement, caller activity and standard hash remain open.

## Public x12 control origins

[Actual public origins](../../Trace/Families/ReducedMachine/ControlOriginTheorems.lean) derives an executing MAIN third-port
zero-to-nonzero high-field write bound to a fetched public rd12 entry for every
nonzero control on the initialized path and every nonzero active worker input.
Readonly refreshes, both raw times and zero/multiple masks remain. No reset or
schedule premise; physical activity and standard round/hash sequencing remain open.

## Actual CSR control resets

[CSR control effects](../../Trace/Families/ReducedMachine/ControlCSRTheorems.lean) derives BOTH zero output limbs for actual
CSR1991 and puts all decoded rd12 CSR edges on the same initialized x12 path.
Nonzero public origins are ordinary code or CSR1984; the bounded oracle remains
an observation. No reset/schedule premise or original CSR/worker Sail claim.

## Initialized arithmetic control writes

[Arithmetic control effects](../../Trace/Families/ReducedMachine/ControlArithmeticTheorems.lean) derives actual ADD/ADDI/SUB/LUI/AUIPC
values from initialized reads and original PC/immediate, retaining rd/x0 and RV32
wrap. All rd12 arithmetic/CSR edges share one complete x12 path. Other reset
profiles, last-reset identification and a standard worker schedule remain open.

## Initialized logic control writes

[Logic control effects](../../Trace/Families/ReducedMachine/ControlLogicTheorems.lean) derive bitwise/comparison values from actual
initialized tokens and original immediate selection. Comparison high always clears;
all rd12 logic/arithmetic/CSR edges share one complete x12 path. Shift/jump/LW
resets, last-reset identification and standard worker scheduling remain open.

## Initialized shift and jump control writes

[Shift/jump control effects](../../Trace/Families/ReducedMachine/ControlShiftJumpTheorems.lean) derive actual SLL/SRL/SRA and JAL/JALR
writes, with input bounds and public PC alignment derived internally. All rd12
shift/jump/logic/arithmetic/CSR edges share one complete x12 path. LW reset values,
last-reset identification and standard worker scheduling remain open.

## Initialized LW control writes

[LW control effects](../../Trace/Families/ReducedMachine/ControlLoadTheorems.lean) derive effective address/alignment and actual
ROM-or-initialized-RAM writes, retaining distinct ROM shadows. All ordinary rd12
write families share one complete x12 path; SW remains a memory write. Last-reset
identification and standard worker scheduling remain open.

## Last relevant control reset

[Last reset and worker suffix](../../Trace/Families/ReducedMachine/ControlLastResetTheorems.lean) derive the last actual public MAIN value
change before every target/active-worker read, or BOTH seed-derived zero limbs.
Every following copy/worker edge remains; nonzero high comes from that last reset.
Exact worker-count folds, physical scheduling and standard hash remain open.

## Control folds over worker path positions

[Exact control folds](../../Trace/Families/ReducedMachine/ControlFoldTheorems.lean) derive both target limbs by iterating the native
update from the last reset over ALL matching worker42 path-edge positions.
Equal-value/zero-mask updates and MAIN copies remain; count bounds and zero IFF
no worker are derived. Original worker-source occurrence bijection, issued-call
counts, physical scheduling and standard hash remain open.

## Original worker-source positions

[Source-position connection](../../Trace/Families/ReducedMachine/ControlSourceTheorems.lean) derives unique partners between actual
worker42 path positions and ORIGINAL complete workerRows active indices. Every
segment fold count equals its original source-index cardinality, retaining
equal-value/zero-mask updates and MAIN copies. Issued-call counts, physical
scheduling and standard hash remain open.

## Original caller provenance and segment counts

[Caller/path accounting](../../Trace/Families/ReducedMachine/ControlCallerTheorems.lean) connects worker42 edges to ORIGINAL caller
indices at the full raw key. Unique position partners and exact segment caller
counts hold on the old matching branch, retaining the >=257 MAIN-proof alternative
and inactive request-positive callers. Physical issuance, standard schedules and
hash remain open.

## Inactive MAIN component fixture

[Complete component fixture](../../Trace/Families/ReducedMachine/InactiveMainTheorems.lean) retains request-positive inactive CSR
rows with the full ordinary memory chain and individual caller/decoder equations.
The derived nonzero caller sum rejects a zero-claim completion. Full global source
acceptance and physical caller activity remain open.
