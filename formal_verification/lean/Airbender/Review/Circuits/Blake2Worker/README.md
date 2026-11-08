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
