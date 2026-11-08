# Verification status

## Active fetched caller request validity (8 November 2026)

[The mixed public projection](Airbender/Review/Circuits/ReducedMachine/CallerDecoder.lean)
combines the seven existing ordinary profiles with original CSRRW. Existing
Unified/Supported/CSR projections and execution roots remain unchanged. Mapping
adds only the sum tag and preserves every public field/query. This explicit scope
excludes MOP and other unsupported operations; decoding is not CSR execution.

[Proof assembly](Airbender/Proofs/ReducedMachine/NativeCallerDecoder.lean) derives
request shape from the original decoded instruction. Pure finite mask calculations
precede witness/native table instantiation. The seven ordinary families have CSR
bit7 zero; complete native BODY and packed Boolean bits therefore derive the FULL
zero request tuple, including kind and ABI-high offset. For CSR, original fields
and all ten query bindings derive the FULL mask129 before the unchanged actual
runtime lookup theorem is applied. The selector w24 alone is never treated as that
full mask or as an unmixed CSR query. Actual runtime membership allows1984/1991
and derives the delegation flag; it gives Boolean request multiplicity and either
the full zero tuple or exact(1,1991,somew36,3). A nonzero request also recovers the
original CSRRW1991 constructor with raw rs1/rd, actual mask129/key1991, native
oracle zero and the actual ABI-high w93 bound. Native oracle zero is not original
Sail nondeterminism; w36 is not identified with an initialized source value here.

[Two short roots](Airbender/Review/Circuits/ReducedMachine/CallerDecoderTheorems.lean)
expose local valid-entry consequences and their lift to EVERY actual active
ordinary physical row of the SAME counted complete MainDecoder source batch.
The independent original stateful public image and named LogicalLookups remain
explicit reference/crypto-extraction boundaries. Fetched public sources and all
ten fields are derived; no expected row opcode/profile, desired clock/read/value/
address/range/key/state/history/fulfilled ledger/result, fake Trace.Accepted,
ClockInputs.previous, dedup, OOB proof object, huge evaluation or table equivalence
is supplied. Joint effects retain main capacity, decoder arguments and actual
worker progress on the SAME inputs. All inactive physical request/decoder
equations, auxiliary poles, inactiveD, worker ports, readonly refreshes, OLDREAD,
unmasked writes and public x0 timestamps remain. No request matching follows
from fixed-challenge sums/capacity, and no Sail frame crosses delegated effects.

[Fourteen controls](Tests/NativeCallerDecoder.lean) check mixed shift/arithmetic/
LW/SW/CSR projections, query preservation, CSR/shift bits, a pure non-Boolean
negative, both active and INACTIVE existing complete LOCAL CSR BODY rows, the
retained inactive request, local multiplicity rejection and the full conditional
joint root. They are not new accepted NONEMPTY counted source/global/whole-worker/
physical witnesses, attacks, defects or absent-enforcement evidence. Valid CSR
fields can constrain a local inactive request too; they are not established for
ALL arbitrary inactive rows. This milestone does NOT prove all requests active,
arbitrary inactive multiplicity Boolean/kind1991, worker anchoring/bounds/rooting,
initialized OLDREAD values/addresses, STAGE2 keys or issuance/fulfillment/converse
accounting. Original CSR/MOP/worker Sail execution/retirement, general public/
physical refinement, cryptography, completeness and parity remain open.

Four modules add31 roots/19 exact parent origins. All5,956 prior ordered roots and
exact audit bytes remain addition-only. Native107 pins, dependencies, deliberate
v3 reference and old source/acceptance remain exact. No new native adoption/pin,
production/circuit/original Sail/importer/exporter/artifact/fixture change, native
generation/heavy replay, finding, issue assumption, project axiom or fix.


## Counted main and public decoder connection (8 November 2026)

[The counted decoder view](Airbender/Review/Circuits/ReducedMachine/MainDecoder.lean)
adds typed decoder observations to each existing initialization/main proof. The
actual u32 count indexes its vector. Main and decoder projections share the SAME
main rows, auxiliaries and claims by construction; no desired row/list/setup or
stream equality is supplied. Separate typed physical observations still require
Rust/JSON extraction refinement. The stronger source interface retains unchanged
complete counted initialization/main/caller/worker/global acceptance, decoder
access constraints on ALL ordinary rows, and the complete decoder table argument
checked ON the constructed public setup. Old acceptance is unchanged. Inactive
rows, auxiliary poles, physical holes/tails and all positional duplicates remain.

[Proof assembly](Airbender/Proofs/ReducedMachine/NativeMainDecoder.lean) derives the
original complete decoder argument on the constructed view and its exact main-list
identity. Joint effects retain main count/capacity and worker progress on SAME
inputs, together with all ordinary decoder access equations, table/access sums,
polynomial value zero, terminal table/access equality and ordinary setup-query
bindings. Generic list composition and public source extraction precede native
count/data/domain instantiation; no millions of rows are evaluated.

A separately named LogicalLookups boundary supplies faithful membership for each
actual execute-one query in the full constructed ordinary physical table. This
remains EXPLICIT cryptographic extraction, never a consequence of fixed-challenge
equations, sums, capacity or compression injectivity. From an original public
stateful Sail decoding image and this boundary, full native BODY derives EVERY
active physical query's original public byte read, Sail decoder execution,
projection and all ten fields. Actual packed-mask bounds exclude holes and the
minus-one physical tail. The projection is general, including the existing CSR
projection; this does not identify seven-profile Unified execution with CSR.

[Two short roots](Airbender/Review/Circuits/ReducedMachine/MainDecoderTheorems.lean)
expose the joint component and conditional public-source conclusions. They assert
no delegated execution, retirement, all-request activity, worker anchoring, clock
bounds/rooting, initialized reads, STAGE2 key agreement or request matching.
All inactiveD/m0 poles, worker ports, readonly refreshes, OLDREAD, unmasked writes
and public x0 times remain. No expected read/value/range/key/clock/state/history/
fulfilled ledger/result, fake Trace.Accepted, ClockInputs.previous, deduplication,
OOB proof object or table-equivalence premise is introduced. Physical public-image
refinement/setup authentication, FFT/LDE/quotient/transcript and general compiler/
Rust/JSON refinement remain separate from the logical extraction boundary.

[Fourteen controls](Tests/NativeMainDecoder.lean) cover shared rows/auxiliaries,
witness and other-setup preservation, ordinary setup binding, exact same main list,
counts/duplicates, empty logical lookups with positive-counter rejection, complete
conditional joint effects and the CSR public-source projection. These are
structural/pure/conditional controls, not a new accepted NONEMPTY source/global/
whole-worker/physical witness, attack, native defect or absent-enforcement claim.
Four modules add26 roots/12 exact parent origins. All5,930 prior ordered roots and
exact audit bytes remain addition-only. Native107 pins, dependencies and deliberate
v3 reference remain exact; no native adoption, production/Sail/old proof/acceptance/
importer/exporter/artifact/fixture change, generation/heavy replay, finding, issue
assumption, project axiom or fix. Next: actual request validity/activity, caller
anchoring and worker unbounded-source exclusion/seed rooting, initialized OLDREAD
values/addresses, raw bounds, STAGE2 keys and issuance/fulfillment/converse
accounting. Original CSR/MOP/worker Sail execution, general public/physical
refinement, cryptography, completeness and parity remain open.


## Counted native main loop and actual ordinary capacity (8 November 2026)

[The source batch](Airbender/Review/Circuits/ReducedMachine/MainBatch.lean) uses the
actual u32 count to index a vector of existing full initialization/main proof
observations. Its list length is derived by construction, without a desired count,
row-list or stream equality premise. Native source guards require positive count,
EVERY processed capacity prefix below MAX_CYCLES, and positive final total. The
stronger SourceAccepted wrapper retains these guards and UNCHANGED complete
existing acceptance on the SAME constructed proof list and worker batch. Prior
COMPLETE EMPTY component controls remain unchanged; they do not pass this positive
main-loop guard. Rust stream/ProofOutput/setup/metadata/transcript/physical
extraction and full compiler/Rust/JSON refinement remain separate boundaries.

Before adaptation, four exact native sources were pinned: statement lib.rs only
MAX_CYCLES, selected verifier size_constants only TRACE_LEN, layout_import's include
path, and generated circuit_layout ONLY its trace_len_log2 scalar23. Existing
unified statement main-loop guards and timestamp constants were independently
rechecked at67ee. This adopts no generated body or layout equivalence and transfers
no119-equation historical coverage to the117-equation native artifact. Prior103
pins remain exact; the new source inventory has107 pins. Dependencies and v3 pin
are unchanged. The selected ordinary capacity is8388607; MAX_CYCLES is2^36.

[Generic proof assembly](Airbender/Proofs/ReducedMachine/NativeMainBatch.lean)
performs the entire fold/prefix-guard/sampling-length/u32-u64 arithmetic before
concrete native domain/data instantiation. Source guards derive1..8192 main proofs,
exact actual ordinary mainRows length equal to the processed capacity counter,
at most68719468544 ordinary positions, and u64 headroom for every actual prefix.
All proof/row duplicates remain. The capacity counts available ordinary positions,
including execute-zero rows, and is not an active-cycle or issued-request count.
The worker slot counter does not supply a caller below-field bound.

[Two short roots](Airbender/Review/Circuits/ReducedMachine/MainBatchTheorems.lean)
expose count effects and their joint conclusion with actual worker progress on
SAME accepted inputs. No expected fulfilled ledger, request matching, clock bound,
initialized history, fake Trace.Accepted, dedup, OOB proof object or huge evaluation
is introduced. All inactiveD/m0 auxiliary poles, worker ports, readonly refreshes,
OLDREAD, unmasked writes and public x0 timestamps remain. Import fidelity and
cryptographic extraction stay explicit; no scalar-to-permutation claim is made.

[Twelve controls](Tests/NativeMainBatch.lean) include zero/excess count rejection,
first/last allowed counts, exact maximum capacity, u64 arithmetic, duplicates,
actual all-ordinary length and the full conditional joint root. A PURE control
passes the count guard for257 proofs while its ordinary capacity exceeds M31.
That counter DATA is not a full accepted nonempty source/global/worker/physical
witness, attack, defect or no-wrap counterexample. It does not derive caller
multiplicity Boolean, actual caller count below M31, activity, issuance or matching.
Four modules add27 roots/6 exact parent origins plus reviewed native source intake;
all5,903 prior ordered roots and exact audit bytes remain addition-only. No
production/Sail/old proof/acceptance/parser/importer/exporter/artifact/fixture change,
native generation/heavy replay, finding, issue assumption, project axiom or fix.
Next: actual caller anchoring and worker unbounded-source exclusion/rooting,
initialized OLDREAD values/addresses, raw bounds and STAGE2 keys, request-versus-
execute and issuance/fulfillment/converse/accounting. Original CSR/MOP/worker Sail,
public/physical refinement, cryptography, completeness and parity remain open.


## Actual worker progress and active-zero read sources (8 November 2026)

[Actual worker clock observations](Airbender/Review/Circuits/ReducedMachine/WorkerClockProgress.lean)
retain all43 old reads and their full raw token addresses, values and BOTH time
fields. Complete native BODY derives Boolean borrows and19bit difference bounds.
The existing generic borrowed comparison, at offset zero, gives strict old-read
progress when both actual clocks are bounded. The local conclusion exposes every
case: processor unbounded OR old read unbounded OR old read strictly earlier.
Neither clock bound nor a desired chronological read is supplied to the public root.

[Proof assembly](Airbender/Proofs/ReducedMachine/NativeWorkerClockProgress.lean)
lifts that calculation to EVERY active port of the SAME actual ordinary worker
list under unchanged complete initialization/main/caller/worker/global acceptance.
An unbounded old read is an exact ACTUAL active-worker write on the SAME complete
memory ledger, retaining address/value/BOTH timestamps and its common raw worker
clock, itself unbounded. Thus each active port has an unbounded processor clock,
a strictly earlier old read, or an exact unbounded active writer. At actual
processing clock zero, strict earlier Nat time is impossible: EVERY one of43 old
reads must come from an actual unbounded active-worker write. This does not exclude
all active zero clocks, establish global bounds/seed rooting/history or anchor a
worker to a caller. The unbounded dependency remains explicit.

[Two short roots](Airbender/Review/Circuits/ReducedMachine/WorkerClockProgressTheorems.lean)
keep full BODY and same-ledger conclusions separate. No new Accepted relation,
expected read/range/clock/state/row-list/fulfilled stream, fake Trace.Accepted or
ClockInputs.previous, activity filter, deduplication, OOB proof object or huge
evaluation is introduced. All inactive worker observations and auxiliary poles,
inactiveD, readonly refreshes, OLDREAD, unmasked writes and public x0 times remain.
Full logical matching/lookups remain explicit cryptographic extraction boundaries.

[Twelve controls](Tests/NativeWorkerClockProgress.lean) cover exact raw token
fields, all43 ports of the existing complete positive LOCAL worker row, full BODY
rejection of active-zero/old-zero DATA, a pure order cycle, duplicate preservation,
COMPLETE EMPTY stronger acceptance and full conditional roots. They are not new
NONEMPTY source/global/whole-worker/physical witnesses, attacks, defects or evidence
of absent other enforcement. Four modules add20 roots/10 exact parent origins;
all5,883 ordered roots and exact audit bytes remain addition-only. Native103 pins,
dependencies, old proofs/acceptance, production/Sail/importer/exporter/native
artifacts/fixtures/findings remain unchanged. No new native adoption, generation,
heavy replay, project axiom, issue assumption or fix. Next: actual nonempty worker
bounds/rooting, initialized OLDREAD addresses/values, STAGE2 keys and actual caller
anchoring/accounting. Original CSR/MOP/worker Sail, public/physical refinement,
cryptography, completeness and native-target/trust-boundary parity remain open.


## Every physical caller raw-clock domain (8 November 2026)

[Raw caller-clock observations](Airbender/Review/Circuits/ReducedMachine/CallerClockDomain.lean)
now retain exact canonical wrap alternatives on EVERY ordinary physical main row,
including execute0 and all request values. Complete native BODY acceptance gives
the actual Boolean carry and both final clock limbs below524288. Carry zero yields
callerLow+1=finalLow, or callerLow=M31minus1 with finalLow zero; callerHigh=finalHigh.
Carry one yields callerLow+1=finalLow+524288, and callerHigh+1=finalHigh or callerHigh
M31minus1 with finalHigh zero. These follow from actual low+4/high+carry equations;
no initial-clock range, old-read bound, active row or desired clock premise is used.

[The proof](Airbender/Proofs/ReducedMachine/NativeCallerClockDomain.lean) performs
canonical successor modulo arithmetic and all endpoint-domain algebra over
abstract naturals before concrete field/domain instantiation. The resulting raw
low is below1048575 OR M31minus1; raw high is below524288 OR M31minus1. A low
sentinel forces high below524288. A high sentinel forces524287<=low<1048575.
Both sentinel cases remain visible, and cannot occur together. This is a canonical
field domain, not a19bit bound, natural chronology, active caller or worker clock
bound. The prior canonical active-state caller-clock result remains separate.

[Two short roots](Airbender/Review/Circuits/ReducedMachine/CallerClockDomainTheorems.lean)
expose full-BODY consequences and their lift to the SAME actual proof list under
unchanged complete initialization/main/caller/worker/global acceptance. Existing
generic sampling retains every ordinary row and positional duplicate, with no
execute/opcode/request filter, deduplication, OOB proof fallback or huge evaluation.
All caller auxiliary values, inactiveD, m0 poles, worker ports, refreshes, OLDREAD,
unmasked writes and public x0 timestamps remain. No request matching, expected
fulfilled stream, fake Trace.Accepted/history, new Accepted relation or extraction
from fixed-challenge sums/capacity is introduced. Import fidelity stays separate.

[Sixteen controls](Tests/NativeCallerClockDomain.lean) cover generic successor,
ordinary/sentinel boundaries and rejections, sentinel failure of19bit bounds,
old complete active/inactive LOCAL CSR bodies, actual old fixture endpoints,
COMPLETE EMPTY acceptance and the full conditional source root. Pure sentinel
domain cases are not accepted native wrap witnesses, global worker/physical
witnesses, attacks, defects or absence-of-other-enforcement evidence. Four modules
add23 roots with9 exact parent origins; all5,860 ordered audit roots and exact bytes
remain addition-only. Native103 pins, dependencies, production/Sail/old proofs/
acceptance/parser/importer/exporter/native artifacts/fixtures/findings are unchanged.
No new native adoption, generation, heavy replay, axiom, issue assumption or fix.

Next: actual nonempty-worker progress/rooting, initialized OLDREAD values/addresses,
raw bounds and STAGE2 keys; actual caller anchoring and issuance/fulfillment/
converse/accounting. Original CSR/MOP/worker Sail, general public/physical refinement,
cryptography, completeness and checked native-target/trust-boundary parity remain open.


## Every native request gate and active main caller clocks (8 November 2026)

[The native request observations](Airbender/Review/Circuits/ReducedMachine/CallerRequests.lean)
retain EVERY ordinary main row of the SAME actual proof list, without an execute,
opcode or request filter. Complete native body equations derive multiplicity as
the CSR selector times the raw delegation value, kind as the source code times
multiplicity, ABI high as SOME source-high times multiplicity, and imported clock
offset three. The selector is Boolean and equals bit 7 of the actual packed mask,
using canonical field representatives and the complete native 18-bit packing.
Thus multiplicity zero is equivalent to selector zero OR delegation value zero;
a nonzero request requires selector one and delegation value nonzero. It also
derives supported one and zero native CSR oracle words. The raw delegation value
and request multiplicity are not declared Boolean under this general body scope.
No valid CSR instruction/mask129, kind1991, execute1 or worker issuance follows.
When packed bit7 is zero, the complete request tuple is zero, with SOMEzero ABI
high and the original offset three retained. No auxiliary pole is discarded.

[The proof assembly](Airbender/Proofs/ReducedMachine/NativeCallerRequests.lean)
performs the entire generic Nat low-window/bit/high calculation before concrete
mask instantiation. It extracts actual equations68 through73 on an abstract setup
and then lifts their consequences through existing bounded, duplicate-preserving
sampling to ALL ordinary main observations of unchanged full initialization/
main/caller/worker/global acceptance. No expected rows/streams, row-list equality,
mask/profile premise, OOB proof-object fallback or huge domain evaluation is used.

Separately, the EXISTING execute1 main-state projection derives caller-clock
observations bounded to 19 bits, exactly row.clock+3, congruent to3 modulo4,
at least7, strictly before the ACTUAL public terminal clock and unique. Initial
state ranges/alignment and row-clock uniqueness come from SAME accepted native
PC/state chronology and full tagged logical matching. The calculation uses no
old-read bound or fake previous-clock interface, accepted memory trace or history.
The generic injective list translation precedes native instantiation. These
clock observations include all active main rows, without a new request filter.
All physical requests and auxiliary values remain in the separate all-row result;
clocks of inactive requests are not proved bounded or attached to active callers.

[Three short roots](Airbender/Review/Circuits/ReducedMachine/CallerRequestsTheorems.lean)
keep body shape, full ordinary-domain consequences and active-state clocks
explicit. Complete execute0/request1 CSR BODY controls still pass. No body-local
execute0-to-request0 rule, source-worker matching, expected fulfilled ledger or
scalar-to-permutation claim is introduced. Full logical matching/lookups remain
explicit extraction boundaries; inactiveD and m0 auxiliary poles remain.

[Eighteen controls](Tests/NativeCallerRequests.lean) cover packed-mask boundaries,
actual complete CSR bodies for both execute flags, retained inactive request,
zero oracle consequence, exact disabled tuple, selector corruption rejection,
clock translation/duplicate preservation, COMPLETE EMPTY stronger acceptance,
full conditional joint roots and exact raw offset. Pure/reference/body/empty/
conditional controls are not NONEMPTY source/global/worker/physical witnesses,
attacks, native defects or absence-of-other-enforcement evidence. Four modules
add29 roots with13 exact parent origins; all5,831 prior ordered roots and exact
audit bytes remain. Native103 pins, dependencies, old proofs/acceptance,
production/Sail/importer/exporter/native artifacts/fixtures and findings remain.
No new native adoption/pin/generation/heavy replay, axiom or issue assumption.

Next: actual active-worker clock progress and seed reachability, initialized
OLDREAD values/addresses and STAGE2 keys; remaining decoder/request-versus-execute
padding and caller-worker issuance/fulfillment/converse/accounting. Original
CSR/MOP/worker Sail effects, general public/physical refinement, cryptography,
completeness and checked native-target/trust-boundary parity remain open.


## Complete local active-worker fixture (8 November 2026)

[The explicit native worker row](Airbender/Review/Circuits/Blake2Worker/PositiveRow.lean)
has multiplicity one, raw processing clock(3,0), all 43 timestamp borrows one,
and every other logical variable zero. It is a local fixture, with all native
ports and aliases retained. Both pointers are zero; no initialized memory history,
issued request, valid round schedule or source-worker acceptance is supplied.

[The kernel proof](Airbender/Proofs/Blake2Worker/NativePositiveRow.lean) checks ALL
352 native equations and ALL 296 lookups: 208 into the complete actual literal
worker fixed pool, two scalar16 queries and 86 timestamp19 queries. It then proves
the SAME existing LocalProcessingAccepted, including all 226 normalized processing
conventions. Assertions are split into small actual source blocks; range and clock
bounds are computed on actual queries. All five zero fixed-table memberships are
derived from existing actual-row/field/XOR theorems. Entire generic coordinate,
vector and typed-lookup proofs precede concrete literal-table instantiation.
There is no table-equivalence premise, recipe-defined membership, opacity or
heavy table-certificate replay. Concrete whole-pool/row equality reductions hit
allocation caps during exploration; the final abstract proofs avoid those paths
and retain all normal resource and lint limits.

[Two short public roots](Airbender/Review/Circuits/Blake2Worker/PositiveRowTheorems.lean)
expose complete local body and processing acceptance. This is a positive local
active row, not a nonempty accepted source proof, worker trace, global/protocol/
physical witness or initialized combined history. It does not establish hashing/
reference correctness, original Sail worker effects, clock progress, request
anchoring or absence of other enforcement. No native defect or issue assumption.

[Twelve controls](Tests/NativeBlake2PositiveRow.lean) check actual multiplicity,
ABI high, raw clock, all 13 zero flags, all 43 old-time pairs and borrows, both
zero pointer pairs, old/new control values, complete body/processing acceptance,
all five actual zero table rows and the active/nonpadding distinction. All
readonly refreshes, OLDREAD, aliases and unmasked writes remain in the source.
Four modules add 17 roots with 10 exact parent origins; every one of the 5,814
prior ordered roots and exact audit bytes remains. Native 103 pins, dependencies,
old proofs/acceptance, production/Sail/importer/exporter/native artifacts and
findings are unchanged. This new logical witness requires no native generation,
new pin/adoption, heavy replay, axiom or desired-result premise.

Next: actual nonempty-worker clock progress and seed reachability on the same
complete ledger, initialized active old-read values/addresses and STAGE2 keys,
request-versus-execute padding, caller-worker issuance/fulfillment/converse/
accounting and original worker round/reference/state/Sail effects. Multiplicity-
one zero-clock exclusion, general public/physical refinement, cryptography,
completeness and checked native-target/trust-boundary parity remain open.


## Active sources of actual worker clocks (8 November 2026)

[The actual worker-clock observations](Airbender/Review/Circuits/ReducedMachine/ActiveWorkerClocks.lean)
retain both raw processing-clock fields and all 43 actual quotient-write ports.
On the SAME unchanged full InitializationBatch.Accepted, every actual read clock
is bounded to 19 bits OR has an exact actual multiplicity-one worker-write source.
If a read clock is unbounded, the source is an actual ordinary worker observation
and Fin43 slot with the identical token, including address, value and both raw
timestamp fields; that source worker's common raw clock is itself unbounded.

[The proof assembly](Airbender/Proofs/ReducedMachine/NativeActiveWorkerClocks.lean)
derives full LocalProcessingAccepted for every actual ordinary worker row from
the configured source acceptance and SAME shared challenges. It reuses accepted
processing Boolean multiplicity and zero masks: inactive rows have BOTH raw
processing-clock limbs zero. Thus inactive workers cannot supply an unbounded
read clock. Generic finite sampling precedes native domain instantiation, keeps
positional duplicates and uses only bounded source membership. All inactive
worker observations, readonly refreshes, OLDREAD, unmasked writes, inactiveD and
m0 auxiliary poles remain. No caller request or worker row is filtered.

[One short root](Airbender/Review/Circuits/ReducedMachine/ActiveWorkerClocksTheorems.lean)
adds no acceptance relation or premise for raw clock bounds, progress, seed
reachability, initialized reads/values/addresses/keys, issued or fulfilled streams,
schedules or results. Full logical matching/lookups remain explicit extraction
boundaries. The result isolates the remaining active-worker dependency; it does
not establish its clock bounds, chronology, request anchoring or initialized
memory history. The prior empty-batch main-history theorem retains its scope.

[Fourteen controls](Tests/NativeActiveWorkerClocks.lean) cover both raw clock
limbs, all 43 write slots, the last port, duplicate sampling, accepted padding,
conditional activity and exact actual source membership, complete EMPTY source
acceptance, and the full conditional source theorem. Wide-clock and activity-one
zero-clock DATA projections are not accepted nonempty worker/source/global/
physical witnesses, attacks, absence-of-enforcement evidence or native defects.
Four modules add 24 roots with 12 exact parent origins; all 5,790 prior ordered
roots and exact audit bytes remain. Native 103 pins, dependencies, old proofs/
acceptance, production/Sail/artifacts/fixtures/importer/exporter and findings are
unchanged. No native adoption/pin/generation/heavy replay or issue assumption.

Next: derive actual active-worker clock progress, bounds and seed reachability
on the same complete ledger, then initialized old-read value/address bounds and
STAGE2 keys, request-versus-execute padding and actual caller-worker accounting.
Multiplicity-one zero-clock exclusion and original CSR/MOP/worker Sail execution,
general public/physical refinement, cryptography, completeness and parity remain open.


## Actual read sources and main-memory history (8 November 2026)

[The native memory observations](Airbender/Review/Circuits/ReducedMachine/NativeMemoryHistory.lean)
retain the SAME actual proof list, complete GPR/RAM seeds and teardown, public PC
endpoints and actual runtime table. For ANY selected worker batch, every actual
read has an exact actual seed, main-write or worker-write token source, including
address/value/both raw timestamps. Every read clock is19bit OR comes from an
actual worker write. That alternative does not assume raw worker ranges or turn
source membership into chronological seed reachability. All43 worker ports and
inactive worker observations remain; no caller request or worker row is filtered.

The explicitly empty selected worker batch is constructed with actual count0 and
outputs empty. SAME full native acceptance is checked ON that batch; no supplied
worker-list/count/fulfilled-ledger equality or nonempty-worker filtering is used.
The main trace contains actual execute1 rows from ALL ordinary rows, exact native
runtime table, complete observed initial/terminal memory and public PC endpoints.
All four actual Trace.Accepted clauses and ClockBoundary are DERIVED, including
full body, activity, PC/state matching and complete memory matching. There is no
placeholder memory, fake accepted trace/history or expected per-row read premise.
Caller requests/claims and source auxiliary equations remain unchanged.

[The proof assembly](Airbender/Proofs/ReducedMachine/NativeMemoryHistory.lean)
reuses unchanged generic clock/graph/memory proofs on that real trace. It derives
ALL old-read clock bounds, newest preceding write/value-token reads, strict read
before access, initialized address support, every seed's exact per-address path
and ONE complete consistent-online Clean memory history. All32 public GPR seed
writes including x0 and every active main port, readonly refresh, OLDREAD and
unmasked write remain. The previous constructed original Sail initial image and
separate native ROM shadows are retained. This is main-memory history under the
explicit empty batch, not combined nonempty-worker history or original CSR/MOP/
worker Sail execution. Alignment/platform, worker clocks/keys, request issuance/
fulfillment/accounting and physical/cryptographic refinement remain open.

[Two short roots](Airbender/Review/Circuits/ReducedMachine/NativeMemoryHistoryTheorems.lean)
keep full-batch read provenance and empty-batch main history separate. Actual
source acceptance and explicit full logical matching/lookups remain unchanged.
Only prior exact duplicate-preserving inactive-main/padded-init cancellations
are reused; inactiveD and m0 auxiliary poles remain. No division/nonzero/inverse,
compression-injectivity, scalar-to-permutation, expected stream/result, opcode/
caller filter or assumption that all physical rows execute is introduced.
Generic abstract list projection, matched-read membership and sampling property
precede concrete native instantiation; all checks retain default resource limits.

[Seventeen controls](Tests/NativeMemoryHistory.lean) cover actual empty-batch
count/list, exact initial/terminal views, both port projections, exact read-source
membership, an unseeded loop showing that membership alone is not rooting,
unmatched-read rejection, duplicate preservation, all32 initial registers,
COMPLETE EMPTY stronger native acceptance deriving real accepted trace/history/
public image, wrong terminal clock8 rejection, and full conditional roots.
Pure/structural/generic-negative/empty/conditional controls are not full positive
NONEMPTY source/global/worker/physical witnesses, attacks or native defects.
Four modules add29 roots with13 exact parent origins; all5,761 prior ordered roots
and exact audit bytes remain. Native103 pins, dependencies, old proofs/acceptance,
production/Sail/artifacts/fixtures/importer/exporter and findings are unchanged.
No new native adoption/pin/generation/heavy replay, axiom or issue assumption.

Next: actual nonempty-worker clock progress and seed reachability on the SAME
complete ledger, then active old-read value/address bounds and STAGE2 key
refinement, request-versus-execute padding and caller-worker accounting. The new
empty-batch result does not discharge those nonempty-worker obligations. No parity.


## Constructed original Sail initial image (8 November 2026)

[The explicit public reference-input constructor](Airbender/Review/Helpers/Memory/ReducedMachineInitialState.lean)
inserts original Sail PC zero and x1 through x31 zero, with original hardwired x0.
It preserves nextPC and every other configuration-register lookup. It reuses the
exact native ROM byte constructor and explicitly inserts zero bytes from4MiB to
4294967299 exclusive. The three bytes above the RV32 address range are a declared
logical reference-input halo: original natural-address four-byte reads at any
canonical, possibly unaligned, RV32 cell succeed. This is not native physical
address-space, alignment, loader, platform-permission or Rust refinement.
Missing registers are actually inserted; bytes beyond both intervals retain their
original lookup, including missing values. No default read is substituted.

[The original-read proofs](Airbender/Proofs/ReducedMachine/NativeInitialState.lean)
derive PC/GPR success and zero architectural RAM reads from those constructors.
The entire generic finite image recursion precedes instantiation, and all byte
interval reasoning is symbolic: no four-GiB or million-word fixture is evaluated.
The existing zero-boot profile is a conclusion. The unchanged full native ROM
extractor/word-read proof is reused; address16 reads21015 through Sail while its
native permutation shadow remains zero. No shadow/ROM-value equality is assumed.
A broad register-frame simplifier hit default recursion and then the default
heartbeat limit; a generic insert-frame lemma and explicit linear rewrites solve
it at unchanged limits. All other configuration lookups remain exact.

[The observed image](Airbender/Review/Circuits/ReducedMachine/InitializationPublicImage.lean)
and [two short roots](Airbender/Review/Circuits/ReducedMachine/InitializationPublicImageTheorems.lean)
use SAME existing complete native initialization acceptance. Successful ORIGINAL
Sail image reads cover the derived architectural GPR/RAM partition; separate
actual native ROM shadows remain in the image. The actual initial native token
list is proved PERM that constructed image, and initial PC/time is0/(4,0).
The SAME actual memory ledger starts from this derived Sail image plus shadows;
all32 public registers including x0 timestamps, all43 worker ports/inactive
workers, readonly refreshes, OLDREADs and unmasked writes remain. Only previously
proved exact multiset cancellations are reused. No per-cell read/value/image,
expected ledger, stream, key, clock, request or result premise is introduced.
No fake accepted trace/history, caller-request filter, division/nonzero answer,
compression injectivity or scalar-to-permutation claim is introduced.

[Twenty controls](Tests/NativeInitializationPublicImage.lean) check original PC/
x0/x31/all-GPR reads, missing PC insertion, configuration/nextPC lookup frames,
first and unaligned RAM, maxRV32 word, last halo byte and missing-preserving lookup
outside it, full native ROM, word4 and its distinct zero shadow, duplicate image
cells, derived boot profile, COMPLETE EMPTY existing acceptance and conditional
roots. These are symbolic/source/reference/structural/empty/conditional controls,
not full positive NONEMPTY source/global/worker/physical witnesses or attacks.
Six modules add37 roots with16 exact parent origins. All5,724 prior ordered roots
and exact audit bytes, native103 pins, old proofs/acceptance, production/Sail,
artifacts/fixtures/dependencies/importer/exporter and findings remain unchanged.
No new native adoption/pin/generation/heavy replay, axiom or issue assumption.

This closes successful original initial-image reads on the observed domain for
the explicit constructor, not arbitrary public-state/domain/platform coverage,
alignment, initialized combined chronological memory, active worker old-read
values/addresses/clocks, STAGE2 key refinement, caller-worker accounting,
original CSR/MOP/worker Sail effects or physical/cryptographic refinement.
Next: combine the actual complete ledger with real chronological memory laws,
derive active old-read values/address bounds and worker clocks/keys, then request/
execute padding and actual issuance/fulfillment/accounting. No parity claim.


## Complete native seed boundary and memory projection (8 November 2026)

[The complete observed boundary](Airbender/Review/Circuits/ReducedMachine/InitializationSeedBoundary.lean)
combines ALL32 actual public GPR seeds, including x0, with the SAME actual
nonpadding RAM seeds. Source register keys derive exact canonical zero-token
encoding. Register/RAM constructor separation and the existing RAM-domain proof
derive the complete observed cell/address domain Nodup, exact zero-token encoding
and every seed clock zero. Final public register observations keep raw timestamps,
including x0; no public timestamp is silently reset or dropped.

[The proof assembly](Airbender/Proofs/ReducedMachine/NativeInitializationSeedBoundary.lean)
derives the exact architectural/ROM-shadow partition using the unchanged native
shadow classifier. All shadow addresses are below4MiB and their actual seed values
are zero. Partitioned domains remain Nodup and every token/duplicate occurrence
is preserved by a permutation; architectural ROM byte values are not identified
with shadow seeds. This is observed support/encoding/classification, not successful
original Sail reads or independent public image/domain coverage, alignment or an
initialized combined worker memory history.

The SAME full tagged logical matching derives an actual memory-only permutation:
complete public GPR+RAM seeds and actual writes match full public teardown and
actual reads. All43 worker ports, including inactive workers, readonly refreshes,
OLDREADs and unmasked writes remain. Only the already proved identical inactive
main and padded initialization contributions are cancelled. No caller-request or
worker filtering, division, nonzero/inverse answer, compression injectivity or
expected stream/result premise. A concrete projection simplification hit the
DEFAULT recursion limit; the entire projection algebra is now generic over
abstract lists BEFORE native instantiation, at unchanged resource limits.

[Two short roots](Airbender/Review/Circuits/ReducedMachine/InitializationSeedBoundaryTheorems.lean)
use SAME complete initialization acceptance. Full logical matching/lookups and
normalized source fidelity remain explicit cryptographic/refinement boundaries.
No fake Trace.Accepted, initialized worker reads/clocks/keys/accounting, original
CSR/MOP/worker Sail frame or physical extraction is inferred.

[Eighteen controls](Tests/NativeInitializationSeedBoundary.lean) cover all32/x0/
x31 seeds, retained final raw x0 timestamps, public memory projection, unique and
architectural GPR cells, exact shadow cutoff0/4194303/4194304, duplicate retention,
actual zero shadow tokens distinct from a nonzero value, mixed-domain partition,
generic duplicate-preserving projection, COMPLETE EMPTY existing acceptance and
conditional roots. These are pure/reference/structural/empty/conditional, not full
positive NONEMPTY source/global/worker/physical witnesses, attacks or defects.
Four modules add33 roots with12 exact parent origins; all5,691 prior ordered roots
and exact audit bytes remain. Native103 pins, old proofs/acceptance, production,
Sail, artifacts, fixtures, dependencies, importer/exporter and findings unchanged.
No new native adoption/pin/generation/heavy replay, axiom or assumption; no parity.

Next: actual public initial-state construction and successful original Sail reads
for the architectural partition, while retaining separate native ROM shadows,
then initialized combined memory/worker bounds and caller-worker accounting.
Canonical zero-token encoding alone is not public image coverage.


## Unique observed native seed domain (8 November 2026)

[The observed seed domain](Airbender/Review/Circuits/ReducedMachine/InitializationSeedDomain.lean)
comes from ALL ordinary rows of the SAME actual main list, after the unchanged
six-field padding cancellation. The seed and teardown lists retain actual field
observations and never filter by execute or worker/request status. Their equality
to the existing native ledger projections is proved in BOTH directions of use.

[The proof assembly](Airbender/Proofs/ReducedMachine/NativeInitializationSeedDomain.lean)
first proves generic finite sampling and product-of-finite-position uniqueness
BEFORE native-domain instantiation. Every position is bounded; there is no
out-of-bounds proof/row/history/ledger fallback or million-row evaluation. The
existing global indexed nonpadding address uniqueness derives address Nodup for
the ACTUAL whole seed list. Duplicate proof/row values are not silently deduplicated.

Every actual seed is derived canonical RAM32 with zero value/time from the SAME
complete initialization acceptance. The unchanged bounded Word lemmas prove its
exact equality to a canonical RAM cell's zero initialToken. The observed cell list
is derived Nodup, and its mapped zero tokens equal the actual seed list. Whole
RV32 addresses above M31 stay Nat/BitVec; there is no whole-word field cast.
[Two short roots](Airbender/Review/Circuits/ReducedMachine/InitializationSeedDomainTheorems.lean)
expose these derived consequences and exact full native logical matching over the
constructed seed/teardown lists plus unchanged public/main/worker access tokens.

This is an OBSERVED domain and canonical encoding result. It does not assert an
independent public domain, successful original Sail reads/initialImage equality,
ImageBoundary/ShadowImageBoundary, architectural ROM values, alignment, combined
chronological memory or worker bounds/keys/accounting. An unaligned canonical RAM
cell remains unaligned. Public x0 timestamps, all worker ports and original source
acceptance/poles remain; no expected seed/read/result stream or new assumption.

[Fifteen controls](Tests/NativeInitializationSeedDomain.lean) check canonical zero
RAM, max RV32 projection, unaligned retention, register/RAM separation, bad value/
time rejection, preserved duplicate source positions, duplicate-key rejection,
generic unique sampling, empty observed lists, COMPLETE EMPTY accepted-domain
consequences, both-sided same-ledger identity, matching and conditional domains.
These are pure/structural/empty/conditional, not full positive NONEMPTY source/
global/worker/physical witnesses, attacks or native defects. Four modules add25
roots with12 exact parent origins; all5,666 prior ordered roots and exact audit
source bytes remain. Native103 pins, dependencies, old proofs/acceptance, production,
Sail, artifacts, fixtures, importer/exporter and findings are unchanged. No new
native adoption/generation/heavy replay, axiom or issue assumption; no parity.

Next: combine actual register and RAM seed domains with actual public initialization
meaning, classify native ROM shadows separately from architectural bytes, and prove
public image/domain coverage before initialized combined memory/worker consequences.
The observed cell-domain proof is not an independent public-image premise.


## Actual native seed ledger and padding cancellation (8 November 2026)

[The initialization ledger](Airbender/Review/Circuits/ReducedMachine/InitializationLedger.lean)
constructs actual nonpadding seed/teardown lists from ALL ordinary rows of the same
native main proofs. Its padding test checks ALL six address/value/time fields;
zero address alone is insufficient. No execution filter is applied to seeds.
Public register/PC, active main port/state and ALL worker access observations stay
in the access list, including x0 public timestamps and readonly refreshes.

[The proof assembly](Airbender/Proofs/ReducedMachine/NativeInitializationLedger.lean)
derives that a six-zero record contributes the IDENTICAL zero RAM token on BOTH
sides. Generic abstract list partition/reordering precedes native instantiation.
Exact uncompressed multiset cancellation preserves duplicates and proves original
FULL logical matching equivalent in BOTH directions to retained matching and to
the explicit seed/teardown plus access ledger. Active port/state effects on a row
with padded initialization remain. No division, nonzero factor, ratio1, compression
injectivity, expected ledger or issued/fulfilled-worker premise is introduced.
Original source acceptance, inactive factors and multiplicity-zero poles remain.

[Three short roots](Airbender/Review/Circuits/ReducedMachine/InitializationLedgerTheorems.lean)
expose these equivalences and derive the actual zero seeds' canonical two-limb RAM
address domain from SAME complete initialization acceptance. Both limbs are16bit,
the Nat radix address is below2^32 and agrees with the actual sorted address;
seed value and raw field timestamp pair are zero. Full RV32 above M31 is retained
without a whole-word field cast. This does not prescribe an architectural/public
RAM region, alignment, image/seed coverage or initialized chronological history.
Logical matching/lookups and normalized source fidelity remain explicit separate
boundaries; no physical extraction or compiler/Rust/JSON refinement is inferred.

[Seventeen controls](Tests/NativeInitializationLedger.lean) check all six padding
fields, zero-address nonpadding retention, inactive seeds, active padded-row ports,
duplicate occurrences/partition, exact zero seed fields, max RV32, wide-limb
rejection, full matching equivalences and conditional domains. Complete EXISTING
CSR BODY plus a local ledger observation is a weaker interface; these are not full
positive NONEMPTY source/global/worker/physical witnesses, attacks or defects.
Four modules add32 roots with12 exact parent origins. All5,634 prior ordered roots
and exact audit source bytes remain; native103 pins and all previous boundaries,
production, Sail, artifacts, fixtures, importer/exporter and findings are unchanged.
No native generation, closed heavy replay, new axiom or issue assumption; no parity.

Next: actual public-native memory domain/image/seed coverage, then chronological
combined memory and active worker reads/value/address/rawclock/key bounds and
caller-worker accounting. Canonical native zero seeds alone do not establish the
public seed coverage required by the initialized logical histories.


## Same-main initialization and full native ledger (8 November 2026)

[The constructed source views](Airbender/Review/Circuits/ReducedMachine/InitializationBatch.lean)
contain ONE existing main-argument proof plus separate actual scalar base/witness/
setup/polynomial/omega and public endpoint observations. The scalar view's
initialization.main IS the original argument's memory MainProof by construction;
caller rows, typed auxiliary trace and both original claims remain on that proof.
No desired row/trace/ledger equality is supplied. Both list projections are derived
maps of the same actual finite list, with no proof-object fallback out of bounds.

Acceptance retains the UNCHANGED complete main/caller/worker/global components
with the same configured worker batch, shared challenges and public memory inputs,
plus complete initialization acceptance on the constructed views and ALL actual
adjacent windows. The SAME [full tagged native logical ledger](Airbender/Review/Circuits/ReducedMachine/TokenLedger.lean)
retains every main/worker/public token and remains an explicit cryptographic
extraction boundary. No expected seed/read/value/key/clock/request/fulfilled-worker
stream, execution filter, count equality or result premise is added.

[The proof assembly](Airbender/Proofs/ReducedMachine/NativeInitializationBatch.lean)
uses abstract finite-list arithmetic/property projections BEFORE native-domain
instantiation. Only unused Nat/Prop projections outside list bounds have0/True;
no accepted row/history/proof object or token ledger is fabricated there. Existing
source-window, local uniqueness and lossless token binding derive all ordinary
initialization bounds, cross-chunk order and nonpadding address uniqueness on the
actual full main list. A generic full-domain sampling proof shows every ordinary
unmasked initialization/teardown token is present in that SAME full ledger on BOTH
sides, including lastordinary and inactive rows. Padding tokens remain.

[Two short roots](Airbender/Review/Circuits/ReducedMachine/InitializationBatchTheorems.lean)
compose unchanged caller/worker scalar/product/capacity results, actual main-state
chronology and these initialization consequences on the SAME inputs. This does
not derive public seed/image coverage, chronological combined worker memory,
active worker read/value/rawclock/key bounds, issuance/fulfillment/accounting,
original CSR/MOP/worker Sail semantics, physical extraction or completeness.
No frame crosses an unproved delegated action; original execution is unchanged.

[Twelve controls](Tests/NativeInitializationBatch.lean) check actual main/caller/
scalar observation identity, retained distinct claims/source data/list projection,
both-sided full-ledger membership and lastordinary inclusion. A COMPLETE EMPTY
stronger selected component feeds the joint root and derives terminal4; terminal8
is rejected. Data/structural/empty/conditional controls are not full positive
NONEMPTY source-aux/global/worker/physical witnesses, attacks or native defects.
Four modules add21 roots with12 exact parent origins; all5,613 prior ordered roots
and exact source bytes remain. Native103 pins, dependencies, artifacts, fixtures,
old acceptance/proofs, production, Sail, importer/exporter and findings are
unchanged. No native generation or closed heavy replay. Cryptographic/general
Rust/JSON/field/LDE/quotient/refinement boundaries remain separate; no parity claim.

Next: actual initialization seed ledger/public-domain and padding treatment,
public image/seed coverage, then chronological combined memory and active worker
bounds/keys/accounting. Same-list coupling and sorted zero tokens alone are not a
desired public seed stream or an initialized worker-memory proof.


## Native initialization windows and cross-chunk uniqueness (8 November 2026)

[The actual native window interface](Airbender/Review/Circuits/ReducedMachine/InitializationWindow.lean)
checks parsed previous-terminal/current-first public addresses. Its parser keeps
BOTH native high-bit masks, the32bit left shift and bitwise OR. The unchanged
native checked-u16 helper was byte-compared and pinned BEFORE adaptation:
103native sources, all previous102 unchanged. The already pinned full-statement
window source was rechecked against exact native67ee before adaptation.
[The parser calculation](Airbender/Proofs/ReducedMachine/NativeInitializationAddressParser.lean)
derives successful parsing and the exact Nat radix address from the already
derived public16bit limbs, including full RV32 words above M31. This is a pure
source reference, not Rust/field-storage/serialization/compiler refinement.

The native IF branch accepts strict public window growth. Its ELSE branch checks
previous terminal address0 AND all four teardown value/time fields0. Both are
retained: no strict-window premise is supplied for padding chunks.
[The window calculations](Airbender/Proofs/ReducedMachine/NativeInitializationWindow.lean)
derive that this fallback forces EVERY previous ordinary record to padding using
the complete source, actual public endpoint binding and strict local sorting.
They then derive weak order for every pair of rows across adjacent chunks, and
strict order from each nonpadding record. An abstract finite chunk induction
extends this to every ordered pair of supplied chunks and every ordinary row.
Global nonpadding actual token-address uniqueness identifies BOTH chunk and row
indices. All padding records/tokens and intermediate chunks remain in the proof.

[Three short roots](Airbender/Review/Circuits/ReducedMachine/InitializationWindowTheorems.lean)
retain EVERY supplied complete boundary/scalar/main/init component and EVERY
native adjacent window in an explicit indexed source-normalized batch. No expected
order, image, seed, read, clock, key, worker/request stream, result or filter is
supplied. This is not full Rust ProofOutput/count/setup-cap/challenge/transcript/
global-memory/delegation acceptance or cryptographic extraction. Coupling this
view to the SAME complete main-argument list and full token ledger, public image/
seed coverage, combined chronological memory history, initialized worker reads/
raw clocks/keys and real caller-worker accounting remain open. Original Sail
execution stays unchanged and excludes CSR/MOP; no unproved delegated frame.

[Sixteen controls](Tests/NativeInitializationWindow.lean) cover zero/max-RV32 parsing,
both wide-limb rejections, retained zero fallback, raw teardown fields on strict
windows, each of four fallback-field corruptions, equal/descending nonzero window
rejections, failed-parser rejection, nonadjacent finite growth/padding retention,
existing complete CSR BODY plus zero public window and conditional full roots.
These are pure/source/reference/conditional controls, not full positive nonempty
source-aux/global/worker/physical witnesses, attacks or native-defect evidence.
Five modules add31 roots with eight exact parent origins and one manual source
reference. All5,582 prior ordered roots and exact source bytes remain. No production/
Sail/old acceptance/proof/importer/exporter/artifact/fixture/dependency change,
native generation or closed heavy replay. Findings remain unchanged; no issue
assumption, new axiom, physical extraction, completeness or checked parity claim.

Next: couple these checks by construction to the SAME actual main-argument list
and full native ledger, then establish public initialization image/seed coverage
and chronological combined memory history. Sorted windows alone do not provide
expected public seeds or active worker bounds.


## Native public initialization endpoints and sorted interval (8 November 2026)

[The public boundary component](Airbender/Review/Circuits/ReducedMachine/InitializationBoundary.lean)
retains the SAME complete scalar/main/init/sorting input and adds the actual twelve
native boundary polynomials. They bind all six address, teardown-value and
teardown-timestamp fields at row0 and rowN-2 to the observed public auxiliary
boundary values. Only trace values receive half-domain scaling; public constants
are unscaled. No desired first/last address, comparison, window, image or seed is
supplied. The last ordinary row N-2 is the public endpoint; normalized N-1 is not.

[The calculations](Airbender/Proofs/ReducedMachine/NativeInitializationBoundary.lean)
derive equality of ALL endpoint fields to their actual public inputs, both public
address pairs' canonical16bit bounds and the public interval containing EVERY
ordinary initialization address. Earlier nonpadding records are strictly below
the public upper endpoint. These consequences use the unchanged natural sorting
proof and the SAME full-family logical lookup boundary. Public teardown values
and timestamps remain raw field limbs; no new value/time range or codec follows.

[Two short roots](Airbender/Review/Circuits/ReducedMachine/InitializationBoundaryTheorems.lean)
expose the actual public bindings, interval and address bounds. Individual
unit-normalized source relations remain separate from physical quotient/LDE/
verifier extraction. This is not Rust/serialization/transcript/commitment or
cryptographic refinement. Native constructor/debug assertions are not promoted
to proof enforcement. Public chunk windows and sorted image/seed coverage,
combined initialized memory/worker history, active worker keys/raw clocks and
real caller-worker accounting remain open. Original Sail execution is unchanged
and still excludes CSR/MOP; no frame crosses unproved delegated actions.

[Twelve controls](Tests/NativeInitializationBoundary.lean) cover all six fields,
unscaled public constants, a nonzero public endpoint SOURCE SLICE, corrupted
address/value/time rejections, a raw wide-timestamp SLICE, unchanged complete
CSR BODY plus its zero boundary, lastordinary versus normalizedlast and complete
conditional interval/strictness. These are not full positive nonempty source-aux,
global, worker or physical witnesses, attacks or native-defect evidence.
Four modules add22 explicit roots and eight exact parent origins plus one manual
source-reference record, preserving all5,560 previous ordered roots/source bytes.
The unchanged native helper was byte-compared and pinned BEFORE adaptation:
102 native pins, all previous101 preserved. Already pinned source dispatch,
scaling and boundary-value definitions were rechecked against exact native67ee.
No production/Sail/parser/exporter/artifact/fixture/dependency change or native
generation/closed heavy replay. Findings, completeness and checked parity remain
unchanged; no native defect or issue-handling assumption is introduced.

Next: actual cross-chunk window checks on these public endpoints, then sorted
public image/seed coverage and chronological combined memory history. Endpoint
binding and sorting alone do not identify initialization zeros with public seeds.


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


**Checked** means kernel-checked claims over imported v2 native constraints
and logical matching under the explicit Review interfaces. See [trust boundaries](TRUST_AND_REVIEW.md)
and the [backport plan](FORMAL_VERIFICATION_PLAN.md). V3 results are source material,
not completed v2 coverage.

## User priority: native reduced machine (2026-10-21)

Work directly on the [actual regenerated combined reduced circuit](Airbender/Review/Circuits/ReducedMachine/NativeArtifact.lean)
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
coverage remains open.** Common seven-profile original fetched execution now
includes LW/SW under an explicit exact-ROM memory/platform/domain scope; existing
six-profile arbitrary ordinary public-code execution remains unchanged.
The active
[regenerated native target](Airbender/Review/Circuits/ReducedMachine/NativeArtifact.lean)
imports 117 native equations, 142 variables and a complete fourteen-region fixed
pool. Original Clean acceptance derives its two actual sign/high-byte queries.
The public fixture is explicit; general public configuration and other operation
semantics and global/physical enforcement remain open. Mixed supported-profile
initialized original normal/fetched execution is now proved under explicit public
initialization/decoder interfaces; other combined profiles remain unfinished.
The historical 119-equation/141-variable/13-region artifact is preserved separately.
It is not assumed to be the current source-generated machine. Main/worker stage-two descriptors now have separate typed auxiliary intakes; unmodeled protocol semantics remain open. These are coverage/fidelity results, not native defects.

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

Final bounded gates pass5291 standard-only explicit axiom roots,270 public
Review roots,4 guide names and4031 links/anchors with context/trace separation.
Independent checks preserve189 v3 and1769 backport identities,80 byte-identical
modules,8 historical plus2 regenerated circuits,98 native sources,25 setup
artifacts and4 exporters. Full Review sampled aggregate footprint604.95MiB/
resident3307.45MiB in18.18s; every started guard reports no owned survivors.
A concrete rejection proof hit default recursion and was redesigned entirely
over an abstract setup BEFORE runtime-pool instantiation; no limit was raised.

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

Final bounded gates pass5275 standard-only explicit axiom roots,268 public
Review roots,4 guide names and4013 links/anchors with context/trace separation.
Independent checks preserve189 v3 and1759 backport identities,80 byte-identical
modules,8 historical plus2 regenerated circuits,98 native sources,25 setup
artifacts and4 exporters. Full Review sampled aggregate footprint605.07MiB/
resident3302.69MiB in18.23s; all started guards report no owned survivors,
with unchanged ceilings and default Lean limits.

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

Final bounded gates pass5264 standard-only explicit axiom roots,267 public
Review roots,4 guide declaration names and3988 links/anchors with context/trace
separation. Independent checks preserve189 v3 and1749 backport identities,
80 byte-identical modules,8 historical plus2 regenerated circuits,98 native
sources,25 setup artifacts and4 exporters. Full Review sampled aggregate
footprint606.13MiB/resident3302.73MiB in18.06s; every started guard reports no
owned survivors. No resource ceiling was raised; this remains a sampled
watchdog plus Lean allocation cap, not an OS hard physical-memory limit.

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

Final bounded validation passes5227 standard-only explicit axiom roots,263 public
Review roots,4 guide declaration names and3970 links/anchors with context/trace
separation. Independent checks preserve189 v3 and1738 backport identities,
80 byte-identical modules,8 historical plus2 regenerated circuit artifacts,
98 native sources,25 setup artifacts and4 exporters. Full Review sampled
aggregate footprint598.40MiB/resident3297.22MiB in19.66s; every started guard
reports no owned survivors. No ceiling was raised. The watchdog is sampled,
not an OS hard physical-memory limit.

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

Bounded validation passes5196 standard-only explicit axiom roots,261 public
Review roots,4 guide declaration names and3941 links/anchors with context/trace
separation. Independent validation checks189 v3 and1728 backport identities,
80 byte-identical modules,8 historical plus2 regenerated circuits,98 native
sources,25 setup artifacts and4 exporters. Source/dependency pins and original
checkout remain intact. Full Review sampled aggregate footprint602.29MiB,
resident3299.36MiB in18.48s; every started guard confirms no owned survivors.
No resource ceiling was raised; this is a sampled watchdog plus Lean allocation
cap, not an OS hard physical-memory limit.

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

Bounded validation passes5169 standard-only explicit axiom roots,260 public
Review roots,4 guide declaration names and3911 links/anchors with context/trace
separation. Independent validation checks189 v3 and1719 backport identities,
80 byte-identical modules,8 historical plus2 regenerated circuit artifacts,
96 native-source pins,25 setup artifacts and4 exporter files. Original checkout,
source pins and dependency versions remain intact. Full Review sampled aggregate
footprint599.18MiB/resident3297.77MiB in29.19s; every started guard confirms no
owned survivors. No resource ceiling was raised; the watchdog remains sampled,
not an OS hard physical-memory limit.

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

Checked milestone gates: all8 new modules,12 theorem regressions and18 executable
intake controls pass under the unchanged bounded serial worker. Public Review
passes5134 standard-only explicit axiom roots,256 public roots,4 guide names and
3866 links/anchors with context/trace separation. Independent provenance checks
189 v3/1708 backport identities,80 byte-identical modules,8 historical+2 regenerated
circuit artifacts,93 unchanged native sources,25 setup artifacts and4 exporter
files; original checkout and dependency pins remain unchanged. Counts are audit
evidence, not parity or defect counts.

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

Checked milestone gates: all8 new modules and18 theorem regressions pass under
the unchanged bounded serial worker. Public Review passes5113 standard-only
explicit axiom roots,254 public roots,4 guide names and3823 links/anchors with
context/trace separation. Independent provenance passes189 v3/1695 backport
identities,80 byte-identical modules,8 historical+2 regenerated circuit artifacts,
93 native sources,25 setup artifacts and4 exporter files; dependency pins and the
original checkout remain unchanged. These counts are audit evidence, not parity.

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

Checked milestone gates: all8 new modules compile under the unchanged bounded
serial worker;14 theorem regressions and14 executable intake controls pass.
The full public Review gate passes5081 standard-only explicit axiom roots,
251 public roots,4 guide names and3770 links/anchors with context/trace separation.
Independent provenance checks189 v3 and1685 backport identities,80 unchanged
reused modules,8 historical+2 regenerated circuit artifacts,90 native sources,
25 setup artifacts and4 exporter files. Original checkout and dependency pins
remain unchanged. Counts are audit evidence, not parity or defect counts.

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

Scoped gates pass5058 explicit standard-only axiom roots,249 public Review
roots,4 guide names and3728 links/anchors with context/trace separation. All12
new regressions pass;4 new modules record7 exact parentef02 template origins and
22 new explicit roots. FullReview used591.89MiB sampled aggregate footprint/
3211.52MiB resident/25.36s; independent provenance22.30/38.38MiB/11.31s passes
189 v3/1675 backport identities,80 identical modules,8 historical/2 regenerated
circuit artifacts,89 native sources,25 setup artifacts and4 exporter files.
Original checkout, proof pins and dependencies remain intact. No native/artifact/
importer/exporter/heavy certificate regeneration or replay occurred.

All started failed/successful guards report no owned survivors. Routine natural
modulo-to-field cast and vector Nat-index API drafts were corrected. A generic
computable location decision procedure performs the actual finite metadata
checks without asking typeclass search to unfold concrete ABI arrays. All final
proofs use default limits; no heartbeat, recursion, allocation, footprint,
resident or wall ceiling was hit or raised. Sampled watchdog/allocation caps
remain distinct from an OS hard physical-memory limit. Counts are audit evidence,
not parity.

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

Scoped gates pass5036 explicit standard-only axiom roots,247 public Review
roots,4 guide names and3693 local links/anchors with context/trace separation.
Seven new modules/tests record11 exact parent7540376 template origins and23
new roots. All12 regressions and6 executable intake controls pass. FullReview
used589.58MiB sampled aggregate footprint/3208.59MiB resident/17.02s; independent
provenance24.61/40.69MiB/11.11s passes189 v3/1668 backport identities,80 identical
modules,8 historical/2 regenerated circuit artifacts,86 native sources,25 setup
artifacts and4 exporter files, with original checkout/dependencies/pins intact.
All started failed/successful guards report no owned survivors. Routine reserved
field-name/prime-field instance/list-induction/column-equality drafts were corrected;
all final proofs use default limits. No heartbeat, recursion, allocation, footprint,
resident or wall ceiling was hit or raised. The native source-rule transcription
and physical enforcement boundary remain explicit; no production/native generation
or unchanged heavy certificate replay occurred. Counts do not establish parity.

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

The scoped gates pass5013 standard-only explicit axiom roots,246 public Review
roots,4 guide declaration names and3646 local links/anchors with context/trace
separation. Five new modules record8 exact parent39d4 template origins and22
new explicit roots; all12 new regressions pass. FullReview used587.84MiB sampled
aggregate footprint/3206.20MiB resident/16.87s; the axiom module used582.47/
3110.12MiB/10.17s. All started failed/successful guards report no owned survivors.
The initial abstract-field syntax draft was specialized to the actual Mersenne31
coefficient representation; a canonical-value rewrite was narrowed to avoid
rewriting its source expression. Final proofs pass default limits, with no cap
hit/raise, foreign opacity or evaluation shortcut. Independent provenance used32.55MiB sampled footprint/49.14MiB resident/11.84s
and passed189 v3/1657 backport identities,80 byte-identical modules,8 historical
and2 regenerated circuit artifacts,86 native sources,25 setup artifacts and4
exporter files; original checkout, dependency versions and proof pins are intact.
Existing native/intake inputs and code are unchanged; no heavy certificate or
native generation was replayed.

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

The final scoped gates pass4991 explicit standard-only axiom roots,245 public
Review roots,4 guide declaration names and3618 links/anchors with context/trace
separation. All13 theorem regressions and6 query-intake controls pass. Full
Review used588.67MiB sampled aggregate footprint/3206.91MiB resident/16.57s;
independent provenance19.11/38.23MiB/10.97s passes189 v3 and1649 backport origin
identities,80 byte-identical modules,8 historical/2 regenerated circuit artifacts,
86 native sources,25 setup artifacts and4 exporter files. Fourteen new modules
record20 exact parent origins; no prior importer/native artifact/source/exporter,
fixture, dependency or original-checkout file changed. Existing unchanged native
and intake controls retain their earlier applicability without heavy replay.

Every started failed/successful guard ended with no owned survivors. Large64,
16 and one late8-query simplification draft reached the default200000 heartbeat
limit; small commands and separate kernel syntax equalities solved that work
at default limits. Abstract typed getter transport avoids dependent data
normalization. No heartbeat, recursion, allocation, footprint, resident or wall
ceiling was raised; sampled watchdog/allocation caps are not OS hard physical
memory limits. Audit counts do not establish parity.

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

The final scoped gates pass4951 explicit standard-only axiom roots,244 public
Review roots,4 guide declaration names and3579 local links/anchors with context/
trace separation. The native gate reproduces both exports and all344384 rows,
with five bad CLI/layout controls;19 new importer controls and12 table regression
roots pass. Full Review used586.03MiB sampled aggregate physical footprint,
3201.69MiB resident memory and18.10s. Independent provenance passes189 v3 and1629
backport origin identities,80 byte-identical modules,8 historical/2 regenerated
circuit artifacts,86 native sources,25 setup artifacts and4 exporter files;
pins, dependencies and the original checkout are preserved.

Every started failed/successful guard ended with no owned survivors. Combined
literal import, coarse XOR9 and dense-array reduction drafts hit Lean's allocation
cap below the watchdog ceilings. Five separate imports, smaller native-block
units, symbolic dense geometry,32by16 finite read cases and generic singleton
assembly pass at default proof limits. No memory, wall-time, recursion or heartbeat
ceiling was raised. These are sampled watchdog/allocation caps, not OS hard
physical-memory enforcement. Audit counts are qualification evidence, not parity.

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

The final worker gates pass: complete local emission counts, native ABI/control
proofs and12 regression roots,24 executable intake controls, scoped native source/
constructor/byte reproduction and2 malformed CLI checks. Full Review checks3618
standard-only axiom roots,238 public Review roots,4 guide names and3535 links/
anchors/layers. Independent exact Git-object provenance checks include86 native
sources; original checkout/pins/dependencies and all prior fixtures stay unchanged.
All owned workers terminated. Checks use the shared single-worker lock, Lean-j1-
M3072 and sampled3072MiB-footprint/4096MiB-resident finite-time watchdog; this is
not an OS hard physical-memory limit. Default heartbeat/recursion failures were
resolved by pure arithmetic and small block-count facts, without raising caps.

## Selected unrolled caller argument reference and normalization (7 November 2026)

The [selected native unrolled prover](../../prover/src/prover_stages/unrolled_prover/mod.rs)
passes literal circuit_sequence0 to ProverCachedData::new. The [cache calculation](../../prover/src/prover_stages/cached_data.rs)
therefore contributes zero additional sequence-high shift for this constructor.
[Kernel checks](Airbender/Proofs/ReducedMachine/NativeCSRArgument.lean) retain the
actual imported trace2^23/three-access geometry and shift23+2-19=6. The earlier
sequence-high question is resolved for this selected constructor; generic cache
calls with nonzero sequence and general Rust refinement remain separate.

[Reviewed source-reference definitions](Airbender/Review/Helpers/Memory/ReducedMachineCSRArgument.lean)
retain native stage2 key aggregation and quotient homogenization: all witness-
linear terms scale by tau, while gamma, literal in-cycle offset3 and sequence-high
terms are added outside that scaling. Symbolic ring proofs identify the quotient
denominator with aggregation of the normalized four-part key for every tau. At
unit scaling, that key equals the actual imported caller key BEFORE compression,
and stage2/quotient denominators agree. This is not a claim that all protocol
points have tau=1 or that arbitrary challenge compression is injective.

[The short public argument root](Airbender/Review/Trace/Families/ReducedMachine/CSRArgument.lean)
constructs the actual initialized caller projection with exact native row origins
and all per-row key/argument identities, retaining full original-source/request/
GPR/native history. Inputs remain full original CSR setup/membership, ordinary
logical seeds, accepted runtime constraints/matching and tracked alignment. Any
commutative target ring, base-field homomorphism and challenges are explicit;
no caller stream or per-row source/read/range/request/result/clock/state/worker
answer, inverse, nonzero denominator or compression-injectivity premise is added.

Nine [independent scalar/reference regressions](Tests/NativeReducedCSRArgument.lean)
check sequence0, exact tuple, stage2/quotient values, gamma and literal offset
outside witness scaling, zero scaling, no double sequence shift and distinct keys
colliding under arbitrary challenge compression. These are reference/algebra
checks, not full positive nonempty accepted CSR witnesses or cryptographic attacks.
Five new modules/tests record six exact parent76847 origins; constructor/cache
sources are newly byte-pinned to67ee, while aggregation/constants were already
pinned and rechecked. All production/native/Sail/input/fixture/dependency bytes
remain unchanged; no defect, assumption/fix, axiom, whole-machine or parity claim.

This closes the selected constructor-zero calculation and reviewed per-row argument
normal form. General Rust/field-encoding/LDE correspondence and physical verifier
argument enforcement remain scoped separately. Main Trace.Accepted still has no
stage2 auxiliary/global worker ledger, so issuance, fulfillment, converse and
accounting are not inferred. NEXT prioritize actual native Blake2 worker artifact/
ABI/constraints and request-worker acceptance/accounting, including stage2 auxiliary
and accumulator connections; do not redo this algebra or earlier caller/source
history. Original CSR/custom/nondeterminism/privilege/PC retirement/common integration,
delegated RAM effects, protocol/terminal/init/physical/crypto/completeness stay open.

Final gates pass 3,595 explicit standard-only axiom roots, 237 public Review
roots, four guide names and 3,500 links/anchors with context/trace separation.
Full Review sampled footprint/resident peaks were 562.37/3,150.08 MiB over 26.57 s.
Independent provenance passes 189 v3-origin/1,450 backport-origin identities,
80 byte-identical modules, eight circuit artifacts, 82 native source pins, 24 setup
artifacts and four exporter files with unchanged pins/dependencies/original
checkout (18.53/36.44 MiB, 9.85 s). Every started guard leaves no owned survivor;
no resource or proof ceiling changed. This is sampled watchdog plus Lean allocation
cap, not an OS hard physical-memory limit. Exact unchanged intake/native/heavy
certificate gates retain their prior applicability and were not repeated.

## CSR row-local caller clocks and chronological projection (7 November 2026)

[The public caller root](Airbender/Review/Trace/Families/ReducedMachine/CSRCallers.lean)
now retains full initialized original-source/request history and constructs a
chronological projection selected by the actual imported multiplicity. All native
rows/tokens, including zero-multiplicity rows and both readonly GPR refreshes,
remain in the full history. No caller stream, per-row source/read/range/request/
clock/state/order/count/worker answer is supplied.

[Exact metadata and clock proofs](Airbender/Proofs/ReducedMachine/NativeCSRCallerClock.lean)
bind the imported request to columns92/94/some93/index3 and row-local timestamp
(w2+3,w3), using the actual intermediate-state clock2/3. Shared initialized native
clock bounds/alignment and unchanged pure write_time establish canonical bounded
timestamp limbs, numerical value=row.clock+3, residue3 modulo4 and nonzero value.
The slot is strictly after every actual GPR access0/1/2 and before the next native
machine clock. Strict row order yields strict caller-clock order, excluding
repeated local caller clocks. Actual runtime request equations/source-derived mask
identify every selected kind1991 and bounded optional ABI-high. The [projection](Airbender/Review/Helpers/Memory/ReducedMachineCSRCallers.lean)
records each caller's actual row origin and these derived facts.

Eight new [clock/filter/order regressions](Tests/NativeReducedCSRCallers.lean) and
one [complete-empty public projection](Tests/NativeReducedCSRHistoryEmpty.lean)
pass: initial slot7, last low-limb slot524287, next high-limb slot524291, four-tick
boundary spacing, zero-multiplicity exclusion, selected participation, descending
order and initialized zero-clock rejection. The complete accepted EMPTY runtime
trace retains a real x0 terminal token, empty original bytes and no CSR privilege
premise at every RV32 PC while projecting no caller. These pure/conditional/empty
checks are not full positive nonempty accepted CSR witnesses or original execution.

Five new modules and one extended test record eleven exact parent4baa origins.
Five unchanged native compiler/prover files are newly byte-pinned to67ee: executor
compilation, unrolled stage2/shared/stage3 and delegation quotient evaluation.
Read-only source inspection confirms the stage-two caller tuple convention. The
stage-three quotient separately includes a circuit-sequence HIGH contribution;
its timestamp representation/normalization must be connected before physical or
global caller-key claims. Do not append that contribution blindly to a witness
representation that may already include it. This is an open refinement boundary,
not a demonstrated discrepancy or native defect.

The checked result is ROW-LOCAL caller projection, not enforced issuance, a worker
request ledger, fulfillment, converse or global accounting. NEXT bind the actual
protocol key/sequence normalization and native request/worker acceptance, then
actual Blake2 ABI/constraints and accounting. Keep original CSR/custom/nondeterminism/
privilege/PC retirement, delegated RAM actions, common execution integration and
protocol/terminal/init/general public/physical/refinement/crypto/completeness open.
Bigint1994 remains outside this runtime target. All production/native/Sail/input/
fixture/dependency bytes and existing seven-profile/old-fixture/memory/shadow scopes
are unchanged; no defect, issue assumption, fix, axiom or parity claim.

Final gates pass 3,578 explicit standard-only axiom roots, 236 public Review
roots, four guide names and 3,488 links/anchors with context/trace separation.
Full Review sampled footprint/resident peaks were 562.51/3,151.08 MiB over 26.88 s.
Independent provenance passes 189 v3-origin/1,444 backport-origin identities,
80 byte-identical modules, eight circuit artifacts, 80 native source pins, 24 setup
artifacts and four exporter files with unchanged pins/dependencies/original
checkout (21.69/39.55 MiB, 10.07 s). Every started guard reports no owned survivors;
default proof/resource ceilings remain unchanged. This is sampled watchdog plus
Lean allocation cap, not an OS hard physical-memory limit. Unchanged intake/native
and heavy-certificate gates retain exact prior code/inputs and were not repeated.

## Original CSR source and request ABI observations (7 November 2026)

[The short runtime request root](Airbender/Review/Trace/Families/ReducedMachine/CSRRequests.lean)
strengthens the checked chronological CSR GPR realization in the very same
rowBefore states. Every native source35/36 is the canonical two-limb encoding of
an original pre-state rs1 read, and its full RV32 numerical value is preserved,
including values above the Mersenne31 modulus. [The local bridge](Airbender/Proofs/ReducedMachine/NativeCSRSource.lean)
uses existing initialized bounds, original unsigned CSR index/query identities
and actual runtime request equations to derive multiplicity, kind and optional
ABI-high from that source. Division by 65,536 is natural-number division before
the field cast; no field-reduced architectural source is substituted.

[CSRRequestHistory](Airbender/Review/Helpers/Memory/ReducedMachineCSRRequests.lean)
retains full native MemoryHistory, every token/segment state/order/permutation,
same-prestate GPR transfer, original source replay, final matching and byte/misa
frames. The new source/request observation is attached to that same constructed
segment. Public inputs remain full original CSR setup/membership, ordinary logical
ImageBoundary, Accepted(runtimeCSRData trace) and tracked alignment. No per-row
source/read/value/range/request/state/worker/success answer is supplied.

Eight [regressions](Tests/NativeReducedCSRRequests.lean) pass: arbitrary-source
nondeterminism has no delegation request, delegation observes the natural high
half, low-half changes preserve it, the 0xffff/0x10000 boundary differs, full RV32
maximum and values above the field modulus retain their high half, and a wrong
request contradicts actual local native constraints and real GPR history. These
are pure-reference/conditional-native checks, not full positive nonempty accepted
CSR witnesses or original CSR/custom/nondeterminism execution.

Five new modules/tests record eleven exact parentbff728 source origins. No native,
production, Sail, import/export, artifact, fixture or dependency input changes.
No native defect, issue assumption, fix, new axiom or parity claim. Imported
in-cycle offset3 remains metadata only. Main Trace.Accepted checks row constraints,
activity and state/memory matching; it does not establish a caller/worker request
ledger. NEXT inspect the actual native compiler/protocol request-clock connection
and derive an honest caller projection before any issuance/accounting claim.
Original CSR/PC retirement, delegated RAM/worker effects, fulfillment/converse,
protocol/terminal/init/general public/physical/refinement/crypto/completeness stay
open. Existing seven-profile execution still excludes CSR/MOP and remains unchanged.

Final gates pass 3,564 explicit standard-only axiom roots, 235 public Review
roots, four guide names and 3,478 links/anchors with context/trace separation.
Full Review sampled footprint/resident peaks were 563.42/3,149.72 MiB over 15.35 s.
Independent provenance passes 189 v3-origin/1,433 backport-origin identities,
80 byte-identical modules, eight circuit artifacts, 75 native sources, 24 setup
artifacts and four exporter files with unchanged pins/dependencies/original
checkout (18.08/37.19 MiB, 10.38 s). Every guard leaves no owned survivor; default
proof/resource ceilings remain unchanged. These are watchdog samples plus Lean
allocation caps, not an OS hard physical-memory limit. No intake changed, so exact
unchanged prior importer/native/heavy-certificate gates were not repeated.

## Initialized native CSR GPR history and word bounds (7 November 2026)

[Fresh CSR port proofs](Airbender/Proofs/ReducedMachine/NativeCSRPorts.lean) bind all
three actual native addresses to original rs1, readonly rs2=x0 and rd, using the
actual CSR field equations and source-derived decoder identities. Both readonly
refreshes, destination OLDREAD, aliases and raw x0 operands remain. [Write proofs](Airbender/Proofs/ReducedMachine/NativeCSRPreservation.lean)
combine actual scalar oracle bounds, candidate/rdmask and original zero flag to
establish bounded writes and local preservation, with no source/range answer.

[Initialized word bounds](Airbender/Review/Trace/Families/ReducedMachine/CSRValues.lean)
instantiate the unchanged single time induction on accepted native matching and
public Sail seed reads. Every actual native read/write/terminal word is bounded,
including previously unchecked source-low35, second read37 and destination OLDREAD.
The proved actual rd-address/x0 rule precedes shared zero propagation; readonly
x0 refreshes are retained and their actual values follow initialized history.

[The short GPR-history roots](Airbender/Review/Trace/Families/ReducedMachine/CSRRegisters.lean)
now construct the complete native memory history, row permutation/clock order,
every rowBefore/rowAfter/past/current/future segment and final Sail cell matching.
All three original GPR reads observe one pre-state before the actual masked write.
[CSR event-space and code proofs](Airbender/Proofs/Trace/Families/ReducedMachine/CSRCodeHistory.lean)
first derive GPR space from fresh actual selected-row address laws, then derive all
byte/misa frames and original stateful source replay at each constructed rowBefore.
No per-row source/read/value/range/state/order/replay/frame/preservation is supplied.

Generic modeled-setup roots and explicit runtime-pool roots keep their public
interfaces separate; runtimeCSRData retains every row, boundary and token. Inputs
are full original CSR public setup/membership, ordinary logical ImageBoundary and
tracked alignment for GPR history. No CSR availability, privilege, expected oracle/
custom-operation success, table identity or worker answer is added. This public
seed constructor is not universal physical boot or independent ROM-shadow setup.
Existing seven-profile/memory/shadow execution scopes remain unchanged.

Seventeen [initialized/alias/port regressions](Tests/NativeReducedCSRInitialized.lean)
and [empty-history roots](Tests/NativeReducedCSRHistoryEmpty.lean) pass: fresh port
rejections, same-prestate aliases/OLDREADs, discarded GPR update, oversized source/
second-read/write/terminal and nonzero x0 rejection, actual readonly x0 read zero,
CSR-shaped positive original query/three-port mechanics, and complete native EMPTY
runtime history with a real terminal x0 token at every RV32 PC. Empty original
bytes and no CSR/privilege premise are explicit. These conditional-native/partial-
positive/complete-empty tests are not full positive nonempty117-equation/22-lookup
accepted CSR witnesses or original CSR instruction execution.

Eleven new modules/tests record eighteen exact parentde55 source origins. These
Sail states realize native GPR transfers; they do not execute the original CSR
clause or delegated RAM effects. Their byte-memory frame must not be transferred
through an unproved worker action. CSR original/custom/nondeterminism/privilege
semantics, PC retirement, request clock/issuance, fulfillment/converse/accounting,
protocol/terminal/init/physical/general refinement/crypto/completeness remain open.
Production/native/Sail/import/export/artifact/fixture/dependency inputs stay unchanged;
no native defect, issue assumption, fix, new axiom or parity claim. NEXT connect
original pre-state source words to request ABI observations and check actual native
caller clock/issuance before worker streams; metadata index3 alone is not issuance.

Final bounded gates pass 3,552 explicit standard-only axiom roots, 234 public
Review roots, four guide declaration names and 3,468 local links/anchors with
context/trace separation. Full Review sampled aggregate footprint/resident peaks
were 565.17/3,148.92 MiB over 18.83 s. Independent provenance passes 189 v3-origin
and 1,422 backport-origin identities, 80 byte-identical modules, eight circuit
artifacts, 75 native sources, 24 setup artifacts and four exporter files; all pins,
dependencies and the original checkout are preserved (18.25/34.62 MiB, 9.88 s).
All started guards report no owned survivors. No resource or proof cap was raised;
these are sampled watchdog measurements plus Lean's allocation cap, not an OS
hard physical-memory limit. Unchanged intake/native/heavy certificate gates retain
their exact prior code and inputs and were not repeated for this proof-only change.

## Original public CSR decoding and runtime effects (7 November 2026)

[The original CSR projection](Airbender/Review/Circuits/ReducedMachine/CSRDecoder.lean)
now retains register CSRRW with raw rs1/rd, readonly rs2=x0, unsigned 12-bit CSR
index, native mask129 and funct3=1. CSRRS/CSRRC/immediate CSR and other operations
remain outside this projection. No x0 opcode rewrite, standalone operand restriction,
CSR allow-list or privileged-execution answer is added. The pinned native reduced
decoder separately zero-extends this index and preserves raw operands; source
inspection is not general Rust decoder/export refinement.

[Native source/field proofs](Airbender/Proofs/ReducedMachine/NativeCSRDecoder.lean)
recover the original constructor, every native operand/rd/x0/index field, canonical
12-bit key and zero high limb from original public construction and all ten query
fields. Full sparse/padded membership plus accepted native packing rejects holes
and the all-minus-one tail. [The short public decoder root](Airbender/Review/Trace/Families/ReducedMachine/CSRDecoder.lean)
requires no per-row source/profile/mask/rd/index answer. Its generic modeled setup
scope remains separate from fixed ROM or physical preprocessing.

[The explicit runtime trace constructor](Airbender/Review/Trace/Families/ReducedMachine/RuntimeCSRData.lean)
selects the checked runtime CSR pool, retaining every row, state/memory boundary
and matching token. The new public runtime-effect root composes original decoding
with accepted constraints on this construction: it derives the local CSR mask and
all previously checked native support/delegation/return/request/ABI-bound effects.
No local mask, desired request/read/value/range/PC/state/worker success or table
identity premise is supplied. This is a CSR-only decoded profile; existing mixed
seven-profile and original-fixture roots remain unchanged. Arbitrary logical public
code is not identified with the constructed pool's retained eight-word ROM.

Fourteen [regression roots](Tests/NativeReducedCSRDecoder.lean) include a complete
independent three-slot original byte image plus one padding row, genuine CSRRW
sources1984/rs1=1/rd=3 and1991/rs1=2/rd=0, a retained unsupported CSRRS hole,
unsigned4095/raw/x0 fields, corrupt funct3/zero/rs2 and native sentinel rejection.
The original decoder succeeds with empty registers, without a CSR-availability or
privileged-execution premise. Conditional accepted-runtime tests derive original
source/runtime key domain and exclude bigint1994 without a supplied mask.
These are original-source/conditional-native tests, not full positive nonempty
117-equation/22-lookup accepted CSR witnesses or original CSR execution.

Seven new modules/tests record eleven exact parent3d25 origins. The unchanged
native CSR operation definition is newly byte-pinned to base67ee. Original CSR
architectural semantics, initialized rs1/read/x0/history, PC retirement, request
clock/issuance, worker fulfillment/converse/accounting and unified protocol remain
open, alongside MOP/reference/physical/general refinement/cryptography/completeness.
Production Rust/circuits/Sail/importers/exporters/artifacts/literals/fixtures and
dependencies remain unchanged; no native defect, issue assumption, fix, new axiom
or parity claim. NEXT derive actual CSR GPR port/write/x0 laws, initialized bounds/
history/source values and native caller clock/issuance before worker composition.

Milestone gates pass 3,513 explicit standard-only axiom roots, 230 public Review
roots, four guide declaration names and 3,447 local links/anchors with context/trace
separation. Full Review used 564.36 MiB sampled aggregate footprint / 3,148.09 MiB
resident / 15.36 s; independent exact provenance used 18.03 / 36.77 MiB / 9.69 s
and passed 189 v3-origin / 1,404 backport-origin identities, 80 byte-identical modules,
eight circuit artifacts, 75 native sources, 24 setup artifacts and four exporter
files. All owned workers terminated under unchanged fixed watchdog/allocation/wall
caps. Two broad decoder simplification drafts reached default recursion depth;
small exact Zicsr rewrites pass at default limits. No cap was raised or foreign
data made opaque. Import/export/native controls retain unchanged inputs and code;
no heavy unchanged data/certificate replay or physical-memory hard-limit claim.

## Runtime CSR full-pool lookup and local effects (7 November 2026)

[The explicit complete pool](Airbender/Review/Circuits/ReducedMachine/Tables/RuntimePool.lean)
now assembles5,771,521 rows in native offset order from the thirteen unchanged
stored regions and the separately exported runtime CSR region. It retains the
eight-word ROM and its complete UNIMP tail. This is a native-shaped logical setup
construction with source-pinned CSR inputs1984/1991, not a universal runtime ROM,
Rust/public export or physical setup certificate. The original complete pool and
its1988/1989 fixture remain unchanged; the earlier regional-only checkpoint below
is retained as history.

[Fresh partition and tag proofs](Airbender/Proofs/ReducedMachine/NativeRuntimePool.lean)
recover every stored region from this pool's membership and isolate tag25 to the
new actual CSR data. The [short pooled CSR/sign roots](Airbender/Review/Circuits/ReducedMachine/Tables/RuntimePoolTheorems.lean)
reuse existing literal certificates only after those data bindings. Thirteen
regional identities follow by construction, without a table-equivalence premise.
[Actual lookup projection](Airbender/Proofs/ReducedMachine/NativeRuntimeQueries.lean)
extracts both tag16 sign/high-byte queries and all four dynamic query/selector
domains from original Clean acceptance of the same117-equation native artifact
on this table. No old full-circuit acceptance is transferred.

[The new local runtime CSR root](Airbender/Review/Circuits/ReducedMachine/RuntimeCSRTheorems.lean)
combines the actual selected query/support equation with the new pooled certificate:
only1984/1991 are supported and only1991 delegates. It derives both oracle bounds,
delegation zero before destination masking, actual readonly GPR routing/candidate/
rdmask/default-PC and every imported masked request field. Actual source-high
slot16 supplies the ABI high-offset bound. The public premise is the explicit
local CSR mask, not original public decoding; there is no desired source/read/
range/output/query/request/state/PC/worker/success or table-identity premise.
In-cycle index3 remains imported metadata, not request clock/issuance/accounting.

Sixteen [regression roots](Tests/NativeRuntimePool.lean) cover all thirteen shared
regions, positive participation of every runtime CSR row in the full pool,
positive1991/1984, old-fixture separation, fixture/bigint exclusion through actual
selected native constraints, nondeterminism zero request/bounded return, delegated
zero return, exact request fields, discarded-rd request retention and oversized
source-high/ABI/absent-selector rejection. They are table/conditional-native checks,
not complete positive nonempty117-equation/22-lookup accepted CSR witnesses.
Eleven exact parent195 source origins record eight new modules/tests. Importers,
exporters, literal/native artifacts, production Rust/circuits/Sail, all old roots,
public fixtures, dependencies and original checkout/caches remain unchanged.
No native defect, issue assumption, fix, new axiom or parity claim.

Milestone gates pass3,490 explicit standard-only axiom roots,228 public Review
roots,four guide declaration names and3,430 local links/anchors with context/trace
separation. Full Review used562.46MiB sampled aggregate footprint/3,143.11MiB
resident/15.18s; independent exact provenance used21.81/37.91MiB/9.59s and passed
189 v3-origin/1,393 backport-origin identities,80 byte-identical modules,eight
circuit artifacts,74 native sources,24 setup artifacts and four exporter files.
Every owned worker terminated. Fixed3072MiB sampled footprint/4096MiB resident,
Lean-j1-M3072 and finite180s module/120s audit caps stayed unchanged; no memory,
wall-time or proof limit was hit or raised. This watchdog plus allocation cap is
not an OS hard physical-memory ceiling. Prior importer/exporter/native controls
retain unchanged code and inputs; no heavy unchanged data/certificate replay.

NEXT derive original public CSR entry/query/source/rd-x0 and request clock/issuance
from accepted native constraints, initialized history and public inputs before
caller streams or Blake2 worker composition. Original CSR/nondeterminism/privilege
and custom MOP reference/initialized/retained/fetched/common execution, actual worker
ABI/constraints/fulfillment/converse/accounting and protocol/terminal/init/physical/
general refinement/cryptography/completeness remain open. Bigint1994 stays outside
this selected runtime target. Earlier seven-profile execution scopes are unchanged.

## Separate actual runtime CSR region (7 November 2026)

The pinned [unified reduced runtime constructor](../../circuit_defs/unrolled_circuits/unified_reduced_machine/src/lib.rs)
uses an allow-list containing nondeterminism1984 and Blake2 CSR1991. Bigint1994
is outside this selected target. A new FV-only exporter mode calls the unchanged
native CSR generator on that source-derived configuration and exports only the
4,096-row tag25 region at native offset1507585. The original complete 5,771,521-row
pool, its eight-word image and delegation fixture1988/1989 remain unchanged.

[The new short regional root](Airbender/Review/Circuits/ReducedMachine/Tables/RuntimeCSRTheorems.lean)
now derives every key's exact support/delegation flags from the separately
[exported actual literal data](artifacts/setup/reduced-runtime-csr-native.json).
[The kernel certificate](Airbender/Proofs/ReducedMachine/NativeRuntimeCSR.lean)
covers all4,096 rows using symbolic zero intervals and finite exceptional slots:
only1984/1991 are supported and only1991 delegates. No foreign data is opaque,
no table-equivalence premise is used and no expected row output is supplied.
A separate pure interval lemma keeps calculation outside imported-record proofs
at default limits.

[The strict importer](Airbender/Import/RuntimeCSRSetup.lean) checks the selected
public configuration, profile, exact geometry, JSON fields and canonical literal
encoding, and emits the same-read data/source bytes. Row semantics are kernel
obligations. Eight [theorem regressions](Tests/NativeRuntimeCSR.lean) preserve
metadata/all-row participation/positive Blake2 and nondeterminism, distinguish
fixture and runtime relations, and reject fixture1988/bigint1994/nondeterminism
as delegation/outside12bit keys. [Importer controls](Tests/NativeRuntimeCSRImport.lean)
reject crossed profiles/configurations, malformed geometry/encoding and extra
fields while retaining the distinction between literal intake and semantics.
The scoped [native reproduction gate](scripts/check_runtime_csr.py) checks the
pinned u32/u16 runtime allow-lists, every native exported row, repeat/byte export
and six malformed CLI/layout cases. New gates join the serial standard workflow.

This certificate covers the actual runtime CSR REGION, not a complete runtime
fixed pool or its placement in accepted native traces. Existing local CSR request
and seven-profile execution roots continue to use the unchanged original pool;
no coverage is transferred to the new region through an equivalence assumption.
Runtime pool/source/decoder/row/worker connections, original CSR/MOP reference
execution, issuance/fulfillment/accounting, physical setup and general refinement/
cryptography/completeness remain open. Twelve exact parent-e05 source origins and
four newly pinned native runtime/ABI source files record the adaptation. Production
Rust/circuits/Sail, existing artifacts/fixture/dependencies are unchanged; no native
defect, issue assumption, production fix, new axiom or parity claim.

NEXT construct and certify the runtime pool/selected CSR query connection from
these actual regional values and existing native regions, or derive the public
CSR source/decoder/clock caller stream, before worker composition. Preserve the
runtime target's Blake2-only delegation scope; do not silently add bigint or
relabel old fixture keys. Other worker targets require their own checked setup.

## Actual native CSR table and local requests (7 November 2026)

[The special-CSR certificate](Airbender/Review/Circuits/ReducedMachine/Tables/CSRTheorems.lean)
now covers all 4,096 actual tag-25 rows in the complete native pool. Symbolic zero
intervals and six/two stored exceptional slots prove the exact explicit fixture:
1984, 1988 and 1989 are supported; only 1988/1989 delegate. Full-pool tag isolation
recovers the canonical 12-bit key and both output flags. This does not generalize
the configured allow-list to other runtime/public setups.

[The short local CSR root](Airbender/Review/Circuits/ReducedMachine/CSRTheorems.lean)
derives the actual selected mask 129 flags, first dynamic query and remaining
inactive tags, then excludes every unsupported key using the actual support
assertion. [Native local observables](Airbender/Review/Circuits/ReducedMachine/CSR.lean)
retain selected immediate routing, the readonly second GPR port, actual oracle/
candidate, GPR destination/masked write and default-PC selection. Actual scalar
slots 4/5 bound the oracle limbs. Delegation forces the actual oracle to zero;
nondeterminism uses a bounded native oracle whose reference value/stream is not
identified here. No source/read/output/range or worker answer is supplied.

[Fresh request bindings](Airbender/Proofs/ReducedMachine/NativeCSRResult.lean)
use actual polynomials 68–73 and exact imported coordinates: multiplicity 92,
kind 94, ABI high offset 93, in-cycle metadata index 3. Delegating rows derive
multiplicity one, their actual key as kind and actual source-high word 36 as ABI
offset. Nondeterminism derives a zero request. The masked ABI offset inherits
its bound from the actual source-high lookup, not an assumed per-row source or
expected offset. An absent ABI group stays absent in the observer; the actual
imported group is proved present. Metadata index 3 is not a global scheduling,
caller issuance, worker fulfillment or accounting theorem.

Thirteen [focused regressions](Tests/NativeReducedCSR.lean) include every fixture
row at its actual native-pool offset, forged support/delegation/outside-key
rejection, conditional unsupported-CSR and nonzero-delegation-oracle rejection,
nondeterminism zero request, discarded destination retaining a delegation request,
ABI-group/bound checks and three independent positive slices of the six actual
CSR request equations. These table/reference/conditional-native/partial-positive
checks are not complete accepted nonempty 117-equation/22-lookup CSR rows,
initialized architectural effects or original execution. Nine new modules/tests
record 18 exact parent-9bc origins; the unchanged active CSR/delegation Rust file
is independently pinned to native base 67ee. No production/native/Sail/artifact/
fixture/dependency changes, native defect/issue assumption or new axiom.

Read-only comparison against native base 67ee also distinguishes this fixture
from worker ABI configuration: [native delegation constants](../../common_constants/src/delegation_types/mod.rs)
assign Blake2 CSR 1991 and bigint CSR 1994 through their respective +7/+10
constants. The fixed imported allow-list is 1988/1989. This is a setup/reference
binding to assess before worker composition, not an established defect or an
identity between fixture requests and those workers. General setup coverage stays
open; neither the existing fixture nor production Rust is changed here.

Original public CSR/MOP decoding, custom-operation/nondeterminism/privilege
reference semantics, initialized source/x0/history and normal/fetched/common
execution remain OPEN. Existing seven-profile execution scopes stay unchanged.
NEXT connect actual caller requests to native worker constraints, fulfillment and
accounting, while assessing the retained custom/reference boundary independently
of v3. Protocol spans, padding/terminal/init/teardown/general Rust/public/physical/
cryptographic/completeness and parity remain open.

## Actual native MOP local arithmetic (7 November 2026)

[The short local MOP theorem](Airbender/Review/Circuits/ReducedMachine/MOPTheorems.lean)
now derives ADDMOD, SUBMOD and MULMOD numerical results from the actual regenerated
117-equation reduced artifact and its scalar lookups. [Its observables](Airbender/Review/Circuits/ReducedMachine/MOP.lean)
refer to native source words, the readonly second GPR port, all four inactive
dynamic tags, actual candidate/destination/masked write and default-PC selection.
They do not assert original pre-state Sail reads or initialized execution.

[Fresh native selectors and fields](Airbender/Proofs/ReducedMachine/NativeMOPFields.lean)
check masks34819/133123/67587 for ADD/SUB/MUL and the actual ADD/MUL/SUB minor
ordering. The actual multiplication relation uses65536 squared=2 modulo
Mersenne31. [The result proof](Airbender/Proofs/ReducedMachine/NativeMOPResult.lean)
uses the actual required final underflow, range-checked subtraction remainder,
Boolean carries and unchanged PURE borrow_iff to derive output<p. Together with
the field relation this identifies the unique canonical numerical result.
No desired result/range or source<modulus premise is supplied; full RV32 source
words may exceed the field modulus. Discarded destinations still retain the
candidate arithmetic/canonical checks. This is custom field arithmetic, and the
upstream Zimop zero-result fallback is not adopted as its reference semantics.

Eleven [focused regressions](Tests/NativeReducedMOP.lean) check field boundaries,
full-RV32 source reduction, canonical modulus/high-bit rejection, discarded
writes, second-port GPR classification and three positive slices of seven actual
native equations with bounded subtraction remainders. Conditional-native,
pure-reference and partial-positive slices are not complete positive NONEMPTY
117-equation/22-lookup accepted rows or original fetched execution. Six new
modules/tests record ten exact parentb727 origins; the unchanged active mop.rs
is independently pinned to the native v2 base. No production/native/Sail/literal/
fixture/dependency input changed, native finding/issue assumption or new axiom.

Original public MOP decoding, custom-spec input/output and retained execution,
initialized/common MOP integration remain OPEN. Existing seven-profile original
execution scopes remain unchanged and exclude MOP/CSR. NEXT certify actual native
SpecialCSRProperties and CSR/delegation query/operand/return/request bindings,
then custom/reference boundaries, caller/worker fulfillment/accounting and unified
protocol spans. Padding/terminal/init/teardown/general Rust/public/physical/crypto/
completeness and parity remain open; this local certificate is not parity.

## Common seven-profile original fetched execution (7 November 2026)

[The new short public root](Airbender/Review/Trace/Families/ReducedMachine/UnifiedFetchedExecution.lean)
now derives finite successful original four-byte fetched execution interleaving
all checked shifts, arithmetic, bitwise, comparison, branch, jump and LW/SW
profiles, actual canonical terminal PC and EVERY architectural terminal cell.
This common memory execution scope uses the explicit exact NativeROM input
constructor. Existing six-profile arbitrary ordinary public-code execution and
separate word-memory roots stay UNCHANGED; arbitrary public images are not
identified with the fixed native eight-word ROM.

[Original constructor-sensitive input interfaces](Airbender/Review/Helpers/Memory/ReducedMachineUnifiedExecution.lean)
activate memory configuration and ordinary tracked RAM-domain requirements ONLY
when the original public program contains memory constructors. Ordinary/empty
programs acquire no CSR availability; branches/JAL require only unrestricted
readable misa, and only JALR activates Machine/security configuration. Every local
CSR/permission comes from meaningful initial reference inputs through REAL mixed
past/control frames. The original MemoryPlatform typeclass remains explicit.
These reference input domains are not native/physical enforcement or findings.

[Fresh local connections](Airbender/Proofs/ReducedMachine/NativeUnifiedExecution.lean)
prove every actual supported GPR-row event survives filtering BEFORE reusing its
checked original execution. [Selected native memory address origins](Airbender/Proofs/Trace/Families/ReducedMachine/UnifiedAddressDomains.lean)
root actual LW-shadow/SW-destination addresses in public architectural/shadow
seeds through full native matching, without assuming all trace rows are memory.
Actual RAM membership/public ordinary domains or bounded ROM exclusion discharge
local special-window access obligations. No per-row profile/domain/CSR/permission
or desired success answer is supplied.

[Common composition](Airbender/Proofs/Trace/Families/ReducedMachine/UnifiedComposition.lean)
derives original source replay, all source/read/range/address/result and actual
transfer/normal retirement inputs at the already checked common projected states.
AUIPC prepared PC, branch/JAL/JALR distinctions, x0/aliases/both readonly refreshes,
OLDREADs, unmasked SW and native RV32 wrap remain. LW-to-x0 reads architectural
memory before its original accessor discards the unmasked value. ROM candidates
come from exact constructed bytes/past frames, independently of ignored shadows;
RAM loads retain actual refreshes. Operation-specific native final bounds, actual
clock/PC chain and unchanged PURE stateful projected composition/terminal lemmas
produce the finite execution and readers. Full native matching retains EVERY
independent shadow token/timestamp. No desired local source/read/write/result/
state/PC/order/replay/preservation/profile/table-equivalence answer is public.

Eleven [configuration/domain/native-filter](Tests/NativeReducedUnifiedExecution.lean)
and [complete EMPTY common fetched](Tests/NativeReducedUnifiedFetched.lean)
regressions pass. They retain ordinary/branch/JAL/empty CSR scopes, reject missing
memory misa/wrong privilege/JALR security/CLINT access/filter loss, and derive
actual terminal PC/x0 readers for every RV32 PC with independent shadow123.
These are input-domain/conditional-native/complete-EMPTY checks, not full positive
NONEMPTY117-equation/22-lookup accepted memory/mixed witnesses. Eight new modules/
tests record17 exact parentf8df origins; production/native/Sail/fixture/dependency
inputs and prior roots are unchanged. No established native defect or new axiom.

NEXT assess actual remaining MOP and CSR/delegation paths against the unchanged
native117-equation artifact, then exact special-CSR table meaning, request/caller/
worker constraints and accounting. Unified protocol spans, padding/terminal/init/
teardown and universal public/physical setup/general refinement/completeness
remain open. This selected common execution does not establish parity.

## Common seven-profile initialized projected history (7 November 2026)

[The new original projection](Airbender/Review/Circuits/ReducedMachine/UnifiedDecoder.lean)
wraps the unchanged six-profile SupportedMode with LW/SW. Existing supported
source-image and execution interfaces retain their scope. [Public decoding](Airbender/Review/Trace/Families/ReducedMachine/UnifiedDecoder.lean)
recovers original bytes, stateful Sail instructions and exact ten-field queries
from complete sparse/padded membership. Native eighteen-bit packing excludes
holes and the minus-one tail. [Profile transport](Airbender/Proofs/ReducedMachine/NativeUnifiedDecoder.lean)
derives each selected original entry; callers supply no per-row profile answer.

[Actual local laws](Airbender/Proofs/ReducedMachine/NativeUnifiedLocal.lean)
select the already checked native write-preservation, x0 and three-port domain
rules. Incoming JAL alignment is derived from public decoding before the range
induction. [The common range root](Airbender/Review/Trace/Families/ReducedMachine/UnifiedValues.lean)
then derives EVERY actual native read/write/terminal range through ONE unchanged
initialized time induction and independent public shadow seeds. LW full-address
ROM shadows remain in native matching and filter only from Sail transfers; RAM
load refreshes and SW OLDREAD/unmasked memory writes remain architectural. All
readonly refreshes, aliases and raw x0 events remain.

[The common projected history and port-domain roots](Airbender/Review/Trace/Families/ReducedMachine/UnifiedHistory.lean)
derive actual chronological projected Sail states, clock order/final matching,
EVERY ROM-byte/misa frame, all row segments and original stateful source replay.
Inputs are original FULL unified public construction, independent shadow image
initialization, exact fixedData native acceptance/FULL decoding, tracked alignment
and public code capacity. No desired read/write/range/result/state/PC/order/replay,
preservation, expected profile/domain or table-equivalence answer is supplied.
These decoder/range/history roots require no CSR availability. Arbitrary logical
public source images are NOT identified with the fixed eight-word native ROM.

Eighteen [decoder](Tests/NativeReducedUnifiedDecoder.lean) and
[history regressions](Tests/NativeReducedUnifiedHistory.lean) check independent
original LW/SW/ADD bytes, all seven masks, negative-immediate/x0 fields, actual
port/range/x0 corruption rejection, code windows and complete actual-native EMPTY
history with architectural x0 plus independent shadow123 and no byte/CSR premise.
They are not full positive NONEMPTY117-equation/22-lookup memory/mixed witnesses.
Fifteen new modules/tests record26 exact parent2cc4535 helper/template origins.
No production/Sail/native/literal/dependency change or established native defect.

**Historical prerequisite checkpoint:** common retained/normal/fetched execution
with LW/SW was open here; it is now checked by the public root above.
Next connect all profile transfers and retirement to THESE common states, with
memory configuration activated only by original public memory constructors and
local CSR/ordinary-address obligations derived through actual past histories.
Preserve branch/JAL/JALR configuration distinctions and the older arbitrary
ordinary public source-image scopes. Exact NativeROM memory execution remains an
explicit separate scope; general Rust/public preprocessing/physical ROM,
workers/protocol/padding/terminal/init/teardown and completeness remain open.

## Original native LW/SW normal and fetched execution (7 November 2026)

[The new short public execution root](Airbender/Review/Trace/Families/ReducedMachine/WordMemoryFetchedExecution.lean)
derives finite ORIGINAL successful four-byte fetched LW/SW stepping, actual
canonical terminal PC and EVERY architectural terminal cell read. This is a
separate word-memory trace; common mixed supported execution still excludes LW/SW.
[The reference conclusion](Airbender/Review/Trace/Families/ReducedMachine/WordMemoryExecution.lean)
filters only architectural terminal observations. Complete accepted native matching
retains EVERY independent shadow seed/read/write/timestamp.

[Fresh normal retirement](Airbender/Proofs/ReducedMachine/NativeWordMemoryRetirement.lean)
transports all checked actual same-pre-state reads/OLDREADs and final writes through
original PC/nextPC updates. Readonly aliases/RAM refreshes, original unmasked LW-to-x0
and actual unmasked SW writes remain. Initial reference configuration follows actual
control frames; retained original clauses run in derived prepared states before
normal_base_next_pc/tick_pc retirement reaches the actual native after-state/PC.
Native PC+4/fullRV32 wrap is checked, never supplied as a desired answer.

[Stateful projected composition](Airbender/Proofs/Trace/ProjectedStatefulComposition.lean)
reuses unchanged PURE filtered grouping and stateful bookkeeping removal, without
a pure-decoder certificate or supplied replay. [Initialized assembly](Airbender/Proofs/Trace/Families/ReducedMachine/WordMemoryComposition.lean)
derives original byte fetch/stateful decoding in every pre-state, local source/
range/address/CSR/permission/ordinary-address obligations, native clock order/PC
chain and terminal observations. Inputs remain exact NativeROM byte construction,
original full public setup, independent-shadow initialization, exact fixedData
acceptance/FULL decoding, aligned tracked cells/code capacity, and the existing
meaningful initial reference configuration/public ordinary-RAM domain. Empty
programs remain CSR-free. No expected row result/state/PC/order/replay or native
table equivalence is public. Physical setup/protocol terminal enforcement is separate.

[Five new regressions](Tests/NativeReducedWordMemoryRetirement.lean) include positive
ORIGINAL normal LW-to-x0 and RAM SW at EVERY RV32 PC with arbitrary readable misa,
real constructed ROM21015 and actual RAM123 writes, plus independent wrap outputs.
[Complete EMPTY native fetched checks](Tests/NativeReducedWordMemoryFetched.lean)
derive terminal PC/x0 readers even at0xffffffff, retaining independent shadow123
without CSR premises. These original-reference/empty tests are NOT full positive
NONEMPTY117-equation/22-lookup accepted native memory witnesses.

NEXT extend the common original projection and initialized memory-aware histories
across all supported profiles, with derived per-profile port domains/preservation/
frames/configuration/retirement. The all-events-GPR frame is inapplicable to mixed
stores. Preserve prior ordinary/empty CSR scopes and AUIPC prepared PC. Other ordinary
profiles, workers/callers/accounting, unified protocol, padding/terminal/init/teardown
and general Rust/public preprocessing/physical ROM/compiler/crypto/completeness/
interrupt/exception/MMIO remain separate. FINDINGS unchanged; no native defect,
issue assumption, production fix, new axiom or parity claim.

## Retained original native LW/SW clauses (7 November 2026)

[The new short public root](Airbender/Review/Trace/Families/ReducedMachine/WordMemoryClauses.lean)
derives successful ORIGINAL execute_LOAD/STORE clauses at the actual projected
row states. [Fresh clause assembly](Airbender/Proofs/ReducedMachine/NativeWordMemoryClauses.lean)
connects the already checked numerical RV32 address/alignment and original
same-pre-state GPR/RAM/ROM transfers to unchanged PURE original virtual-memory,
physical access and retained load/store lemmas. Original constructors, raw operands,
sign extension and unmasked load-to-x0 behavior remain; SW copies rs2 to actual
RAM without dummy-rd masking. All local reads/writes/states/results are derived.

[Meaningful reference inputs](Airbender/Review/Helpers/Memory/ReducedMachineWordMemoryPlatform.lean)
require initial Machine/zero-mstatus, readable unrestricted misa/environment/PMP
addresses/hart, disabled PMP/HTIF and one permissive RV32 PMA region ONLY when the
public memory program is nonempty. A public tracked-RAM domain excludes the pinned
CLINT/signature windows. [Fresh native ROM bounds](Airbender/Proofs/ReducedMachine/NativeWordMemoryPlatform.lean)
and [actual initialized address origins/configuration transport](Airbender/Proofs/Trace/Families/ReducedMachine/WordMemoryPlatform.lean)
derive EVERY local ordinary address and CSR/permission from these inputs and real
past history. No per-row desired address/configuration/permission/success answer is
public. These describe reference inputs, not native/physical configuration or MMIO
enforcement, and are not issue-handling assumptions. Empty/transfer-only scopes
remain CSR-free. The retained original memory-platform typeclass remains explicit.

[Initialized assembly](Airbender/Proofs/Trace/Families/ReducedMachine/WordMemoryClauses.lean)
keeps complete native matching, independent shadows, all actual row states,
original replay and numerical/architectural effects. [Nine regressions](Tests/NativeReducedWordMemoryClauses.lean)
cover absent misa/wrong privilege and special-domain rejection, independent platform
boundaries, positive ORIGINAL ROM LW-to-x0/RAM SW with arbitrary misa, and complete
EMPTY actual-native clauses with independent shadow123/noCSR. These are conditional/
original-reference/empty evidence, NOT full positive NONEMPTY117-equation/22-lookup
accepted native LW/SW witnesses.

The subsequent normal/fetched milestone above now derives PC preparation/retirement
and finite fetched stepping. Common mixed memory histories remain next. Current common six-profile support
still EXCLUDES LW/SW. Original interrupts/exceptions/MMIO and general Rust/public
preprocessing/physical ROM/compiler/crypto/completeness/global protocol/init/teardown
remain separate. No native defect, issue assumption, production fix, new axiom or
parity claim; FINDINGS unchanged.

## Original native LW/SW same-pre-state transfers (7 November 2026)

[Fresh projected-port proofs](Airbender/Proofs/ReducedMachine/NativeWordMemoryProjectedPorts.lean)
bind all retained actual reads and the final write to ONE original pre-state.
Actual readonly GPR/RAM refreshes stutter before the destination write, preserving
source/destination aliases and every retained OLDREAD. ROM-prefix load shadows
are filtered only from Sail transfers; all native tokens/timestamps remain matched.

[Original transfer proofs](Airbender/Proofs/ReducedMachine/NativeWordMemoryTransfers.lean)
derive original rs1/rs2 observations, architectural RAM reads and writes, and ROM
reads from exact constructed fixture bytes transported through real past history.
The ignored shadow value is independent. The ORIGINAL unmasked load write uses
Sail's x0 accessor to discard its result AFTER the architectural memory read.
SW copies original rs2 to actual RAM; decoded dummy rd0 never masks this write.

[The short public root](Airbender/Review/Trace/Families/ReducedMachine/WordMemoryTransfers.lean)
derives [all chronological transfers and numerical effects](Airbender/Review/Helpers/Memory/ReducedMachineWordMemoryTransfers.lean)
from original full public setup on the exact NativeROM input constructor,
independent-shadow initialization, exact fixedData acceptance/full decoding,
aligned tracked cells and public code capacity. [Assembly](Airbender/Proofs/Trace/Families/ReducedMachine/WordMemoryTransfers.lean)
discharges every source/range/address/PC/result/state/read/write/order/replay
obligation internally. No desired local answer or arbitrary/native table identity
is supplied; no initial CSR availability is needed at this transfer boundary.

[Eight regressions](Tests/NativeReducedWordMemoryTransfers.lean) check aliased load
OLDREAD/source and SW sources, rejection of a changing-store stutter, load-to-x0
stutter through the unmasked original accessor, retained architectural load reads,
ROM/shadow independence, and a complete EMPTY actual-native public transfer scope
with shadow123 and no CSR premise. These conditional-native/original-accessor/empty
checks are NOT full positive NONEMPTY117-equation/22-lookup accepted LW/SW witnesses.

The retained clause milestone above now discharges original memory access/configuration
through initial public reference inputs and actual address origins/transfers. Actual
PC preparation/normal/fetched execution and common mixed histories remain next. Common six-profile support still EXCLUDES LW/SW. No local desired
success/configuration/read/state/frame answer may bypass retained clauses. General
Rust/public preprocessing/physical ROM/compiler/crypto/completeness and global
protocol/init/teardown remain separate. FINDINGS unchanged; no native defect,
issue assumption, production fix, new axiom or parity claim.

## Projected native LW/SW memory history and code frames (7 November 2026)

[Fresh actual x0 preservation](Airbender/Proofs/Trace/Families/ReducedMachine/WordMemoryZeroRegister.lean)
binds original public LW rd/x0 to the actual masked write. SW's actual memory
third port cannot be x0; its OLDREAD/unmasked write remains present. Both readonly
refreshes use their actual initialized reads. [Full native matching and shadow
projection](Airbender/Proofs/Trace/Families/ReducedMachine/ShadowHistory.lean) derive
x0 propagation, every retained event's architectural seed origin and all projected
chronological Sail states/final cell matching. The complete native history and
ALL independent shadow seeds/reads/writes/timestamps remain accepted and matched;
only Sail transfers at ROM-shadow addresses are filtered.

[Exact port domains](Airbender/Proofs/ReducedMachine/NativeWordMemoryDomains.lean)
derive source0 retention, LW port1 filtering ONLY below4MiB, retained RAM-load
refreshes and retained SW memory port2 from fresh actual mixed-port/canonical
address bindings. [Initialized address origins](Airbender/Review/Trace/Families/ReducedMachine/WordMemoryAddressDomains.lean)
root effective RAM addresses in actual public architectural cells and effective
ROM-shadow addresses in independent public shadow seeds. No expected per-row
address/domain/value or architectural ROM identity is supplied.

[Memory-aware code frames](Airbender/Proofs/Trace/Families/ReducedMachine/WordMemoryCodeHistory.lean)
derive preservation of EVERY ROM byte from actual architectural Sail transfers,
including missing bytes and code outside tracked word cells. Original indexed
public construction with count at most1,048,576 derives every complete four-byte
instruction window in ROM. The actual byte frame/control-CSR frame then replays
the retained stateful decoder in every constructed pre-state. No per-row code read,
no-code-write, frame or CSR value answer is public. The exact native ROM constructor's
all-word reads now transport through these actual projected histories internally.

[Short public history root](Airbender/Review/Trace/Families/ReducedMachine/WordMemoryHistory.lean)
derives the [history observable](Airbender/Review/Helpers/Memory/ReducedMachineWordMemoryHistory.lean):
complete native matching, row permutation/clock order, every projected Sail segment
state, final cell matching, ROM-byte/misa frames and original decoder replay.
Inputs are original full word-memory setup, independent-shadow public initialization,
exact fixedData acceptance/full decoding, aligned tracked cells and the meaningful
public code capacity. No read/write/state/order/frame/preservation/result answer
is supplied. The all-events-GPR frame is not used for LW/SW.

[Ten regressions](Tests/NativeReducedWordMemoryHistory.lean) check exact source/ROM/
RAM/store port filtering, missing ignored-shadow seed and architectural RAM cell
rejection, initialized nonzero x0-event rejection and public code-window bounds.
A positive ORIGINAL Sail RAM write changes data to123 while preserving a real
ROM code byte; a complete actual-native EMPTY history uses independent shadow123
without CSR or architectural byte reads. These are conditional-native/original
Sail-group/empty checks, NOT full positive NONEMPTY117-equation/22-lookup accepted
native LW/SW or retained instruction execution.

The subsequent transfer milestone above binds these groups to original same-pre-state
GPR/RAM/ROM reads and writes. Retained LOAD/STORE access/platform/privilege/configuration
and normal/fetched execution remain separate before common mixed integration. Common six-profile support still EXCLUDES LW/SW. General Rust/
public preprocessing/physical ROM/crypto/compiler/completeness and global protocol/
initialization/teardown remain separate. No native defect, issue assumption, axiom,
production fix or parity claim; FINDINGS remains unchanged.

## Exact native ROM to original Sail bytes (7 November 2026)

[Native ROM input construction](Airbender/Review/Helpers/Memory/ReducedMachineROMImage.lean)
extracts the actual eight public words from the unchanged native dataImage column,
retains the unchanged UNIMP fallback and explicitly inserts all four MiB of
little-endian bytes into original Sail memory. Registers and every outside byte
are preserved. The constructor overwrites that ROM interval; it does not infer
missing bytes or identify arbitrary logical decoder images with the fixed fixture.
[Symbolic proofs](Airbender/Proofs/ReducedMachine/NativeROMImage.lean) derive EVERY
aligned original ROM word read, including the complete repeated0xc0001073 tail,
and the full original public wordROMImage extraction into a computed descriptor.
An eight-slot exact kernel certificate and symbolic tail bridge connect these
words to the ALREADY certified native ROM reference. The million-word vector and
four-MiB map are not evaluated during the proof; no table-equivalence or desired
per-row read premise is supplied. Unchanged PURE extraction/byte-read/insertion
lemmas are reused after fresh actual fixture binding, without old standalone
native constraints/masks/tables/acceptance transfer.

[Short constructor root](Airbender/Review/Trace/Families/ReducedMachine/ROMImage.lean)
exposes complete extraction/reads and register/outside-byte frames. [Actual native
LW ROM read](Airbender/Review/Circuits/ReducedMachine/WordMemoryROMTheorems.lean)
uses accepted native fixed-pool constraints, explicit LW mask and actual ROM-region
restriction to derive the same original byte read at its native effective address.
Alignment/bounds/lookup output derive from actual constraints. The ignored native
shadow read and its independent public seed value are neither dropped nor equated
with the original ROM bytes. This local result uses the constructed input state,
not yet projected chronological native/Sail row states or retained LOAD execution.

[Nine regressions](Tests/NativeReducedROMImage.lean) check all eight independent
word values, first/last UNIMP padding, complete public extraction, register and
RAM-byte preservation, an explicitly overwritten ROM byte, independent shadow123
versus ROM21015, a still-missing byte above ROM, and corrupt native ROM output
rejection. These constructor/reference/conditional-native checks are NOT complete
positive NONEMPTY117-equation/22-lookup accepted LW/SW or original memory execution.

Actual event domains, projected initialized native/Sail memory states and byte-code
frames are now checked above. NEXT original port/read/write and retained LW/SW
clauses/common integration. The all-events-GPR frame remains inapplicable. Meaningful constructed
reference input is not Rust loader/public preprocessing/physical-ROM refinement,
boot/zero enforcement, a native defect/issue assumption or whole-machine parity.
Production Rust/Sail/native data/dependencies remain unchanged; FINDINGS stays at
zero established native defects.

## Independent native ROM-shadow initialization (7 November 2026)

[Actual reduced shadow inputs](Airbender/Review/Helpers/Memory/ReducedMachineShadowImage.lean)
construct zero-clock native seeds from original Sail reads of architectural GPR/RAM
cells plus independent public32bit shadow-address/value pairs in the4MiBROM prefix.
The public domain is unique and separates architectural cells from shadow addresses.
Every shadow token remains in native matching; its value is independent of Sail ROM
bytes. [Constructor proofs](Airbender/Proofs/Trace/Families/ReducedMachine/ShadowImage.lean)
derive seed uniqueness, initial/native seed clocks, ALLcanonical seed ranges and
exact architectural seed-image projection. No per-row native read, state, clock or
shadow-to-ROM value answer is supplied. These reuse unchanged PURE public input/
cell-address/filter lemmas, with fresh actual NativeReducedFamily context; no old
standalone masks/constraints/tables/acceptance is transferred.

The [short initialization root](Airbender/Review/Trace/Families/ReducedMachine/ShadowInputs.lean)
exposes those constructor consequences. [Independent-shadow range](Airbender/Review/Trace/Families/ReducedMachine/WordMemoryShadowValues.lean)
and [numerical effect roots](Airbender/Review/Trace/Families/ReducedMachine/WordMemoryShadowResults.lean)
reuse newly proved actual reduced write preservation and unchanged time induction/
assembly to derive EVERY actual read/write/terminal bound and LW/SW numerical
address/write/PC result under this boundary. The ordinary initialImage roots remain
unchanged. Architectural memory/GPR state realization and retained Sail execution
are still separate from these numerical native words.

[Eight regressions](Tests/NativeReducedShadowInputs.lean) construct independent shadow
value123 at address16 without ANY Sail byte there, prove the actual read failure,
compare the distinct native ROM reference, derive architectural projection and
seed bounds, check a concrete complete empty native accepted/range boundary, and
reject duplicate/outside-shadow seed domains. These are public input/conditional
numerical/empty checks, NOT full positive NONEMPTY117-equation native memory rows
or original LOAD/STORE execution. Physical native boot/zero initialization is not
asserted by this meaningful logical public input construction.

The exact fixed8wordROM/padding byte constructor is now checked above. NEXT derive
initialized architectural versus shadow event domains, projected native
memory/Sail states and code-byte frames, retained LOAD/STORE clauses and common
mixed integration. General physical/Rust public export and projected
Sail memory/execution remain OPEN. Do not equate independent shadow values with
architectural ROM words or supply desired local reads/states/frames. Common six-profile
execution still excludes LW/SW. No defect, issue assumption, production/Sail/data/
dependency change, new axiom or parity claim. Ten exact parenteecbtemplate/helper
origins record seven new modules/tests.

Final gates pass3220explicit standard-only axiom roots,209public Review roots,
4guide names,3223links/anchors and context/trace separation. Full Review551.87MiB
footprint/3126.52MiB resident/14.72s; independent provenance19.63/35.69MiB/8.53s
passes189v3-origin/1211backport-origin identities,80byte-identical modules,8circuit
artifacts,68native sources,23setup,4exporters,unchanged dependencies/originalcheckout.
Pure seedproofs474.05/2845.92MiB/2.22s;independent range/results480.92/2876.34/2.12;
eight tests482.58/2885.09/2.23;Axioms546.56/3101.59/4.56. All failed/successful
owned workers terminated; no memory/wall-time/heartbeat/recursion ceiling hit/raised.
Arithmetic/M31 imports and explicit fixture state/register/error/lint corrections
verified. A small reference-function evaluation draft did not reduce and was
replaced by original Sail lemmas; no invalid draft or new opacity was accepted.
Same shared lock,Lean-j1-M3072,3072MiB aggregate footprint/4096MiB resident and finite
180second module/120second audit budgets. Sampled watchdog plus Lean allocation cap,
not an OS hard physical-memory limit.

## Earlier initialized native LW/SW numerical values (7 November 2026)

[Fresh mixed-port bindings](Airbender/Proofs/ReducedMachine/NativeWordMemoryPorts.lean)
identify ALL3actual register/memory cells after original public decoding. LW uses
rs1, the full effective-address memory shadow, and original rd; SW uses rs1, readonly
rs2 and the actual effective-address memory destination. Native scalar bounds
justify canonical address encoding. Both readonly refreshes and destination OLDREAD
remain events, retaining aliases/x0. Actual RAM-only SW routing proves disjointness
from EVERY native ROM-prefix WORD CELL; this is not yet a Sail byte-code frame.
[Small memory observables](Airbender/Review/Helpers/Memory/ReducedMachineWordMemory.lean)
record only these derived cells, without supplied memory reads or states.

[Write preservation](Airbender/Proofs/ReducedMachine/NativeWordMemoryPreservation.lean)
derives bounded LW candidates from exact certified ROM outputs or the earlier actual
second-port memory read, then applies original decoded rd/x0 masking. SW copies the
full earlier second-port register read to memory WITHOUT dummy-rd masking. These
proved rules feed ONE unchanged shared initialized time induction. The short
[public range root](Airbender/Review/Trace/Families/ReducedMachine/WordMemoryValues.lean)
derives EVERY actual read/write/terminal bound, including formerly unchecked low
source35 and ignored ROM-shadow read37, from public seed-image construction and
accepted native matching/full original decoding. No source/read/range/preservation
answer is supplied publicly.

[Initialized numerical results](Airbender/Review/Trace/Families/ReducedMachine/WordMemoryResults.lean)
derive canonical effective source+original-immediate address/fullRV32wrap, alignment,
RAM-only stores, all3port cells, exact ROM-versus-RAM load writes and unmasked store
writes, original load rd/x0 effects and bounded PC+4/fullRV32rollover. Original public
query/source membership discharges immediate/incomingPC/alignment; initialized history
discharges ALL source bounds. Native final-PC selection precedes unchanged increment
lemmas. [References/effects](Airbender/Review/Circuits/ReducedMachine/WordMemoryResult.lean)
are numerical actual words, NOT supplied desired answers or original pre-row Sail
GPR/architectural memory observations. Calculations/assembly remain under Proofs.

[Eleven regressions](Tests/NativeReducedWordMemoryValues.lean) reject oversized actual
source/secondread/write/terminal words under the full public range interface, reject
corrupt mixed-port cells, exclude stores from ROM-prefix cells, retain unmasked SW
writes despite dummy rd0, derive load-x0 zero writes, compare independent ROM/RAM/
shadow references and check native PCwrap. These conditional initialized/reference
checks do NOT add complete positive NONEMPTY117-equation/22lookup native LW/SW rows.

This numerical scope uses the explicit ordinary initialImage/ImageBoundary construction.
Independent ROM-shadow seeds/ledger, original fixed-ROM byte construction, memory-aware
Sail state/history/code-byte frames and retained LOAD/STORE execution remain OPEN.
The exact native8wordROM is not equated with arbitrary original public decoder images;
shadow values are not asserted to be architectural ROM words. Common supported
execution still excludes LW/SW. NEXT construct that independent-shadow/public-ROM
initializer and derive actual original memory transport; do not use all-events-GPR
frames or supplied per-row read/state/code-frame answers. No native defect, issue
assumption, production/Sail/native-data/dependency change, new axiom or parity claim.
Eighteen exact parent648template/pure-helper origins record eleven new modules/tests.

Final gates pass3199explicit standard-only axiom roots,206public Review roots,
4guide names,3206links/anchors and context/trace separation. Full Review553.74MiB
footprint/3124.97MiB resident/15.00s; independent provenance19.25/35.36MiB/8.37s
passes189v3-origin/1201backport-origin identities,80byte-identical modules,8circuit
artifacts,68native sources,23setup,4exporters,unchanged dependencies/originalcheckout.
Ports506.31/2893.16MiB/10.77s;preservation497.94/2883.11/2.54;ranges479.77/2871.91/2.04;
numericalresults498.58/2883.97/2.38;traceassembly481.60/2876.08/2.05;elevenregressions
491.58/2884.41/2.37;Axioms547.15/3101.38/13.00. Every failed/successful owned worker
terminated; no memory/wall-time/heartbeat/recursion ceiling hit/raised. Ordinary
canonical/vector/zero-branch/import/wrapped-entry proof corrections verified.
Unchanged shared lock,Lean-j1-M3072,3072MiB aggregate footprint/4096MiB resident,
finite180second module/120second audit budgets. Sampled watchdog plus Lean allocation
cap, not an OS hard physical-memory limit.

## Earlier original native LW/SW public decoding (7 November 2026)

[Original word-memory projection](Airbender/Review/Circuits/ReducedMachine/WordMemoryDecoder.lean)
preserves LOAD(false,4)/STORE(4), raw rs1/rs2/rd/x0, original12bit Sail sign extension,
actual reduced LW1025/SW16386 and rawfunct3=2. Native IType clears only LW's unused
readonly rs2 index; SType clears SW's dummy decoded rd, without discarding its actual
memory write. [Constructor/query proofs](Airbender/Proofs/ReducedMachine/NativeWordMemoryDecoder.lean)
derive those unused indices, immediate bounds/mask/tag and all actual ten-query fields.
Canonical native immediate words derive from original decoded bounds. No native
source range, expected profile/result/state or field answer is supplied.

[One short public root](Airbender/Review/Trace/Families/ReducedMachine/WordMemoryDecoder.lean)
uses original public byte/stateful image construction, accepted native constraints
and FULL sparse/padded decoder membership to recover original sources and actual
mask/source/destination/x0/immediate/tag fields. Accepted18bit native packing excludes
holes and allminus1tail; no supplied exclusion or filtered original constructors.
Generic explicit four-field modeled setup suffices for this decoder-only scope.
No numerical fixed-table meaning or arbitrary/native table identity is assumed.

[Nine regressions](Tests/NativeReducedWordMemoryDecoder.lean) construct independent
original LW/SW/ADD bytes into complete3slots+1padding, derive BOTH word-memory
SourceWith entries, retain negative immediate/x0 fields, reject unsupported subword
constructors, check hole/sentinel membership/native exclusion and reject corrupt
actual tag/zero fields. No old standalone compiled mask/table/accepted row is reused.
The logical public image is NOT the exact native eight-word ROM fixture or a general
Rust decoder-export/preprocessing/physical certificate. These are NOT complete
positive NONEMPTY117-equation/22lookup native memory witnesses.

Initialized native source/memory values and write preservation, code nonoverlap,
original byte/ROM/shadow correspondence, retained Sail clauses and common mixed
execution remain OPEN. Common six-profile execution still excludes LW/SW. NEXT derive
fresh native register-versus-memory port bindings and proved RAM/ROM write rules,
then initialized ranges/history; do not reuse current all-events-GPR code frames.
No native defect, issue assumption, production/Sail/data/dependency change, axiom or
parity claim. Eight exact parent5360template/pure-helper origins record six new modules/tests.

Final gates pass3168explicit standard-only axiom roots,204public Review roots,
4guide declaration names,3189links/anchors and context/trace separation. Full Review
552.95MiB footprint/3122.53MiB resident/20.60s; independent provenance19.42/35.52MiB/
8.17s passes189v3-origin/1183backport-origin identities,80byte-identical modules,
8circuit artifacts,68native sources,23setup,4exporters and unchanged dependencies/
original checkout. Decoder479.55/2860.97MiB/2.18s;trace470.72/2844.20/2.03;
nine regressions497.61/2874.64/2.48;Axioms544.88/3098.20/4.67. All workers terminated;
no memory/time/heartbeat/recursion ceiling hit/raised. Exact raw-tag coercion and
fixture arithmetic spacing corrections are checked; no invalid draft accepted.
Unchanged shared lock,Lean-j1-M3072,3072MiB aggregate footprint/4096MiB resident and
finite180second module/120second audit budgets. Sampled watchdog plus Lean allocation
cap, not an OS hard physical-memory limit.

## Earlier native word-memory addresses and exact fixed tables (7 November 2026)

[Actual access proofs](Airbender/Proofs/ReducedMachine/NativeWordMemoryAccess.lean)
derive LW's shadow address39/40=effective address61/62 on BOTH ROM and RAM paths,
ROM/RAM selectors86/87, candidate116/117, original-field destination7/0 and field
zero-mask8. They derive SW's readonly source address6/0, actual memory address45/46=
61/62 and unmasked memory write43/44=37/38. Store writes never use architectural
rd-zero masking. Both readonly refreshes, load shadow reads and store OLDREAD stay
in native matching. [Short access roots](Airbender/Review/Circuits/ReducedMachine/WordMemoryTheorems.lean)
keep native masks explicit with generic modeled setup. Actual74/75 effective-address
limb equations and default/final PC selection are checked. [Internal RV32 addition](Airbender/Proofs/ReducedMachine/NativeWordMemoryNumerics.lean)
reuses unchanged shared scalar/carry and pure addition lemmas AFTER fresh memory
bindings. Its source/immediate bounds remain internal, awaiting public decoding/history.

[Complete symbolic certificates](Airbender/Proofs/ReducedMachine/NativeWordMemoryTables.lean)
check all65,536actual tag18offset rows, all65,536tag23separator rows and ALL1,048,576
tag24ROM rows including the full repeated tail. [Exact full-pool meanings](Airbender/Review/Circuits/ReducedMachine/Tables/WordMemoryTheorems.lean)
follow tag isolation at native offsets327681/393473/459009: offset bits0/1; high-limb
RAM predicate64≤high and shadow high%64; aligned ROM keys below4MiB with the exact
retained eight-word fixture/padding. No standalone/native table identity is inherited.
No arbitrary-table equality/equivalence, input bound, sampled comparison, native_decide,
foreign-data opacity or regenerated literal is used.

[Native address roots](Airbender/Review/Circuits/ReducedMachine/WordMemoryAddressTheorems.lean)
derive canonical aligned LW addresses and its mandatory modulo-address ROM query,
INCLUDING RAM loads, plus canonical aligned SW addresses at or above4MiB. These
local conclusions have NO source/address/range/result input answers. [Twelve regressions](Tests/NativeReducedWordMemoryAccess.lean)
lift EVERY row of all three regions at its actual full-pool offset, connect all8public
ROM words to the reference, check independent edge values/corruption/oversized or
misaligned ROM rejection and actual four-assertion addition slices at carry/negative/
fullRV32wrap edges. Positive slices are NOT full117-equation/22lookup accepted LW/SW.

Original full public LW/SW decoding, initialized source/memory correspondence,
canonical selected values/rd-x0 bindings, write preservation, mixed range/history,
code preservation/nonoverlap, retained Sail memory clauses and common fetched execution
remain OPEN. In particular the exact native eight-word ROM is NOT an arbitrary original
public program image; general Rust/public decoder-export/preprocessing/physical ROM
fidelity remains separate. Common six-profile execution still excludes LW/SW. No native
defect, issue assumption, production/Sail/native-data/dependency change, new axiom or
whole-machine/parity claim. Seventeen exact parenta117template/helper origins record
twelve affected Lean paths. FINDINGS and prior importer/native-export inputs are unchanged.

Final gates pass3152explicit standard-only axiom roots,203public Review roots,
4guide declaration names,3178links/anchors and context/trace separation. Full Review
552.54MiB footprint/3123.36MiB resident/17.06s. Independent exact provenance
19.44/35.53MiB/8.25s passes189v3-origin/1175backport-origin identities,80byte-identical
modules,8circuit artifacts,68native sources,23setup artifacts,4exporters and unchanged
dependencies/original checkout. Access551.86/2907.77MiB/6.64s,queries517.11/2881.42/3.63,
internal addition481.00/2847.19/2.09,complete table certificates508.83/2850.30/4.03,
full-pool values491.34/2829.38/2.53,native address consequences481.44/2859.72/2.23,
twelve regressions512.67/2887.20/2.84,Axioms544.49/3097.45/4.61. All failed/successful
owned workers terminated; no memory/wall-time/heartbeat/recursion limit hit/raised.
Shared lock,Lean-j1-M3072,3072MiB aggregate footprint/4096MiB resident and finite
180second module/120second audit budgets are unchanged. This remains a sampled
watchdog plus Lean allocation cap, not an OS hard physical-memory limit.

## Earlier native word-only memory routing foundation (7 November 2026)

[Word-memory references](Airbender/Review/Circuits/ReducedMachine/WordMemory.lean)
name explicit LW1025/SW16386 masks. [NativeWordMemorySelectors](Airbender/Proofs/ReducedMachine/NativeWordMemorySelectors.lean)
derives ALL18header/major/minor bits from actual Boolean assertions0..17/packed112:
LW update-rd0/load-major10; SW rs2-use1/store-major14. [Actual fields](Airbender/Proofs/ReducedMachine/NativeWordMemoryFields.lean)
use equations32/33/113/114 to derive selected operand47/48 from immediate9/10 for
LW or second-port37/38 for SW. LW second-port space88=0/third89=1; SW second88=1/
third89=0. These are actual memory-space events, not all GPR accesses or a discarded
x0 write. [One short local root](Airbender/Review/Circuits/ReducedMachine/WordMemoryTheorems.lean)
keeps decoded mask explicit and generic modeled setup; no numerical table premise.

Unchanged native base load.rs/store.rs are newly hash-pinned. Active reduced machine
uses LoadOp<false,false,true>/StoreOp<false>, so only LW/SW; third load flag is
AVOID_MASKING_ROM_ACCESS_ADDRESS. Native IType/SType headers and sorted decoder keys
are inspected, not a general Rust decoder-export certificate. [Six regressions](Tests/NativeReducedWordMemoryRouting.lean)
check exact masks/all18lists, rejection of wrong load/store port spaces and actual
selected vectors. These conditional native consequences are NOT full positive native
117-equation/22lookup memory fixtures, original GPR/Sail execution or address bounds.

Effective address/addition/scalar/carry/alignment/ROM-space/query/value/masked-write/
public decoding/initialized preservation/original memory/code frame remain OPEN.
Do not drop ROM/RAM shadow reads or memory oldreads; do not reuse all-events-GPR code
preservation for stores. Current common six-profile execution still excludes LW/SW.
No native defect, issue assumption, production/Sail/data/dependency change, axiom or
whole-machine/parity claim. Five exact parent287 origins record five new modules/tests;
native source pins now68. Full memory/physical/general fidelity remain separate.
Final gates pass3117explicit standard-only axiom roots,196public Review roots,
4guide names,3161links/anchors/context-trace separation. Full Review548.71MiB
footprint/3119.94MiB resident/14.67s; independent exact provenance17.00/33.05MiB/8.17s
passes189v3-origin/1158backport-origin identities,80byte-identical modules,8circuit
artifacts,68native sources,23setup,4exporters and unchanged dependencies. Selectors
629.05/2978.31MiB/6.88s,fields491.08/2854.34/2.74,root471.83/2817.23/1.97,tests471.09/2825.00/4.53,
Axioms543.82/3095.42/4.65. Concrete Boolean-choice reduction before field arithmetic
and a public namespace were corrected; all failed/successful workers terminated. No
memory/time/heartbeat/recursion ceiling hit/raised. Shared lock,Lean-j1-M3072,3072MiB
aggregate footprint/4096MiB resident,finite180second modules/120second audits unchanged.
Guard sampled watchdog plus Lean allocation cap,not OS hard physical-memory enforcement.

## Mixed original native jumps and supported execution (7 November 2026)

The [common original projection](Airbender/Review/Circuits/ReducedMachine/SupportedDecoder.lean)
now admits JAL/JALR interleaved with selected shifts, five arithmetic forms, bitwise,
comparisons and all six branches. SupportedMode is Sum ShiftMode (Sum ArithmeticMode
(Sum BitwiseMode (Sum ComparisonMode (Sum BranchMode JumpMode)))). Original constructors,
raw/x0/alias operands, sign extension, raw JAL/U-type funct3 and actual native masks
are retained. [Derived profile transport](Airbender/Proofs/ReducedMachine/NativeSupportedDecoder.lean)
recovers one of SIX exact original entries plus PC/byte/instruction/query identities.
Family mapping changes no actual ten-field query. No per-row expected profile is public.

[Common native local rules](Airbender/Proofs/ReducedMachine/NativeSupportedLocal.lean)
now include fresh actual jump write/x0/register-space/selected-PC/retained-clause
bindings. Jump return preservation needs incoming PC alignment; [common public
membership](Airbender/Proofs/Trace/Families/ReducedMachine/SupportedValues.lean)
derives it BEFORE unchanged common initialized range induction, avoiding a source-range
cycle. One range/x0/native-clock Clean-to-Sail/code/misa/replay history covers every
interleaved profile. JAL's x0 reads, immediate readonly rs2/x0, old destination,
JALR source-before-aliased-write and actual masked writes stay present. AUIPC's
prepared architectural PC remains derived. Operation-specific final bounds replace
any universal PC+4 assertion; original RV32 wrap and jump bit0 clearing remain checked.

The SAME short [public_supported_execution](Airbender/Review/Trace/Families/ReducedMachine/SupportedExecution.lean)
now derives finite original successful four-byte fetched execution, actual terminal
PC bounds and ALL terminal cell reads across all SIX profiles. Inputs are original
supportedDecoderSetupImage, ImageBoundary(fixedData trace), Accepted(fixedData trace),
FULL SupportedDecodedTrace, aligned tracked cells and [SupportedISA](Airbender/Review/Helpers/Decoder/ReducedMachineSupported.lean).
Initial misa readability is required only when the original public program contains
BTYPE/JAL/JALR; value unrestricted. Only original JALR requires initial Machine/readable
mseccfg with MLPE clear. Actual past history/control frames derive every local read;
ordinary/empty CSR-free and branch-only security-free scopes remain. No desired local
source/range/read/return/target/result/PC/state/order/replay/CSR value or table-identity
answer is public. Exact fixedData constructs the checked native pool retaining all
rows/boundaries. This configuration is an original-reference boundary, not a native
finding/issue assumption or physical enforcement.

[Six new mixed regressions](Tests/NativeReducedSupportedJumps.lean) check independent
JAL/ADD/JALR original public bytes/all sources/complete3slot+1padding image, negative
jump/x0/raw fields, arbitrary readable misa and missing misa/security rejection.
Updated branch/ordinary/CSR-free empty tests and affected bitwise/comparison tests
pass. These are public source/configuration/conditional native/empty evidence, NOT
complete positive NONEMPTY117-equation mixed native witnesses. Native8word fixed
fixture remains unchanged; logical images are not equated with ROM/export/physical
setup. Next assess remaining actual ordinary profiles, then delegation accounting,
unified protocol, padding/terminal/init. No production/native/Sail/data/dependency
change, native defect, issue assumption, new axiom, whole-machine coverage or parity.
Twenty-two exact parent127 origins record ten affected Lean paths.
Final gates pass3108explicit standard-only axiom roots,195public Review roots,
4guide names,3147links/anchors/context-trace separation. Full Review550.81MiB
footprint/3121.23MiB resident/16.02s; independent exact provenance19.38/35.47MiB/8.06s
passes189v3-origin/1153backport-origin identities,80byte-identical modules,8circuit
artifacts,66native sources,23setup,4exporters and unchanged dependencies. Every affected
common layer and dependent regression is rebuilt; local507.45/2941.06MiB/7.93s,common
ranges491.90/2922.12/2.04,composition490.02/2933.84/2.60,new tests509.15/2953.48/2.62,
Axioms544.34/3095.41/4.22. A missing explicit declarative helper import was corrected;
all remaining proofs/tests pass first check. All owned workers terminated, no memory/
time/heartbeat/recursion ceiling hit/raised. Shared lock,Lean-j1-M3072,3072MiB aggregate
footprint/4096MiB resident,finite180second modules/120second audits unchanged. Guard is
sampled watchdog plus Lean allocation cap,not OS hard physical-memory enforcement.

## Initialized original native jump fetched execution (7 November 2026)

[One short public root](Airbender/Review/Trace/Families/ReducedMachine/JumpFetchedExecution.lean)
now derives finite original successful four-byte JAL/JALR fetched execution from
original jumpDecoderSetupImage, ImageBoundary(fixedData trace), Accepted(fixedData
trace), FULL JumpDecodedTrace, aligned tracked cells and [initial reference CSR
configuration](Airbender/Review/Helpers/Decoder/ReducedMachineJump.lean). Actual
source bounds/incoming PC alignment follow original public membership and initialized
native ranges. All original row states/reads/masked writes/code/misa/decoder replay,
actual native clock order/PC chain and terminal PC/cell reads are derived internally.
JAL's x0 source reads, readonly rs2/x0, old destination/aliases and discarded writes
remain present. JAL x0 jumps while its data stutters; JALR clears target bit0 and
reads its source before an aliased destination write. RV32 wrap is retained.

[JumpComposition](Airbender/Proofs/Trace/Families/ReducedMachine/JumpComposition.lean)
discharges EVERY source/alignment/CSR prerequisite of the checked local retirement
proof. JumpISA requires readable misa, value unrestricted, only for a nonempty public
jump program; original JALR additionally requires initial Machine privilege/readable
mseccfg with MLPE=0. Every local CSR read derives through actual past history/control
frames. Empty programs and GPR-only theorems require no CSR reads; direct-only JAL
programs require no privilege/security read. This is an explicit original-reference
configuration boundary, not a native defect/issue assumption or physical enforcement.
Terminal bounds use actual selected jump output or the public initial PC for empty
traces, not universal PC+4. No local source/range/read/target/return/result/PC/state/
order/replay/CSR value or table-equivalence answer is public. Original interrupts/
exceptions and general physical/compiler/cryptographic/completeness stay separate.

[Seven regressions](Tests/NativeReducedJumpConfiguration.lean) and [empty runs](Tests/NativeReducedJumpFetched.lean)
check original raw/x0/alias fields, arbitrary readable misa, JAL without security
CSRs, missing misa/security rejection, concrete accepted zero-row execution for
EVERY RV32 PC and top terminal reader0xffffffff with NO CSR reads. These are source/
configuration/empty/conditional native consequences, NOT complete positive NONEMPTY
117-equation/22lookup accepted native jumps. Native fixed eight-word/CSR/nondeterminism
fixture is unchanged; modeled public images are not equated with physical setup.
Common supported projection still excludes jumps; separate jump-only execution does
not establish mixed histories. Next integrate actual jump profile/query transport,
preservation/PC/CSR rules into common initialized execution. Eleven exact parent40
origins record six affected modules/tests; no native/Rust/Sail/data/dependency change,
finding, issue assumption, new axiom, whole-machine coverage or parity claim.
Final gates pass3102explicit standard-only axiom roots,195public Review roots,
4guide names,3125links/anchors/context-trace separation. Full Review550.59MiB
footprint/3119.58MiB resident/14.98s; independent exact provenance19.13/56.12MiB/8.08s
passes189v3-origin/1131backport-origin identities,80byte-identical modules,8circuit
artifacts,66native sources,23setup,4exporters and unchanged dependencies. Composition
483.80/2885.91MiB/2.18s,public479.39/2875.33/1.91,empty tests480.83/2887.89/2.18,
configuration tests484.35/2891.48/9.64,Axioms545.20/3095.61/6.36. All owned workers
terminated; ordinary fixture insert syntax/dependent map typing/unused simp corrections
verified. No memory/time/heartbeat/recursion ceiling hit/raised. Shared lock,Lean-j1-M3072,
3072MiB aggregate footprint/4096MiB resident,finite180second modules/120second audits
unchanged. Sampled watchdog plus Lean allocation cap,not OS hard physical-memory limit.

## Local native jumps execute retained Sail clauses (7 November 2026)

[NativeJumpExecution](Airbender/Proofs/ReducedMachine/NativeJumpExecution.lean)
recovers retained original JAL/JALR constructors from the new public projection and
instantiates unchanged pure retire_jump only after new actual native return/target/
rd-x0/GPR bindings. It derives get_arch_pc from actual incoming-PC preparation via
retired_state_history, uses original source reads before aliased writes, and projects
normal_base_next_pc/retained clause/tick_pc retirement to the actual native after-state.
JAL x0 data stutters still jump; JALR uses the checked low-bit-cleared target.

This is an INTERNAL local row theorem. Its actual source bound, incoming alignment,
misa readability and conditional JALR Machine/readable mseccfg with MLPE=0 remain
obligations for initialized trace composition. No such local answer is added to a
public interface. The CSR boundary follows retained original Sail landing-pad/jump
behavior, not a native defect/issue assumption. Next derive every local read/configuration
from public initial configuration and actual past history, construct original replay/
row order/PC chain, then expose initialized fetched execution and common integration.
Neither public initialized jump execution nor mixed jump support is claimed here.
Six exact parentd80 origins record the single assembly module, using only pure old
reference/retirement definitions and fresh actual native bindings. No old split native
mask/column/table/acceptance identity, production/Sail/data/dependency change, finding,
new axiom, full-machine coverage or parity. No complete positive native jump fixture.
Final gates pass3090explicit standard-only axiom roots,194public Review roots,
4guide names,3104links/anchors/context-trace separation. Full Review549.37MiB
footprint/3119.75MiB resident/14.65s; independent exact provenance19.44/35.50MiB/7.87s
passes189v3-origin/1120backport-origin identities,80byte-identical modules,8circuit
artifacts,66native sources,23setup,4exporters and unchanged dependencies. Local
retirement489.78/2895.27MiB/6.60s,Axioms542.95/3092.91/4.59. Explicit zero/nonzero
register cases corrected canonical roundtrip/dependent-decider rewrites; every
failed/successful guard reports no survivors. No memory/time/heartbeat/recursion
ceiling hit/raised. Shared lock,Lean-j1-M3072,3072MiB aggregate footprint/4096MiB
resident,finite180second module/120second audit budgets remain unchanged. Guard is
sampled watchdog plus Lean allocation cap,not OS hard physical-memory enforcement.

## Original native jump GPR/cell history (7 November 2026)

[Fresh jump port bindings](Airbender/Proofs/ReducedMachine/NativeJumpPorts.lean)
use actual source60/61/113/destination100..107/114 equations and original decoded
rs1/rs2/rd/x0 before unchanged shared native_history_read/write. JAL's original
source1/x0 still participates although its actual numerical base is PC; readonly
rs2/x0 remains on both immediate forms. All three source/old-destination reads
observe one original Sail pre-state, retaining JALR aliases and masked writes.
[Initialized zero preservation](Airbender/Proofs/Trace/Families/ReducedMachine/JumpZeroRegister.lean)
derives every actual x0 event from public seeds/native matching; no zero-read/write
answer is supplied. [Register-space/event and code proofs](Airbender/Proofs/Trace/Families/ReducedMachine/JumpCodeHistory.lean)
derive preserved code/misa and original stateful decoder replay.

[One short public root](Airbender/Review/Trace/Families/ReducedMachine/JumpRegisters.lean)
derives native-clock chronological row segments, every original GPR/cell state,
all3reads, actual masked writes, final matching and decoder replay from original
jumpDecoderSetupImage, ImageBoundary trace, Accepted trace, full JumpDecodedTrace
and aligned tracked public cells. No state/order/read/write/result/replay answer or
initial CSR readability premise is supplied. The four-field modeled setup remains
explicit; these port/history proofs need no numerical table semantics. Calculations
stay under Proofs; [public memory helpers](Airbender/Review/Helpers/Memory/ReducedMachineJump.lean)
contain only small transfer/history observables. Raw GPR states retain their control
state; actual incoming PC preparation, retained JAL/JALR clauses/normal/fetched
execution and common jump integration remain next. Numerical jump results are
separately checked at exact fixedData; no arbitrary/native table identity is used.

[Eight regressions](Tests/NativeReducedJumpRegisters.lean) reject wrong rs2/high
address/RAM selector, retain aliased sources/old destination, derive discarded x0
whole-data stutter and reject initialized nonzero x0 events. The exact imported
three-port/x0 positive group is unchanged mechanics evidence, not a full117-equation
jump acceptance or an original decoder fixture. No new complete positive nonempty
native jump, physical setup/export/ROM, native defect, issue assumption, axiom,
whole-machine coverage or parity is claimed. Ten exact parent0aaa origins record
seven modules/tests; native/Rust/Sail/data/dependencies remain unchanged.
Final gates pass3088explicit standard-only axiom roots,194public Review roots,
4guide names,3099links/anchors and context/trace separation. Full Review550.40MiB
footprint/3113.30MiB resident/26.73s; independent exact provenance19.31/35.42MiB/8.18s
passes189v3-origin/1114backport-origin identities,80byte-identical modules,8circuit
artifacts,66native sources,23setup artifacts,4exporters and unchanged dependencies.
All seven modules/tests pass on their first proof check; ports489.61/2876.36MiB/12.31s,
zero preservation495.13/2878.23/2.46,register history480.22/2874.52/2.11,tests488.85/2872.28/2.18,
Axioms542.20/3092.42/4.44. A runner path typo stopped on a missing file and was
corrected; all owned workers terminated. Shared lock,Lean-j1-M3072,3072MiB aggregate
footprint/4096MiB resident and finite180second modules/120second audits unchanged.
No memory/time/heartbeat/recursion ceiling hit/raised; guard is sampled watchdog
plus Lean allocation cap,not OS hard physical-memory enforcement.

## Original decoded and initialized jump numerics (7 November 2026)

[Original JAL/JALR projection](Airbender/Review/Circuits/ReducedMachine/JumpDecoder.lean)
retains x0/raw operands, original21/12bit Sail sign extension and raw JAL
funct3=imm.toNat/4096%8 (JALR0). It uses actual native masks33025/257 and parser
source fields JAL0/0,JALRrs1/0. [Complete source recovery](Airbender/Review/Trace/Families/ReducedMachine/JumpDecoder.lean)
derives every actual ten-field binding from original public bytes/stateful full
sparse/padded membership; native18bit packing excludes holes/tail. Direct offset
parity follows from retained original Sail decoding, without a filter or public
parity answer. Native parser inspection is not general Rust decoder-export fidelity.

[Actual return proofs](Airbender/Proofs/ReducedMachine/NativeJumpReturn.lean)
derive canonical default49/50 PC+4/full RV32 wrap, candidate116/117 and original
rd/x0-masked writes before range induction. Incoming canonical PC/alignment follows
public query/membership, requiring no source range. [Proved preservation](Airbender/Proofs/ReducedMachine/NativeJumpPreservation.lean)
then feeds unchanged shared time induction; [all native read/write/terminal bounds](Airbender/Review/Trace/Families/ReducedMachine/JumpValues.lean)
include actual source-low35, both readonly ports, aliases and discarded writes.
There is no supplied source range or preservation rule and no induction cycle.

[Decoded numerical assembly](Airbender/Proofs/ReducedMachine/NativeJumpDecodedResult.lean)
discharges every raw_result base/immediate bound internally: JAL uses public PC,
JALR uses initialized actual first-read range, and offset uses original sign extension.
Exact native cleanup plus raw bit1 rejection implements full-width low-bit clearing.
Original JAL parity/incoming alignment derive no direct-target change; JALR retains
bit0 clearing. [One short public result](Airbender/Review/Trace/Families/ReducedMachine/JumpResults.lean)
derives canonical return/candidate/original-rd write, raw/selected target and final
PC bounds/alignment with full RV32 wrap. Inputs are original jumpDecoderSetupImage,
ImageBoundary(fixedData trace), Accepted(fixedData trace), FULL JumpDecodedTrace and
row membership. Every source/range/PC/offset/alignment/parity/carry/return/target/
write result is derived; no intermediate state or table-equivalence answer is public.
Exact fixedData constructs NativeFixed.table, retaining all rows/boundaries. Numerical
words are not yet original pre-row Sail GPR observations or executed clauses.

[Ten regressions](Tests/NativeReducedJumpDecoder.lean) check three original public
JAL/JALR/x0 source entries, complete3slot+1padding image, negative offsets/raw JAL7,
JALR aliases, direct parity, corrupt tag/zero rejection, native return wrap,
independent target edges and initialized unchecked source bound. Only original
bytes/stateful decoder evidence is reused from the old fixture, never native
masks/tables/constraints/acceptance. These positives are not complete nonempty
117-equation accepted native jumps. The logical three-word source image is not
the unchanged native eight-word/CSR/nondeterminism fixture or physical ROM/export.

Next bind original jump GPR/cell histories, selected operands/PC observations and
retained clauses/normal/fetched execution before common integration. Current common
five-profile execution still excludes jumps. Native public/physical/compiler/
cryptographic/completeness and original interrupt/exception boundaries stay separate.
Twenty-two exact parent56 origins record fourteen modules/tests; no native/Sail/data/
dependency change, finding, issue assumption, new axiom or parity claim.
Final bounded gates pass3065 explicit standard-only axiom roots,193 public Review
roots,4guide names,3077links/anchors and context/trace separation. Full Review
547.07MiB footprint/3118.36MiB resident/14.71s; independent exact provenance
19.34/35.44MiB/8.09s passes189v3-origin/1104backport-origin identities,80byte-identical
reused modules,8circuit artifacts,66native sources,23setup artifacts,4exporters and
unchanged dependencies. Fourteen affected modules/tests and Axioms pass; numerical
assembly491.84/2877.59MiB/2.39s,ten tests506.07/2910.06/2.65s,Axioms543.24/3093.06/4.43s.
Every owned worker terminated. Shared lock,Lean-j1-M3072,3072MiB aggregate footprint/
4096MiB resident and finite180second modules/120second audits remain unchanged.
No memory/time/heartbeat/recursion ceiling hit or raised; guard is sampled watchdog
plus Lean allocation cap,not an OS hard physical-memory limit.

## Native jump routing and output PC bounds (7 November 2026)

[Actual reduced jump references](Airbender/Review/Circuits/ReducedMachine/Jump.lean)
use masks257 (JALR) and33025 (JAL), update-rd bit0/JUMP major bit8/JAL minor bit15.
[Native Boolean/packed recovery](Airbender/Proofs/ReducedMachine/NativeJumpSelectors.lean)
derives every18bit under the explicit local mask. [Actual field equations](Airbender/Proofs/ReducedMachine/NativeJumpFields.lean)
derive selected immediate9/10, readonly rs2 address/register space, base81/82
selected from incoming PC0/1 or source35/36 through46/47, shared addition74/75 into
raw target61/62 with carry95/wrap63, cleanup query61/64/65/tag17 and actual48 bit1
rejection. Candidate116/117 is default49/50; actual rd address/field-zero-masked
write and final13/14=cleaned65/raw-high62 are derived. All ports remain present.
[One short local root](Airbender/Review/Circuits/ReducedMachine/JumpTheorems.lean)
keeps decoded mask/mode explicit. Original rd=x0 has not yet been bound to the
field zero flag, and default return fields are not yet original Sail observations.

[Numerical proofs](Airbender/Proofs/ReducedMachine/NativeJumpNumerics.lean) reuse
only exact unchanged native scalar/carry checks and the already certified actual
tag17 cleanup region after new jump query bindings. There is no split-table
identity or data regeneration. Raw addition is kernel-checked with internal
base/immediate bounds pending original public decoding/initialized discharge.
The second short root derives raw bit1 rejection and canonical four-byte final
PC bounds/alignment with no source/input/target-bound or expected-result premise.
This is a local native consequence, not original decoded/initialized jump or
whole-machine execution. JALR bit0 clearing, JAL decoded offset parity and full
original architectural target/return behavior remain connections to prove.

[Eight regressions](Tests/NativeReducedJump.lean) check exact masks/all-bit lists,
RAM-source rejection, immediate selection with readonly rs2 retained, discarded
write with return candidate retained, raw bit1/oversized-final rejection and
independent native base/addition slices. Six-assertion positives cover only native
20/23/46/47/74/75; they are not full117equations/22lookups/accepted jumps or Sail
execution. [Unchanged native jump source](../../cs/src/machine/ops/jump.rs) is now
hash-pinned to the exact v2 base; active reduced dispatch calls it. Source parsing
inspection is not a general Rust decoder-export certificate.

Common supported execution still has the five checked shift/arithmetic/bitwise/
comparison/branch profiles; jumps are excluded pending original public fields,
initialized ranges/GPR/operand/PC/retained-clause/fetched connections. Next derive
original JAL/JALR raw fields, x0, sign extension/raw funct3, canonical inputs and
PC+4 return/cleaned target, then extend common history and any meaningful initial
CSR configuration after those prerequisites. Other ordinary/protocol/padding/
terminal/init, native public/physical/compiler/cryptographic/completeness and
original interrupt/exception scopes remain open. No native defect, issue assumption,
fix, new axiom, production/Sail/data/dependency change or parity claim. Ten exact
parenta4a origins record six new modules/tests and66 native sources are pinned.
All six new modules and eight regressions pass. Full Review checks 3,035 explicit
standard-only axiom roots, 190 public Review roots, four guide names, 3,047 links/
anchors and layer separation, using 548.76 MiB footprint/3,116.81 MiB resident in
14.73 s. Independent exact provenance used 16.92/32.94 MiB in 7.79 s, checking189
v3-origin/1,082backport-origin identities,80byte-identical modules,eight circuit
artifacts,66native sources,23setup artifacts,four exporters and unchanged dependencies.
Every failed/successful guard returned no live owned survivors. No memory/wall-time/
heartbeat/recursion ceiling was hit or raised; ordinary unused-simp, vector equality
and imported trace-column projection corrections were verified. Prior importer/
CLI/native-export controls keep exact unchanged inputs/applicability. FINDINGS is
unchanged with zero established native defects.

## Mixed native conditional branch execution (7 November 2026)

[The original common projection](Airbender/Review/Circuits/ReducedMachine/SupportedDecoder.lean)
now admits selected shifts, five arithmetic forms, bitwise register/immediate,
comparisons and all six retained BTYPE branches. Original raw operands/x0/sign
extension/SRAI1055/U-type raw funct3 and every actual ten-field query are preserved.
[Derived five-profile transport](Airbender/Proofs/ReducedMachine/NativeSupportedDecoder.lean)
selects exact original entries and query equality, without a supplied row profile.
[Common local proofs](Airbender/Proofs/ReducedMachine/NativeSupportedLocal.lean)
add actual branch readonly/dummy-zero preservation, x0 and register-space rules
before the shared initialized range/history/code/misa/replay proofs. All three
branch ports remain present, including the dummy old read and zero write.

The common PC interface now derives canonical incoming bounds/alignment and
operation-specific final bounds. It no longer asserts universal PC+4. Existing
ordinary per-profile PC+4/full RV32 wrap proofs remain unchanged. Actual branch
condition/target/PC effects justify its final bound; original decoded parity and
both actual readonly source ranges are discharged internally from the common
public construction/history. [Fetched composition](Airbender/Proofs/Trace/Families/ReducedMachine/SupportedExecution.lean)
then invokes checked per-profile original normal retirement and constructs one
native-clock PC chain/finite run. AUIPC's prepared architectural PC and each
branch's actual incoming PC stay derived, as do all states/reads/results/replay.

[The public execution root](Airbender/Review/Trace/Families/ReducedMachine/SupportedExecution.lean)
now explicitly takes [SupportedISA](Airbender/Review/Helpers/Decoder/ReducedMachineSupported.lean):
if the public program contains a retained BTYPE, initial Sail misa must be readable,
with unrestricted value. This program-level reference configuration derives each
local CSR read through actual history; it supplies no per-row ISA value. Programs
without branches, including the existing CSR-free empty fixture, need no readable
misa. The other inputs remain original public supportedDecoderSetupImage,
ImageBoundary(fixedData trace), Accepted(fixedData trace), full SupportedDecodedTrace
and aligned tracked cells. Exact fixedData selects the unchanged native pool while
preserving all rows/boundaries. Conclusions remain successful original four-byte
fetched execution, actual bounded terminal PC and all terminal cell reads. There
is no source/range/result/condition/target/PC/state/order/replay/table-identity answer
premise. Original interrupt/exception and native physical/setup boundaries remain
separate; initial CSR availability is not a native defect or issue assumption.

[Six new regressions](Tests/NativeReducedSupportedBranches.lean) construct an
independent original branch/arithmetic three-word public image plus one padding
row, derive byte/stateful sources for every slot, check all six negative-offset
x0 projections, unrestricted readable misa, rejected absent misa for a branch
program and vacuous CSR availability for an ordinary program. Existing 25-slot
shift/bitwise/ADD and original comparison source tests pass with the widened
projection; common source/x0/terminal rejections and CSR-free empty execution still
pass. These are public source/configuration/conditional native checks, not a
complete positive nonempty117-equation branch/mixed accepted native witness.
Logical public images are not equated with the unchanged native eight-word/CSR/
nondeterminism fixture, physical ROM/export or general preprocessing fidelity.

Mixed branch integration is now checked. Remaining jumps/load-store/ordinary
profiles, workers/callers/accounting/protocol/padding/terminal/init and general
compiler/cryptographic/completeness boundaries remain open. Fifteen exact parent
c814 origins record nine changed/new Lean modules/tests. No production/native/
Sail/data/dependency change, finding, new axiom, issue assumption or parity claim.
All affected bounded modules and the six new regression roots pass. Full Review
checks 3,010 explicit standard-only axiom roots, 188 public Review roots, four guide
names, 3,023 links/anchors and layer separation, using 547.70 MiB footprint/
3,116.36 MiB resident in 14.59 s. Independent exact provenance used 16.45/33.03 MiB
in 7.76 s, checking 189 v3-origin/1,072 backport-origin identities, 80 byte-identical
modules, eight circuit artifacts, 65 native sources, 23 setup artifacts, four
exporters and unchanged dependencies. Every failed/successful worker terminated;
no memory/wall-time/heartbeat/recursion ceiling was hit or raised. Small explicit
entry typing, finite fixture token spacing and unused-simp corrections were verified.
Prior importer/CLI/native-export controls keep unchanged inputs/applicability.
FINDINGS remains unchanged with zero established native defects.

## Original initialized branch fetched execution (7 November 2026)

[Actual branch ports](Airbender/Proofs/ReducedMachine/NativeBranchPorts.lean)
now bind original rs1/rs2 and the present x0 dummy port before shared Sail read/
write transport. All three reads observe one pre-state, including aliases; the
actual zero dummy write is a whole-data-state stutter. [One public history root](Airbender/Review/Trace/Families/ReducedMachine/BranchRegisters.lean)
derives chronological row states, native matching, all reads/writes, final cells,
code/misa frames and original stateful decoder replay. No state/order/read/write
or replay answer is supplied.

[Retained BTYPE predicates and clauses](Airbender/Proofs/ReducedMachine/NativeBranchClauseReference.lean)
execute all six original branches. [Actual local execution](Airbender/Proofs/ReducedMachine/NativeBranchExecution.lean)
prepares the actual incoming native PC, derives its original architectural read,
and uses previously checked native condition/target/final-PC effects before
normal preparation/clause/tick retirement. [Fetched composition](Airbender/Proofs/Trace/Families/ReducedMachine/BranchComposition.lean)
discharges both actual readonly ranges, incoming alignment and original decoder
offset parity internally. Native-clock matching constructs every row state and
PC chain; source decoding is replayed in those states. [One short public root](Airbender/Review/Trace/Families/ReducedMachine/BranchFetchedExecution.lean)
derives finite original successful four-byte fetched execution, actual terminal
PC bounds and all terminal cell reads. No source/range/condition/target/PC/state/
order/replay answer or arbitrary-table equivalence is a public premise.

The fetched interface additionally requires that the public initial Sail state
has a readable misa register. Its value is unrestricted. Original jump_to reads
that CSR even for aligned targets; code/history and PC-control frames derive
each local read. This is a reference-state configuration boundary, not a native
defect or issue-handling assumption. Original public branch image construction,
ImageBoundary(fixedData trace), Accepted(fixedData trace), complete BranchDecodedTrace
and aligned tracked public cells are the other inputs. Exact fixedData preserves
every row/boundary and selects NativeFixed.table. The native eight-word/CSR1988,
1989/enabled-nondeterminism fixture and all production/native/Sail/dependency
inputs remain unchanged; modeled source images are not physical ROM/export
certificates. Original interrupt/exception paths stay separate.

[Eight port/history regressions](Tests/NativeReducedBranchRegisters.lean) check
wrong source index/high address/RAM selector rejection, aliases, dummy x0 old
read and data stutter, initialized x0 rejection and the exact three-port group.
[Four retained-clause regressions](Tests/NativeReducedBranchExecution.lean) check
independent outcomes for all six predicates, equal/sign-crossing operands,
ordinary/wrapped retirement with arbitrary misa, taken negative wrap and untaken
halfword offsets. [Two empty native fixtures](Tests/NativeReducedBranchFetched.lean)
check public execution at every RV32 PC and the top endpoint. These do not add a
complete positive nonempty117-equation native branch witness. Existing complete
SLL/x0 witnesses are unchanged. Branch-only original fetched execution is now
checked; common mixed branch integration remains next, with operation-specific
PC effects replacing universal PC+4. Other ordinary/protocol/padding/terminal/
init and public/physical/compiler/cryptographic/completeness boundaries remain
open. No native defect, new axiom, issue assumption, production fix or parity claim.

All affected bounded modules and fourteen new regression roots pass. Full Review
checks 3,003 explicit standard-only axiom roots, 188 public Review roots, four
guide names, 2,997 links/anchors and layer separation, using 546.95 MiB footprint/
3,114.52 MiB resident in 14.34 s. Independent exact provenance used 19.02/35.09 MiB
in 7.65 s, checking 189 v3-origin/1,057 backport-origin identities, 80 byte-identical
modules, eight circuit artifacts, 65 native sources, 23 setup artifacts, four
exporters and unchanged dependencies. Every owned worker terminated; no memory,
wall-time, heartbeat or recursion ceiling was hit or raised. Ordinary draft
name/import/state/Word endpoint corrections passed subsequent bounded checks.
Prior importer/CLI/native-export controls retain exact unchanged inputs and
applicability. FINDINGS remains unchanged with zero established native defects.

## Original decoded and initialized branch numerics (7 November 2026)

[Original BTYPE projection](Airbender/Review/Circuits/ReducedMachine/BranchDecoder.lean)
retains all six constructors, raw rs1/rs2 (including x0), unfiltered original
offset and Sail sign extension. Actual native fields use mask70, dummy rd0/x0 and
raw funct3=0/1/4/5/6/7, matching the pinned reduced parser. [Source recovery](Airbender/Proofs/ReducedMachine/NativeBranchDecoder.lean)
derives every actual ten-field query binding from original public byte/stateful
full sparse/padded membership. Accepted native18bit packing excludes holes/tail.
Offset parity follows from the retained original Sail decoder and sign-extension
lemma; no even-offset premise or constructor filter is introduced. [The short
public source root](Airbender/Review/Trace/Families/ReducedMachine/BranchDecoder.lean)
keeps logical membership separate from native Rust export/ROM/physical enforcement.

[Proved native preservation](Airbender/Proofs/ReducedMachine/NativeBranchPreservation.lean)
uses the actual zero-write third port, with both readonly refreshes retained in
matching. [Initialized time induction](Airbender/Review/Trace/Families/ReducedMachine/BranchValues.lean)
derives every actual read/write/terminal Word range, including source-loww35.
No local source bound or supplied write-preservation rule is public.
[Initialized numerical assembly](Airbender/Proofs/Trace/Families/ReducedMachine/BranchResults.lean)
derives both actual readonly ranges, selected operand transport, canonical incoming
PC/offset, public incoming alignment and original decoded offset parity. It then
instantiates the checked native condition/target/PC proofs with every internal
prerequisite discharged. [One short result](Airbender/Review/Trace/Families/ReducedMachine/BranchResults.lean)
derives actual six-way branch condition, canonical PC+offset/full RV32 target,
actual selected final PC bounds/alignment and target/default choice. No source,
range, condition, target, carry, PC, alignment/parity or intermediate-state answer
is supplied. Numerical words remain actual native reads, not yet original Sail
GPR observations or retained branch clause/fetched execution.

Public premises are original branchDecoderSetupImage, ImageBoundary(fixedData trace),
Accepted(fixedData trace), full BranchDecodedTrace and row membership. Exact
fixedData selects NativeFixed.table, retaining all rows/state/memory boundaries;
no arbitrary-table identity is used. The native eight-word/CSR1988,1989/enabled-
nondeterminism fixture is unchanged. The six-word modeled public source image
plus two padding rows is not equated with that native fixed configuration.

[Eight regressions](Tests/NativeReducedBranchDecoder.lean) check all six original
public byte/stateful sources, complete six-slot/eight-row public setup, original
offset parity, negative offset with x0 source aliases, corrupt raw funct3 rejection,
initialized unchecked-low-source bound and final PC bounds/alignment. Only original
bytes/decoder evidence is reused from the old standalone fixture; no old native
mask/table/constraints/acceptance is transferred. These are source/conditional
initialized checks, not full positive nonempty117-equation accepted native branch
witnesses. Branches remain outside mixed common execution. Next bind actual GPR/
cell history, retained Sail BTYPE clauses and normal/fetched execution, then extend
common support with operation-specific PC effects. Other ordinary/protocol/setup/
terminal/init/completeness boundaries remain open. No native defect, issue assumption,
production fix or parity claim; native/Sail/data/dependency inputs are unchanged.

All affected bounded modules and eight regressions pass. Full Review checks 2,965
explicit standard-only axiom roots, 186 public Review roots, four guide names,
2,963 links/anchors and layer separation, using 547.63 MiB footprint/3,113.02 MiB
resident in 20.52 s. Independent provenance used 19.19/35.28 MiB in 7.63 s,
checking 189 v3-origin/1,038 backport-origin identities, 80 byte-identical modules,
eight circuit artifacts, 65 native sources, 23 setup artifacts, four exporters
and unchanged dependencies. All owned workers terminated under unchanged ceilings
and finite budgets. No resource/proof ceiling was hit or raised in this public
milestone. Prior importer/CLI/native-export controls retain unchanged inputs and
applicability; FINDINGS remains unchanged with zero established native defects.

## Native branch conditions and numerical PC effects (7 November 2026)

[New actual branch calculations](Airbender/Proofs/ReducedMachine/NativeBranchCondition.lean)
connect the checked native subtraction remainder to full RV32 source equality,
unsigned borrow and operand signs. The actual packed tag22 resolver then derives
all six BEQ/BNE/BLT/BGE/BLTU/BGEU conditions and zero comparison output. Natural
packing is proved from actual Boolean/sign bounds. The native resolver flips
borrow on differing signs; its validity follows from bounded actual operands,
without transferring the old split resolver on inconsistent tuples. Source
bounds remain internal prerequisites for later initialized history discharge.
The unchanged [pure condition reference](Airbender/Review/Circuits/ReducedMachine/Branch.lean)
retains all six original tags and full-width equality/signed/unsigned ordering.

[Every actual tag17 cleanup row](Airbender/Proofs/ReducedMachine/NativeBranchCleanup.lean)
is proved symbolically from native dataT17: key, bit1 and four-byte-cleared word.
[One short full-pool claim](Airbender/Review/Circuits/ReducedMachine/Tables/NativeBranchTheorems.lean)
derives canonical key/both outputs from actual complete-pool membership. All65,536
rows are covered; no table-equivalence premise, regenerated data or sample-only
inference is used. This new region certificate reuses exact pure column proofs;
the complete128-row resolver certificate is unchanged.

[Actual native PC calculations](Airbender/Proofs/ReducedMachine/NativeBranchPC.lean)
use scalar lookups2/3 to derive both target bounds, Boolean22/24 to derive high
wrap71/low carry96, and actual76/77 to derive PC+offset with full RV32 rollover.
Actual40/41 plus the recovered cleanup query reject a taken target with bit1 set.
Together with original incoming alignment and even offset, internal effects
assembly derives canonical final PC, the actual conditional target/default choice
and four-byte successor alignment. Untaken offset misalignment is not excluded.
The selected condition/target/output bounds are derived, not supplied. Both source
bounds, PC/offset bounds, incoming alignment and offset parity remain internal;
public decoding and initialized history must discharge them before an initialized
branch execution theorem. No new public numerical theorem exposes those answers.

[Eight regressions](Tests/NativeReducedBranchResults.lean) lift every actual cleanup
row at native pool offset262145, check independent signed/unsigned/equality edges,
reject wrong zero/comparison outputs, taken misalignment and oversized cleanup keys,
and check actual target Boolean22/24+76/77 slices at ordinary, low-carry, negative
offset and full-wrap values. These four-assertion positive slices are not complete
117-equation accepted native branches, original public decoding or Sail execution.
Branches remain outside common supported initialized execution. Original public
branch fields/GPR/retained clauses and preparation/retirement/fetched execution are
next. Native data/public fixture, Rust/circuit, original Sail and dependencies are
unchanged. No native defect, issue assumption, production fix or parity claim.

All affected bounded modules and eight regressions pass. Full Review checks 2,942
explicit standard-only axiom roots, 183 public Review roots, four guide names,
2,936 links/anchors and layer separation, using 546.54 MiB footprint/3,112.73 MiB
resident in 14.66 s. Independent pinned provenance used 16.66/32.70 MiB in 7.39 s,
checking 189 v3-origin/1,022 backport-origin identities, 80 byte-identical modules,
eight circuit artifacts, 65 native sources, 23 setup artifacts, four exporters
and unchanged dependencies. Every owned worker terminated under unchanged limits.
A direct fixed-pool equation extraction reached the default recursion limit;
generic equation extraction replaced it without raising any limit or making
foreign data opaque. No memory/wall-time cap was reached. Prior importer/CLI/
native-export controls retain unchanged inputs and applicability; FINDINGS unchanged.

## Native branch selector/routing foundation (7 November 2026)

[Actual branch model](Airbender/Review/Circuits/ReducedMachine/Branch.lean) retains
mask70: rs2-use, branch and CONDITIONAL_COMMON_KEY bits. [Selector proofs](Airbender/Proofs/ReducedMachine/NativeBranchSelectors.lean)
derive every one of eighteen bits from native Boolean assertions and packed112.
[Actual fields](Airbender/Proofs/ReducedMachine/NativeBranchFields.lean) derive
selected readonly rs2 operands, actual source address/register-space, shared
subtraction equations, cleanup17/resolver22 query fields, and final-PC selection
between actual conditional target69/70 and default49/50. The third native port
remains present at register x0 with zero write; its old read still participates
in matching. No original register/condition/target answer is inferred from these
local fields. [One short routing root](Airbender/Review/Circuits/ReducedMachine/BranchTheorems.lean)
keeps the decoded native mask explicit and the modeled setup generic.

[Shared zero-test proof](Airbender/Proofs/ReducedMachine/NativeConditionalEquality.lean)
uses actual assertions78..81 and scalar range checks to derive
w68=1 exactly when both actual subtraction remainder limbs61/62 are zero, after
the actual conditional major flag is derived. It needs no source-word bound,
supplied zero flag, expected source equality or table identity. This is remainder
zero semantics; its connection to original branch operand equality is still open.
The already certified complete128-row native resolver is unchanged and not replayed.

[Seven regressions](Tests/NativeReducedBranchRouting.lean) check the exact mask/bit
list, update-rd and RAM-source rejection, actual zero dummy write, corrupt equality
flag rejection and positive zero/nonzero five-assertion native zero-test slices.
The slice checks Boolean21 and assertions78..81 only, not full117-equation native
acceptance, original public decoding, branch condition/target or execution.
Original branch conditions, target arithmetic/alignment, public fields/GPR/Sail
clauses and initialized execution remain next. The common public fetched theorem
still supports shifts/arithmetic/bitwise/comparisons only; branches are excluded.
Native conditional.rs was already pinned unchanged. No production/Sail/imported/
exported/literal/public fixed configuration/dependency change, native defect,
issue-handling assumption, full-machine coverage or parity claim.

All affected bounded modules and seven regressions pass. Final gates check 2,917
explicit standard-only axiom roots, 182 public Review roots, four guide names,
2,913 local links/anchors and layer separation. Full Review used 545.98 MiB
footprint/3,110.70 MiB resident in 14.80 s. Independent provenance used 19.08/
35.17 MiB in 7.52 s, checking 189 v3-origin/1,012 backport-origin identities,
80 byte-identical modules, eight circuit artifacts, 65 native sources, 23 setup
artifacts, four exporters and unchanged dependencies. Every worker terminated
under unchanged 3,072 MiB footprint/4,096 MiB resident limits, Lean -j1 -M3072
and finite budgets. No resource/proof ceiling was hit or raised. Prior importer/
CLI/export controls retain unchanged inputs; FINDINGS remains unchanged.

## Native comparisons in initialized original execution (7 November 2026)

[Actual port proofs](Airbender/Proofs/ReducedMachine/NativeComparisonPorts.lean)
bind original rs1/rs2/rd to all three native ports before shared GPR history is
used. Both sources and old destination observe one pre-state, including aliases;
readonly rs2/x0 still participates for immediate forms. The small
[transfer observable](Airbender/Review/Helpers/Memory/ReducedMachineComparison.lean)
contains only these original observations and the actual masked write.
[Original primitive correspondence](Airbender/Proofs/ReducedMachine/NativeComparisonClauseReference.lean)
proves signed/unsigned Sail comparisons equal their RV32 references, then sequences
the retained SLT/SLTU/SLTI/SLTIU clauses. [Native clause assembly](Airbender/Proofs/ReducedMachine/NativeComparisonClause.lean)
uses actual selected operands and canonical numerical writes, with both readonly
source bounds kept internal. [Native PC arithmetic](Airbender/Proofs/ReducedMachine/NativeComparisonPC.lean)
uses the already proved actual no-jump/default selection and original query
bounds/alignment to derive bounded PC+4 and complete RV32 rollover.
[Normal execution](Airbender/Proofs/ReducedMachine/NativeComparisonExecution.lean)
transports the constructed states through original PC preparation and retirement.

[Common original support](Airbender/Review/Circuits/ReducedMachine/SupportedDecoder.lean)
now includes comparisons alongside shifts, arithmetic and bitwise. [Profile/query transport](Airbender/Proofs/ReducedMachine/NativeSupportedDecoder.lean)
derives the original instruction and exact ten-field query, without supplied
per-row profile answers. [Actual local rules](Airbender/Proofs/ReducedMachine/NativeSupportedLocal.lean)
justify common range/x0/native-clock Sail history and code/misa/decoder frames.
[The same short public fetched-execution root](Airbender/Review/Trace/Families/ReducedMachine/SupportedExecution.lean)
now derives original successful four-byte stepping, terminal PC bounds and every
terminal cell read across interleaved supported rows. Public inputs remain the
original public image/decoder construction, ImageBoundary(fixedData trace),
Accepted(fixedData trace), full SupportedDecodedTrace and aligned tracked cells.
Both actual read bounds, states, order, results, PC effects and decoder replay
are conclusions or internally discharged prerequisites. AUIPC's prepared incoming
architectural PC remains derived. Exact native fixedData acceptance is retained;
no arbitrary-table equivalence or desired row/state/result premise is added.

[Six original execution regressions](Tests/NativeReducedComparisonExecution.lean)
check all eight ordinary/x0 forms, independent signed/unsigned/negative-immediate
outputs, normal retirement at ordinary and wrapped PCs, discarded data stutters
with PC advance, wrong tag rejection and actual decoded x0 masking.
[Common decoder tests](Tests/NativeReducedSupportedDecoder.lean) additionally
recover an original public SLTIU slot under the expanded projection. These are
original Sail/source and conditional native regressions, not a new complete
positive nonempty117-equation comparison/mixed witness. Existing full SLL/x0
native fixtures are unchanged. The modeled public image is not equated with the
native eight-word/CSR/nondeterminism fixture or physical ROM/setup.

Other ordinary profiles, worker/caller accounting, protocol spans, padding/terminal
machine enforcement and initialization/teardown remain open. General compiler/
Rust/JSON/native public export/preprocessing/ROM/physical fidelity, cryptography,
completeness and original interrupt/exception paths retain separate boundaries.
No native defect, issue-handling assumption, production fix or parity claim.

All affected bounded modules and regressions pass. Final gates check 2,898 explicit
standard-only axiom roots, 181 public Review roots, four guide names, 2,891 local
links/anchors and layer separation. Full Review used 545.13 MiB footprint and
3,111.25 MiB resident in 14.48 s; independent pinned provenance used 18.83/34.92 MiB
in 7.41 s. Provenance checks 189 v3-origin and 1,006 backport-origin identities,
80 byte-identical reused modules, eight circuit artifacts, 65 native sources,
23 setup artifacts and four exporter files. All workers terminated under unchanged
3,072 MiB footprint/4,096 MiB resident caps, Lean -j1 -M3072 and finite budgets.
No memory/time/heartbeat/recursion ceiling was reached or raised. Prior importer/
CLI/native-export controls retain unchanged inputs and applicability; no unchanged
heavy certificate or native data was regenerated. FINDINGS remains unchanged.

## Native comparisons: original decoding and initialized numerical results (7 November 2026)

[The actual comparison model](Airbender/Review/Circuits/ReducedMachine/Comparison.lean)
retains native masks65/67 and the tag22 packed-key resolver. [New selectors](Airbender/Proofs/ReducedMachine/NativeComparisonSelectors.lean)
derive all18native bits. [Actual field equations](Airbender/Proofs/ReducedMachine/NativeComparisonFields.lean)
derive register/immediate selection, readonly rs2/register-space, subtraction/
borrow equations, candidate(low=w67,high=0), actual masked rd/address and conditional
PC routing. These connections use the actual117equation artifact, not old split masks.

[Every one of128actual tag22rows](Airbender/Proofs/ReducedMachine/NativeConditionalTable.lean)
is kernel-checked, including inconsistent flag combinations. [Full-pool semantics](Airbender/Review/Circuits/ReducedMachine/Tables/NativeConditionalTheorems.lean)
selects that actual region from the complete5771521rowpool. Native signed resolution
flips unsigned borrow when operand signs differ. The historical split resolver
selects the first sign on differing-sign inputs; those functions differ on
inconsistent flag tuples. No whole-table identity is inherited. [New native arithmetic](Airbender/Proofs/ReducedMachine/NativeComparisonResult.lean)
proves canonical packed keys, no-jump/Boolean output/candidate bounds and exact
signed/unsigned comparison. The latter uses internal bounded operands and unchanged
pure Word.borrow_iff/signed_lt_iff only after actual native subtraction/sign queries.
Both internal source ranges are discharged by initialized history below. This
interface difference is not a native defect or issue-handling assumption.

[Original SLT/SLTU/SLTI/SLTIU projection](Airbender/Review/Circuits/ReducedMachine/ComparisonDecoder.lean)
preserves original x0 constructors/raw operands, 12-bit sign extension and raw
funct3=2/3. [Public source recovery](Airbender/Review/Trace/Families/ReducedMachine/ComparisonDecoder.lean)
derives every actual ten-field query binding from original byte/stateful full
sparse/padded membership; native18bit packing excludes holes/tail. [Write preservation](Airbender/Proofs/ReducedMachine/NativeComparisonPreservation.lean)
uses derived resolver bounds and decoded rd/x0, retaining both readonly refreshes.
[Initialized ranges](Airbender/Review/Trace/Families/ReducedMachine/ComparisonValues.lean)
feed these proved rules into unchanged shared time induction and derive every
read/write/terminal Word bound, including source-loww35. [Canonical initialized results](Airbender/Review/Trace/Families/ReducedMachine/ComparisonResults.lean)
derive complete RV32 candidates and actual original-rd/x0 masked writes. No source,
read, operand, result, local range, preservation-rule or intermediate-state answer
is supplied publicly. Exact fixedData acceptance keeps native lookup semantics;
no arbitrary-table equality/equivalence premise is added.

[Nine regressions](Tests/NativeReducedComparison.lean) cover all8ordinary/x0
projections, every actual resolver row at offset393345, independent signed/unsigned
and negative-immediate boundaries, inconsistent-flag table behavior, wrong-jump/
oversized-key/corrupted-funct3 rejection, original public SLTIU byte/stateful slot
and initialized oversized-source rejection. These table/source/conditional native
checks are not full positive nonempty117equation comparison execution fixtures.
Native conditional.rs is newly hash-pinned to the unchanged v2 base; branch table
source was already pinned. No production/native/imported/exported/literal/Sail/
public fixed configuration/dependency input changed.

The numerical-only checkpoint below is superseded by the execution checkpoint
above. Its next steps were to bind all actual comparison ports to original GPR/cell history, selected
operands and retained original Sail clauses, derive numerical PC preparation/
retirement/fetched execution and extend the common supported profile. Current
public_supported_execution still admits shifts, arithmetic and bitwise only;
comparison numerical traces here are separate. Other combined operations,
workers/callers/accounting, protocol spans, padding/terminal/init/teardown, native
public/export/preprocessing/ROM/physical setup, compiler/Rust/JSON, cryptography/
completeness and original interrupt/exception boundaries remain open. No native
finding, issue assumption, production fix, new axiom or parity claim.

Final gates pass 2,877 explicit standard-only axiom roots, 181 public Review
roots, four guide declaration names, 2,848 links/anchors and context/trace layers.
Full Review used 545.60 MiB footprint / 3110.11 MiB resident in 24.66 seconds.
Independent exact provenance passes 189 v3-origin and 992 backport-origin
identities, 80 byte-identical reused modules, eight circuit artifacts, 65 native
sources, 23 setup artifacts and four exporter files, with unchanged dependency
pins. It used 19.05 MiB footprint / 35.14 MiB resident in 7.32 seconds. Every owned
worker terminated under unchanged caps with no survivors. No memory, wall-time,
heartbeat or recursion ceiling was raised or hit. Prior importer/CLI/native
compilation/export controls retain unchanged inputs and prior applicability.

## Original native bitwise and mixed fetched execution (7 November 2026)

[Original bitwise projection](Airbender/Review/Circuits/ReducedMachine/BitwiseDecoder.lean)
preserves XOR/OR/AND and their immediate constructors, raw operands, x0 and original
12-bit sign extension. [Actual field recovery](Airbender/Proofs/ReducedMachine/NativeBitwiseDecoder.lean)
derives native masks 33/35, raw funct3 tags 4/6/7, rs1/rs2/rd/x0 and immediate limbs
from the actual ten-field query. [One short public root](Airbender/Review/Trace/Families/ReducedMachine/BitwiseDecoder.lean)
uses original public byte/stateful decoder construction and complete sparse/padded
membership. Native eighteen-bit packing excludes holes/tail without an exclusion input.

[Native port bindings](Airbender/Proofs/ReducedMachine/NativeBitwisePorts.lean)
prove all three original register addresses before applying unchanged shared
memory-history read/write lemmas. Both sources and old destination observe one
pre-state, including aliases. [Selected operands](Airbender/Proofs/ReducedMachine/NativeBitwiseOperand.lean)
keep actual readonly rs2/x0 separate from selected sign-extended immediates.
[Decoded numerical results](Airbender/Proofs/ReducedMachine/NativeBitwiseDecodedResult.lean)
reuse the checked byte arithmetic and derive canonical full RV32 candidate and
original rd/x0-masked writes, with no numerical range premise.
[Original clauses](Airbender/Proofs/ReducedMachine/NativeBitwiseClause.lean),
[actual PC+4/RV32 wrap](Airbender/Proofs/ReducedMachine/NativeBitwisePC.lean) and
[local normal execution](Airbender/Proofs/ReducedMachine/NativeBitwiseExecution.lean)
compose after those new native bindings; no old split mask/constraint/table is transferred.

[The common original projection](Airbender/Review/Circuits/ReducedMachine/SupportedDecoder.lean)
now admits shifts, five arithmetic profiles and all six bitwise forms. Derived
profile/query transport supplies proved native write/x0/register-space/PC/execution
rules. The existing [common initialized range induction](Airbender/Review/Trace/Families/ReducedMachine/SupportedValues.lean)
and native-clock memory/GPR/code/misa history now cover interleaved bitwise rows.
[Finite fetched execution](Airbender/Review/Trace/Families/ReducedMachine/SupportedExecution.lean)
derives original normal preparation/clause/retirement, terminal PC bounds and all
terminal cell reads from original public construction, ImageBoundary, accepted
fixedData, full SupportedDecodedTrace and aligned tracked cells. Reads, ranges,
selectors, operands, results, PCs, intermediate states, order and decoder replay
remain conclusions. AUIPC's prepared architectural PC is still derived internally.
Exact NativeFixed.table acceptance remains mandatory; no table-equivalence premise
or desired local bound/read/result/state/PC answer is added.

[Six new bitwise regression roots](Tests/NativeReducedBitwiseExecution.lean)
check all twelve ordinary/x0 forms, independent cross-limb/sign-bit/negative-immediate
results, original retirement at ordinary/wrapped PCs, all discarded data stutters,
wrong-tag rejection and actual decoded x0-masked writes. [The common public-image tests](Tests/NativeReducedSupportedDecoder.lean)
now prove original SourceWith evidence for every one of the 25 slots, including
all twelve bitwise slots, with seven padding rows. Existing common initialized
source/x0/terminal rejection and empty-execution checks pass after the extension.
These positive original Sail/image checks do not certify a new complete positive
nonempty 117-equation bitwise/arithmetic/mixed native witness; only the earlier
SLL/x0 full native witnesses close that separate concrete scope.

The native eight-word/CSR/nondeterminism fixture and all native/imported/exported/
literal/Sail/dependency inputs are unchanged. The modeled original 25-word public
image is not equated with the native fixed fixture. Other combined profiles,
workers/callers/accounting, protocol spans, padding/terminal/init/teardown, original
interrupt/exception paths and general compiler/Rust/JSON/public decoder-export/
preprocessing/ROM/physical/cryptographic/completeness boundaries remain separate.
No native defect, issue assumption, production fix or parity claim is added.

Final gates pass 2,830 explicit standard-only axiom roots, 176 public Review
roots, four guide names, 2,811 links/anchors and context/trace separation. Full
Review used 544.23 MiB footprint / 3107.56 MiB resident in 14.06 seconds.
Independent exact provenance passes 189 v3-origin and 967 backport-origin
identities, 80 byte-identical reused modules, eight circuit artifacts, 64 native
sources, 23 setup artifacts and four exporter files, with unchanged dependencies.
It used 20.08 MiB footprint / 36.14 MiB resident in 7.26 seconds. Every owned worker
terminated with no survivors at unchanged caps; no memory, wall-time, heartbeat
or recursion ceiling was hit or raised. Prior 592 importer controls, eight CLI
inputs and 47 native generation/export controls retain exact unchanged inputs
and applicability; no native/literal regeneration or heavy certificate replay.

## Native reduced bitwise byte/word results (6 November 2026)

This earlier local numerical snapshot is retained; its original execution gaps are
closed by the 7 November checkpoint above.

[Actual reduced bitwise observables](Airbender/Review/Circuits/ReducedMachine/Bitwise.lean)
retain native masks 33/35 and four byte triples. [Selector proofs](Airbender/Proofs/ReducedMachine/NativeBitwiseSelectors.lean)
derive every eighteen header/major/minor bit from the actual Boolean assertions
and packed112 equation in two small profiles. [Native field proofs](Airbender/Proofs/ReducedMachine/NativeBitwiseFields.lean)
derive register/immediate selection, readonly rs2/register-space addressing,
all four actual query triples/tags, inverse-256 source decomposition, candidate
byte assembly, actual masked destination/address and default-PC selection.
Original public bitwise decoding has not yet supplied those explicit local masks/tags.

[Literal identities](Airbender/Proofs/ReducedMachine/NativeBitwiseData.lean) kernel-check
exact equality of independently emitted native dataT4/dataT6/dataT7 with the
unchanged certified XOR/OR/AND byte data. [Full-pool transport](Airbender/Proofs/ReducedMachine/NativeBitwiseTable.lean)
isolates the actual tags from all 5,771,521 native rows, then transports getters
through these proved identities. [One short table root](Airbender/Review/Circuits/ReducedMachine/Tables/NativeBitwiseTheorems.lean)
derives both byte-key bounds, output bound and exact bitwise value. No region,
table-equivalence or desired-result premise is supplied. All 65,536 rows of each
actual byte region inherit checked arithmetic only after this native connection.

[Canonical word assembly](Airbender/Proofs/ReducedMachine/NativeBitwiseResult.lean)
derives the actual source, selected operand and candidate word bounds directly
from accepted byte queries, including the low source limb w35. It reconstructs
all six natural limbs using native inverse-256/candidate equations and unchanged
pure byte/word packing. [Two short row roots](Airbender/Review/Circuits/ReducedMachine/BitwiseTheorems.lean)
derive complete RV32 XOR/OR/AND candidate bits and actual field-masked rd port.
No source/read/byte/output bound or result answer is supplied. Explicit native
mask/register form and raw funct3 tag remain until original public decoding is
composed. Candidate/source words are actual fields, not yet original pre-row Sail
GPR observations. The port formula alone does not bind rdZeroFlag to original rd=x0.

[Ten regressions](Tests/NativeReducedBitwise.lean) lift every actual native byte
row at offsets 1/65,537/131,073, check independent zero/crossing/max expected byte
values, reject corrupted outputs/wrong operation/oversized byte keys, retain
immediate readonly rs2/x0 participation and discarded candidate obligations,
derive local low-source bounds, and retain cross-limb/sign-bit RV32 values above
M31. Positive byte-pool members and conditional native consequences are not
complete positive 117-equation bitwise instruction or initialized execution fixtures.
Native binops.rs is newly hash-pinned to the unchanged v2 base; no production,
importer/exporter/literal/configuration/Sail/dependency input changed.

Next derive original public XOR/OR/AND register/immediate decoding, rd/x0/operand
binding and actual Sail local execution, then extend the common supported
initialized execution. SupportedMode currently still admits only shifts and
ADD/ADDI/SUB/LUI/AUIPC. Other combined operations, worker/accounting/protocol,
padding/terminal/init and general public/compiler/preprocessing/ROM/physical/
cryptographic/completeness boundaries remain open. No native defect, issue-handling
assumption, fix or parity claim is added.

All affected bounded modules and final gates pass: 2,801 explicit standard-only
axiom roots, 175 public Review roots, four guide names, 2,770 links/anchors and
context/trace separation. Full Review used 542.74 MiB footprint / 3104.61 MiB
resident in 14.10 seconds. Independent provenance passes 189 v3-origin and
945 backport-origin identities, 80 reused modules, eight circuit artifacts,
64 native sources, 23 setup artifacts and four exporter files. It used
19.59 / 36.16 MiB in 7.00 seconds. Every owned worker terminated under unchanged
3072/4096 MiB ceilings, Lean -j1 -M3072 and default proof limits.

## Mixed native shift/arithmetic fetched execution (6 November 2026)

[One original public projection](Airbender/Review/Circuits/ReducedMachine/SupportedDecoder.lean)
now admits the previously checked SLL/SRL/SRA register/immediate forms together
with ADD/ADDI/SUB/LUI/AUIPC. It preserves original instructions/operands, x0,
sign extension, encoded SRAI 1055 and raw U-type funct3. Other combined operations
remain unsupported. [Profile/query transport](Airbender/Proofs/ReducedMachine/NativeSupportedDecoder.lean)
derives a checked local interface from that original projection; mapping only
its family tag preserves every actual ten-field query value. Full original
public byte/stateful sparse/padded membership and native packing exclude holes/tail.
[The public decoding claim](Airbender/Review/Trace/Families/ReducedMachine/SupportedDecoder.lean)
returns original sources and actual queries without supplied per-row classifications.

[Common initialized ranges](Airbender/Review/Trace/Families/ReducedMachine/SupportedValues.lean)
now derive every read/write/terminal word bound across interleaved supported rows.
[Native local rules](Airbender/Proofs/ReducedMachine/NativeSupportedLocal.lean) derive
write preservation, x0 preservation, register space, numerical PC and normal row
execution by exact original profile/query transport into the separately checked
actual native proofs. [One range induction](Airbender/Proofs/Trace/Families/ReducedMachine/SupportedValues.lean)
and [one x0/history induction](Airbender/Proofs/Trace/Families/ReducedMachine/SupportedZeroRegister.lean)
retain all readonly refreshes/discarded accesses. [Code history](Airbender/Proofs/Trace/Families/ReducedMachine/SupportedCodeHistory.lean)
derives original code/misa preservation and stateful decoder replay across both profiles.

[One short fetched-execution root](Airbender/Review/Trace/Families/ReducedMachine/SupportedExecution.lean)
now composes mixed supported rows into finite original successful four-byte Sail
execution, deriving terminal PC bounds and all terminal cell reads. [Assembly](Airbender/Proofs/Trace/Families/ReducedMachine/SupportedExecution.lean)
constructs chronological native row states/PC chain, discharges both actual read
bounds/alignment and invokes checked native local execution. AUIPC retains its
derived prepared incoming PC observation. No per-row profile, source/range/read,
write-preservation, operand/result, PC/carry/state/order/replay answer is supplied.
Every mixed numerical claim uses Accepted(fixedData trace), selecting exactly
NativeFixed.table without an arbitrary-table equality/equivalence premise.

[Seven decoder/image regressions](Tests/NativeReducedSupportedDecoder.lean) construct
all 25 original public slots and seven padding rows with the new projection,
retaining SLL at PC0 and ADD at PC96 in one original Sail image. They check both
sources, native masks/x0/sign/SRAI/U-type fields, unsupported holes, actual query/
padding membership and corrupt raw funct3 rejection. [Five execution/range roots](Tests/NativeReducedSupportedExecution.lean)
check concrete empty execution/every RV32 terminal endpoint, initialized oversized
source/terminal rejection and nonzero native x0-event rejection. Public-image and
empty/local positives do not certify a complete positive nonempty 117-equation
arithmetic or mixed trace; those remain separate fixture coverage.

Other combined operations, workers/callers/accounting, protocol spans,
padding/terminal and initialization/teardown remain open. Original interrupt/
exception paths, general compiler/Rust/JSON, native public decoder-export,
preprocessing/ROM/physical setup, cryptography and completeness stay separate.
The native eight-word/CSR/nondeterminism fixture is unchanged and is not equated
with the original 25-word modeled decoder image. No native defect, issue-handling
assumption, production fix or parity claim is added. Native/importer/exporter/
literal/configuration inputs, original Sail clauses and dependencies are unchanged.

All affected bounded modules and final gates pass: 2,772 explicit standard-only
axiom roots, 172 public Review roots, four guide names, 2,744 links/anchors and
context/trace separation. Full Review used 543.54 MiB footprint / 3104.62 MiB
resident in 14.19 seconds. Independent exact provenance passes 189 v3-origin and
930 backport-origin identities, 80 reused modules, eight circuit artifacts,
63 native sources, 23 setup artifacts and four exporter files. It used
18.89 / 34.95 MiB in 6.95 seconds. Every owned worker terminated under unchanged
3072/4096 MiB ceilings, Lean -j1 -M3072 and default proof limits.

## Original native arithmetic fetched execution (6 November 2026)

[Two short public roots](Airbender/Review/Trace/Families/ReducedMachine/ArithmeticExecution.lean)
now derive original arithmetic instruction histories and [finite fetched execution](Airbender/Review/Trace/Families/ReducedMachine/ArithmeticFetchedExecution.lean)
from original public byte/stateful arithmetic image construction, actual public
seed/PC inputs, accepted native matching, complete arithmetic sparse/padded
membership and aligned tracked public cells. Every source/read/write/range,
selected operand, result, PC/carry, row order, intermediate state and decoder
replay is derived. Actual terminal PC bounds and all terminal cell reads follow.
Successful ordinary four-byte execution excludes original interrupt/exception paths.

[Native selected operands](Airbender/Proofs/ReducedMachine/NativeArithmeticOperand.lean)
retain the readonly rs2/x0 access even on immediate forms. [Clause assembly](Airbender/Proofs/ReducedMachine/NativeArithmeticClause.lean)
uses actual arithmetic numerical results and original GPR transfers. [Native PC proofs](Airbender/Proofs/ReducedMachine/NativeArithmeticPC.lean)
connect new arithmetic final-PC selection to the already checked native increment,
deriving canonical bounds/alignment and complete RV32 rollover. [Local execution](Airbender/Proofs/ReducedMachine/NativeArithmeticExecution.lean)
places the actual incoming native PC into the constructed state and derives
AUIPC's original get_arch_pc observation through nextPC preparation. It then
executes retained clauses and original retirement. [Trace assembly](Airbender/Proofs/Trace/Families/ReducedMachine/ArithmeticComposition.lean)
discharges both internal source ranges, alignment and all state/control inputs,
replays the original stateful decoder and composes chronological native rows.
No per-row range/read/result/PC/state or table identity is supplied publicly.

[Six retirement/initialized regression roots](Tests/NativeReducedArithmeticExecution.lean)
cover all ten ordinary/x0 forms at ordinary and wrapped PCs, independent ADD
carry/SUB borrow/negative ADDI/LUI-above-M31 values, and AUIPC at nonzero incoming
PC and wrap. They also derive actual initialized segment execution and reject
oversized terminal PCs. [Two concrete empty-trace roots](Tests/NativeReducedArithmeticFetched.lean)
check the full modeled public execution interface for every RV32 PC and the
terminal reader at 0xffffffff. Positive local Sail and empty native tests do not
certify a complete positive nonempty 117-equation arithmetic row.

The generic native four-field setup remains explicit; arithmetic needs only
scalar checks and polynomials. No arbitrary table is equated with NativeFixed.table.
Future mixed shift/arithmetic execution must retain exact fixedData acceptance
for shift numerical semantics. The native eight-word/CSR/nondeterminism fixture,
compiler/Rust/JSON/native public decoder-export/preprocessing/ROM/physical setup,
cryptography and completeness boundaries are unchanged. Mixed-profile execution,
other combined operations, workers/accounting/protocol, padding/terminal and
initialization/teardown remain open. No native defect, issue-handling assumption,
production fix or parity claim is added. Native/importer/exporter/literal inputs,
original Sail clauses and dependencies are unchanged.

All affected bounded modules and final gates pass: 2,737 explicit standard-only
axiom roots, 169 public Review roots, four guide names, 2,702 links/anchors and
context/trace separation. Full Review used 542.58 MiB footprint / 3104.45 MiB
resident in 13.95 seconds. Independent provenance passes 189 v3-origin and
908 backport-origin identities, 80 unchanged reused modules, eight circuit
artifacts, 63 native sources, 23 setup artifacts and four exporter files. It used
30.70 / 47.31 MiB in 6.76 seconds. Every owned worker terminated under unchanged
3072/4096 MiB ceilings and default Lean proof limits.

## Original native arithmetic Sail register history (6 November 2026)

[One short public claim](Airbender/Review/Trace/Families/ReducedMachine/ArithmeticRegisters.lean)
now constructs actual chronological original Sail GPR/cell histories for the
five arithmetic profiles. Original public byte/stateful decoding, public seed/PC
construction, accepted native matching and aligned tracked cells derive row
order, all segment states, all three reads in one pre-state, actual masked
writes, terminal cell matching, preserved code/misa and original decoder replay.
No per-row read/value/result/state/order/replay answer is supplied.

[Actual port bindings](Airbender/Proofs/ReducedMachine/NativeArithmeticPorts.lean)
reuse only exact unchanged native readonly metadata. New arithmetic equations
and original decoded rs1/rs2/rd fields identify every actual source and destination
register cell, including immediate/x0 aliases. The readonly rs2 input participates
even when the selected arithmetic operand is immediate. [Zero preservation](Airbender/Proofs/Trace/Families/ReducedMachine/ArithmeticZeroRegister.lean)
derives the actual x0 mask and uses unchanged shared initialized induction.
[Code history](Airbender/Proofs/Trace/Families/ReducedMachine/ArithmeticCodeHistory.lean)
derives register address space per event before proving code/misa frames and
original stateful replay. [Segment assembly](Airbender/Proofs/Trace/Families/ReducedMachine/ArithmeticRegisterHistory.lean)
then reuses unchanged shared native-clock/Sail realization. [Review observables](Airbender/Review/Helpers/Memory/ReducedMachineArithmetic.lean)
contain only the small GPR-transfer/history contract.

[Eight regression roots](Tests/NativeReducedArithmeticRegisters.lean) cover all
five masks' mixed-port rejection, source/old-destination aliases, discarded x0
whole-data-state stutters and initialized nonzero-x0-event rejection. The positive
exact imported-port x0 group fixture is reused unchanged; it does not certify a
complete accepted 117-equation arithmetic instruction. Generic native setup is
explicit and no arbitrary/native table identity is assumed. Original selected
operand/clause execution and numerical PC preparation/retirement remain separate:
AUIPC observes the incoming architectural PC, which must be placed into the
constructed row state before its clause is executed. Mixed shift/arithmetic
execution and broader worker/protocol/padding/terminal/init boundaries remain
open. No native defect, issue-handling assumption, production fix or parity claim
is added; native/importer/exporter/literal/dependency inputs are unchanged.
All affected bounded modules and final gates pass: 2,717 standard-only axiom
roots, 167 public Review roots, four guide names, 2,671 links/anchors and
context/trace separation. Full Review used 541.24 MiB footprint / 3101.00 MiB
resident in 14.09 seconds. Independent provenance passes 189 v3-origin and
892 backport-origin identities, 80 reused modules, eight circuit artifacts,
63 native sources, 23 setup artifacts and four exporter files. It used
19.41 / 34.77 MiB in 6.70 seconds. All owned workers terminated under unchanged
3072/4096 MiB ceilings and default proof limits.

## Initialized native reduced arithmetic values (6 November 2026)

[Original arithmetic decoding](Airbender/Review/Trace/Families/ReducedMachine/ArithmeticDecoder.lean)
now derives actual ADD/ADDI/SUB/LUI/AUIPC mask/source/rd/x0/immediate/funct3
fields from public original Sail bytes, stateful decoding and full sparse/padded
membership at the actual native ten-field query. [The reference projection](Airbender/Review/Circuits/ReducedMachine/ArithmeticDecoder.lean)
retains original x0 constructors, sign-extended ADDI and raw U-type funct3 bits.
[Proofs](Airbender/Proofs/ReducedMachine/NativeArithmeticDecoder.lean) reuse the
already checked native eighteen-bit mask bound to exclude holes/tail; no
exclusion, expected selector or immediate-range answer is supplied.

[Initialized range soundness](Airbender/Review/Trace/Families/ReducedMachine/ArithmeticValues.lean)
now derives every actual read/write/terminal word bound from original public
seeds and native matching. [Actual arithmetic write preservation](Airbender/Proofs/ReducedMachine/NativeArithmeticPreservation.lean)
uses native scalar checks and original decoded immediate/rd/x0 fields; it
discharges the prior LUI immediate-bound gap without a source-bound premise.
[Shared induction assembly](Airbender/Proofs/Trace/Families/ReducedMachine/ArithmeticValues.lean)
retains readonly refreshes and discarded writes.

[Complete numerical arithmetic results](Airbender/Review/Trace/Families/ReducedMachine/ArithmeticResults.lean)
now derive canonical RV32 candidate words and actual original-rd/x0 masked
writes. [Internal decoded composition](Airbender/Proofs/ReducedMachine/NativeArithmeticDecodedResult.lean)
proves selected operand/immediate/PC bounds; [trace assembly](Airbender/Proofs/Trace/Families/ReducedMachine/ArithmeticResults.lean)
discharges both actual source-read bounds from initialized history. No source,
operand, PC, immediate range, expected result or intermediate state is a public
input. The explicit generic native setup remains modeled: arithmetic scalar and
polynomial proofs need no dynamic-table numerical meaning, and no arbitrary
setup is equated with the native fixed pool. This does not certify universal
native decoder-export/preprocessing/ROM/physical setup.

[Nine decoder/source regressions](Tests/NativeReducedArithmeticDecoder.lean)
include six existing original public byte entries, all five x0 constructors,
negative ADDI, nonzero U-type funct3, holes/padding and corruption rejection.
[Three initialized consequences](Tests/NativeReducedArithmeticValues.lean)
reject oversized source/terminal words and derive discarded zero writes. These
are original source and conditional native checks, not complete positive
117-equation arithmetic execution fixtures. Arithmetic native words are not yet
original pre-row Sail GPRs or original retained clause/fetched execution. Mixed
shift/arithmetic execution, remaining profiles, workers/accounting/protocol,
padding/terminal and initialization/teardown remain open. No native circuit,
importer/exporter/data/dependency input changed; no defect or issue-handling
assumption is added. All affected bounded modules and final gates pass: 2,694
standard-only axiom roots, 166 public Review roots, four guide declaration names,
2,651 links/anchors and context/trace separation. Full Review used 541.93 MiB
footprint / 3100.08 MiB resident in 14.07 seconds. Independent exact provenance
passes 189 v3-origin and 882 backport-origin identities; 80 reused modules,
eight circuit artifacts, 63 native sources, 23 setup artifacts and four exporter
files remain unchanged. It used 16.44 / 32.48 MiB in 6.69 seconds. All guards
report no owned survivors, with unchanged memory and proof limits. Earlier
snapshots below retain their checked scope.

## Native reduced arithmetic equations (6 November 2026)

[Two short local claims](Airbender/Review/Circuits/ReducedMachine/ArithmeticTheorems.lean)
now cover actual ADD/ADDI/SUB/LUI/AUIPC routing, four zero tags, readonly rs2
address/register space, native candidate assembly, actual masked destination
write/address and default-PC selection. [Five explicit native masks](Airbender/Review/Circuits/ReducedMachine/Arithmetic.lean)
remain inputs here; original arithmetic public decoding is not yet connected.
[All eighteen flags](Airbender/Proofs/ReducedMachine/NativeArithmeticSelectors.lean)
follow from accepted Boolean/packed equations. [Native fields](Airbender/Proofs/ReducedMachine/NativeArithmeticFields.lean)
connect actual equations32/33,54/55,60/61,74/75,85/89/93/97,98..107,110/111,113/114.
No standalone arithmetic mask,table or compiled equation is transferred.

[Internal numerical proofs](Airbender/Proofs/ReducedMachine/NativeArithmeticResult.lean)
derive scalar result bounds from actual lookups0/1 and carry/borrow bounds from
Boolean20/23,then instantiate unchanged pure RV32 limb lemmas. They retain
full wrap/borrow and immediate LUI words. Arithmetic input/PC/immediate bounds
remain internal prerequisites awaiting original public decoder and initialized
range/history discharge; no new public numerical/execution claim supplies them
as answers. LUI output preservation specifically still needs decoded immediate
bounds. [Nine regressions](Tests/NativeReducedArithmetic.lean) pass for explicit
masks,immediate readonly participation,RAM-source rejection,source-independent
ADD output bounds,x0 discard,ADD/AUIPC wrap,SUB borrow and high LUI words. These
are conditional native consequences,not complete accepted arithmetic fixtures.

The five profile proofs replace one combined selector proof that reached the
DEFAULT heartbeat limit; no limit increased. The targeted bounded modules and full gates pass:
2,666 standard-only axiom roots, 163 public Review roots, four guide declaration
names, 2,619 guide links/anchors and context/trace separation. Full Review used
540.16 MiB footprint / 3096.58 MiB resident in 14.05 seconds. Independent exact
provenance passes 189 v3-origin and 863 backport-origin identities, 80 unchanged
reused modules, eight circuit artifacts, 63 native sources, 23 setup artifacts
and four exporter files. It used 18.72 / 34.81 MiB in 6.69 seconds. All owned
workers terminated under unchanged 3072/4096 MiB caps and Lean -j1 -M3072.
No native/importer/exporter/literal/configuration/dependency input changed.
Three unchanged Rust source files are additionally hash-pinned,not modified.
No native defect,fix,issue-handling assumption or parity is established. Other
combined arithmetic decoding/initialized original execution,remaining operation
profiles,workers/accounting/protocol,padding/terminal and init/teardown remain.

## Current v3 adaptation (2026-11-06)

[The adaptation snapshot](V3_ADAPTATION.md) pins PR #585 at
b29277dd895499574e317a994fd89243a72f06cb and distinguishes its unified CPU from
the reduced unrolled assembly. Five shared modules are copied unchanged from
that revision, including four arithmetic proof modules with transparent capacity
names. Original Clean and pinned Sail instruction semantics remain unchanged;
no v3 field encoding, native compiler certificate, finding, fix or machine
soundness result is inherited.

The structural reduced checks cover every tagged query field/table and actual
argument coordinates. The complete source bytes are retained. The complete serial bounded pass covers 777 source/test modules, including
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
checkout and dependency versions are unchanged. The immediate next connection is actual native reduced
fixed/setup regions and public ROM/CSR configuration, then combined native row
semantics, initialized execution, worker/caller accounting and terminal/padding
boundaries. Existing five-family standalone execution remains separate.
A new hourly continuation task is active at the user's request; the previous
task remains paused. Production circuit code stays unchanged; confirmed issues
require documented evidence and explicit narrow interface assumptions.

## Reduced sign/high-byte fixed region (6 November 2026)

[The native reduced region](Airbender/Review/Circuits/ReducedMachine/Tables/SignHigh.lean)
now has a kernel certificate for all 65,536 literal rows: bounded key, exact
sign and high byte, and the actual ID-16 tag. The FV-only exporter calls the
unchanged registered native generator and retains compiled offset 196609.
The certificate reads the imported affine/periodic blocks symbolically at the
default Lean recursion and heartbeat settings. It assumes no table recipe or
expected outputs. Membership here is in the exported region; recovering it from
the full pooled setup, public ROM/CSR configuration and tag isolation remain open.

All seven new modules and the expanded axiom module passed targeted bounded
compilation. Eleven semantic regressions cover geometry, byte/sign boundaries
and wrong key/sign/high-byte/tag rejection. Seventeen runtime importer controls
pass, including a check that geometry validation alone does not assert contents.
All 39 native-export reproducibility/input checks pass, including the new region.
The complete axiom audit passes 2,320 roots using only Lean's standard three,
and all 138 public Review theorems have explicit audit roots. The successful
regional proof used at most 1496.76 MiB footprint and 3574.66 MiB resident;
resource ceilings were unchanged and no live owned process remained.
The earlier complete intake pass above is retained as its own checkpoint;
unchanged ordinary-family builds were not repeated for this isolated addition.
No production circuit code changed, no native defect was established and no
new interface assumption was introduced.

## Regenerated native reduced target and complete pool (6 November 2026)

Fresh compilation of the unchanged pinned native Rust differs from the shipped
historical JSON. It produces 112 quadratic/five linear equations, 142 logical
variables, witness width 107 and 5,771,521 generic rows, including native
truncation ID 47 at offset 5,705,985. The historical JSON has 114 quadratic/five
linear equations, 141 variables, width 106 and 5,705,985 generic rows. Source,
configuration and both artifacts are retained explicitly; the old file is not
rewritten and their accepted relations are not assumed equivalent.

[The full native table](Airbender/Review/Circuits/ReducedMachine/Tables/Native.lean)
reads all fourteen actual exported regions, with all four fields and no added
row. Its public fixture retains eight image words, delegation CSRs 1988/1989
and the native enabled nondeterminism setting. Independent native CLI cases
also check changed and empty public images/allow-lists and actual UNIMP padding.
Literal blocks are split into small declarations at default recursion and
heartbeat limits. No production circuit or machine code changed.

[Tag isolation](Airbender/Proofs/ReducedMachine/NativePool.lean) proves each
region's actual fourth column and recovers the certified sign/high-byte region
from complete pool membership. The short [native row claim](Airbender/Review/Circuits/ReducedMachine/Theorems.lean)
then derives bounded keys, signs and high bytes for both constant queries from
original Clean acceptance of the regenerated constraints. The six full query
fields, common table, setup extent and changed initialization/request coordinates
have independent [mechanical checks](Airbender/Proofs/ReducedMachine/NativeArtifactChecks.lean).
No table-equivalence, desired-output or per-row numerical premise is supplied.

Validation passes for targeted native modules, the expanded axiom module and
historical import/emission regressions. All 592 importer controls pass
(492 existing, 44 historical reduced, 17 sign/high-byte and 39 current native),
as do all eight CLI inputs and 47 native compilation/export/input controls.
The complete audit passes 2,353 axiom roots using only Lean's standard three,
all 140 public Review theorem roots, guide links and layer separation. Provenance
checks 80 byte-identical reused modules, seven historical plus one regenerated
circuit artifact, 60 native sources, 23 setup artifacts and four exporter files;
189 v3 source identities and 700 earlier backport identities remain exact.
The original checkout and dependency versions are unchanged. Successful bounded
checks stayed at or below 1497.71 MiB footprint and 3576.36 MiB resident; limits
were unchanged and no live owned process remained. Unchanged ordinary execution
modules retain their prior complete checkpoint, rather than a repeated broad build.

The fixture does not establish arbitrary public ROM/CSR construction, semantics
of all other tagged operations, physical setup, compiler refinement, decoder
membership, initialized histories, delegation accounting or execution soundness.
Those remain the next native-machine obligations. The historical checkpoint
continues to have exactly its previous conditional meaning.

## Native dynamic selector domains (6 November 2026)

The [native row theorem](Airbender/Review/Circuits/ReducedMachine/Theorems.lean)
now derives the domain of every one of the four dynamic lookup selectors from
original Clean acceptance. The fourth field remains the actual evaluated witness
expression. Complete pooled membership proves its canonical value belongs to the
fourteen actual native IDs; no per-row selector premise or extra disabled row is
introduced. An absent-ID-32 query is rejected by the checked complete pool.

Seven affected modules, including the expanded axiom module, pass direct serial
bounded compilation with explicit correct output paths. The complete audit now
passes 2,358 roots and all 141 public Review theorems, with standard axioms only.
The selector proof checks used at most 530.52 MiB footprint and 3048.59 MiB
resident, with unchanged limits and no owned survivors. Native generated inputs,
public configuration and operation semantics are unchanged, so the preceding
592 importer/eight CLI/47 native export controls remain the relevant checkpoint.
Operation-specific selector identities, flags, operand routing and results still
need proofs against the actual native constraints.

## Native reduced shift routing and truncation (6 November 2026)

The [short native claim](Airbender/Review/Circuits/ReducedMachine/Theorems.lean)
now covers all six SLL/SLLI/SRL/SRLI/SRA/SRAI packed-mask cases on the regenerated
combined machine. All eighteen mask-bit bounds and the exact natural packed sum
come from original native equations. A supplied decoded packed mask determines
the twelve operation flags and rs2 routing; individual selector values are never
premises. The actual equations derive tags 47/37/37/20, the source-two
register/immediate route, its low-limb bound, exact modulo-32 shift amount and
unused third-field zero. These are local row facts, not instruction soundness.

[Tag isolation](Airbender/Proofs/ReducedMachine/NativePool.lean) now recovers any
selected literal region. The [native truncation certificate](Airbender/Proofs/ReducedMachine/NativeTruncation.lean)
checks definitional equality of actual stored columns with the previously
certified truncation columns; offsets remain distinct. It reuses the unchanged
symbolic row lemma with no table-equivalence premise. Calculations live under
Proofs; the [Review row model](Airbender/Review/Circuits/ReducedMachine/Row.lean)
contains only mask references and actual observables.

[Six regressions](Tests/NativeReducedShift.lean) reject oversized keys, wrong
remainders and nonzero unused fields, recover immediate-last/register-zero limb
boundaries and exclude standalone sign-fill tag 52 from this machine's tag-20
slot. The affected modules, all 2,378 axiom roots and all 143 public Review
theorem roots pass with unchanged watchdog limits. The largest affected proof
used 837.17 MiB footprint and 3055.92 MiB resident; the complete Review gate
used 536.33/3077.67 MiB. Every guard finished without owned survivors. No production source, generated native input or
public fixture changed; the preceding 592 importer/eight CLI/47 native controls
remain applicable rather than being regenerated without changed inputs.

The decoded mask is still an explicit input. Original public decoding must derive
it before initialized execution can use this claim. Shift table-37/sign-fill
semantics, results, actual masked writes, PC effects, other operations and the
remaining machine/protocol boundaries remain open. No new native defect or
issue-handling assumption is introduced.

## Native reduced arithmetic-shift filler (6 November 2026)

The [native row claim](Airbender/Review/Circuits/ReducedMachine/Theorems.lean)
now derives the actual sign-fill word and both output-limb bounds for all six
shift-mask cases. The three minor bits come from accepted Boolean/packed-mask
constraints, not supplied control answers. The actual fourth dynamic query is
recovered from equations 94/95/96 and its derived tag 20. Native constant queries
supply the high-limb sign; truncation supplies the bounded amount. Canonical
field arithmetic recovers the complete seven-bit key without an extra bound
premise. The public decoded-mask input remains explicit.

The [literal certificate](Airbender/Proofs/ReducedMachine/NativeSignFill.lean)
checks all 128 actual tag-20 rows and their output bounds in the kernel. The
[reference](Airbender/Review/Circuits/ReducedMachine/Tables/Shift.lean) retains
original native sign/control/amount packing and the explicit zero-shift case.
[Reference calculations](Airbender/Proofs/ReducedMachine/SignFillReference.lean)
and [row assembly](Airbender/Proofs/ReducedMachine/NativeShiftFill.lean) stay under
Proofs. Eleven [regressions](Tests/NativeReducedSignFill.lean) cover shifts
0/16/17/31, positive/logical controls, wrong filler rejection and actual selected
row boundary consequences. The affected modules and complete axiom/Review gates
pass: 2,398 explicit axiom roots, 145 public Review roots and all guide/layer
checks. The largest successful affected proof used 838.72 MiB footprint and
3073.80 MiB resident; the complete Review gate used 539.61/3085.50 MiB. All
completed without owned survivors under unchanged resource caps.
Native setup/compiler/importer inputs did
not change, so the preceding 592 importer/eight CLI/47 native controls remain
applicable.

The attempted table-37 cross-artifact column comparison exceeded the existing
resident or Lean allocation limits; every owned process terminated. Even a
small slice through the whole imported column required a different evaluation
strategy. Its unverified draft is excluded from the source tree and coverage.
Table-37 meaning, contribution assembly, full results, masked writes/PC, public
decoding and initialized execution remain open. This resource boundary is not
a native circuit defect, table-equivalence premise or new interface assumption.

## Native reduced contribution writes and PC selection (6 November 2026)

The [short native claims](Airbender/Review/Circuits/ReducedMachine/Theorems.lean)
now recover both actual tag-37 queries, including the native direction/amount/limb
keys and the actual output fields. [Query assembly](Airbender/Proofs/ReducedMachine/NativeShiftQueries.lean)
uses original Clean acceptance and derived direction/tags; it does not supply
membership, table equivalence or arithmetic output answers as premises.

[Actual port observables](Airbender/Review/Circuits/ReducedMachine/ShiftWrite.lean)
retain the imported source-one read, mixed destination address, destination write,
rd/zero-flag coordinates and outgoing PC. [Metadata checks](Airbender/Proofs/ReducedMachine/NativePorts.lean)
bind their real columns. [Header recovery](Airbender/Proofs/ReducedMachine/NativeShiftHeader.lean)
derives the update/no-source bits. [Native equation assembly](Airbender/Proofs/ReducedMachine/NativeShiftWrite.lean)
then derives left/right cross-limb selection, inactive load zeros, the candidate,
actual zero-flag masking and destination register-space address. The actual final
PC selects the native default-PC candidate. These statements need no expected
write, source-range or successor-PC premise.

[Eight conditional regressions](Tests/NativeReducedWrite.lean) cover discarded
writes with both queries retained, rejection of nonzero discarded writes,
left/right cross-limb assembly, arithmetic zero-shift filler and either outgoing
PC limb mismatch. They are consequences of original native acceptance, not
complete accepted execution fixtures. The affected bounded modules and complete
axiom/Review gates pass: 2,420 explicit axiom roots and 148 public Review roots,
with exact provenance and guide/layer checks. All owned workers terminated under
the unchanged allocation, footprint, resident and wall-time limits. No circuit,
compiler/importer input or literal pool changed; the preceding 592 importer,
eight CLI and 47 native controls remain applicable.

Table-37 arithmetic meaning remains unverified. This milestone proves assembly
of its actual output fields, not their numeric shift result. The explicit packed
mask, original public decoding, architectural rd/x0 connection, initialized source
reads, numerical PC+4/wraparound, combined Sail execution, workers and protocol
boundaries remain open. The earlier failed large table-37 checks were not retried.
No defect, circuit fix or new interface restriction is introduced.

## Complete native reduced shift-column transport (6 November 2026)

The [actual column certificate](Airbender/Proofs/ReducedMachine/NativeShiftColumns.lean)
now checks both output columns for every index in the 4,194,304-row native tag-37
region. It derives exact getter equality to the previously certified native
SLL-low/SRL-high columns. The right half reverses the earlier split table's two
output columns. A [symbolic boundary proof](Airbender/Proofs/ReducedMachine/ShiftBlocks.lean)
retains the native merger of 1,048,576 left-half zeros with the first right-half
zero and the remaining 65,535 ascending values. No table-equivalence premise,
new setup fixture or native generation is introduced.

Twenty independently emitted periodic blocks are identified with the existing
certified templates. Literal structure is reduced before small, complete
64-value kernel checks; geometry is handled symbolically. Eight bounded block
assemblies cover all 148/291 actual output blocks. The
[reference shapes](Airbender/Proofs/ReducedMachine/NativeShiftReferences.lean)
retain exact prior source hashes, and all proof calculation stays under Proofs.
The largest successful template used 530.09 MiB footprint/2867.55 MiB resident;
full column composition used 499.67/2819.36 MiB. No proof limit was increased.

The affected bounded modules and complete axiom/Review/provenance/guide gates
pass: 2,459 explicit standard-only axiom roots and 148 public Review roots. The
existing public row surface is unchanged. Native data, exporter/importer inputs,
production circuit/Rust and dependencies remain unchanged; the prior 592
importer, eight CLI and 47 native controls remain applicable.

This closes the large literal-column identity gap, not the complete numerical
row/query or instruction theorem. A combined second-output numerical assembly
still exceeds Lean's allocation cap despite separately checked native transport,
old arithmetic and small reference identities. Its draft is outside the source
tree and excluded from coverage. Every failed/limited worker terminated without
survivors; no ceiling was raised. Canonical pooled numerical query results,
source/key binding, complete shift words, public decoding/rd/x0, numerical PC,
initialized execution and machine/protocol boundaries remain open. Resource
failures and unfinished composition are not native defects or new interface
assumptions.

## Native reduced numerical shift contributions (6 November 2026)

The [numerical row certificate](Airbender/Proofs/ReducedMachine/NativeShiftRows.lean)
now fixes the key, both arithmetic outputs and tag at every one of the actual
4,194,304 shift rows. The [pooled query theorem](Airbender/Review/Circuits/ReducedMachine/Tables/ShiftTheorems.lean)
derives a canonical 22-bit packed key, exact numerical outputs and both 16-bit
bounds from original full native pool membership with tag 37. Right outputs
retain their actual high/low order. The existing exact column certificate is
used as a proved connection, never as an equivalence assumption.

The [short selected-row claim](Airbender/Review/Circuits/ReducedMachine/Theorems.lean)
now derives both numerical fields and bounds for each actual source-one limb's
contribution. [Proof assembly](Airbender/Proofs/ReducedMachine/NativeShiftContributions.lean)
uses both queries already recovered from native equations, the derived tags and
the complete pool. The decoded packed mask remains explicit. The statement
uses the actual field-packed key's canonical value: it does not yet identify
that key with the initialized architectural source limb, supply a source bound,
or establish the complete shifted word, rd/x0, numerical PC or execution.

[Eleven regressions](Tests/NativeReducedNumerics.lean) cover the first/last left
and right rows, right shift-zero/one/sixteen boundaries, reversed right output
rejection, corrupted left carry, oversized key and retained numerical bounds
for discarded writes. Positive cases are members of the actual complete pool;
they are not complete 117-equation execution fixtures. Existing affected native
routing/filler/write/pool tests also pass.

This closes the numerical composition allocation gap recorded at the preceding
column checkpoint. A small generic vector projection prevents arithmetic
expansion when selecting a limb. Separate arithmetic, low getter, high getter,
row, pool and contribution modules pass at default proof settings; no literal,
importer, exporter, production circuit/Rust or dependency changed. All 2,482
explicit standard-only axiom roots and 150 public Review roots pass, with exact
provenance and guide/layer gates. The prior 592 importer controls, eight CLI inputs
and 47 native generation/export controls retain unchanged inputs. No native
issue or new interface restriction is established; parity remains open.

## Native reduced initialized clocks and logical history (6 November 2026)

The [new registry](Airbender/Review/Helpers/Context/ReducedMachine.lean) binds the
actual regenerated 117-equation artifact, imported state/decoder columns, all
three actual mixed/register ports and an explicit four-field modeled setup-table
type. It remains separate from the historical shipped artifact. Clock/history
correctness does not certify the setup table's arithmetic, arbitrary public
configuration or physical argument enforcement.

[Native timestamp extraction](Airbender/Proofs/ReducedMachine/NativeTimestamp.lean)
checks actual Boolean equations 27..30, both final-clock equations 115/116 and
all eight timestamp queries 8..15. [Exact clock metadata](Airbender/Proofs/ReducedMachine/NativeClockMetadata.lean)
retains previous-clock pairs 132/133, 135/136 and 138/139, actual borrow bits
134/137/140 and port offsets 0/1/2. These obligations now instantiate the unchanged
shared clock contract. No local clock, alignment, prior-value, ordering or
intermediate-state answer is supplied.

Two [short public history claims](Airbender/Review/Trace/Families/ReducedMachine/History.lean)
now derive a complete Clean-consistent memory history and newest preceding read
for every actual native port from original Sail public seed/PC construction and
accepted native state/memory matching. They also derive every local/prior clock
input, strict access ordering and exactly four terminal ticks per participating
row. Readonly refreshes, mixed addresses and actual masked writes stay in matching.
The claims allow unordered row lists; the existing shared proofs derive chronology.

[Four conditional regressions](Tests/NativeReducedHistory.lean) retain low-clock
carry, reject finite timestamp-epoch overflow, reject a nonpreceding read using
derived initialization clocks, and reject incorrect terminal row accounting.
These are consequences of actual native acceptance, not complete positive
117-equation execution fixtures. All affected bounded modules, 2,497 explicit
standard-only axiom roots, 152 public Review roots and exact provenance/guide/layer
gates pass at unchanged resource settings, with no owned survivors.

Native Rust explicitly relies on initialized RAM consistency rather than a local
source-one low-limb range check. This new logical history connection is necessary
but does not by itself derive word ranges. The next range step must establish
native write preservation for supported decoded combined operations and feed
that proved rule into shared initialized range induction. No desired read/range,
write-preservation or result premise is added to the public claims. Canonical
source-key binding, complete shift words, public decoding/rd/x0, numerical PC,
original instruction execution and worker/protocol/padding/terminal/init boundaries
remain open. The four-tick clock conclusion is not terminal machine/protocol
soundness. No native defect or issue-handling assumption is established.

## Native reduced original public shift decoding (6 November 2026)

The [selected decoder projection](Airbender/Review/Circuits/ReducedMachine/Decoder.lean)
retains original SLL/SRL/SRA and immediate forms, native reduced masks, actual
source/rd indices, raw funct3, x0 flags and SRAI's encoded 1024 immediate bits.
Original stateful Sail decoding and public byte reads construct the independent
sparse/padded table. The [membership boundary](Airbender/Review/Helpers/Decoder/ReducedMachine.lean)
uses the actual imported native ten-field query; it supplies no expected mask,
zero flag, operand, range or result.

[Native proofs](Airbender/Proofs/ReducedMachine/NativeShiftDecoder.lean) derive a
262,144 packed-mask bound from all eighteen actual Boolean bits and the original
packed equation. Native acceptance therefore excludes sparse holes and the
all-minus-one tail. The [short public trace claim](Airbender/Review/Trace/Families/ReducedMachine/Decoder.lean)
recovers the original public entry, actual source/rd/x0/immediate fields and the
previously explicit shift mask. [Trace assembly](Airbender/Proofs/Trace/Families/ReducedMachine/Decoder.lean)
stays under Proofs. Local conditional shift theorems retain their small mask
interface; clients can now derive that mask from this public decoder contract.

[Eight regressions](Tests/NativeReducedDecoder.lean) check twelve ordinary/x0
projections, reuse original public Sail decoding for their exact bytes, exercise
all 25 original public slots including unsupported holes, preserve SRAI immediate
1055 and the six actual x0 masks, reject RV32 amounts 32/63 and out-of-profile
instructions, retain modeled padding membership while rejecting its native
selection, and reject a corrupted destination-zero flag. Only original public
byte/state/decode lemmas are reused; no old split-family decoder table or mask
identity is transferred. These are not full positive 117-equation execution fixtures.

This is a logical selected-profile decoder connection, not a new literal native
Rust decoder-export certificate or universal public fixed-ROM/physical preprocessing
binding. The existing eight-word fixed-pool fixture is unchanged. No equivalence
with old decoder tables or unsupported-profile coverage is assumed. Native write
preservation, initialized word ranges/source keys, full shift words, numerical PC,
other combined families and original execution/protocol/terminal/init remain open.
All affected bounded modules, 2,513 standard-only axiom roots, 153 public Review
roots and exact provenance/guide/layer gates pass at unchanged limits. No native
defect or new issue-handling assumption is established.

## Native reduced initialized shift ranges and canonical keys (6 November 2026)

The [concrete trace constructor](Airbender/Review/Trace/Families/ReducedMachine/FixedData.lean)
selects exactly the checked native fixed pool and retains every row and explicit
state/memory boundary. Acceptance is checked on that constructed trace; no premise
equates an arbitrary table with the native pool. The retained public fixture and
its separate compiler/preprocessing/physical setup boundaries are unchanged.

[Canonical key calculations](Airbender/Proofs/ReducedMachine/NativeShiftNatural.lean)
prove bounded native limb/amount/direction packing and its exact actual tag-37
arithmetic interpretation. Symbolic gap/divisibility/complement lemmas prove both
natural assembled limb bounds for every one of the 32 amounts in all three modes.
They retain logical/positive/arithmetic-zero-shift cases and native right-output
order. [Actual candidate recovery](Airbender/Proofs/ReducedMachine/NativeShiftBounded.lean)
uses the real contribution queries, derived sign filler and native equations to
identify both candidate values and bounds. Its earlier-source premise is internal
and is removed by initialized history in the public claims.

[Native write preservation](Airbender/Proofs/ReducedMachine/NativeShiftPreservation.lean)
keeps readonly refreshes and derives actual zero-flag masking from original public
decoding. The last port depends only on the earlier first read. The
[shared time induction assembly](Airbender/Proofs/Trace/Families/ReducedMachine/Values.lean)
therefore derives every native read, actual write and terminal word range from
original public seeds, actual fixed-pool acceptance and complete selected-shift
decoder membership. No per-row range, source value, clock, selector, expected
read/write or preservation rule is supplied. The
[short public range theorem](Airbender/Review/Trace/Families/ReducedMachine/Values.lean)
includes discarded reads/writes. The formerly unchecked source-one low limb is
now bounded in this initialized selected profile.

[Both actual source keys](Airbender/Review/Trace/Families/ReducedMachine/Sources.lean)
now have their exact natural limb/amount/direction packing, using those derived
bounds and the original public decoded mask. This is native key/word-range
soundness, not original Sail GPR/cell transport or complete shifted-word/instruction
execution. Other combined operation profiles, numerical PC+4/wraparound,
workers/accounting/protocol/padding/terminal/init remain unfinished. General native
preprocessing/ROM/physical fidelity remains separately scoped.

[Nine regressions](Tests/NativeReducedRanges.lean) retain left/right last-amount
results, four negative arithmetic boundaries, positive arithmetic zero fill,
both native packed-key boundaries and exact setup selection. Initialized public
claims reject oversized low source reads and actual writes, and derive discarded
zero writes while preserving bounded source participation. These are not complete
positive 117-equation execution fixtures.

The first finite large-coefficient bound search hit Lean's allocation cap; a
scalar-only version and isolated amount31 probe confirmed the cost was arithmetic,
not imports. All failed workers terminated with no survivors and no ceiling raised.
Symbolic stride/gap proofs plus tiny complete power/filler identities now pass at
default proof settings. Successful arithmetic modules stay below500MiB footprint;
actual candidate recovery used568.67MiB and generic projections804.47MiB, within
unchanged ceilings. All affected bounded modules, 2,548 explicit standard-only
axiom roots, 155 public Review roots and exact provenance/guide/layer gates pass.
No native defect, circuit fix or new issue-handling assumption is introduced.

## Native reduced complete RV32 shift words (6 November 2026)

[The short initialized result claim](Airbender/Review/Trace/Families/ReducedMachine/Results.lean)
now derives canonical complete RV32 candidate words and actual masked destination
writes for selected original shifts. Public initialization, complete original
public shift decoding and acceptance against concrete fixedData supply all source
ranges; no source, expected result, write-preservation rule or intermediate state
is added to the public interface. Original rd/x0 determines whether the actual
write is zero, while the actual candidate/read participation is retained.

[Observables and references](Airbender/Review/Circuits/ReducedMachine/ShiftResult.lean)
remain under Review. [Pure contribution words](Airbender/Proofs/ReducedMachine/NativeShiftWords.lean)
instantiate unchanged checked arithmetic identities; [complete assembly](Airbender/Proofs/ReducedMachine/NativeShiftAssembly.lean)
reuses the prior pure RV32 limb-result lemmas only after a new symbolic natural
word/filler connection. The arithmetic-zero exception, reversed native right
output order and all 32 amounts are retained. [Actual native result lifting](Airbender/Proofs/ReducedMachine/NativeShiftResult.lean)
uses the already checked candidate bounds/equations and decoded x0 mask.
[Trace assembly](Airbender/Proofs/Trace/Families/ReducedMachine/Results.lean)
discharges the internal source-bound premise from initialized history. No split
native table, mask or constraint is assumed equivalent.

[Eight regressions](Tests/NativeReducedResults.lean) check exact cross-limb and
last-amount words for all three shifts, negative arithmetic zero shift, all 32
positive arithmetic amounts, encoded SRAI/high-operand low-five-bit selection,
rejection of a logical result for a negative arithmetic shift, discarded writes
with the real candidate retained, and initialized all-zero-write consequences.
They are numerical and conditional native consequences, not full positive
117-equation accepted execution fixtures.

All affected bounded modules, 2,569 standard-only axiom roots and 156 public
Review roots pass with exact provenance, guides and layer gates. Full Review used
538.91 MiB footprint and 3095.23 MiB resident at unchanged ceilings, with no
owned survivors. Original Sail
cell/GPR transport, native source-two address/readonly binding, numerical PC+4
and wraparound, original instruction execution, other combined profiles and
worker/protocol/padding/terminal/init remain open. The native fixed public fixture,
compiler/preprocessing/ROM and physical enforcement boundaries are unchanged.
No native defect or issue-handling assumption is established.

## Native reduced original Sail register history (6 November 2026)

[The short public register-history claim](Airbender/Review/Trace/Families/ReducedMachine/Registers.lean)
now constructs native-clock-ordered original Sail cell states, all source and
old-destination GPR observations in one pre-state, actual masked GPR writes,
final cell matching and preserved code/misa. Original public shift decoding is
replayed in every constructed pre-state. Public seed/domain construction,
acceptance against concrete fixedData, complete original public shift membership
and aligned tracked cells are the inputs. No local state/read/write/result,
selected address-space flag, x0 event value or decoder replay answer is supplied.

[Native port recovery](Airbender/Proofs/ReducedMachine/NativeShiftPorts.lean)
checks both readonly sources and derives the actual mixed second-port register
flag, rs2 low address and zero high address from native equations 60/61/113.
The actual mixed destination is already tied to original rd. All three original
indices are therefore bound to actual native accesses; immediate/x0 aliases stay
in history. [Zero preservation](Airbender/Proofs/Trace/Families/ReducedMachine/ZeroRegister.lean)
uses actual decoded x0 masking, readonly refreshes and unchanged shared induction
from public seed reads. [Code/replay proofs](Airbender/Proofs/Trace/Families/ReducedMachine/CodeHistory.lean)
derive register address space for each event from accepted native constraints,
then preserve all memory bytes and misa. [History assembly](Airbender/Proofs/Trace/Families/ReducedMachine/RegisterHistory.lean)
reuses unchanged shared chronological grouping and original Sail realization;
[observable contracts](Airbender/Review/Helpers/Memory/ReducedMachine.lean)
keep states/order/reads/writes/replay as conclusions.

[Eight regressions](Tests/NativeReducedRegisters.lean) reject wrong rs2 addresses,
nonzero high addresses and RAM selection for all six shift masks, retain source
and old-destination aliases in one pre-state, prove discarded x0 state stutters,
and reject initialized nonzero-x0 events. A positive exact imported three-port
Sail-group fixture retains all x0 refreshes/writes; its assignment is explicitly
not a complete 117-equation accepted instruction/execution fixture.

All affected bounded modules, 2,592 explicit standard-only axiom roots and 157
public Review roots pass with exact provenance, guide and layer gates at unchanged
limits. Full Review used 539.29 MiB footprint/3093.80 MiB resident in 16.74 seconds;
all owned processes terminated. Original selected-operand/clause execution, numerical PC+4/wrap and fetched
execution remain open. Other combined profiles, worker/accounting/protocol spans,
padding/terminal/init and compiler/preprocessing/ROM/physical enforcement remain
separate. No native defect, circuit fix or issue-handling assumption is added.

## Native reduced original Sail shift clauses (6 November 2026)

[The short initialized clause-history claim](Airbender/Review/Trace/Families/ReducedMachine/Clauses.lean)
now derives execution of every selected retained original Sail shift clause into
the same after-state as the actual native GPR transfers. Public image/decoder
construction, seed/domain boundary, concrete fixedData acceptance, full original
shift decoding and aligned tracked cells are the inputs. Source ranges, actual
reads, selected register/immediate operands, numerical results, masked writes and
all states are derived; no per-row result, source, selector or intermediate-state
answer is supplied. Original x0 instructions and all native readonly accesses
remain present, including immediate rs2/x0 aliases.

[Operand observables](Airbender/Review/Circuits/ReducedMachine/ShiftOperand.lean)
separate the actual readonly second-port word from selected operandWord.
[Native operand recovery](Airbender/Proofs/ReducedMachine/NativeShiftOperand.lean)
derives the exact register/immediate mask bit from the original Sail constructor,
then uses actual native routing and bounded public immediate fields. This retains
encoded SRAI 1055 rather than applying the old split mask threshold or columns.
[Pure original-clause sequencing](Airbender/Proofs/ReducedMachine/NativeShiftClauseReference.lean)
reuses the checked original Sail primitive/encoded-amount lemmas; the exact
ofNat32 logical immediate projection is proved explicitly. [Actual native clause
assembly](Airbender/Proofs/ReducedMachine/NativeShiftClause.lean) consumes the
already proved native numerical write and actual GPR transfers, preserving the
original x0 discard behavior. [Trace composition](Airbender/Proofs/Trace/Families/ReducedMachine/Clauses.lean)
discharges the internal source bound through initialized ranges.
[Observable contracts](Airbender/Review/Helpers/Memory/ReducedMachineClauses.lean)
remain under Review; calculations and sequencing stay under Proofs.

[Eight regression roots](Tests/NativeReducedClauses.lean) check twelve original
ordinary/x0 projections and concrete numerical outputs, actual original Sail
clause execution for all twelve forms, six whole-data-state x0 stutters, actual
native SRAI 1055 selection with the readonly rs2=x0 port retained, conditional
native x0 clause execution, execution between states derived by initialized
public history, and rejection of all three illegal 32/63 immediate forms. The
positive local fixtures establish original Sail execution, not complete accepted
117-equation native rows. General positive native execution fixtures remain open.

All affected bounded modules, 2,607 explicit standard-only axiom roots and 158
public Review roots pass with exact provenance, guides and layer gates at unchanged
limits. Full Review used 538.86 MiB footprint/3090.44 MiB resident in 23.85 seconds,
with no owned survivors. Numerical PC+4/wrap, normal PC preparation/retirement and fetched initialized
shift execution remain unfinished; clause execution alone does not establish
them. Other combined profiles, workers/accounting/protocol/padding/terminal/init
and compiler/preprocessing/ROM/physical/cryptographic/completeness boundaries
remain separate. No native defect, production fix or issue-handling assumption
is introduced.

## Native reduced numerical PC successor (6 November 2026)

[The short public PC claim](Airbender/Review/Trace/Families/ReducedMachine/PC.lean)
now derives canonical/aligned incoming PC, bounded outgoing PC and complete RV32
PC+4 for every selected original shift row, including full top-word rollover.
Original public byte/stateful decoder construction, full sparse/padded membership
and actual native acceptance are the inputs. Incoming range/alignment, native
carry bits, output ranges and the successor are conclusions, not per-row answers.
The PC equations are independent of fixed-table meanings, so the generic native
registry's modeled setup remains explicit; no setup equivalence or physical
preprocessing claim is needed or inferred. The existing concrete fixed-pool
fixture and its separate fidelity boundary are unchanged.

[Small PC observables](Airbender/Review/Circuits/ReducedMachine/PC.lean) use actual
native incoming0/1 and outgoing13/14 columns. [Native calculation](Airbender/Proofs/ReducedMachine/NativePC.lean)
checks Boolean equations18/19, low/high carry gates/inverses/selects34..39,
inverse columns51/53, carry columns52/54 and default candidate49/50. It adapts the
prior checked v2 arithmetic argument only after those new native connections;
actual selected final-PC equations110/111 complete the link. Original public
query/decoder sources derive incoming canonical bounds/alignment and exclude
padding. The internal bounded/aligned-input calculation is fully discharged by
[trace assembly](Airbender/Proofs/Trace/Families/ReducedMachine/PC.lean). No old
split constraint, table, metadata or expected successor is assumed equivalent.

[Eight PC regression roots](Tests/NativeReducedPC.lean) check all eight actual
imported increment assertions at zero, the last noncarrying low word, low carry
and full RV32 wrap; independent numerical edges; corrupted low/high rejection;
full-native conditional decoded wrap; public rejection of oversized
successors; exact original decoded-PC agreement; and x0 PC advancement despite
discarded GPR writes. The positive fixtures satisfy the exact eight-equation PC
gadget, not all117native equations/lookups. Complete positive accepted execution
fixtures remain open. Two deep closed mutation evaluations reached the default
recursion limit; symbolic polynomial differences replaced them without raising
proof/resource limits. All owned processes terminated, with no resource-limit hit.

All affected bounded modules, 2,621 explicit standard-only axiom roots and 159
public Review roots pass with exact provenance, four guide names, 2,560 guide
links/anchors and layer gates. Full Review used 539.69 MiB footprint/3096.38 MiB
resident in 14.06 seconds; independent pinned provenance used 16.17/33.31 MiB
in 6.58 seconds. Both report no owned survivors at unchanged ceilings. Exact
provenance checks 189 v3-origin and 829 prior-backport identities; production
inputs and dependencies are unchanged. Original normal PC preparation/retirement and fetched initialized execution remain open;
numerical PC+4 alone does not establish them. Other combined operations and native
worker/accounting/protocol/padding/terminal/init and compiler/preprocessing/ROM/
physical/cryptographic/completeness boundaries remain separate. No native defect,
production fix or issue-handling assumption is introduced.

## Native reduced initialized original fetched shift execution (6 November 2026)

[The short public instruction-history claim](Airbender/Review/Trace/Families/ReducedMachine/Execution.lean)
and [finite fetched-execution claim](Airbender/Review/Trace/Families/ReducedMachine/FetchedExecution.lean)
now connect initialized selected native shifts to original Sail normal nextPC
preparation, retained clause execution and tick_pc retirement. Original public
byte/stateful decoder image construction, accepted concrete fixedData matching,
complete ShiftDecodedTrace and aligned tracked public cells are the inputs. All
ranges, actual reads/writes, original selected operands, native PC successors,
row order, intermediate states and decoder replay are derived. The finite Sail
execution starts at the actual public state and ends at the actual native terminal
PC with every terminal token interpreted by an original Sail cell read. Terminal
PC bounds follow from a native successor or the public initial PC on empty traces.
No expected successor/result, local range or intermediate-state premise is added.

[Local native retired execution](Airbender/Proofs/ReducedMachine/NativeShiftExecution.lean)
transports actual native cell histories through original nextPC/PC updates,
instantiates the already checked actual mixed-port/GPR/clause/result proofs and
uses the checked native numerical PC successor. [Instruction-history assembly](Airbender/Proofs/Trace/Families/ReducedMachine/Execution.lean)
discharges local source bounds/alignment from initialized ranges/original public
decoding. [Small execution observables](Airbender/Review/Helpers/Memory/ReducedMachineExecution.lean)
remain under Review. [Fetched composition](Airbender/Proofs/Trace/Families/ReducedMachine/Composition.lean)
replays original byte/stateful decoding in each derived pre-state, uses actual
native clock matching to construct the PC chain and chronological row segments,
and instantiates unchanged shared normal-step/composition/postcondition lemmas.
No split native constraint, table or mask is assumed equivalent.

[Four retired-execution regression roots](Tests/NativeReducedExecution.lean)
cover all twelve original ordinary/x0 forms at ordinary PCs and full wrap, six
discarded whole-data-state stutters with PC advancement in both modes, initialized
actual segment construction/execution and rejection of oversized actual terminal
PCs. [Two fetched-boundary regression roots](Tests/NativeReducedFetched.lean)
prove a concrete actual-native zero-row accepted execution for every RV32 PC and
recover the actual original PC reader at 0xffffffff. The positive Sail fixtures
and empty native fixture do not establish a complete positive nonempty117-equation
accepted execution row. That witness coverage remains open. All corrections were
small names/frame/endpoint elaboration fixes; no resource limit or proof-setting
increase was needed and every worker terminated.

All affected bounded modules, 2,634 explicit standard-only axiom roots and 161
public Review roots pass with exact provenance, four guide names, 2,589 guide
links/anchors and layer gates. Full Review used 540.54 MiB footprint/3092.03 MiB
resident in 23.83 seconds; independent provenance used 16.28/32.67 MiB in6.48s.
All owned workers terminated at unchanged ceilings. Exact pinned provenance
checks189v3-origin/843backport-origin identities with unchanged inputs/dependencies. This
closes the selected original shift profile's initialized normal/fetched execution
connection under the stated interfaces. It does not establish other combined
profiles, native public/fixed-ROM preprocessing or physical setup, padding/terminal
machine enforcement, worker/caller/accounting/unified protocol or initialization/
teardown. Successful ordinary four-byte Sail stepping is the reference; original
interrupt/exception paths and general compiler/Rust/JSON/cryptographic/completeness
boundaries remain separate. No native defect, production fix or issue-handling
assumption is introduced. This is not v3 parity or full reduced-machine coverage.

## Complete positive native SLL/x0 execution fixtures (6 November 2026)

[Two complete native witnesses](Tests/NativeReducedWitness.lean) now satisfy all
117 actual regenerated equations and all22lookups against the actual 5,771,521-row
fixed pool. They execute original SLL x3,x1,x2 at PC0 and SLL x0,x1,x2 at PC48 with
x1=x2=1. Both retain candidate2; the actual write is2 for rd3 and0 for rd0. Every
scalar/timestamp lookup and both sign/high-byte queries are included, as are the
actual truncation,shift contribution and filler rows. No split-family native
constraint,witness value or table identity is transferred.

[The nonempty public trace fixtures](Tests/NativeReducedFixture.lean) prove actual
native activity,state matching and complete three-port memory matching,including
readonly refreshes and discarded x0 participation. Original Sail reads construct
all public seeds and initial PCs. Original public byte/stateful decoding builds
the complete13-slot prefix with unsupported holes and3padding rows; actual native
masks/fields are newly projected and complete native ten-field query membership
is checked at each actual row. The imported native fixed fixture remains its
separate unchanged eight-word/CSR configuration. This modeled public setup is not
assumed equal to a native Rust preprocessing export or physical fixed-ROM setup.

[Positive initialized execution](Tests/NativeReducedPositive.lean) instantiates
the already checked public native theorem with every premise proved. It derives
finite original fetched execution and actual original Sail terminal PC/GPR reads:
PC4/x3=2 for the ordinary row; PC52/x3=0 and x0=0 for the discarded row. The same
nonzero native candidate2 participates in both,while only the actual write masks
to zero. Changing that port write rejects full native acceptance. No expected
state,source bound,read,result or successor is a theorem premise. These are two
nonempty accepted native row/trace fixtures,not merely local Sail examples or PC
slices. Other modes,immediates,aliases,wrapping and multi-row fixture variants
remain separate coverage work; no universal completeness claim follows.

Whole-row simp reached the default recursion limit; small complete32/32/32/21
polynomial blocks plus individual lookups replace it. A transparent named evaluator
keeps index rewrites out of the expanded native matrix. Small state-component
certificates and abstract-setup equation extraction likewise avoid deep reductions.
All exact data remain kernel-checked; no opacity,resource/proof limit increase,
native_decide or project axiom is used. All owned workers terminated,with no
memory/wall-time limit hit. The arithmetic draft construction is independently
checked by Lean; Python candidate evaluation is not a trusted certificate.

All affected bounded modules, 2,643 explicit standard-only axiom roots and 161 public
Review roots pass with exact provenance, four guide names, 2,602 links/anchors
and layer gates. Full Review used 539.27 MiB footprint/3096.86 MiB resident in25.20s;
independent provenance used15.89/34.64MiB in6.54s. All owned processes terminated
at unchanged limits. Exact pinned origins pass189v3/852backport identities,with
unchanged native inputs and dependencies. This establishes positive accepted execution examples for the selected actual native target under
its stated public interfaces. Other combined operations,workers/callers/accounting,
unified protocol spans,padding/terminal machine and initialization/teardown,
general native public/setup/preprocessing/ROM/physical correspondence and compiler/
cryptographic/completeness remain open. No native defect,production fix or new
issue-handling assumption is introduced; this is not full reduced-machine/v3 parity.

## Checked coverage

| Circuit | Coverage |
| --- | --- |
| [Native combined reduced](Airbender/Review/Circuits/ReducedMachine/NativeArtifact.lean) | Actual 117-equation artifact and complete native fixed pool. Selected original public shifts derive initialized ranges, canonical keys and [complete RV32 candidates/actual x0-masked writes](Airbender/Review/Trace/Families/ReducedMachine/Results.lean). [Original Sail register histories](Airbender/Review/Trace/Families/ReducedMachine/Registers.lean) now derive states/GPR transfers/code frames and decoder replay. [Original shift clause history](Airbender/Review/Trace/Families/ReducedMachine/Clauses.lean) now derives operand selection and original clause execution at the actual GPR after-state. [Numerical native PC+4/wrap](Airbender/Review/Trace/Families/ReducedMachine/PC.lean) now follows from original public decoding and actual native carry equations. [Original initialized normal/fetched shift execution](Airbender/Review/Trace/Families/ReducedMachine/FetchedExecution.lean) now composes to the actual terminal PC/cells. [Two complete nonempty SLL/x0 fixtures](Tests/NativeReducedPositive.lean) now check all117equations/22lookups and instantiate original public initialization/decoding/execution. Other combined profiles and protocol/terminal/init remain open; no full reduced-machine/parity claim. The historical shipped JSON is distinct. |
| [ADD/SUB](Airbender/Review/Circuits/AddSub/Theorems.lean) | Conditional ADD/ADDI/SUB/LUI/AUIPC destination and original Sail PC/register effects. Packed native masks derive the eight selector bits. The actual masked destination write is observed. Aligned PC wraparound and discarded x0 writes are included. |

| Integration | Coverage |
| --- | --- |
| [Jump/branch/SLT fixed effects](Airbender/Review/Circuits/JumpBranchSlt/Theorems.lean) | All 36 native equations, six scalar/eight timestamp/two fixed queries and exact metadata imported. Actual cleanup/conditional table certificates derive key bounds and exact native control/cleanup values; full active JAL witness and alignment rejection checked. Supported native masks now derive both outgoing PC limb bounds; the JAL -4 negative-high witness shape fails an actual scalar query. Public decoding is checked below; initialized history and cell transfers are checked below; original Sail instruction/trace execution remains open. |
| [Public control decoding](Airbender/Review/Circuits/JumpBranchSlt/Decoder.lean) | Actual public bytes and original Sail decoding construct a full sparse/padded ten-column table. Native equations reject holes/tail, recovering supported masks, canonical inputs/alignment and exact x0 flags; the short native claim derives outgoing PC bounds without a mask/range premise. Separate SLTI/branch masks, retained x0 operations and raw JAL funct3 are checked. Concrete native program export and initialized native history are certified below; original Sail instruction execution and terminal instruction-state matching remain open. |
| [Initialized native control history](Airbender/Review/Trace/Families/JumpBranchSlt/History.lean) | The separate native clock/port registry proves the shared clock contract from actual control equations/queries. Public Sail seeds/PC and complete native matching derive every row/prior clock, complete Clean history and newest reads for all three ports, retaining readonly alias refreshes and actual masked writes. Control word bounds and Sail cell transfers are checked below; original instruction execution remains separate. |
| Initialized control values/cells | [Word bounds](Airbender/Review/Trace/Families/JumpBranchSlt/Values.lean) derive every native read/write/terminal range from actual public sparse decoding and initialized matching. [Sail cell history](Airbender/Review/Trace/Families/JumpBranchSlt/SailHistory.lean) derives all intermediate cell states in native clock order, including x0 preservation from actual masks. Original control instruction execution and terminal instruction-state matching remain open. |
| [Initialized control register transfers](Airbender/Review/Trace/Families/JumpBranchSlt/Registers.lean) | Original public decoding and native clock-ordered history derive all original source/destination GPR reads and the actual masked write at constructed row boundaries. Both source reads and the old destination read use one cell-history pre-state, including aliases. Original control clauses, native operation semantics and PC retirement remain open. |
| [Native saved jump links](Airbender/Review/Circuits/JumpBranchSlt/Theorems.lean) | Full original public decoding and every native constraint derive the actual JAL/JALR PC+4 write, including discarded x0. Native mask classification recovers selectors; actual scalar ranges and Boolean carry equations prove RV32 addition. Exported-JAL, logical JALR/x0, local full native wrap and altered-write rejection regressions pass. Target calculation is checked below; original control instruction execution remains open. |
| [Initialized native jump targets](Airbender/Review/Trace/Families/JumpBranchSlt/Targets.lean) | Actual public bytes, initialized matching and native equations derive every JAL/JALR target and four-byte alignment, including JALR bit-zero clearing. Source/PC/immediate bounds, original JAL parity, selectors and carries are derived. The exported negative JAL and initialized aliasing JALR pass; full original instruction execution/retirement remains open. |
| [Initialized native comparison results](Airbender/Review/Trace/Families/JumpBranchSlt/Comparisons.lean) | Native equations, actual scalar/fixed queries, original public metadata and initialized matching derive all four SLT/SLTU/SLTI/SLTIU masked results. Operand ranges, selector identity, signs, borrow and x0 mask are derived. Signed/unsigned disagreement and negative-immediate/x0 regressions pass; branch semantics and original full instruction execution remain open. |
| [Native comparison PC advancement](Airbender/Review/Trace/Families/JumpBranchSlt/ComparisonPC.lean) | Actual public decoding and native acceptance derive PC+4 and four-byte alignment for all four comparisons. Native scalar ranges supply both outgoing bounds, Boolean carries retain RV32 wrap and raw candidate routing is preserved. All four initialized fixtures, full local wrap and altered-PC rejection pass; original Sail retirement and branch semantics remain separate. |
| [Initialized native branch conditions](Airbender/Review/Trace/Families/JumpBranchSlt/Branches.lean) | Original public decoding and initialized matching derive all six branch conditions, equality/sign/borrow flags, both routing bits and actual zero writes. Native inverse equations identify equality and actual scalar/fixed queries resolve signed/unsigned order. Eighteen initialized cases cover both outcomes per opcode; branch targets and original Sail retirement remain separate. |
| [Initialized native branch targets](Airbender/Review/Trace/Families/JumpBranchSlt/BranchTargets.lean) | The checked six conditions select PC+offset or PC+4 with RV32 wrap and four-byte alignment. Original public decoding derives parity, incoming bounds/alignment and selectors; actual native carry, range, routing and cleanup constraints determine both outgoing limbs. Eighteen initialized cases, local negative/wrap rows and taken-only alignment rejection pass; original Sail clauses/retirement remain separate. |
| [Initialized original comparison execution](Airbender/Review/Trace/Families/JumpBranchSlt/ComparisonExecution.lean) | Exact original SLT/SLTU/SLTI/SLTIU clauses and shared preparation/retirement reach native output PCs in constructed initialized-history segment states, including retained x0 source reads and discarded writes. All four original-byte fixtures execute from actual public states; full fetched control composition/terminal matching and original jump/branch clauses remain separate. |
| [Initialized original branch execution](Airbender/Review/Trace/Families/JumpBranchSlt/BranchExecution.lean) | Original BEQ/BNE/BLT/BGE/BLTU/BGEU clauses prepare and retire to exact native targets in constructed initialized-history segments. Actual public misa readability is explicit, with unrestricted value and history-derived CSR preservation. Eighteen unchanged native fixtures execute both outcomes per opcode from configured public states and derive complete data-state stuttering. Original jumps and full fetched control composition/terminal matching remain separate. |
| [Initialized original jump execution](Airbender/Review/Trace/Families/JumpBranchSlt/JumpExecution.lean) | Original JAL/JALR clauses retire to native targets and actual masked link writes in constructed history segments. Actual initial misa is readable; traces containing JALR use Machine privilege and MLPE-clear mseccfg, transported through history. The existing negative JAL and aliasing JALR execute from public states, reaching 0xfffffffc/link four and 264/link eight. JAL needs no privilege/security entries. Full fetched control composition/terminal matching remains separate. |
| V2 artifact import | All 34 quadratic and 3 linear equations, four 16-bit and eight 19-bit timestamp queries from the pinned ADD/SUB layout. Bounds/placement guards and both native zero coefficient encodings. |
| Reused foundation | Unchanged property definitions, word representation/arithmetic and pinned Sail reference/execution lemmas. Source hashes are checked. |
| Native state/port clocks | Typed physical state and three direct ports, including actual destination writes. Four-tick advancement and strict previous-write/port order follow from imported equations/queries under initial/prior clock bounds and alignment. The initialized-history layer now derives these local inputs from matching and initial boundaries. |
| Initialized logical memory | Accepted native state/memory matching, initial clock bounds/alignment and unique seed addresses construct complete Clean online consistency, per-address paths and newest preceding reads. Readonly refreshes and actual destination writes are included. Public Sail seed/initial-PC construction is checked separately below. |
| Public initial image | Actual Sail register/RAM and PC reads construct native seed tokens and initial PC at native clock four. Missing registers/bytes reject construction. Seed word/clock bounds and address uniqueness follow; no per-row values or clocks are supplied. Physical boot/profile remains separate. |
| Native decoder placement | Ten-column v2 query order, separate rd-zero flag, packed mask and actual memory/witness bank placement are imported and mechanically checked. Unsupported extra descriptor fields fail closed. Selected-profile construction and logical membership are checked below; generation/export remains separate. |
| Public decoder setup | Actual public bytes and pinned Sail decoding construct selected five-opcode rows at PCs 4*i with power-of-two capacity and the complete native-shaped minus-one tail. Missing/unsupported/effectful entries fail. Native packed-mask equations exclude padding before logical membership recovers public source evidence, zero flags and canonical PC/immediate words. Rust generation/export fidelity remains separate. |
| Initialized native word bounds | Public Sail seeds, accepted matching/clocks and complete decoder membership derive every native read, actual masked write and terminal word bound. No per-row bounds or flag answers are supplied. |
| Native-to-Sail history | Public seeds, native matching and complete decoder membership derive actual Sail cell reads/writes and all intermediate states. Native masked writes preserve x0 without v3 NOP preprocessing. Public RAM-cell alignment supplies disjoint byte windows. Native clocks derive row ordering/grouping and readonly refreshes stutter even with aliases; decoder indices identify actual Sail GPR reads/writes. Instruction execution is checked below. |
| Native PC path | Successful public setup retains its indexed PCs and derives every incoming bound/alignment through RV32 truncation. Native carry/wrap equations derive bounded outgoing successors; state matching and the actual public initial PC bound the terminal PC, including empty traces. No per-row PC premise is supplied. Actual Sail retirement and complete execution are checked below. |
| Decoded arithmetic row retirement | Proof-layer assembly derives mask/zero flag, preprocessing, operand/immediate bounds, original Sail reads, PC facts and native observable mapping for all five arithmetic opcodes. Original Sail normal preparation/execution/retirement reaches the actual masked native write. Control-register commutation supplies rebased PC reads. No erased-source or per-row numerical premise is added to the initialized assembly. Complete trace composition is checked below. |
| Initialized arithmetic execution | Public Sail state and selected five-opcode setup, accepted native constraints/state/memory matching and public RAM alignment derive a finite original Sail normal-path trace to exact terminal PC/register/RAM values. All row order, reads, bounds, selectors, preprocessing, intermediate states and retirement effects are proved. Actual code-byte reads and pure original decoding are preserved across native GPR updates; empty traces are included. Physical setup/argument enforcement remains separate. |
| [Word-memory native transfers](Airbender/Review/Circuits/WordMemory/Theorems.lean) | All 31 quadratic/four linear equations, two scalar/eight timestamp queries and both fixed three-column ROM queries are imported. Three native ports and all decoder columns are checked. Complete native-shaped separator/ROM tables derive canonical aligned address limbs, exact ROM data, mixed port selection, masked RAM/ROM loads and RAM-only stores. The native Mersenne31 source-plus-immediate address calculation derives both carries and RV32 wraparound from explicit source/immediate bounds. PC bounds/alignment and native clock inputs yield modular PC successors, four-tick advancement and strict port order. Public decoding and initialized logical history/ranges are checked below; actual Sail cell transfers are checked below for the full supplied native image; architectural projection is checked separately below, while original instruction execution is checked below; physical boot/padding/ROM binding remains open. |
| [Word-memory public decoding](Airbender/Review/Trace/Families/WordMemory/Decoder.lean) | A separate checked native registry and original public LW/SW bytes construct complete padded setup. The native Boolean store mask rejects padding before membership recovers actual Sail source evidence, exact rd-zero flags, canonical register indices, immediate/PC bounds and incoming alignment. Sign extension and original x0 loads are retained. Logical ranges and actual Sail cell histories are checked below. Instruction execution is checked below; architectural boot/padding/shadow-state binding remains open. |
| [Public ROM image/read bridge](Airbender/Review/Trace/Families/WordMemory/ROMImage.lean) | Original Sail byte reads construct a length-preserving ROM vector; excessive counts and missing bytes fail. Native table data is recovered as an actual Sail read inside the extracted prefix. A complete 1048576-word extraction derives coverage of every native ROM address. Full native UNIMP padding is retained; no expected-read/table-equivalence premise is supplied. Supplying Sail boot/padding/shadow state and proving physical setup/export remain separate. |
| [Initialized word-memory history](Airbender/Review/Trace/Families/WordMemory/History.lean) | The native clock instance reuses shared matched-clock recovery and complete Clean history/latest-read proofs for every native port. Actual public seed/PC reads discharge initial clocks, ranges and unique addresses; no per-row clock/read/order premise is supplied. Readonly ROM-shadow accesses remain participating native accesses. Their architectural projection has a separate checked claim below. |
| [Word-memory value ranges](Airbender/Review/Trace/Families/WordMemory/Values.lean) | Native load/store/mask equations preserve word bounds through earlier port copies or canonical ROM data. Full padded decoder membership recovers the zero flag. The unchanged shared decreasing-time induction derives every read, actual write and terminal word bound from actual public seeds and matching, including discarded shadow reads and x0-masked writes. Actual Sail cell transfers are checked below for the supplied native image; the separate projected history is checked below; Original instruction execution is checked below; physical boot/ROM binding remains open. |
| [Initialized word-memory native effects](Airbender/Review/Trace/Families/WordMemory/Inputs.lean) | The first native port's initialized range and actual public decoder setup discharge every local numerical input to the existing native address/PC/clock calculations. Effective-address addition, bounded aligned incoming PCs, bounded RV32 PC successors and four-tick/port-order laws follow, retaining wraparound. No per-row range, carry, PC, clock or desired effect is assumed. Actual Sail cell transfers are checked below for the supplied native image; the separate projected history is checked below; Original instruction execution is checked below; physical boot/ROM binding remains open. |
| [Word-memory Sail cell histories](Airbender/Review/Trace/Families/WordMemory/SailHistory.lean) | Mixed-port equations and full decoder membership prove hardwired x0 preservation. Shared Clean-to-Sail realization and native row grouping derive actual cell reads/writes, intermediate states and final cell matching from the supplied public seed image and public RAM alignment. Readonly refreshes preserve the instruction pre-state; decoder metadata identifies the original Sail source GPR. This retains all native shadow cells as tracked RAM; a separate checked projection below omits shadows. Original instruction execution is checked below; physical boot/ROM binding remains open. |
| [Native shadow value preservation](Airbender/Review/Circuits/WordMemory/Theorems.lean) | Every imported native RAM port mapped below the four-MiB ROM boundary preserves its exact raw value code. Full constraints and port metadata exclude final-port stores there; the first two ports only refresh timestamps. No initial Sail image, expected value or ROM-byte equivalence is assumed. Full native matching retains all shadow tokens; the separate projected architectural history is checked below. |
| [Architectural word-memory projection](Airbender/Review/Trace/Families/WordMemory/Projection.lean) | Whole-address restriction preserves original Clean online consistency and latest values. Public initialization reads only architectural GPR/RAM cells and retains independently supplied canonical native shadow seeds. Native clocks/unique addresses, x0 writes, row order, actual Sail cell transfers and final architectural matching follow while the complete native memory history retains all shadow seeds/accesses. The unchanged shared range induction also derives every full native read, actual write and terminal word bound, including erased shadow accesses. No shadow/Sail read, per-port bound or shadow/ROM equality is assumed. Original instruction execution is checked below; physical native boot/profile and ROM-table binding remain separate. |
| [Projected word-memory row interfaces](Airbender/Review/Trace/Families/WordMemory/Inputs.lean) | Separate architectural/shadow initialization, actual public decoding and full native matching now derive effective-address addition, bounded aligned native PCs, modular successors and native clock/port effects. Shared readonly-prefix transport recovers every retained Sail port read in the instruction pre-state and the actual final masked write. Full native constraints prove that the final port always targets a GPR or RAM outside the ROM prefix. Native shadow matching is retained without Sail shadow reads. Original LOAD/STORE execution/retirement is checked below; physical boot/ROM binding remains separate. |
| [Word-memory code/ROM preservation](Airbender/Review/Trace/Families/WordMemory/CodeHistory.lean) | Initialized projected transfers preserve every byte below four MiB, including missing bytes and code outside tracked cells, and every successful public ROM extraction. Native constraints and projected cell realization keep actual stores outside this region. For public programs fitting the native ROM region, indexed setup construction supplies complete code-byte windows and original Sail reads/decoding survive every prefix. A real changing RAM store and dependent load retain code/ROM evidence without later-read, intermediate-state or desired-value premises. Original instruction execution is checked below; physical boot/export remains separate. |
| [Word-memory platform configuration](Airbender/Review/Trace/Families/WordMemory/Platform.lean) | Initialized projected histories preserve the public original Sail Machine/PMP/PMA configuration. Eight platform modules are copied unchanged from the pinned source. Native RAM address/port equations derive actual Sail reads/writes and alignment; unchanged Sail translation, permission and ordinary-memory helpers transport those effects into actual virtual-memory calls. The dependent native SW/LW regression derives a virtual store and later read of 123 with no supplied intermediate state/read/result. Public ordinary-address and configuration conditions remain explicit. Original clauses and row preparation/retirement are checked below; complete trace composition is checked below; physical boot/export remains separate. |
| Original word-memory clauses | [ROM transport](Airbender/Proofs/Trace/Families/WordMemory/ROMTransport.lean) composes actual public byte extraction, retained source reads, native address/alignment and preserved configuration into original Sail virtual ROM reads. Native ROM bounds derive ordinary addresses. [Clause assembly](Airbender/Proofs/Trace/Families/WordMemory/ROMExecution.lean) derives the original unmasked destination effect from native masked writes, including original x0 without NOP projection. [Initialized regressions](Tests/WordMemoryROMTransport.lean) construct real decoder/ROM bytes and reach original LW clause results in the same actual native after-state, with full shadow matching and shadow value 123 distinct from actual ROM word 0xc0001073. [RAM clause assembly](Airbender/Proofs/Trace/Families/WordMemory/RAMExecution.lean) derives load/store selectors and original registers/immediate from the public decoder, actual rs2/RAM reads from retained ports, and original RAM LW/SW results in the actual cell-transfer states. [The reversed dependent fixture](Tests/WordMemorySailHistory.lean) reaches original SW then LW results with actual read 123 and actual destination write, without an intermediate state/read/result premise. Ordinary-address and configuration conditions remain explicit. Row preparation/PC retirement is checked below; complete word-memory trace composition is checked below. |
| Decoded word-memory row retirement | [Original clause selection](Airbender/Review/Helpers/Decoder/Instruction.lean) reuses the pinned dispatcher without v3 discarded-load deviations. [Retirement](Airbender/Proofs/Trace/Families/WordMemory/Retirement.lean) transports actual histories, configuration and ROM bytes through original nextPC preparation and tick_pc. [Native assembly](Airbender/Proofs/Trace/Families/WordMemory/Execution.lean) derives effective addresses and exact modular native PC successors from initialized matching/public decoding, selecting original RAM LW/SW or ROM LW. No prepared read/state or desired PC result is assumed. Ordinary/x0 ROM regressions retire to native PC 4; reversed dependent SW/LW normal steps derive actual PC 8 and terminal RAM/x3 values 123. Local ordinary-RAM and extracted-prefix coverage domains remain explicit; complete finite trace/fetch composition is checked below; physical boot/export remains open. |
| Range tables | Actual native range16/timestamp19 prefixes and modeled active zero fill have exact unchanged Clean static-table meanings. The reserved normalization row, physical multiplicities and Rust trace/LDE refinement remain separate. |

## Remaining work

- Generalize native export certificates to arbitrary public programs and refine the checked complete row model against Rust trace construction; connect physical initialization and expand mixed/custom programs.
- Extend initialized execution to shift/binop and the remaining supported families; preserve each native metadata and argument boundary. Complete standalone control and unsigned MUL/DIV execution are checked below.
- Backport the remaining ordinary circuit families, worker operations, unified machine, full traces and initialization/teardown.
- Retest v3 findings against v2 before carrying over counterexamples or temporary assumptions.
- Prove the deferred import/compiler/cryptographic connections under a separately scoped claim.

No whole-machine or cryptographic soundness is claimed. Completeness is defined
but unproved. Unsupported fixed tables, dynamic selector profiles beyond the four native shift/binop witnesses, unpaired byte ranges and inter-row linkage are rejected by the importer.

## Initialized word-memory execution

[The short public theorem](Airbender/Review/Trace/Families/WordMemory/Theorems.lean)
proves [finite original Sail execution](Airbender/Review/Trace/Families/WordMemory/Execution.lean)
from actual public state, decoder/ROM extraction, full accepted native matching
and public domains. It checks actual code-byte reads and original decoding at
every instruction, then normal preparation, LW/SW and retirement. Exact native
terminal PC and architectural terminal cells follow from full native history.
Shadow tokens remain matched independently; their values are not Sail ROM bytes.

[Address-domain assembly](Airbender/Proofs/Trace/Families/WordMemory/AddressDomain.lean)
roots each effective address in public cells or public shadow seeds. Ordinary RAM
and coverage by the actual ROM prefix are public domain conditions; no per-row
range, read, order, intermediate state or desired result is supplied. Public
Machine/PMP/PMA configuration and program size within ROM remain explicit.
[Composition](Airbender/Proofs/Trace/Families/WordMemory/Composition.lean) preserves
code, pure decoding, configuration and actual ROM extraction through every
realized prefix. Empty traces preserve actual PC and cells. Physical boot/padding,
setup/export, mixed families and cryptographic enforcement remain separate.
Architectural fetch permissions, exceptions and interrupts remain outside this
successful-step reference relation.

## Fixed native boot and padding paths

[The short native-boot theorem](Airbender/Review/Trace/Families/WordMemory/NativeBoot.lean)
replaces arbitrary initial values/PC reads with the unchanged original Sail
zero-initialization profile, native PC zero/time four and all-zero native seeds.
[Assembly](Airbender/Proofs/Trace/Families/WordMemory/Boot.lean) derives the existing
architectural/shadow initializer and complete original LW/SW execution. Actual
initial reads still come from Sail; missing cells are not defaulted.
[Full native paths](Airbender/Proofs/Trace/Families/WordMemory/BootShadow.lean)
force terminal shadows to remain zero without interpreting them as physical ROM.

Native source review confirms zero GPR/RAM initialization and address-preserving
zero witness masks below four MiB. The proving loader zero-pads its input word
image; the raw ROM table constructor retains UNIMP only beyond its supplied
image. [The separate padding model](Airbender/Review/Helpers/Tables/WordROMPadding.lean)
proves full extent, prefix retention and zero tail symbolically. The explicit
[loader constructor](Airbender/Review/Helpers/Tables/PaddedROMImage.lean) now
inserts actual zero bytes into Sail memory and derives complete four-MiB public
ROM extraction without evaluating a huge map/list. Prefix/outside bytes, all
registers, the original zero profile and public configuration are preserved.
Public decoder setup survives when its code fits the supplied prefix. The added
[short padded-boot theorem](Airbender/Review/Trace/Families/WordMemory/NativeBoot.lean)
derives all ROM-shadow coverage from construction. Ordinary/x0 native fixtures
exercise complete original execution, byte boundaries and previously absent
zero reads; missing and excessive prefixes reject construction. Public alignment,
configuration, ordinary RAM and code-prefix inclusion stay visible. Physical
initialization/setup exports, Rust/compiler refinement and argument enforcement
remain open.

## Native setup geometry and tagged row model

[Imported setup placement](Airbender/Review/Helpers/Tables/SetupColumns.lean) now
covers the exact arithmetic/word-memory widths 12/16, scalar columns 0/1,
three-value-plus-tag generic groups, ten-column decoder groups, all 62 native
table offsets, decoder capacity and the final row reserved for normalization.
Malformed extents, overlaps, missing dummy rows and changed offsets fail closed.

[The native-shaped active row model](Airbender/Review/Helpers/Tables/PhysicalSetup.lean)
retains the dummy tuple, every separator/ROM tuple with native tags 23/24 and all
zero padding. [Symbolic proofs](Airbender/Proofs/WordMemory/PhysicalSetup.lean)
recover exact logical membership and reject wrong-table/dummy/padding tags.
[One short public read claim](Airbender/Review/Trace/Families/WordMemory/Setup.lean)
derives actual Sail words from tagged ROM membership after explicit loader
construction. A nonempty original-LW fixture proves original/padded reads and
altered-data rejection without expected-read or table-equivalence premises.
No large trace/map/list is evaluated. Actual regional native values are now checked
for the fixture below; general program construction, physical trace assembly,
normalization/LDE refinement and argument enforcement remain open.

## Actual native setup export

[The native exporter](../native_setup_exporter/README.md) now calls the pinned
v2 table driver, word-memory decoder materializer and range16 generator directly.
Its [9 KiB fixture](artifacts/setup/word-memory-native.json) retains separate
public image/text inputs, all 1,114,113 generic tuples with native offsets/tags,
all 1,048,576 decoder slots and all 65,536 scalar entries. Lossless compression
is checked against every materialized value before serialization. No full setup
trace, LDE or witness is built. [Literal import](Airbender/Import/SetupEmbed.lean)
and [symbolic certificates](Airbender/Proofs/WordMemory/NativeSetup.lean) check every
ROM/separator/range row, unsupported decoder tail and public image zero tail.
The short [exported-ROM read claim](Airbender/Review/Trace/Families/WordMemory/Setup.lean)
connects actual tagged exported rows to original Sail bytes after explicit padding,
with the actual four-word prefix extraction as its public input condition.
The original LW/SW/x0 prefix and explicit unsupported UNIMP slot are checked.
These certificates cover this pinned native fixture; arbitrary programs, arithmetic
native decoder certificates are checked separately below; full physical trace
padding/normalization/LDE, initialization and argument enforcement remain open.

## Sparse native decoder construction

[Sparse public decoding](Airbender/Review/Helpers/Decoder/SparseSetup.lean) now
reads every supplied word and retains unsupported pure decoder results as holes
at their original PCs. Missing bytes and effectful decoding reject construction.
The complete native-shaped minus-one tail is retained. [Recovery](Airbender/Proofs/Trace/Families/WordMemory/SparseDecoder.lean)
reuses the actual native Boolean store-mask equation to exclude both holes and
tail slots before deriving original Sail bytes/decoding, canonical PC/immediate
bounds, incoming alignment and the exact x0 flag. No per-row metadata or desired
result is supplied.

A [second actual native export](artifacts/setup/word-memory-holes-native.json)
places UNIMP between LW and SW/LW-to-x0. Supported PCs remain 0, 8 and 12.
[Public byte data](Airbender/Review/Circuits/WordMemory/Tables/NativeSparseData.lean)
and [certificates](Airbender/Proofs/WordMemory/NativeSparseSetup.lean) construct the
sparse setup through original Sail reads/decoding and prove every exported decoder
row equals its constructed row, including the interior hole and million-slot tail.
[Two short public claims](Airbender/Review/Trace/Families/WordMemory/SparseDecoder.lean)
cover general successful sparse construction and this pinned actual export.
[The nonempty regression](Tests/WordMemory.lean) satisfies every original native
row equation and lookup for an x0 load at PC 12 before recovering its original
public source through exported membership. Missing bytes/capacity and supported
post-hole fields are checked separately. The separate initialized execution claim
below now composes sparse decoding with full native matching. Arbitrary-program Rust decoder refinement and full physical
trace/argument connections remain open.


## Initialized sparse word-memory execution

[The short sparse execution claim](Airbender/Review/Trace/Families/WordMemory/SparseExecution.lean)
now derives the same finite original Sail LW/SW relation and exact native terminal
PC/cells from successful sparse construction and full accepted native matching.
Public initialization, configuration, actual ROM extraction, ordinary RAM and
ROM-prefix seed coverage retain their existing meanings. Native equations reject
holes/tail before selecting real entries; every original indexed PC is preserved.

[Internal constructor evidence](Airbender/Proofs/Trace/Families/WordMemory/ProgramImage.lean)
is derived from actual strict or sparse construction. Shared native numerical,
code-frame, original clause/retirement and terminal assembly then serve both
builders. The existing strict public claim is unchanged. The internal supported
entry list is only a proof selection index; the public sparse table keeps every
physical hole and no code byte or PC is rewritten. No per-row bound, source/read,
intermediate state, desired result or table-equivalence premise is introduced.

[The nonempty initialized regression](Tests/SparseExecution.lean) reuses the full
native x0-load witness and actual exported decoder slot three. Real public code,
registers, CSRs and RAM bytes plus complete native state/memory tokens derive
original fetched execution from public PC 12 to PC 16, unchanged RAM 123 and x0
zero. The unsupported word at PC four remains in the public image. The supplied
initial PC is 12; this does not assert control flow that skips an executed hole.
General Rust/Sail decoder agreement, arbitrary-program export certificates,
physical setup/initialization and cryptographic enforcement remain separate.


## Native shared scalar prefixes

[The separate scalar artifact](artifacts/setup/scalars-native.json) now retains
all 65,536 range16 and 524,288 timestamp19 values using two lossless affine
blocks. The standalone exporter calls the native range16 API and copies the
pinned prover's three-line timestamp generation clause unchanged, using the
native constant reexported by cs. The standard gate checks that exact clause
identity, every compressed value and byte-for-byte regeneration. No prover
build, dependency change or full physical trace allocation is required. Existing
program fixtures and their format are unchanged.

[Literal scalar data and active rows](Airbender/Review/Helpers/Tables/NativeScalarData.lean)
retain both actual prefixes, then model the native active zero fill. The final
normalization row stays outside this domain. [Symbolic certificates](Airbender/Proofs/Tables/NativeScalars.lean)
prove every prefix/filler row and exactly the original 16/19-bit range meanings,
then connect them to the unchanged Clean range helpers used by both circuits.
A [short shared scalar claim](Airbender/Review/Helpers/Tables/NativeScalars.lean)
adds no table-equivalence premise. Repeated zero filler is retained as valid
range data; this statement does not prove physical lookup multiplicities.

[Regressions](Tests/NativeScalars.lean) check both compiled column placements 0/1,
actual prefix endpoints, the first filler and last active row, exact regional
endpoints and out-of-range rejection. The importer rejects malformed extents,
widths, canonical values, unknown nested fields and incompatible profiles.
These are complete native regional data certificates plus a source-shaped
active-padding model. Formal Rust physical trace/normalization/LDE/argument
refinement and arbitrary-program certificates remain separate. The concrete
arithmetic decoder certificate is checked below.

## Actual native arithmetic decoder export

[The native arithmetic artifact](artifacts/setup/arithmetic-native.json) now
retains all 1,048,576 ten-column decoder slots from the actual v2 arithmetic
preprocessor/materializer. Its seven public words exercise ADD, signed ADDI,
SUB to x0, LUI/AUIPC with nonzero raw funct3 bits, an unsupported UNIMP word at
PC 20 and another ADD at its original PC 24. Existing program/scalar artifacts
and the unchanged exhaustive lossless codec retain their meanings.

[Independent public bytes and entries](Airbender/Review/Circuits/AddSub/Tables/NativeSetupData.lean)
feed original Sail reads and decoding. [Kernel certificates](Airbender/Proofs/AddSub/NativeSetup.lean)
construct the sparse setup and prove equality of every actual exported row,
including the interior hole and full tail. Native packed-mask equations exclude
both sentinels before [the short source claim](Airbender/Review/Trace/Families/AddSub/NativeDecoder.lean)
recovers original public evidence. Row equality is proved, never assumed.
[The regression](Tests/NativeArithmeticSetup.lean) checks all five field shapes,
public text identity and a complete native ADD row at PC 24 with actual exported
membership. Nineteen importer checks reject malformed and incompatible artifacts;
fixture and equivalent binary text reproduce byte for byte.

This is a concrete native-data/source certificate. General Rust/Sail decoder
agreement, arbitrary-program certificates, custom modular MOP semantics and
physical trace/argument refinement remain separate. Sparse initialized arithmetic
execution is now checked below. No instruction skipping an executed hole or new implementation defect
is claimed.

## Initialized sparse arithmetic execution

[The short sparse arithmetic claim](Airbender/Review/Trace/Families/AddSub/SparseExecution.lean)
now derives original fetched/decoded ADD/ADDI/SUB/LUI/AUIPC execution and exact
terminal PC/cells from actual public initialization, successful sparse byte/Sail
construction and complete accepted native matching/decoder membership. Public
RAM-cell alignment remains visible. Native packed-mask equations reject every
unsupported hole and tail row before source selection.

[Internal indexed constructor evidence](Airbender/Proofs/Trace/ProgramImage.lean)
is derived from either actual builder. The existing arithmetic numerical,
original Sail clause/retirement, history/code-frame and terminal proofs then
serve both. The strict public theorem keeps its original statement. The supported
entry list is an internal proof index; all public code bytes and original indexed
PCs remain intact. No indexed-source, per-row bound/read, intermediate state,
desired terminal value or table-equivalence premise is added to the public claim.

[The nonempty regression](Tests/SparseArithmeticExecution.lean) selects actual
exported slot six at PC 24. Full native equations/lookups and complete aliased
x1-port matching derive the clock-four/five refreshes, destination read and actual
clock-six write. Original public bytes/decoding then yield execution to PC 28 and
x1=246. The UNIMP word at PC 20 remains in memory; public initial PC 24 does not
assert control flow skipping an executed hole. General Rust decoder agreement,
arbitrary-program export certificates, custom MOPs and physical trace/argument
refinement remain separate.

## Active native decoder setup rows

[The direct native padding export](artifacts/setup/decoder-padding-native.json)
now calls the same native decoder-padding API as physical setup assembly. Its
ten canonical Mersenne31 values are all minus one. Exact regeneration and twelve
strict importer checks preserve the separate parsing/emission fidelity boundary.
The native materializer comment mentions possible zeros, but the executable
materializer and active setup filler use minus one; no zero-padding premise is
introduced.

[The active row model](Airbender/Review/Helpers/Tables/NativeDecoderData.lean)
retains each of the three actual decoder prefixes and all 15,728,639 additional
active rows. The final c0-normalization row is excluded. [Symbolic certificates](Airbender/Proofs/Tables/NativeDecoder.lean)
prove the actual sentinel is already present in every prefix, so [full active
membership](Airbender/Review/Helpers/Tables/NativeDecoder.lean) adds no query.
This equivalence is proved from literal data, never supplied as a premise. Physical
lookup multiplicities remain a separate boundary.
Compiled arithmetic/word-memory placement at columns 2/6, native capacity,
supported post-hole rows and both active padding boundaries are checked without
enumerating or allocating a 2^24-row trace.

[The short arithmetic execution bridge](Airbender/Review/Trace/Families/AddSub/ActiveSetup.lean)
uses this complete active decoder domain with the existing public constructor,
accepted native matching and sparse execution. The initialized alias regression
still derives PC 24 to 28 and x1=246 through actual exported membership. An
internal word-memory adapter also derives its sparse decoder membership.
Existing native packed-mask/store-mask equations reject the retained sentinel.
These are native data certificates and a source-shaped active-row model; general
Rust full-trace/normalization/LDE refinement, arbitrary-program certificates and
physical lookup/cryptographic enforcement remain separate. No defect is established.

## Complete active setup rows

[Complete row definitions](Airbender/Review/Helpers/Tables/NativeRowsData.lean)
now combine actual scalar prefixes, tagged generic tables and actual decoder
prefixes/fillers at the imported 12/16-column layouts. [Three short claims](Airbender/Review/Helpers/Tables/NativeRows.lean)
recover scalar bounds, actual decoder data and tagged membership. [Projection
proofs](Airbender/Proofs/Tables/NativeRows.lean) also connect these columns to the
unchanged Clean scalar, ROM and separator tables. Full query widths must fit;
the arithmetic layout cannot authenticate a nonexistent generic group.

[Boundary regressions](Tests/NativeRows.lean) check that decoder filler overlaps
the still-active tagged ROM region, while final active rows mix scalar/generic
zeros with decoder minus-one values. Truncated windows, scalar overflow and wrong
padding tags reject. Only small row widths are evaluated; the active domain stays
symbolic. [The short arithmetic bridge](Airbender/Review/Trace/Families/AddSub/PhysicalSetup.lean)
uses actual decoder columns of these complete rows, and the unchanged initialized
alias witness still derives PC 28/x1=246. Native equations, state/memory matching
and public byte/Sail construction retain their existing meanings.

This checks complete source-shaped row assembly and logical column membership.
The decoder connection still covers the three pinned concrete exports. General
Rust trace construction, arbitrary-program decoder certificates, reserved-row
normalization/LDE, physical lookup multiplicities and cryptographic enforcement
remain separate. No implementation defect or table-equivalence premise is added.

## Native jump/branch/SLT fixed effects

[The native control artifact](Airbender/Review/Circuits/JumpBranchSlt/Artifact.lean)
now imports all 33 quadratic/three linear equations, six scalar/eight timestamp
queries and both native fixed triples. Exact port/clock/decoder/setup metadata is
checked. The explicit control profile rejects mixed/repeated/reversed tables and
wrong offsets; memory imports retain their existing meaning.

[Actual native table data](artifacts/setup/jump-control-native.json) comes from
the family table driver and unchanged lossless codec. It retains 65,536 cleanup
rows tagged 17 followed by 128 conditional rows tagged 43, with no inserted dummy
row. The conditional query keeps flags and funct3 in separate columns. [Certificates](Airbender/Proofs/JumpBranchSlt/ControlTables.lean)
prove every cleanup row symbolically, every conditional row by small finite
kernel checks and exact native tagged membership through [two short claims](Airbender/Review/Helpers/Tables/Control.lean).

[The short local circuit claim](Airbender/Review/Circuits/JumpBranchSlt/Theorems.lean)
derives key bounds, the control result, retained bit one and the cleaned low PC
from actual imported queries. [A full active JAL witness](Tests/JumpControl.lean)
satisfies every equation/lookup and exercises that public claim. Altered results,
oversized flags and a JAL target with bit one set reject; its cleanup-table row
alone remains valid. Three wrong import modes and 27 new importer checks pass.

Initialized jump/branch/SLT reads and original Sail execution remain open.
Public control decoding is checked below. The native PC assessment adds no
verifier-closure premise. General Rust/JSON/Lean refinement, physical trace/normalization/LDE and
cryptographic lookup enforcement remain separate.

## Native control PC bounds

[The short native PC claim](Airbender/Review/Circuits/JumpBranchSlt/Theorems.lean)
derives both actual outgoing limb bounds under supported decoder masks
1/2/4/8/16. [Selector calculations](Airbender/Proofs/JumpBranchSlt/Selectors.lean)
recover one-hot selection from the five native Boolean equations and packed
mask equation. [PC assembly](Airbender/Proofs/JumpBranchSlt/PC.lean) proves that
outgoing high variable 14 equals candidate variable 43, ranged by actual scalar
query index 5; outgoing low variable 13 equals ranged key 42 or cleaned value 48.
No outgoing/terminal range, expected PC or verifier-PC closure is a premise.
Public-byte/decoder membership now derives that supported mask below;
initialized control execution remains separate.

[Local regressions](Tests/JumpPC.lean) check every native constraint for JAL mask
1 and immediate -4 at PC zero, with target limbs 65532/65535 and actual link
write four. Actual public decoder fields are checked below. The field
minus-one high-limb variant passes all 36 polynomials and the other 15 queries,
but fails actual scalar query index 5. Thus this v3 F01 witness shape is rejected
by v2 native constraints. This does not claim general jump/branch/SLT Sail or
terminal-history soundness, nor resolve other families' boundary obligations.

## Public control decoding

[The public projection](Airbender/Review/Circuits/JumpBranchSlt/Decoder.lean)
follows the pinned [native decoder](../../cs/src/machine/ops/unrolled/decoder/jump_slt_branch.rs):
five masks, original x0 operations and the separate zero flag.
SLTI/SLTIU use mask 8, branches use mask 16, and JAL retains raw encoding funct3
bits: JAL -4 has tag 7. The pinned original Sail decoder supplies instructions;
no source v3 NOP, discarded-jump mask or JAL tag convention is imported.
The reused sparse constructor reads every actual public word, keeps unsupported
pure words at their original PCs, preserves the complete minus-one tail, and
rejects missing bytes, effectful decoding or insufficient capacity.

[Proof assembly](Airbender/Proofs/JumpBranchSlt/Decoder.lean) first derives packed
mask <=31 from actual native Boolean/mask equations, excluding every sentinel.
Membership then recovers original bytes/decoding and all ten native query fields.
Canonical PC/immediate limbs, incoming alignment, exact x0 flag, raw funct3 and
supported masks follow. [One short public claim](Airbender/Review/Circuits/JumpBranchSlt/Theorems.lean)
combines this source recovery with outgoing PC bounds; no caller-supplied mask,
word/PC range, expected decoding result or verifier-PC closure is a premise.

[Public-byte regressions](Tests/JumpDecoder.lean) use JAL -4, an interior UNIMP
hole and original SLTIU-to-x0 at PC 8. The complete native JAL row with tag 7
passes the public claim; its earlier local tag-zero variant fails membership.
The noncanonical high-PC variant retains actual public membership and passes
all polynomials, but fails the native range query. Constructor tests retain
signed/unsigned comparisons, both jumps to x0 and all six branch conditions;
missing bytes/capacity and the full hole/tail domain are checked.

Initialized native control history is checked below. Original Sail cell/instruction
execution and terminal matching remain open. Actual native program-prefix export
is certified below for the concrete input; general Rust decoder/setup/trace
refinement and cryptographic enforcement remain separately scoped.

## Actual native control decoder export

[The actual native prefix](artifacts/setup/jump-decoder-native.json) calls the pinned
signed jump/branch/SLT decoder through the existing preprocessor/materializer.
Its 3.7 KiB lossless artifact retains all 1,048,576 ten-column rows: original
JAL -4 with raw funct3 7, UNIMP at PC 4, original SLTIU-to-x0 at PC 8 and the
complete minus-one tail. Fixture and little-endian text modes reproduce identical
output; partial/oversized text rejects before output. Separate strict importer
profiles reject unsigned-only, crossed-family, malformed and noncanonical data.

[Literal public data](Airbender/Review/Circuits/JumpBranchSlt/Tables/NativeSetupData.lean)
reuses the preceding byte fixture without changing its words or original Sail
instructions. [Certificates](Airbender/Proofs/JumpBranchSlt/NativeSetup.lean) reuse
the arithmetic certificate structure: three finite prefix checks and a symbolic
full-tail proof establish every exported row equals the independently constructed
public table. [One short export claim](Airbender/Review/Circuits/JumpBranchSlt/Theorems.lean)
then derives public source evidence and outgoing PC bounds from actual membership
and every accepted native constraint, without table-equivalence or range premises.
[Regressions](Tests/NativeJumpSetup.lean) include the full native JAL row, retained
post-hole x0 fields, actual public text and rejection of the old local tag-zero query.

This certifies the concrete input. Arbitrary programs, general Rust/JSON/compiler
refinement, physical trace/normalization/LDE, original Sail control cell/instruction
execution, terminal matching and cryptographic enforcement remain open.
Initialized native control history is checked below.

## Initialized native control history

[The separate control registry](Airbender/Review/Helpers/Context/JumpBranchSlt.lean)
binds all three imported register ports, raw state/clock columns and ten-column
decoder placement. [Native clock extraction](Airbender/Proofs/JumpBranchSlt/Timestamp.lean)
reuses the word-memory calculation structure with the checked control equation/
query indices. Four-tick advancement, 19-bit carry and strict previous-write/port
ordering feed the unchanged shared clock/history proofs through a proved instance.

[One short public claim](Airbender/Review/Trace/Families/JumpBranchSlt/History.lean)
uses actual Sail seed/PC construction and full native state/memory matching to
construct complete Clean history and newest preceding reads for every port.
All row/prior clock bounds and seed-address uniqueness are derived. No expected
read, per-row range/clock/order or desired terminal value is supplied.

[The nonempty JAL -4 regression](Tests/ControlHistory.lean) retains both aliased
x0 reads, the public old x1 value 123 and actual link write four. Its second read
consumes the first timestamp refresh; stale local rows still pass every native
constraint but fail full matching. Actual exported decoder membership is retained.
Missing explicit register data rejects initialization. A separate full native row
checks lower-clock carry; derived port effects and terminal clocks are checked.

Control word/write bounds, hardwired-x0 preservation and actual Sail cell history
are now checked below. Original control instruction execution, exact terminal
instruction-state matching, physical control boot, general Rust/trace refinement
and cryptographic enforcement remain separate.

## Initialized control values and Sail cells

[Native write calculations](Airbender/Proofs/JumpBranchSlt/Writes.lean) derive the
actual destination bounds from the one-hot native selectors, masked-write
equations, scalar-ranged link and exact conditional-control table. Successful
public sparse decoding supplies supported masks and the x0 flag. [The short
range claim](Airbender/Review/Trace/Families/JumpBranchSlt/Values.lean) combines
these rules with public seeds and unchanged decreasing-time history induction,
deriving every native read/write/terminal word bound, including aliased refreshes.

[Native x0 preservation](Airbender/Proofs/Trace/Families/JumpBranchSlt/ZeroRegister.lean)
uses the actual destination address, decoded zero flag and four native write
equations. Shared induction derives zero-valued x0 writes throughout the accepted
history. [The short Sail cell claim](Airbender/Review/Trace/Families/JumpBranchSlt/SailHistory.lean)
reuses unchanged row grouping and Clean-to-Sail realization to derive intermediate
states and actual cell reads/writes in native clock order. It supplies no expected
read, per-row bound, selected schedule or intermediate state.

[The exported-JAL regression](Tests/ControlValues.lean) constructs the same public
bytes with the explicit initialized register state, transfers actual exported
membership and applies both claims. It retains both x0 refreshes and checks that
the actual final port reads old x1=123 and writes the link four. A malformed
zero flag of two satisfies all local native constraints and makes the write
unbounded; full decoder membership rejects it. This checks the explicit lookup
boundary rather than establishing an accepted-trace defect. Original control
instruction execution, terminal instruction-state matching, physical control
boot and Rust/compiler/cryptographic refinement remain open.

## Initialized control register transfers

[The native port connection](Airbender/Proofs/Trace/Families/JumpBranchSlt/PortReads.lean)
reuses unchanged readonly-prefix transport: both source reads and the old
destination read use one cell-history pre-state, even with aliases. Full native
decoder membership identifies the actual original Sail GPR accessors; the final
port performs the actual masked register write, retaining x0 behavior.

[One public claim](Airbender/Review/Trace/Families/JumpBranchSlt/Registers.lean)
combines actual public sparse construction with initialized native matching and
[proof-layer segment assembly](Airbender/Proofs/Trace/Families/JumpBranchSlt/RegisterHistory.lean).
Derived clock order fixes the complete row sequence. Shared append/split proofs
construct each row's before/after states and its older/current/newer Sail histories;
no segment state, expected read, selected schedule or desired write is supplied.
Each segment retains source evidence from original public bytes and pure Sail decoding.

[The exported-JAL regression](Tests/ControlRegisters.lean) extracts its singleton
segment from that public theorem and derives both x0 reads, old x1=123 and the
actual link write four. This connects original register accesses to native cell
transfers; original control instruction clauses, native branch/jump/comparison
semantics, PC preparation/retirement and full terminal instruction-state matching
remain open. Physical setup/Rust/compiler/cryptographic refinement stays separate.

## Native saved jump links

[Native link arithmetic](Airbender/Proofs/JumpBranchSlt/Link.lean) now reuses the
original Boolean carry extraction and unchanged modular word addition. Actual
v2 assertions 9/5 constrain low/high carries 49/28; equations 29/30 compute the
saved PC+4 in scalar-ranged columns 26/27. Native equations 20..23 then force the
actual destination columns 38/39 to that word or the discarded x0 write.

[One short circuit claim](Airbender/Review/Circuits/JumpBranchSlt/Theorems.lean)
uses actual public sparse construction and full native decoder membership to
derive both PC bounds and the exact zero flag. Masks one/two classify the native
JAL/JALR domain; [packed-mask recovery](Airbender/Proofs/JumpBranchSlt/Selectors.lean)
derives every operation selector. No selector, carry, PC-word bound, flag or
expected write is supplied. The original v3 field inverse is not reused.

[Regressions](Tests/JumpLink.lean) retain the actually exported negative JAL link,
check all native constraints for an odd-source JALR and original JAL-to-x0, and
construct their independent original-byte logical setup. The JALR link is eight;
the x0 row retains raw link twelve but writes zero. An unmasked x1 link wraps
from PC 0xfffffffc to zero under all native constraints; that case is a local
row regression, not an initialized/public-decoder trace. Altered link data fails.
General native export certificates for the new logical fixture,
comparison/branch semantics, original Sail clauses/PC retirement and full terminal
instruction-state matching remain open. Rust/compiler/cryptographic refinement
stays separate.

## Initialized native jump targets

[Native target calculation](Airbender/Proofs/JumpBranchSlt/Target.lean) now reuses
original modular word addition and bit cleanup with v2 bindings. Assertions 10/8
constrain carries 50/44; equations 31/32 add PC or rs1 and the immediate into
candidate 42/43. The actual sixth scalar query bounds the high candidate, so no
v3 final-high closure premise is imported. Native cleanup query 15, alignment
assertion 26 and routing equations 27/28 derive the final PC and four-byte alignment.
JAL preserves its even sum; JALR clears bit zero and rejects a sum with bit one set.

[The short initialized claim](Airbender/Review/Trace/Families/JumpBranchSlt/Targets.lean)
uses public Sail initialization, complete native matching and full sparse decoder
membership. Shared initialized induction derives source bounds; actual public
bytes supply PC/immediate ranges and exact mask identity. The unchanged original
[Sail decoder parity proof](Airbender/Proofs/Sail/Decoder.lean) and native metadata
projection derive JAL offset parity. No operand bound, selector, parity, carry,
expected read or desired target is supplied by the public caller.

[Regressions](Tests/JumpTarget.lean) derive the actually exported negative-JAL
target 0xfffffffc from public PC zero. A new logical original-byte JALR fixture
starts at PC four with public x1=257; native matching retains the aliased rs1/rd
refresh and derives target 264 from odd sum 265. Its full public initialization,
lookup and every native equation/query are checked. Local JAL-to-x0 and modular
0xfffffffc-plus-eight target regressions pass. A bit-one JALR target has a valid
cleanup row but is rejected by native alignment. Local wrap is not an initialized
execution certificate, and the new logical fixture has no new general native
export certificate. Original Sail instruction clauses/PC retirement, branch
semantics, complete control execution and terminal instruction-state
matching remain open; Rust/compiler/cryptographic refinement stays separate.

## Initialized native comparison results

[Native comparison calculations](Airbender/Proofs/JumpBranchSlt/Comparison.lean)
now derive the actual masked SLT/SLTU/SLTI/SLTIU result. Equations 29/30 and
Boolean carries 49/28 reuse original subtraction/borrow lifting and unchanged
word arithmetic. Actual scalar queries zero/one range remainder 26/27. Assertions
18/19 use positive high-limb flags 31/33 and scalar-ranged shifted limbs 32/34;
the proof keeps this native encoding and complements the flags in the actual
four-bit control key. Inverse equations 16/17 derive equality-bit Booleanity.
The checked native conditional table determines signed/unsigned result 35, and
write equations 20..23 force actual masked destination 38/39.

[One short initialized claim](Airbender/Review/Trace/Families/JumpBranchSlt/Comparisons.lean)
uses actual public bytes, full sparse decoder membership and complete native
matching. Native packed masks derive register/immediate selectors; original
metadata derives signed/unsigned funct3 and the x0 flag. Shared initialized range
induction supplies both register words, while public decoding bounds the immediate.
No selector, sign/borrow bit, operand bound, expected read or desired result is
supplied. The original [signed word-ordering lemmas](Airbender/Proofs/Arithmetic/Comparison.lean)
are copied unchanged, with source hashes recorded.

[Four separately initialized regressions](Tests/ControlComparisons.lean) compare
register -1 with one (SLT true, SLTU false), and positive source 123 with the
sign-extended immediate -1 (SLTI false, SLTIU true). The original SLTIU-to-x0
retains raw result one but writes zero, with its rd read consuming the dummy x0
readonly refresh. That query also occurs in the prior actual native export.
All original-byte construction, public register/PC initialization, native
constraints and memory matching are checked. A reversed positive flag preserves
its high-limb field equation with shifted value 98303, but actual scalar query two
rejects it. This is enforcement of the native range boundary, not a new defect.
The new logical program has no new general native export certificate. Branch
semantics, original Sail instruction clauses/PC retirement, complete control
execution and terminal instruction-state matching remain open; general
Rust/compiler/cryptographic refinement stays separate.

## Native comparison PC advancement

[Comparison PC arithmetic](Airbender/Proofs/JumpBranchSlt/ComparisonPC.lean)
now derives PC+4 and four-byte alignment for SLT/SLTU/SLTI/SLTIU, including
RV32 rollover. Native equations 24/25 exclude branch routing; equations 31/32
and Boolean carry assertions 10/8 determine candidate 42/43. Actual scalar
queries four/five bound both limbs. Equations 27/28 route that raw candidate
directly to final PC 13/14. Unlike the source layout, comparison PC does not
pass through cleanup. Original modular word addition is reused unchanged;
no final-high closure assumption is imported.

[One short public claim](Airbender/Review/Trace/Families/JumpBranchSlt/ComparisonPC.lean)
derives incoming PC bounds/alignment and comparison identity from original
public bytes, complete decoder membership and native acceptance. It needs no
register-image boundary: this numerical PC calculation reads no source GPR.
No per-row selector, carry, range, alignment or expected PC is supplied.
[Regressions](Tests/ComparisonPC.lean) reuse all four separately initialized
comparison fixtures, check a full native local 0xfffffffc-to-zero row, and reject
an altered outgoing PC with unchanged decoder columns. The wrap row is local,
not an initialized/public-decoder execution or a new native program export.
Original Sail instruction clauses/retirement, branch semantics and complete
control execution/terminal instruction-state matching remain open. General
Rust/compiler/cryptographic refinement remains separate. No new v2 defect is
established.

## Initialized native branch conditions

[Native branch calculations](Airbender/Proofs/JumpBranchSlt/Branch.lean) now
derive BEQ/BNE/BLT/BGE/BLTU/BGEU conditions from actual constraints. Original
word subtraction/borrow and signed ordering are reused unchanged. Scalar
queries zero/one range remainder 26/27; inverse equations 16/17 identify equality
bit 29 with equality of both operand words. The unchanged positive-high proof
is shared with comparisons, preserving native flags 31/33 and scalar queries
two/three. The actual conditional table determines result 35; equations 24/25
derive taken/complement 46/45. Equations 20..23 force the actual unused write
38/39 to zero independently of the decoder-owned x0 flag.

[One short initialized claim](Airbender/Review/Trace/Families/JumpBranchSlt/Branches.lean)
derives both operand bounds from complete native matching and branch identity
and all six funct3 tags from original public bytes/decoding. No per-row range,
selector, equality/sign/borrow bit, expected read or desired condition is supplied.
[Eighteen initialized regressions](Tests/Branches.lean) use the six original
branch words and operand pairs (-1,1), (1,-1) and (1,1). Every opcode has both
outcomes; signed/unsigned disagreement, equality, complementary routing and
the retained zero destination event are checked through full native acceptance,
public initialization and decoder membership. A false equality flag and false
BEQ answer satisfy the actual conditional table but fail the native inverse
equation. This confirms enforcement, not a new v2 defect. The new logical program
has no new native export certificate. Branch target arithmetic, original Sail
clauses/retirement and complete control execution/terminal instruction-state
matching remain open; general Rust/compiler/cryptographic refinement is separate.

## Initialized native branch targets

[Native branch PC arithmetic](Airbender/Proofs/JumpBranchSlt/BranchPC.lean)
now derives PC+offset when taken and PC+4 otherwise, preserving RV32 wrap and
four-byte alignment. Equations 24/25 derive complementary routing; equations
31/32 and the unchanged native Boolean-carry proof determine candidate 42/43.
Actual scalar queries four/five bound both limbs. An untaken row routes the raw
candidate; a taken row uses cleanup, but original offset parity and native
assertion 26 exclude either low target bit before cleanup. Both cases therefore
retain the exact calculated word. Original modular word addition is reused
unchanged; no final-high closure premise is imported.

[One short initialized claim](Airbender/Review/Trace/Families/JumpBranchSlt/BranchTargets.lean)
reuses the checked six branch conditions from initialized matching. Original
public decoding derives incoming PC/offset bounds, alignment, exact selectors
and offset parity through the unchanged Sail decoder/sign-extension lemmas.
No per-row bound, parity, carry, decision or desired PC is supplied.
[Regressions](Tests/BranchTargets.lean) reuse all eighteen initialized original
branch cases. Full local native rows additionally cover taken offset -4, taken
PC+8 wrap and untaken PC+4 wrap with ignored offset two. A taken offset-two row
has valid cleanup membership but fails the actual bit-one assertion. The local
negative/wrap rows are not initialized/public-decoder executions or new native
program exports. No v2 defect is established. Original Sail clauses/retirement,
complete control execution and terminal instruction-state matching remain open;
general Rust/compiler/cryptographic refinement stays separate.

## Initialized original comparison clauses and retirement

[Original comparison execution](Airbender/Proofs/Trace/Families/JumpBranchSlt/ComparisonExecution.lean)
now connects SLT/SLTU/SLTI/SLTIU to their pinned original Sail clauses and normal
preparation/retirement. The native result proof and initialized matching derive
both operands, signed/unsigned comparison and the actual masked write. Public
decoder columns recover exact constructors, indices, immediate sign extension
and distinct register/immediate masks. Original word-ordering, register access,
PC preparation, history framing and retirement lemmas are reused unchanged.
The source nonzero-destination and final-high interfaces are not imported:
native v2 x0 operations retain their original reads, and actual candidate range
queries already supply both successor bounds.

[The public segment claim](Airbender/Review/Trace/Families/JumpBranchSlt/ComparisonExecution.lean)
constructs the complete clock-ordered native cell history and every comparison's
before/after states. The original clause retires to the exact native output PC
in those derived states; no operand, result, prepared state, successor or
intermediate state is supplied. [Regressions](Tests/ComparisonExecution.lean)
reuse all four separately initialized original-byte fixtures and execute from
their actual public states. SLTIU-to-x0 reads public x1=123, discards its true
comparison against sign-extended -1, preserves the complete data state and
retires PC eight to twelve. This is a segment execution/retirement result;
general fetched trace composition and terminal instruction-state matching,
original jump/branch clauses and their CSR effects remain separate. New native
program export, general Rust/compiler and cryptographic refinement are not
claimed. No v2 implementation defect is established.

## Initialized original branch clauses and retirement

[Original branch execution](Airbender/Proofs/Trace/Families/JumpBranchSlt/BranchExecution.lean)
now connects all six native branch conditions and targets to pinned original
Sail BTYPE clauses and normal preparation/retirement. Complete native matching
derives both source bounds and actual same-pre-state reads; original public
decoding derives the BTYPE constructor, indices, funct3 and sign-extended offset.
The existing native target proof supplies exact PC+offset/PC+4 and four-byte
alignment, including the previously checked RV32 arithmetic wrap behavior.
The source branch mask twenty-four and old columns/final-high interface are
replaced by native v2 mask sixteen, actual ports and derived target bounds.

[The public segment claim](Airbender/Review/Trace/Families/JumpBranchSlt/BranchExecution.lean)
constructs every before/after state and retires the original clause to the native
output PC. Original Sail requires a successful misa read on a taken aligned
target. A real public initial CSR entry is therefore explicit; its value is
unrestricted. The [original control-flow module](Airbender/Proofs/Sail/ControlFlow.lean)
is copied unchanged, and [unchanged CSR frame proofs](Airbender/Proofs/Trace/ControlFlowCSR.lean)
transport that entry through complete native history. No per-row CSR, operand,
result, prepared state, target PC, final-high closure or intermediate state is
supplied.

[Regressions](Tests/BranchExecution.lean) reuse all eighteen native original-byte
fixtures unchanged and add only the actual public misa entry, universally over
its 32-bit value. Both outcomes of every opcode execute from their actual public
states, derive complete data-state stuttering from the real discarded write and
reach the checked target. The prior partial fixtures have no misa entry and the
original accessor cannot succeed there. This is an explicit original-state
boundary, not a native constraint defect; a whole missing-CSR branch exception
trace is not claimed. General fetched control composition/terminal instruction-
state matching, original JAL/JALR clauses and their landing-pad CSR profile,
new native program exports and general Rust/compiler/cryptographic refinement
remain separate.

## Initialized original jump clauses and retirement

[Original jump execution](Airbender/Proofs/Trace/Families/JumpBranchSlt/JumpExecution.lean)
now connects checked native JAL/JALR links and aligned targets to pinned original
clauses and preparation/retirement. [Pure jump definitions](Airbender/Proofs/JumpBranchSlt/JumpModel.lean)
and the complete [original retirement declaration](Airbender/Proofs/Sail/JumpRetirement.lean)
are copied unchanged into internal modules. Native v2 masks one/two, immediate
9/10, actual masked destination 38/39 and PC 13/14 replace the source layout.
JAL's original raw funct3 bits and x0 masking remain intact. Existing native
queries and matching derive ranges/targets, including RV32 wrap, without the
source final-high closure premise or supplied link/read/result/state.

[The public segment claim](Airbender/Review/Trace/Families/JumpBranchSlt/JumpExecution.lean)
constructs every history segment and executes its exact public-decoded clause.
A real initial misa entry has unrestricted value. Traces containing JALR use
actual initial Machine privilege and a real mseccfg value with MLPE clear;
other security bits are unrestricted. Unchanged CSR frames derive those reads
at every row. JAL-only traces need no privilege/security entries. Original
landing-pad behavior is retained under this explicit platform profile.

[Regressions](Tests/JumpExecution.lean) reuse the unchanged exported negative-JAL
and logical aliasing-JALR native histories, bytes and decoder certificates,
adding only actual public CSR entries. JAL retires PC zero to 0xfffffffc and
writes link four over x1=123. JALR reads old x1=257 before its aliased link write
eight and retires PC four to 264, clearing bit zero of 265. Both original
retirements share the exact native write's constructed after-state. The JAL
state has no privilege/security entry; the prior partial JALR state's original
privilege accessor cannot succeed. No native defect or whole missing-CSR
exception trace is claimed. Full fetched control composition and terminal
instruction-state matching, new native program exports and general
Rust/compiler/cryptographic refinement remain separate.

## Fetched control execution and terminal matching

[The complete control claim](Airbender/Review/Trace/Families/JumpBranchSlt/Execution.lean)
now composes JAL/JALR, all six branches and SLT/SLTU/SLTI/SLTIU into finite
original Sail execution from public initialization. The unchanged shared
composer derives actual row order, intermediate states, fetch/decode evidence
and every preparation/execution/retirement step. Native register history
preserves the public instruction bytes. Existing native retirement proofs
supply each row's behavior; actual terminal PC and tracked register reads
follow from full state/memory matching. Scalar candidate queries and state
matching also derive both raw terminal PC limb bounds, including empty traces;
no source terminal-closure premise is copied.

The actual initial misa entry and conditional JALR Machine/MLPE-clear profile
remain explicit; history transports their reads. No schedule, intermediate
state, expected read/result, per-row step or terminal bound is supplied.
[Existing jump/branch fixtures and an empty trace](Tests/ControlExecution.lean)
check fetched execution, including negative JAL and all eighteen branch cases.
[A two-row logical native program](Tests/ControlSequence.lean) presents JAL then
aliasing JALR in reverse witness order: JAL writes x1=4, JALR consumes that link
and writes x1=8, and the composed execution ends at PC four. A stale x1=124
variant still passes every local native constraint, public decoder membership
and full state matching, but actual memory matching rejects it. This is a
checked enforcement boundary, not a native defect or a new Rust program-export
certificate. Unified whole-machine/protocol composition, remaining families,
physical initialization/teardown and general Rust/compiler/cryptographic
refinement remain separate.

## Unsigned mul/div native artifact and byte tables

[The native artifact](Airbender/Review/Circuits/MulDiv/Artifact.lean) now retains
all 43 quadratic/six linear equations, six scalar/eight timestamp queries and
six exact three-column RangeCheckSmall queries. These pair all eleven declared
byte columns; the final odd column keeps two zero padding entries. Checked
native setup metadata retains table ID eight, offset zero and 65,536 rows.
Native state/port/decoder metadata is imported separately from semantic claims.
Two optimized-out variables retain bounded, unique scratch metadata; every
attempt to consume such an address as a constraint/query input is rejected.

[Actual native table-driver data](Airbender/Review/Helpers/Tables/NativeSmallRangeData.lean)
is exported reproducibly from pinned v2 Rust with its fourth tag column.
[Symbolic certificates](Airbender/Proofs/MulDiv/SmallRange.lean) prove every one
of the 65,536 actual rows and exact Clean membership through stored periodic
columns, without enumerating the domain or assuming table equivalence.
[The native queries](Airbender/Proofs/MulDiv/ByteBounds.lean) derive all eleven
byte bounds directly from accepted local constraints. No numerical bound or
expected arithmetic result is supplied.

[Boundary regressions](Tests/MulDivArtifact.lean) accept byte endpoints and
reject overflow, nonzero third padding and wrong native tags. Importer
mutations reject missing/repeated/unmapped queries, odd-byte padding changes,
optimized-out equation/query use, scratch overflow/aliasing and altered table
profiles/geometry. This closes the unsigned mul/div importer dependency;
At this artifact checkpoint numerical correctness, public decoding, initialized
history and original Sail execution were still unfinished. The numerical
connection is checked below. No native defect is established.
General Rust/compiler/physical argument refinement remains separate.

## Native unsigned MUL/MULHU/DIVU/REMU arithmetic

[The public numerical claim](Airbender/Review/Circuits/MulDiv/Theorems.lean)
now derives both the selected result and actual destination-zero-masked write
from all accepted native equations/queries. Its explicit local interfaces are
the native packed operation mask, the input register's two-limb bound and the
actual destination-zero flag. No quotient, remainder, product, byte/carry/output
range or desired result is supplied. Public decoding, initialized history and
original Sail preparation/execution/retirement remain subsequent connections.

[The product connection](Airbender/Proofs/MulDiv/Product.lean) reuses the entire
unchanged shared integer byte-column theorem. V2 explicit bytes and split
carries replace source aliases; native queries/assertions derive every needed
byte/carry/output bound. [Division](Airbender/Proofs/MulDiv/Division.lean)
rebinds the inverse scale to 32768 in Mersenne31, derives a strict nonzero
remainder bound from the native borrow and resolves zero divisors to quotient
0xffffffff and remainder equal to the dividend. [Result assembly](Airbender/Proofs/MulDiv/Results.lean)
binds native packed masks MUL=2, MULHU=0, DIVU=3, REMU=1, raw result selection
and both actual masked write limbs. Calculations stay under Proofs.

[Forty full local native witnesses](Tests/MulDivWitness.lean) cover all four
operations, both ordinary/discarded x0 writes, zero/zero, maximal dividend with
zero divisor, maximal product, divisor 257 and 123 divided by seven. Each of
[the four](Tests/MulDivMul.lean) [operation](Tests/MulDivMulhu.lean)
[modules](Tests/MulDivDivu.lean) [checks](Tests/MulDivRemu.lean) proves every
native equation/query, applies the public claim and rejects a corrupted actual
write. Proofs are split at the default proof-step limit; memory/thread ceilings
are unchanged. These are complete local assignments, not initialized fetched
execution or new native Rust program exports. No v2 defect is established.

## Initialized unsigned MUL/DIV decoding and native results

[The short public trace claim](Airbender/Review/Trace/Families/MulDiv/Theorems.lean)
now derives all local numerical interfaces from actual public bytes, seed/PC reads
and accepted native state/memory/decoder matching. MUL/MULHU/DIVU/REMU selected
results and actual masked destination writes follow, including zero divisors and
original x0 destinations. No per-row operand bound, packed selector, zero flag,
expected read or desired result is supplied. Original Sail operation clauses,
preparation/retirement and finite fetched MUL/DIV execution remain unfinished.

[Stateful sparse construction](Airbender/Review/Helpers/Decoder/StatefulSetup.lean)
executes the pinned original Sail decoder in the public initial state. It retains
native PCs 4*i, unsupported instruction holes, capacity and the complete
all-minus-one tail. Byte/decoder errors reject construction. Extension-dependent
decoding reads actual misa; the earlier pure constructors remain available for
their checked base-ISA families. [The entire decoder-frame proof](Airbender/Proofs/Sail/DecoderFrame.lean)
is copied unchanged from the pinned source and proves state preservation and
replay with the same misa. Native two-bit mask equations exclude all sentinel
slots before membership recovers original source evidence and exact query data.

[Initialized native history](Airbender/Review/Trace/Families/MulDiv/History.lean)
reuses complete Clean online consistency and latest-read assembly for all three
native ports. Checked native clock equations discharge the shared instance.
[Range induction](Airbender/Review/Trace/Families/MulDiv/Values.lean) retains both
readonly timestamp refreshes and the actual masked destination write, deriving
every native read, write and terminal word bound. [Numerical assembly](Airbender/Proofs/Trace/Families/MulDiv/Results.lean)
then invokes the previously checked native arithmetic with these derived inputs.

[Sixteen complete initialized traces](Tests/MulDivInitializedFixture.lean) cover
all four operations, ordinary/x0 writes and ordinary/zero divisors. Actual public
bytes and misa=0x40001000 construct their native-shaped setup, including an UNIMP
hole and the full 2^20-row tail. [Original-decoder regressions](Tests/MulDivDecoderCases.lean)
reject every opcode when M is disabled. [Boundary regressions](Tests/MulDivMetadata.lean)
retain locally valid wrong tags and a compensating flag-2/unbounded write, then
prove full public lookup membership rejects both. These are logical argument
boundary checks, not native defects or new Rust program-export certificates.
Physical initialization, setup/compiler refinement, cryptographic enforcement,
whole-machine/protocol composition and completeness remain separately scoped.

## Original Sail MUL/DIV register histories

[The short public register-history theorem](Airbender/Review/Trace/Families/MulDiv/Registers.lean)
now derives original Sail operand/old-destination reads and the actual masked
write from public bytes, initialized seeds and accepted native matching. All
three reads use the same instruction pre-state, including source/destination
aliases. Clock-derived ordering and every segment state are constructed.
[Observable definitions](Airbender/Review/Helpers/Memory/MulDiv.lean) keep the
public statement short; calculations and proof assembly stay under Proofs.

[Native x0 preservation](Airbender/Proofs/Trace/Families/MulDiv/ZeroRegister.lean)
uses actual write equations 35/36 and decoder-owned flags, then invokes unchanged
shared Clean-to-Sail realization. The original generic three-port address/read/
write declarations are copied unchanged from the pinned source and resolve
against checked native v2 metadata. [Code/configuration frames](Airbender/Proofs/Trace/Families/MulDiv/CodeHistory.lean)
preserve every public byte and misa, replaying original stateful decoding in
real later states without a per-row decoding or CSR-read premise.

[All sixteen initialized cases](Tests/MulDivRegisters.lean) now obtain actual
Sail writes and full-state stuttering for x0. [A reversed two-row program](Tests/MulDivRegisterChain.lean)
checks MUL x3,x1,x2 followed by MUL x1,x1,x2, with actual original bytes at PCs
zero/four and a real first update. The second decoder runs in its constructed
pre-state; aliased operand/destination reads are 123/7 and the actual write is
861. The stale old-destination timestamp retains all local constraints, public
decoding and state matching but fails native memory matching. This validates
the logical argument boundary, not a native defect or a new Rust export.

Original MUL/DIV operation clauses, preparation/PC retirement and finite fetched
execution remain unfinished. These are Sail cell-transfer histories, not full
instruction traces. Physical boot/setup/compiler refinement, cryptographic
argument enforcement, unified execution/protocol spans and completeness remain
separately scoped.

## Original local MUL/DIV execution and PC retirement

[The short public instruction-history theorem](Airbender/Review/Trace/Families/MulDiv/Execution.lean)
now combines constructed real register histories with original local MUL,
MULHU, DIVU and REMU execution. [Its observable definitions](Airbender/Review/Helpers/Memory/MulDivExecution.lean)
record original instruction identity, actual native successor bounds and the
original preparation/clause/retirement transition for every native row. Public
bytes, initialized matching and decoder membership derive the operand ranges,
register reads, operation selection, x0 behavior and PC inputs.

[Original clause assembly](Airbender/Proofs/MulDiv/Clauses.lean) reuses the pinned
source's signed low-product, unsigned high-product and integer division/remainder
proofs against actual native v2 results and masked writes. [Local retirement](Airbender/Proofs/MulDiv/Execution.lean)
transports real native cell histories through Sail's own nextPC preparation and
PC retirement, identifying the complete actual after-state. Original discarded
x0 operations and source/destination aliases are retained.

[The native PC proof](Airbender/Proofs/MulDiv/PC.lean) checks actual Boolean,
carry and inverse gates, deriving both successor bounds and modular RV32 PC+4.
[A full imported native row](Tests/MulDivPC.lean) satisfies every equation and
lookup while wrapping 0xfffffffc to zero. [All sixteen initialized cases](Tests/MulDivExecution.lean)
execute the original four clauses, including zero divisors and x0 writes that
still retire PC. [The actual alias sequence](Tests/MulDivRegisterChain.lean) now
executes and retires the second original MUL from PC four to eight after its
real prefix update.

These are original local instruction transitions over constructed histories.
Complete finite fetched MUL/DIV execution still needs stateful-decoder-aware
composition; no fetched wraparound program or new Rust export is claimed.
Physical initialization, general Rust/JSON/compiler refinement, cryptographic
argument enforcement, unified execution/protocol spans and completeness remain
separately scoped. No native defect is established by this checkpoint.

## Complete fetched MUL/DIV execution

[The short public fetched-execution theorem](Airbender/Review/Trace/Families/MulDiv/FetchedExecution.lean)
now derives a finite original Sail execution from actual public initialization
to the native terminal PC and register values. Every step fetches public bytes,
runs original stateful decoding in its real pre-state, and uses original MUL,
MULHU, DIVU or REMU preparation/execution/retirement. Actual native equations,
full decoder membership and initialized matching derive all operand reads,
ranges, masks, row order, intermediate states and PC boundaries. Terminal PC
bounds come from native successors or the public initial PC for an empty trace.

[Stateful composition](Airbender/Proofs/Trace/StatefulComposition.lean) adapts the
existing native row induction and reuses the unchanged original decoder-frame
proof. It derives replay through PC bookkeeping from actual misa preservation;
the public claim has no pure-decoder, separate ISA-read, replay or per-row step premise.
[Family assembly](Airbender/Proofs/Trace/Families/MulDiv/Composition.lean) reuses
actual code/configuration frames, native clocks, real history splitting and the
unchanged shared terminal-state/read proof. The prior pure composition helper
and original Sail/Clean semantics remain unchanged.

[Complete regressions](Tests/MulDivFetched.lean) cover all sixteen initialized
cases, concrete terminal arithmetic values, original x0 discards, unsigned
zero-divisor behavior and empty execution. The actual newest-first two-MUL
alias program now fetches/decodes after a real prefix update and reaches PC
eight with x1 and x3 equal to 861, without supplied intermediate or final-state
premises. The previous stale-timestamp negative test remains rejected by native
memory matching.

The local native PC proof retains aligned RV32 rollover; this checkpoint adds
no fetched wraparound fixture or new Rust export. Physical initialization,
general Rust/JSON/compiler refinement, cryptographic argument enforcement,
unified execution/protocol spans and completeness remain separately scoped.
Shift/binop and subword memory are next. No native defect is established.

## Actual native shift/binop decoder data

[The short public data certificate](Airbender/Review/Trace/Families/ShiftBinop/NativeDecoder.lean)
connects actual Rust preprocessing/materialization to independently read public
bytes and original Sail decoding for twelve ordinary register/immediate forms,
their twelve original x0 variants and an unsupported ADD hole. Every one of the
1,048,576 exported rows is checked. [Internal proofs](Airbender/Proofs/ShiftBinop/NativeSetup.lean)
check the small prefix and actual stored sentinel blocks structurally, reusing
existing sparse setup and column proof structure with no table-equality premise.

The native v2 profile retains x0 destinations, uses full sign-extended 16-bit
binary immediate limbs, and retains SRAI funct7 bits (shift 31 gives immediate
1055). Its operation mask/tag encoding differs from v3. [Regressions](Tests/ShiftDecoder.lean)
check those differences and unsupported constructors. Actual exporter runs
reproduce both fixture and binary-text output, reject unsupported REV8/rotate
and illegal RV32 shift words, and confirm filtering with an empty CSR allow-list.
Strict import profiles reject malformed data and crossed arithmetic/control exports.

This is a finite native decoder-data certificate. Dynamic lookup selectors and
the large shift/binop tables still require a checked constraint import; the
compiled importer continues rejecting them. Shift/binop circuit soundness,
initialized execution, custom CSR/oracle semantics, general Rust/compiler
refinement and cryptographic enforcement remain separate. No native defect is
established. The next checkpoint is native dynamic table import and membership.

## Native zero and binary lookup rows

[Two short public helper claims](Airbender/Review/Helpers/Tables/NativeBinary.lean)
now identify original Clean XOR/OR/AND membership with actual native tagged rows
and derive both byte-key bounds and the exact bytewise result. The actual Rust
driver exports the complete low-ID prefix: zero plus tables 4/6/7 at offsets
0/1/65537/131073. Reproduction checks those offsets against the native compiled
layout. All 196,608 binary rows and the conditional zero row are certified.

[Output certificates](Airbender/Proofs/Tables/BinaryXorCertificate.lean) reuse
the source's full literal-block kernel-check structure; OR and AND have matching
certificates. [Geometry](Airbender/Proofs/Tables/BinaryColumns.lean) proves actual
periodic keys, tags and block coverage structurally. [Internal assembly](Airbender/Proofs/Tables/Binary.lean)
connects these to exact native membership and bitwise results without supplied
bounds, output values or table-equivalence premises. Two generic source proof
modules and the mathematical byte-operation definition are copied unchanged.

[Regressions](Tests/NativeBinary.lean) retain native offsets/zero data, cover
complementary and terminal byte keys and reject byte 256 or a changed XOR result.
Strict import profiles reject malformed prefix data and crossed control/mul-div
artifacts. The combined geometry check initially hit Lean's allocation cap;
splitting it and replacing evaluated coverage with source-shaped structural
geometry resolved it under the unchanged caps.

This closes the native binary-table prerequisite. Dynamic selectors, large
16-bit shift tables, custom CSR/oracle semantics, shift/binop circuit soundness
and initialized execution remain unfinished. General Rust/JSON/compiler and
physical cryptographic enforcement remain separate; no native defect is established.

## Native truncation, padded range and sign-fill rows

[Four short public helper claims](Airbender/Review/Helpers/Tables/NativeShiftScalars.lean)
connect original Clean membership to actual native truncation, sign-fill and
zero-padded range rows. They derive input/limb bounds, low-five-bit truncation,
both zero padding fields and the exact RV32 sign-fill mask. Negative input at
shift zero yields an empty mask, matching the native unbounded shift by 32.

[Actual exported data](artifacts/setup/shift-scalars-native.json) contains all
2,228,224 selected rows, including the complete 2,097,152-row sign-fill table.
Native IDs 47/52/53 retain compiled offsets 200705/8654849/10752001; unexported
regions are not erased from placement metadata. Rust materializes and drops each
selected table separately, verifies its lossless compression and JSON roundtrip,
and reproduction compares the artifact and offsets with the pinned native layout.

[Internal geometry](Airbender/Proofs/Tables/ShiftScalarColumns.lean) reuses the
unchanged affine getters and periodic-column proof. [Lower](Airbender/Proofs/Tables/SignFillLow.lean)
and [upper](Airbender/Proofs/Tables/SignFillHigh.lean) sign-fill proofs select actual
constant blocks over 64 symbolic half-limb domains; they do not enumerate two
million rows. [Independent mask arithmetic](Airbender/Proofs/Tables/ShiftScalarBounds.lean)
and [membership assembly](Airbender/Proofs/Tables/ShiftScalars.lean) supply the
short public claims without output, range or table-equivalence premises.

[Regressions](Tests/NativeShiftScalars.lean) cover truncation/range terminal keys,
negative shifts zero/one/sixteen/31, positive sign boundary and changed results,
nonzero padding and oversized packed keys. The combined upper-mask proof reached the resident ceiling; splitting it into
four independent 16-domain certificates resolved the calculation without raising
resource limits. Strict import rejects crossed profiles,
wrong native tags/offsets, missing or noncanonical columns and incomplete extents.

This closes the native scalar/sign-fill table prerequisite. Four large logical
shift tables and dynamic constraint import remain next, followed by numerical
family soundness and initialized execution. Custom CSR/oracle semantics, general
Rust/JSON/compiler refinement and cryptographic enforcement remain separate.
No native implementation defect is established.

## Native low-input logical right shift

[Two short public helper claims](Airbender/Review/Helpers/Tables/NativeSrlLow.lean)
connect original Clean membership to every actual native low-input SRL row.
Membership derives the packed-key/output bounds, zero high output and exact
RV32 logical-right-shift result of the zero-extended 16-bit input limb. No
bounds, output values or table-equivalence premises are supplied.

[The native export](artifacts/setup/shift-srl-low-native.json) retains ID 50,
compiled offset 4460545 and all 2,097,152 rows. The existing regional exporter
now shares its unchanged native-generation/codec pipeline with this profile.
Reproduction checks the entire artifact and actual compiled offset, and retains
byte-identical output for every existing native profile. Strict import rejects
changed tags/offsets, field/profile/version, incomplete or noncanonical columns,
wrong extents and crossed binary/scalar/control/mul-div profiles.

[Actual stored-block partitions](Airbender/Proofs/Tables/SrlLowParts.lean)
retain all 74 blocks and their exact extents. Six source-shaped output
certificates, beginning with [the affine/periodic prefix](Airbender/Proofs/Tables/SrlLowPart0.lean),
prove all block entries symbolically. They reuse unchanged affine and periodic
getters and the original block checker, avoiding two-million-row enumeration.
[Independent arithmetic](Airbender/Proofs/Tables/SrlLowMath.lean) connects division
by powers of two to the standard RV32 bitvector shift; [internal assembly](Airbender/Proofs/Tables/SrlLow.lean)
combines this with actual native keys, padding, tags and complete membership.

[Regressions](Tests/NativeSrlLow.lean) cover shifts zero/one/fifteen/sixteen/31,
the final surviving bit and its lower boundary, the actual final native row,
and malformed output/high-padding/packed-key queries. All certificate modules
use the same serial Lean and sampled watchdog ceilings.

This closes one of the four native logical-shift table connections. The two
left-shift tables and high-input right-shift table remain, followed by faithful
dynamic lookup import, numerical family soundness and initialized execution.
Custom CSR/oracle semantics, general Rust/JSON/compiler refinement and
cryptographic enforcement remain separate. No native defect is established.

## Native high-input logical left shift

[Two short public helper claims](Airbender/Review/Helpers/Tables/NativeSllHigh.lean)
connect original Clean membership to all actual native high-input SLL rows.
Membership derives packed-key/output bounds, zero low output and exact wrapped
RV32 logical-left-shift semantics for the input limb placed in bits 16–31.
The whole word is reconstructed as a bitvector from its canonical limb; no
whole-word Mersenne31 cast, output bound or table-equivalence premise is supplied.

[The native export](artifacts/setup/shift-sll-high-native.json) retains ID 49,
compiled offset 2363393 and all 2,097,152 rows. The unchanged selected-table
pipeline obtains values/tags from the native Rust API and placement from the
pinned compiled layout. Reproduction checks the complete artifact and preserves
byte-identical output for all previous native profiles. Strict import rejects
changed metadata, noncanonical/incomplete columns and crossed profiles.

[Structural geometry](Airbender/Proofs/Tables/SllHighParts.lean) retains all 74
actual blocks and six exact partitions. Ten stored templates use the source raw
array helpers and kernel checks of at most 64 queries per calculation. The
largest template contains 1024 entries; the combined templates contain 2046.
[Symbolic periodic assembly](Airbender/Proofs/Tables/SllHighPart4.lean) is proved
over arrays before instantiating those checked sizes/values. Direct imported-data
normalization reached the resident/Lean allocation limits; this staging keeps
the same ceilings and avoids two-million-row enumeration. Every limit/failure
left no owned surviving worker.

[Independent arithmetic](Airbender/Proofs/Tables/SllHighMath.lean) connects the
result to the standard RV32 bitvector shift and truncation. [Internal assembly](Airbender/Proofs/Tables/SllHigh.lean)
combines actual keys, zero padding, tags, full output certificates and canonical
field values. [Regressions](Tests/NativeSllHigh.lean) check shifts zero/one/fifteen/
sixteen/31, top-bit loss, the last surviving bit and its next-bit boundary,
and malformed output/low-padding/packed-key queries. Discarded bits match RV32;
no native implementation defect is established.

Native low-input SLL and high-input SRL remain, followed by faithful dynamic
lookup import, numerical family soundness and initialized execution. Custom
CSR/oracle semantics, general Rust/JSON/compiler refinement and cryptographic
enforcement remain separate.

## Native low-input logical left shift

[Two short public helper claims](Airbender/Review/Helpers/Tables/NativeSllLow.lean)
connect original Clean membership to every actual native low-input SLL row.
Membership derives the packed-key bound, both 16-bit output bounds and exact
RV32 left-shift semantics after reconstructing the low/high output limbs.
Carry across bit 16 and truncation past bit 31 follow from the native values;
no output bounds, table equivalence or desired shift result is assumed.

[The actual native export](artifacts/setup/shift-sll-low-native.json) retains
ID 48, compiled offset 266241 and all 2,097,152 rows. Strict literal import checks
its complete canonical four-column data and exact regional metadata. Native
reproduction preserves all previous profiles byte-for-byte; crossed SLL/SRL and
scalar/binary/control profiles reject.

[Checked reuse](Airbender/Proofs/Tables/SllLowColumns.lean) identifies the entire
low-output column with the previously certified native SLL-high output column.
[Structural geometry](Airbender/Proofs/Tables/SllLowParts.lean) retains all 145
high-output blocks: six symbolic prefix partitions and the existing 73-block
SLL-high suffix. [Generic certificate transport](Airbender/Proofs/Tables/BlockTransport.lean)
reuses those proved values after an independently proved shift-sixteen index
translation. [Arithmetic](Airbender/Proofs/Tables/SllLowMath.lean) reconstructs
RV32 results with standard quotient/remainder identities. Existing block
semantics, checked templates and native codec remain unchanged.
Direct imported-column normalization reached the resident watchdog limit;
structural list equality replaces it under unchanged ceilings. The watchdog
confirmed termination of every owned worker after that limit.

[Regressions](Tests/NativeSllLow.lean) check shifts zero/one/fifteen/sixteen/31,
first carry and its preceding input, the final surviving bit and the following
discard boundary, plus malformed low/high/limb/key queries. No native defect is
established. High-input SRL remains before faithful dynamic constraint import,
numerical family soundness and initialized execution; general Rust/compiler
refinement and cryptographic enforcement remain separate.

## Native high-input logical right shift

[Two short public helper claims](Airbender/Review/Helpers/Tables/NativeSrlHigh.lean)
connect original Clean membership to all 2,097,152 actual high-input SRL rows.
Membership derives the packed-key and both output-limb bounds, then exact RV32
logical-right-shift semantics for the input placed in bits 16–31. Reconstruction
uses canonical limbs; no whole-word Mersenne31 cast, desired result or
table-equivalence premise is supplied.

[The actual native export](artifacts/setup/shift-srl-high-native.json) retains
ID 51 and compiled offset 6557697. Strict literal import preserves its complete
four-column data; native reproduction preserves every prior profile byte-for-byte.
Crossed profiles, changed metadata, incomplete/noncanonical data and unknown fields
reject. Compiler/JSON/Rust refinement remains a separate fidelity boundary.

[Checked reuse](Airbender/Proofs/Tables/SrlHighColumns.lean) identifies the entire
high-output column with native SRL-low. [All 146 low-output blocks](Airbender/Proofs/Tables/SrlHighParts.lean)
retain their actual geometry: the initial zero block spans 65,537 rows, ten
periodic templates start one word into each shift and the first shift-eleven
affine block has 2,047 rows. Ten structural template proofs use kernel checks of
at most 64 stored entries per calculation. Five symbolic prefix partitions and
[unchanged generic transport](Airbender/Proofs/Tables/BlockTransport.lean) reuse
73 native SRL-low blocks after an independently proved shift-sixteen translation.
[Arithmetic](Airbender/Proofs/Tables/SrlHighMath.lean) derives both reconstructed
limbs and standard bitvector semantics without two-million-row enumeration.

[Regressions](Tests/NativeSrlHigh.lean) check rotated-template/cross-shift edges,
the shortened affine/reset boundary, shifts zero/one/fifteen/sixteen/31 and final
surviving bits, plus malformed low/high/limb/key queries. No native defect is
established. Helper membership/results are now checked for all four native
logical-shift limb tables. Faithful dynamic constraint import, numerical family
soundness and initialized shift/binop execution remain unfinished; general
Rust/compiler refinement and cryptographic enforcement remain separate.

## Validation

Current checked checkpoint:

- Library, both CLI entrypoints and all one hundred and thirty-seven concrete test modules pass.
- Importer regressions: 492 checks pass.
- Axiom audit: 2291 explicit roots; only propext, Classical.choice and Quot.sound.
- All one hundred and thirty-seven public Review theorems (forty-six circuit claims, sixty-four trace claims and twenty-seven helper claims including the two reused port-representation lemmas) have explicit axiom roots; guide references, links and layering checks pass.
- Source provenance: 79 unchanged reused files, six native circuit artifacts, fifty native Rust sources plus compiled shift-offset metadata, twenty-one native setup artifacts and four exporter source/manifest/lock files.
- Aliased sources/destination form a nonempty accepted history. A stale alias
  read passes local constraints and is rejected by logical memory matching.
- Public Sail x1/PC reads construct the accepted alias fixture; missing register and byte data reject construction.
- Original-opcode SUB-to-x0 with nonzero source operands passes native constraints and the public Sail theorem.
- Actual ADD bytes build a padded setup and yield public Sail source evidence and native read/terminal bounds. The retained padding is rejected by native equations. A bad zero flag passes local constraints and makes an unbounded write, but lookup membership rejects it.
- U-type raw funct3, sign-extended ADDI, original-opcode x0 decoding and invalid setup capacity regressions pass.
- Actual Sail history realizes the alias fixture; all three reads use the instruction pre-state and the destination writes 246. An initialized original SUB-to-x0 fixture retains nonzero operands/raw result and its masked write is an actual Sail stutter.
- The accepted public alias fixture derives all PC inputs/successors and its terminal bound. An empty-row fixture derives its terminal bound from the actual public initial PC. The native wraparound regression passes through the factored column-only calculation.
- The accepted alias ADD now reaches original Sail retirement with all local interfaces derived. Actual SUB bytes construct the x0 setup; original SUB-to-x0 retires PC+4 with the native data stutter, without caller-supplied operand or Sail-read interfaces.
- Complete execution passes on the alias ADD, original SUB-to-x0 and empty trace. Reversed dependent ADD/ADDI witness rows derive a finite original Sail trace reaching PC 8 and x2=247; no intermediate read/state or final-value premise is supplied.
- Full native RAM load/store and ROM load rows pass, including x0-masked ROM loads. Native UNIMP padding is retained; changed ROM values, unaligned addresses and ROM stores are rejected. Fixed-query arity, table selection and column mapping fail-closed regressions pass.
- Non-padding public ROM data loads both actual write limbs. Native source-plus-immediate address addition, PC increment and clock order pass on full rows; a native witness simultaneously wraps address and PC from 0xfffffffc to zero. Local row interfaces retain explicit inputs; initialized history now derives native clock inputs and word ranges.
- Actual LW/SW bytes and nonempty accepted word-memory traces recover public original Sail source evidence, including LW to x0. Full minus-one padding is retained/rejected by the native store-mask equation. Negative immediates, unsupported subword/unsigned constructors, missing bytes and insufficient capacity are checked. A flag-2 row passes native constraints but fails full decoder membership.
- Actual public LW bytes construct a ROM image; a full native ROM-load row recovers those bytes through the public Sail read theorem. Consistently altered native ROM data is rejected. Native UNIMP tail entries remain present while absent Sail padding bytes remain actual failures. Missing bytes and excessive counts reject extraction.
- Nonempty public LW/SW and x0/ROM-shadow fixtures derive complete Clean history, newest reads, every row/prior clock input and all native word ranges. Actual public bytes build the decoder setup. Omitting a discarded shadow read's initialization token fails logical matching. The shadow fixture explicitly initializes the logical native RAM cell; architectural ROM projection is not claimed.
- Initialized public LW/SW/x0/ROM-shadow fixtures derive native effective addresses, incoming PC ranges/alignment, bounded modular successors and clock/port order through the existing calculations, without local numerical premises.
- Actual source-GPR reads, RAM-load register writes, RAM-store byte writes and x0/ROM-shadow cell stuttering are derived from nonempty initialized histories. Reversed dependent SW/LW rows construct real public decoder bytes and derive an intermediate store state, subsequent read of 123 and destination register write; no intermediate state/read or final-value premise is supplied. These are cell-transfer results, not original instruction execution claims.
- Ordinary and x0 ROM-load shadow ports satisfy the general native value-preservation theorem. A real changing RAM store is excluded from every address in the readonly shadow region. Native matching/initialization obligations remain intact.
- Whole-address Clean projection preserves consistency and newest writes. Separate architectural/ghost initialization derives native clocks, unique addresses and x0 preservation without reading shadow bytes from Sail. Accepted ordinary/x0 ROM loads retain their native shadow event, derive actual masked Sail register writes and final architectural matching, even with missing shadow bytes and distinct native shadow/ROM values. No expected read, intermediate state or table-equivalence premise is supplied. This does not bind physical zero boot or prove original LOAD/STORE execution.
- The projected initializer also derives every full native read, actual write and terminal word bound using the existing shared decreasing-time induction and native decoder/mask rules unchanged. Ordinary/x0 ROM-load regressions retain bounds for shadow cells with no Sail bytes, without per-row/port range premises.
- The projected initializer and actual public decoder now discharge every native address/PC/clock interface through the same calculations as the full-image boundary. General retained-port transport derives original Sail source-GPR reads and actual masked writes for ordinary/x0 ROM loads with unreadable shadows. The reversed dependent RAM store/load regression now exercises retained RAM reads/writes through these same transport lemmas, deriving its intermediate state and later read unchanged.
- Initialized projected histories preserve all ROM-prefix byte entries and successful public ROM extractions. The reversed SW/LW regression derives a RAM change from zero to 123 while retaining both original instructions and their two-word public ROM image; missing byte 16 stays absent. Ordinary/x0 ROM loads retain absent shadow bytes and their full native shadow refreshes. Code-window bounds come from actual indexed setup construction under the public native-ROM program-size bound; no expected later fetch is supplied.
- Public Machine/PMP/PMA configuration now survives complete initialized projected native histories. The same reversed SW/LW fixture initializes actual public CSRs and reaches original Sail virtual-memory store/load results through checked translation, permissions and platform helpers. Native matching and public construction derive all source/address/value/intermediate-state inputs. Original ROM/RAM clauses and row preparation/retirement are now checked below; general trace composition is now checked above.
- Initialized ordinary/x0 ROM fixtures derive actual extraction, original virtual reads and original LW clause execution to the actual masked-write after-state. Native shadow value 123 stays matched and differs from the actual loaded ROM word 0xc0001073. No expected-read/value or desired-state premise is supplied; original x0 decoding is retained. Original RAM clauses and row preparation/retirement are checked below; general trace composition is now checked above.
- The unchanged reversed accepted native SW/LW fixture now reaches the original instruction clauses in its derived states. Native/public construction supplies selectors, source/address facts and actual reads. The later load reads the real preceding store value 123 and reaches the actual destination write; no intermediate state, expected read or desired result is supplied. All previous cell, code, ROM and virtual-memory regressions remain intact.
- The same original clauses now pass native row preparation/retirement. Ordinary/x0 ROM loads retain actual memory behavior and reach native PC 4; reversed SW/LW normal steps start from the actual public Sail state and reach PC 8, RAM 123 and x3=123 from native terminal matching. The combined proof derives addresses/native successors and dispatches original instructions without per-row read, prepared-state or desired-PC inputs. General finite trace/fetch composition is now checked above.
- General fetched/decoded word-memory execution passes on reversed dependent SW/LW, ordinary/x0 ROM loads and an empty native trace. The same general relation reaches actual PC 8 and native terminal RAM/x3=123. Native matching retains independent shadow value 123 while actual ROM reads 0xc0001073. All local address domains are derived from public cells/seeds; no per-row range/read/order/state/result premise is supplied.
- Fixed-zero native boot passes on original ordinary/x0 LW fixtures with all actual GPRs zero, real public instruction/ROM bytes and fully matched zero native shadows. General execution derives PC four and actual masked destinations; full native paths derive terminal shadow zero. Invented seed values and an actual nonzero public GPR are rejected. Symbolic padding checks retain input words and distinguish zero loader padding from raw-table UNIMP fallback; absent Sail padding bytes remain actual failures.
- Explicit Sail byte padding derives full four-MiB extraction, original zero-profile/configuration/setup preservation and complete native boot execution on ordinary/x0 loads. Prefix and out-of-ROM bytes are retained, the last ROM byte is zero and a formerly missing tail word becomes readable. Missing/oversized supplied prefixes reject construction. All large extents are handled symbolically; no evaluated large certificate or supplied padding/coverage/read/state/result premise is used.
- Exact setup metadata for both native artifacts and fifteen added importer regressions pass. The active four-column tagged row model has exactly the existing ROM/separator meanings, including every dummy/padding tuple. Nonempty original Sail bytes and explicit zero padding derive actual reads from tagged ROM membership; altered words and wrong padding tags are rejected. The normalized final setup row is explicitly outside this model's lookup domain; actual Rust/export/LDE and argument correspondence remains separate.
- The standalone native exporter passes offline locked checking and exact fixture reproduction. Little-endian binary image/text inputs reproduce the fixture; partial words and oversized inputs reject before output. Lean certifies all actual regional ROM/separator/range values, the entire unsupported decoder tail and the loader's image zeros; original LW/SW/x0 and explicit UNIMP/sentinel regressions pass. Compressed-field, extent, region, tag and unknown-field mutations fail closed. Parse/emission, general Rust/compiler refinement and physical trace/LDE/argument connections remain separate.
- Sparse public construction retains actual unsupported interior words at their original PCs and rejects missing/effectful inputs. Native equations derive hole/tail exclusion, original Sail sources, canonical decoder words/alignment and exact x0 flags. The second native export reproduces exactly and its entire decoder matches constructed public Sail data. A full native x0-load constraint witness at PC 12 recovers actual source evidence beyond the UNIMP hole; missing bytes/capacity and all post-hole fields pass. Sparse initialized execution and arbitrary-program Rust refinement remain separate.
- Sparse initialized original execution passes with real code/register/CSR/RAM bytes, complete native matching and actual exported slot-three membership. The existing full x0-load witness starts at public PC 12, retains the PC-four hole, and derives terminal PC 16, RAM 123 and x0 zero. The same strict initialized execution, boot and padding regressions remain intact.
- Both shared scalar prefixes reproduce exactly from the native API/extracted timestamp clause. Symbolic proofs cover every actual value and modeled active filler row, retaining repeated zero rows in the domain and excluding normalization. Existing Clean range helpers have proved exact membership connections. Prefix/padding/endpoints, both compiled placements and fourteen strict importer regressions pass. No full trace is evaluated; physical Rust/argument enforcement remains separate.
- Native control PC bounds pass for all five supported packed masks. A complete JAL -4 witness retains canonical target 0xfffffffc; its noncanonical high-limb variant passes all native polynomials and the other fifteen queries but is rejected by the actual candidate-high range query. No terminal range or verifier-PC closure premise is supplied.
- Public control decoding now derives all local decoder inputs from original Sail bytes and full sparse/padded membership. The full JAL -4 witness uses actual raw funct3 seven and derives outgoing PC bounds without a mask premise; tag-zero mismatch, x0 comparisons/jumps, all branch tags, unsupported holes/tail and missing bytes/capacity regressions pass. The malformed high-PC variant retains real public membership and all polynomials but fails the native range query. Initialized original control execution remains open.
- The native control decoder prefix reproduces exactly and every slot equals the actual public Sail constructor. Raw JAL tag 7, original post-hole SLTIU-to-x0 fields, public text, complete tail, crossed importer profiles and tag-zero rejection pass. The accepted full JAL row instantiates the short exported-decoder source/PC claim.
- Native control clocks and all three imported ports discharge the shared history contract. A full JAL -4 history starts from actual Sail x0/x1/PC reads, consumes its aliased readonly refresh and retains the actual link write. Stale local reads pass native constraints but fail memory matching; explicit missing-register data rejects initialization. Lower-clock carry, every derived port effect and exact terminal clock accumulation pass.
- No handwritten project warnings, admitted proofs or project axioms.
- Serial bounded gates pass; parent/child timeout and memory probes confirm termination with no live owned processes.

Run the [reproduction commands](README.md#reproduce) for the current checkpoint.

## Complete compiled shift/binop lookup projection

[The native artifact](Airbender/Review/Circuits/ShiftBinop/Artifact.lean) now imports
all 47 quadratic/three linear equations, eight timestamp queries and four dynamic
lookups. Physical witness selectors 24/28/32/36 resolve to logical variables
42/46/50/54 and remain evaluated fourth Clean query fields. Setup, decoder,
clock and all three direct memory ports have checked kernel bindings.

[The tagged table](Airbender/Review/Circuits/ShiftBinop/Tables/Native.lean) reads
all twelve actual exported regions in compiled offset order, spanning 10,817,537
rows. It retains the native zero row and every tag without inserting another
inactive row. [Structural inclusion proofs](Airbender/Proofs/ShiftBinop/NativeLookup.lean)
cover every row of every region. Existing binary/scalar/four-limb certificates
supply mathematical helper results separately. Direct closed-data regression
calculations hit Lean's allocation cap; structural row transport replaces them
under unchanged ceilings, with no surviving owned workers after the failure.

The CSR-properties region uses the exact native compilation-test generator:
nondeterminism enabled with an empty delegation CSR list. [Its actual data](artifacts/setup/shift-csr-properties-native.json)
retains ID 25, offset 196609 and all 4096 rows. Native source explicitly requires
separately configured CSR contents for proving/setup; this profile does not bind
runtime CSR setup or establish custom CSR/oracle/delegation execution semantics.
The strict regional importer rejects an unbound runtime profile.

[Kernel regressions](Tests/ShiftArtifact.lean) check all query expressions,
selector evaluation, metadata/placements and actual zero/CSR/final native rows.
[Importer regressions](Tests/ArtifactImport.lean) reject missing/extra/wide/short
queries, crossed/unknown selectors, unmapped/aliased physical variables, changed
offsets/extents and malformed/crossed CSR data. All native profiles reproduce
byte-for-byte. This closes the concrete local import prerequisite; numerical
shift/binop soundness and initialized original Sail execution remain unfinished.
General Rust/JSON/compiler refinement and cryptographic argument enforcement
remain separate. No native implementation defect is established.

## Accepted native shift/binop lookup resolution

[The short lookup claims](Airbender/Review/Circuits/ShiftBinop/Lookups.lean)
now extract all four actual tagged queries from original Clean constraint
acceptance. The fourth fields are the evaluated witnesses at logical columns
42/46/50/54. Accepted canonical selectors lie exactly in the twelve stored tags;
[structural partition and tag uniqueness](Airbender/Proofs/ShiftBinop/NativeRegions.lean)
exclude cross-region substitution across all 10,817,537 actual rows.

[Resolution assembly](Airbender/Proofs/ShiftBinop/NativeResolution.lean) derives
exact binary/scalar/four logical-shift helper membership from each selected tag.
Existing helper result proofs therefore apply directly to accepted native queries,
without a table-equivalence or desired-result premise. Tag zero requires all
three fields to be zero; it does not disable arbitrary inputs or outputs. The
CSR tag resolves only the recorded compilation fixture, with the runtime setup
and custom instruction boundaries unchanged.

[Combined-table regressions](Tests/ShiftLookups.lean) cover valid binary and all
shift-table boundaries, incorrect results/selectors, unsupported tags, nonzero
inactive data, crossed SLL regions and canonical field selector wraparound.
These are checked lookup connections, not complete numerical circuit or
initialized shift/binop Sail execution. Operation routing and row/state assembly
remain the next milestone. No native implementation defect is established.

## Decoded native shift/binop operation routing

[The short routing claim](Airbender/Review/Circuits/ShiftBinop/Routing.lean)
now connects original public-byte construction and actual native decoder membership
to all four table selectors, register/immediate operand selection and zero ordinary
delegation-request multiplicity. [Observable references](Airbender/Review/Circuits/ShiftBinop/RoutingModel.lean)
retain the six native bits and distinct raw funct3. SLL uses tags 47/48/49/0,
SRL 47/50/51/0 and SRA 47/52/50/51; each binary form uses its original funct3
in all four slots. SRAI retains the native immediate's funct7 payload.

[Selector recovery](Airbender/Proofs/ShiftBinop/Selectors.lean) derives Booleanity
and a canonical mask at most 63 from actual equations. [Original source recovery](Airbender/Proofs/ShiftBinop/Decoder.lean)
excludes unsupported slots and the complete minus-one tail. [Routing assembly](Airbender/Proofs/ShiftBinop/Routing.lean)
derives the observed tags and operands without supplied operation bits, table
choices, output values or a table-equivalence premise. Logical column 37 is the
native request multiplicity; its zero value for ordinary forms does not establish
worker/request protocol soundness or custom CSR semantics.

[Regressions](Tests/ShiftRouting.lean) check complete native constraints and all
lookups for twelve ordinary forms and their x0 variants, then apply the public
claim using actual original byte reads. All 96 fixture queries have native-table
membership certificates. Six [four-row groups](Tests/ShiftRoutingPart0.lean) keep
closed equation checks and symbolic native query transport within unchanged
budgets. Wrong sign-fill tags, wrong immediate selection and injected CSR bits
reject. Numerical word results, actual Sail register reads, initialized family
history/execution and runtime CSR setup remain separate. No native defect is
established.

## Native binary numerical results and actual x0 writes

[The short public binary claim](Airbender/Review/Circuits/ShiftBinop/Binary.lean)
now derives exact native XOR/OR/AND results for register and immediate forms from
original public-byte construction, native decoder membership and accepted native
constraints. [References and observables](Airbender/Review/Circuits/ShiftBinop/BinaryModel.lean)
retain the actual first-source limbs, selected second operand, selected result
and masked destination write. Both input words and the selected result are
bounded conclusions, including when the decoded destination is x0.

[Four-query extraction and native equation assembly](Airbender/Proofs/ShiftBinop/BinaryQueries.lean)
retain the actual Mersenne31 inverse of 256, 8388608. Every accepted byte key and
result is below 256; native equations therefore reconstruct six canonical limbs.
[Word assembly](Airbender/Proofs/ShiftBinop/BinaryValues.lean) uses original bitvector
concatenation lemmas to prove exact RV32 operations, preserving full word values
above the field modulus. [Actual masking and decoded assembly](Airbender/Proofs/ShiftBinop/BinaryResults.lean)
derive discarded x0 writes from native destination equations and the public
entry's zero flag. No operand-bound, selected-output, table-equivalence or
individual operation-bit premise is added to the public claim.

[Regressions](Tests/ShiftBinary.lean) reuse complete accepted native fixtures for
all twelve binary register/immediate/x0 cases, apply the public result root and
retain negative immediates, full RV32 values above Mersenne31 and nonzero selected
results discarded at x0. Corrupted byte reconstruction, selected limbs and x0
writes reject. No native implementation defect is established. Native shift
numerical assembly, family clocks/ports, initialized register/history transport
and original Sail instruction execution remain open. Runtime CSR setup, worker
protocol enforcement, cryptography and general Rust/JSON/compiler refinement
remain separate boundaries. The preceding sections are earlier checkpoints.

## Native shift contributions and selected-word assembly

[The short shift contribution claim](Airbender/Review/Circuits/ShiftBinop/Shifts.lean)
now derives the actual native low-five-bit truncation, all three contribution
slots and exact selected-word assembly for SLL/SRL/SRA and their immediate forms.
[References and observables](Airbender/Review/Circuits/ShiftBinop/ShiftModel.lean)
retain actual key/result columns, source columns and native slot order. The first
query bounds the selected low operand below 65536, computes its remainder modulo
32 and forces its padding field to zero.

[Native equation assembly](Airbender/Proofs/ShiftBinop/ShiftEquations.lean) recovers
each packed source/amount field equation from accepted constraints. [Contribution
resolution](Airbender/Proofs/ShiftBinop/ShiftParts.lean) connects each actual tagged
query to the checked native SLL/SRL/sign-fill helper and derives key bounds, both
output-limb bounds and exact canonical-key RV32 contributions. SLL/SRL's inactive
third slot is the literal native zero row. SRA uses sign fill, low-input SRL and
high-input SRL in that order. [Selected assembly](Airbender/Proofs/ShiftBinop/ShiftContributions.lean)
lifts both native three-limb sums without Mersenne31 wrap and derives exact RV32
addition of the contributions; no preselected result or input-range premise is
added to the public claim.

[Regressions](Tests/ShiftContributions.lean) reuse complete accepted native rows
for all twelve shift register/immediate/x0 cases and apply the public root.
SRAI retains encoded immediate 1055, truncates to 31 and combines 0xfffffffe,
zero and one. SLLI/SRLI shift-31 and discarded x0-selected values pass; corrupt
packed keys, nonzero inactive contributions and omitted sign fill reject.
This checkpoint states contributions of actual canonical packed keys. Binding
their quotient/remainder to initialized bounded source reads, canonical selected
limbs and complete architectural shifts remains unfinished, as do family clocks,
initialized register/history transport and original Sail instruction execution.
Runtime CSR setup, worker protocol enforcement, cryptography and general
Rust/JSON/compiler refinement remain separate. No native defect is established;
earlier sections retain their checkpoint scope.

## Native shift/binop initialized clocks and memory history

[The short public history claim](Airbender/Review/Trace/Families/ShiftBinop/History.lean)
now derives complete Clean memory consistency and latest preceding reads for
all three native ports from original Sail public register/PC seeds and accepted
native state/memory matching. The [native registry](Airbender/Review/Helpers/Context/ShiftBinop.lean)
retains the actual constraints, decoder metadata, clock columns and memory ports.
[Metadata checks](Airbender/Proofs/ShiftBinop/ClockMetadata.lean) retain the complete
10,817,537-row tagged setup geometry. [Clock extraction](Airbender/Proofs/ShiftBinop/Timestamp.lean)
uses the actual two carry equations and all eight timestamp queries. The
[shared instance](Airbender/Proofs/Trace/Families/ShiftBinop/History.lean) derives
four-tick advancement, strict port order and all row/prior bounds and alignment
from initialization and matching. No local clock, schedule or expected-read
premise is added to the public claim.

[Complete initialized regressions](Tests/ShiftHistoryFixture.lean) check state
and memory permutations for all twenty-four ordinary register/immediate/x0 rows,
with original Sail seeds for x0, x1, x2, x3 and PC. [Native local checks](Tests/ShiftHistoryRows.lean)
correct only the last prior-clock column for six immediate/x0 aliases: the second native port
refreshes x0 at time five, which the destination port must consume. All fifty
native equations, eight timestamp queries and four unchanged tagged queries
pass. All six stale alternatives satisfy local constraints but fail native
logical memory matching. [Public applications](Tests/ShiftHistory.lean) derive
complete history, latest reads and clock inputs without separately supplied
bounds, alignment or ordering. This confirms the required matching behavior;
no native implementation defect is established.

Source-word bounds and canonical packed-key binding remain unfinished, as do
actual Sail cell transfers and original shift/binop instruction/fetched execution.
Runtime CSR setup, worker protocols, cryptography and general Rust/JSON/compiler
refinement remain separate boundaries. Earlier sections retain their checkpoint
scope.


## Initialized shift/binop word bounds and canonical source keys

[The short value claim](Airbender/Review/Trace/Families/ShiftBinop/Values.lean)
now derives every native read, actual write and terminal word range from original
public code construction, actual Sail seeds/PC and accepted native matching.
[Native write preservation](Airbender/Proofs/Trace/Families/ShiftBinop/Values.lean)
uses full native decoder membership to select binary results or shift sums and
retain the exact x0-masked destination. Readonly ports keep their actual refreshes.
The unchanged shared time induction supplies the earlier source bounds; no
per-row operand/read/range or desired-result premise is added.

[Internal limb references](Airbender/Proofs/ShiftBinop/LimbModel.lean) preserve two
native 16-bit source limbs, all 32 shift amounts and SRA's sign-fill/low/high
order. Separate [SLL](Airbender/Proofs/ShiftBinop/SllLimbBounds.lean),
[SRL](Airbender/Proofs/ShiftBinop/SrlLimbBounds.lean) and
[SRA](Airbender/Proofs/ShiftBinop/SraLimbBounds.lean) calculations prove that every
actual contribution half sum is canonical, including both sign domains. No v3
byte-table layout or unchecked overlap assumption is used.

[The short source claim](Airbender/Review/Trace/Families/ShiftBinop/Sources.lean)
now derives exact natural packed-key values and their source/amount remainders
and quotients, together with actual source/selected bounds. [Observables](Airbender/Review/Circuits/ShiftBinop/SourcesModel.lean)
retain actual native columns and literal inactive zero slots. [Field lifting](Airbender/Proofs/ShiftBinop/ShiftSourceBounds.lean)
uses initialized source bounds to exclude Mersenne31 wrap; [trace assembly](Airbender/Proofs/Trace/Families/ShiftBinop/Sources.lean)
combines those bounds with original decoded entries and accepted contributions.
Canonical-source binding is derived, rather than postulated.

[Original-byte fixtures](Tests/ShiftValuesFixture.lean) preserve the actual native
25-slot public program and replay the unchanged original Sail decoder after GPR/PC
updates with the same misa image. [Initialized applications](Tests/ShiftValues.lean)
cover all twenty-four ordinary/x0 rows and all twelve concrete shift cases,
including corrected readonly x0 alias clocks and bounded discarded selected words.
Whole architectural shift results, actual Sail cell/GPR transfers and original
instruction/fetched execution remain unfinished. Runtime CSR configuration,
worker protocols, cryptographic enforcement and general compiler refinement stay
separate. This is proof coverage, not a new defect finding; the findings bar and
historical coverage archive are unchanged.

## Initialized whole shift/binop numerical results

[The short public result claim](Airbender/Review/Trace/Families/ShiftBinop/Theorems.lean)
now derives exact canonical selected and actual destination limbs for all six
ordinary SLL/SRL/SRA/XOR/OR/AND families, including immediate forms and discarded
x0 writes. Actual public Sail code construction, public seed/PC reads, complete
native matching and full decoder membership supply all premises. No source/range,
operation-selector, desired-result or expected-write premise is supplied.

[Numerical references](Airbender/Review/Circuits/ShiftBinop/ResultsModel.lean)
retain whole RV32 operations and architectural low-five-bit shift amounts.
Separate [SLL](Airbender/Proofs/ShiftBinop/SllLimbResult.lean),
[SRL](Airbender/Proofs/ShiftBinop/SrlLimbResult.lean) and
[SRA](Airbender/Proofs/ShiftBinop/SraLimbResult.lean) calculations reconstruct
whole results from the actual native two-limb contribution order across all 32
amounts. SRA derives the architectural sign bit; its positive and negative
calculations use separate declarations to retain default proof budgets. No
memory or heartbeat ceiling is raised.

[Native assembly](Airbender/Proofs/ShiftBinop/Results.lean) combines canonical
source-key lifting with accepted contributions and exact decoded x0 masking.
It proves low-limb modulo 32 equals whole-operand low-five-bit extraction,
retaining SRAI's encoded funct7 payload. [Initialized assembly](Airbender/Proofs/Trace/Families/ShiftBinop/Results.lean)
supplies source bounds from the unchanged shared history induction and proves
every selected/write limb equals its canonical numerical result encoding.

[All twenty-four initialized regressions](Tests/ShiftResults.lean) apply the
public claim and derive concrete outputs for every ordinary/x0 fixture, retaining
negative SRA, shifts 31, SRAI 1055→31, XORI -1, ORI -2048 and ANDI 2047.
Original Sail cell/GPR transfers, instruction clauses, PC retirement and fetched
execution remain unfinished. Runtime CSR/worker protocols, physical cryptographic
enforcement and general compiler refinement remain separate. This is coverage,
not a new defect finding; the finding standard and historical archive are unchanged.

## Initialized original Sail shift/binop register histories

[The short public register-history claim](Airbender/Review/Trace/Families/ShiftBinop/Registers.lean)
now constructs actual original Sail GPR reads/writes, all native-clock-ordered
segment states, final cell matching and code/misa preservation from actual public
code/seeds/PC and full native matching/decoding. Public tracked-cell alignment
remains explicit. No expected read, intermediate state, result, write or decoder
replay is supplied. [Observables](Airbender/Review/Helpers/Memory/ShiftBinop.lean)
retain the first two readonly accesses and the actual masked destination port;
all three reads use the same real row pre-state, including aliases.

[Native x0 preservation](Airbender/Proofs/Trace/Families/ShiftBinop/ZeroRegister.lean)
uses the original rd/zero-flag lookup columns and actual mask equations 39/40,
with write columns 59/60. Readonly refreshes preserve their exact reads. The
unchanged shared decreasing-time and Clean-to-Sail realization/grouping proofs
derive the actual intermediate cell histories. [Source-entry recovery](Airbender/Proofs/Trace/Families/ShiftBinop/Decoder.lean)
uses the complete native padded decoder and rejects every sentinel-tail row.

[The three port transport declarations](Airbender/Proofs/ShiftBinop/PortReads.lean)
are copied unchanged from the pinned original source and checked against actual
v2 port/decoder metadata. [Code/configuration frames](Airbender/Proofs/Trace/Families/ShiftBinop/CodeHistory.lean)
use native register-space addresses and the unchanged original stateful Sail
misa-frame theorem to replay decoding after real GPR updates. [Internal assembly](Airbender/Proofs/Trace/Families/ShiftBinop/RegisterHistory.lean)
derives every row's source/destination transfers and all segment states.

[All twenty-four regressions](Tests/ShiftRegisters.lean) derive the original
entry from its actual native PC query, original Sail transfers, actual numerical
result writes and preserved code/misa. All twelve original x0 variants preserve
the entire Sail data state, including six immediate/x0 readonly aliases.
Original instruction clauses, PC preparation/retirement and complete fetched
execution remain unfinished. Runtime CSR/worker protocols, physical cryptographic
enforcement and general compiler refinement remain separate. This is coverage,
not a new defect finding; the findings bar and historical archive are unchanged.

## Initialized original Sail shift/binop clauses

[The short public clause-history claim](Airbender/Review/Trace/Families/ShiftBinop/Clauses.lean)
now derives original Sail clause execution for all six ordinary operations and
all twelve register/immediate forms from actual public code/initialization and
full accepted native matching/decoding. [Observables](Airbender/Review/Helpers/Memory/ShiftBinopClauses.lean)
retain original instructions, actual constructed GPR histories and the same
native row pre/post states. Source reads, source bounds, selected operands,
masked writes and intermediate states are derived rather than supplied.

[Internal clause assembly](Airbender/Proofs/ShiftBinop/Clauses.lean) executes the
original pinned register/immediate clauses through the unchanged original
dispatcher. Actual native routing and public immediate columns determine the
complete selected operand. Sign extension is retained; SRAI's original encoded
funct7 bits are proved to leave its architectural low-five-bit shift count
unchanged. Actual native numerical results and masked destination writes reach
the original clause's same after-state, including original x0 opcodes and aliases.
[Initialized assembly](Airbender/Proofs/Trace/Families/ShiftBinop/Clauses.lean)
derives source bounds and exact original entries from the existing initialized
history and actual original public decoding.

[All twenty-four complete regressions](Tests/ShiftClauses.lean) now construct
original Sail clause executions and actual native transfers with preserved
code/misa. All twelve original x0 variants actually execute and preserve the
whole data state, including all six immediate/destination aliases. Original
RV32 profile decoding still rejects shift amounts 32 and 63. PC preparation,
retirement and complete fetched execution remain next. Custom CSR/worker
protocols, physical cryptographic enforcement and general compiler refinement
remain separate. This adds coverage, with no new defect finding; the findings
standard and historical archive are unchanged.

## Initialized original fetched shift/binop execution

[The short public fetched-execution claim](Airbender/Review/Trace/Families/ShiftBinop/FetchedExecution.lean)
now derives finite original Sail execution and actual terminal PC/cell reads for
the selected ordinary SLL/SRL/SRA/XOR/OR/AND profile, including all twelve original
register/immediate forms and discarded x0 variants. Actual public bytes and
initialization, full accepted native matching/decoding and public tracked-cell
alignment are visible premises. No expected read/result, local PC bound or
alignment, intermediate state, decoder replay or table equivalence is supplied.

[Native PC assembly](Airbender/Proofs/ShiftBinop/PC.lean) uses the actual shift
carry gates, inverses and output equations 41..46 and Boolean indices 6/7. Original
public query/setup construction derives the incoming canonical aligned PC;
accepted native equations derive outgoing bounds and modular +4. [Complete row regressions](Tests/ShiftPC.lean) retain low-limb carry and full RV32 wraparound.
[Original retirement assembly](Airbender/Proofs/ShiftBinop/Execution.lean) transports
the actual native history through original nextPC preparation, the retained
original clause and original retirement. [The local public claim](Airbender/Review/Trace/Families/ShiftBinop/Execution.lean)
constructs all actual row states and retired steps; [observables](Airbender/Review/Helpers/Memory/ShiftBinopExecution.lean)
keep original dispatch, native states and the exact successor PC visible.

[Stateful fetched composition](Airbender/Proofs/Trace/Families/ShiftBinop/Composition.lean)
uses actual native GPR history to preserve code/misa and replay original decoding
in each actual pre-state. Native PC matching composes the original fetched normal
steps through arbitrary accepted finite row histories, including empty traces.
Raw terminal PC bounds follow from native/public matching. [All twenty-four retirement regressions](Tests/ShiftExecution.lean) derive actual states and all
twelve x0 retirements; [fetched regressions](Tests/ShiftFetched.lean) derive exact
terminal PCs and GPR values for every ordinary/register/immediate/x0 case, plus
empty execution from actual public initialization. Remaining ordinary/subword
memory coverage, runtime CSR setup, delegation and unified protocol/terminal
boundaries remain separately scoped. General compiler refinement and physical
cryptographic enforcement are unchanged boundaries. This is coverage progress;
no new native-v2 defect is established and the findings standard is unchanged.

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

## Historical coverage and boundary notes

The following 71 entries were accumulated in the former Findings register through
20 October 2026. They record successive proof checkpoints, scope boundaries and
positive/negative regressions. **They are not 71 defects or vulnerability findings.**
Earlier statements retain their snapshot scope; the latest sections above describe
subsequent completed connections. The [findings register](FINDINGS.md) now separates
confirmed defects, assessed exclusions, unresolved bindings and unassessed v3
candidates under the same standard as the pinned v3 review.

| Case | Evidence and disposition |
| --- | --- |
| V2 PC rollover | [Native rollover fixture](Tests/PC.lean) accepts PC 0xfffffffc to zero. The v2 proof preserves this modular behavior instead of importing the source artifact's no-overflow conclusion. [Public native PC assembly](Airbender/Review/Trace/PC.lean) now derives incoming alignment/bounds and outgoing/terminal bounds, retaining RV32 indexed-PC truncation. Actual Sail retirement and complete execution are checked below. This is a supported aligned path, not a reported implementation defect. |
| Local decoder/history interfaces | [Model](Airbender/Review/Circuits/AddSub/Model.lean) explicitly retains the packed decoder mask, x0 flag, preprocessing, input bounds, initial PC alignment and original Sail reads. [Selectors](Airbender/Proofs/AddSub/Selectors.lean) derives individual selector bits. Public decoding and initialized history now derive value/read/PC facts. [Decoded row assembly](Airbender/Proofs/Trace/Arithmetic.lean) now derives all local interfaces and original Sail row retirement. [Initialized arithmetic execution](Airbender/Review/Trace/Families/AddSub/Theorems.lean) now composes these rows to exact terminal PC/cells. Remaining families and physical argument enforcement are separate. |
| Native clock boundary | [Clock proof](Airbender/Proofs/AddSub/Timestamp.lean) derives native advancement and port order; all per-row/prior bounds and alignment now follow from accepted logical matching and only initial clock boundaries. Typed port/state metadata is checked separately from memory-argument enforcement. |
| Stale alias reads | [Initialized-history regression](Tests/InitializedHistory.lean) shows that a second read reusing the seed timestamp passes local native row constraints but fails actual logical memory matching. This validates the separate memory boundary; it is not a v2 implementation vulnerability. The complete-history theorem derives newest preceding reads. |
| Logical initial image | [Trace memory claim](Airbender/Review/Trace/History.lean) takes explicit seed/final tokens and logical matching. [Public constructors](Airbender/Review/Helpers/Memory/PublicImage.lean) now bind seeds and initial PC to actual Sail state; native word bounds and actual subsequent Sail cell reads/writes are derived, while physical boot/profile binding remains pending. No desired read/result or table-equivalence premise was introduced. |
| Decoder-owned zero flag | Native equations 24/25 use decoder variable 8 only to mask raw output into actual writes. Its Boolean/value relation comes from decoder matching, so history bounds cannot be promoted from raw-output bounds alone. Full padded logical decoder membership now recovers the flag; native masked-write and initialized-history word bounds follow. [A bad-flag fixture](Tests/InitializedHistory.lean) passes local equations and has an unbounded write, but full lookup membership rejects it. This validates the separate argument boundary, not an implementation defect. |
| V2 discarded writes retain decoding | Native v2 preprocessing retains the original opcode mask/operands for rd=x0, then masks the actual destination write. The prior local interface inherited an unnecessary source-style NOP restriction; it is removed. [Original Sail SUB x0,x1,x2](Tests/CircuitRows.lean) now has a checked nonzero-operand native row and public theorem application. Native masked-write equations now prove x0 preservation for initialized history; [the complete SUB fixture](Tests/X0History.lean) derives actual Sail stuttering without NOP preprocessing. [Retirement regressions](Tests/X0History.lean) now construct actual SUB bytes and derive original Sail PC retirement from these facts. No Rust behavior was changed. |
| V2 decoder padding | The native all-minus-one padding tail is retained in the logical setup. [Packed-mask bounds and padding exclusion](Airbender/Proofs/Trace/DecoderSetup.lean) reject it from actual ADD/SUB equations/Boolean bits, with no per-row PC-bound or desired-field assumption. Other setup/filler domains remain unassessed. |
| Selected setup construction | [Public setup](Airbender/Review/Helpers/Decoder/Setup.lean) reads actual bytes and original Sail decoding for the five arithmetic opcodes. It rejects missing/unsupported/effectful entries and retains native-shaped capacity/padding. General Rust generation/export fidelity and mixed/custom programs remain separate; no table-equivalence premise is used. |
| V2 word-memory ROM queries | [Native transfer theorem](Airbender/Review/Circuits/WordMemory/Theorems.lean) derives alignment, exact public ROM data, port selection, masked loads and RAM-only stores from all native equations/queries. Both ROM queries are unconditional, including RAM shadow queries; ROM loads retain a discarded readonly RAM access. Complete table models retain native 0xc0001073 UNIMP padding. The native address calculation now derives low/high carries and RV32 wraparound under source/immediate bounds. Checked PC/clock laws retain rollover and native port offsets under explicit local inputs. Public LW/SW decoding now recovers actual Sail source evidence and exact zero flags/PC/immediate facts. Initialized logical reads/ranges now include discarded ROM-shadow accesses. Actual Sail cell histories now realize the full supplied native image. Separate architectural projection is now checked below; original instruction execution is checked below; physical boot/ROM/setup binding remains pending. These are supported native behaviors, not implementation defects. |
| V2 word-memory decoder boundary | [Public decoder theorem](Airbender/Review/Trace/Families/WordMemory/Decoder.lean) uses actual LW/SW bytes and full padded membership. Native store-mask Booleanity rejects the minus-one tail; original x0 loads and sign extension remain intact. [A flag-2 regression](Tests/WordMemory.lean) passes the complete native row constraints, but decoder membership rejects it. This confirms the separate decoder-owned flag boundary; it does not establish an implementation vulnerability. |
| Public ROM prefix versus Sail padding | [Extraction and read bridge](Airbender/Review/Trace/Families/WordMemory/ROMImage.lean) derive native ROM data from actual public Sail bytes within the extracted prefix. Full extraction covers every ROM address. Native UNIMP padding is retained, but extraction does not populate absent Sail padding bytes; [the boundary regression](Tests/WordROMImage.lean) preserves that actual read failure. Physical boot/padding/shadow-state binding remains open. No table-equivalence or expected-read premise was added. |
| Discarded ROM-shadow participation | [Initialized native history](Airbender/Review/Trace/Families/WordMemory/History.lean) retains all three ports, including the readonly RAM port of an x0 ROM load. [The omitted-shadow regression](Tests/WordMemoryHistory.lean) fails actual memory matching; accepted fixtures derive newest reads, clocks and ranges without per-row answers. The shadow fixture explicitly initializes the native RAM cell. All native RAM accesses below four MiB are now proved value-preserving; the actual matching still retains their timestamp refreshes. Whole-address projection now omits these addresses from architectural Sail histories while retaining full native matching; physical boot/ROM binding remains open. This is not a native implementation defect. |
| Initialized native numerical inputs | [Native-row assembly](Airbender/Review/Trace/Families/WordMemory/Inputs.lean) now discharges source/immediate bounds, PC bounds/alignment and native clock inputs from actual public construction and accepted logical history/decoding. Existing native calculations derive address addition and modular PC successors. Actual Sail cell histories are now checked for the supplied native image; the separate projected history is checked below, while original instruction execution is checked below; physical boot/ROM binding remains open. No desired address/PC result was added as a premise. |
| Sail cell realization versus architectural ROM | [Actual cell histories](Airbender/Review/Trace/Families/WordMemory/SailHistory.lean) derive all transfers/states and hardwired x0 preservation from native matching, public seed construction and decoder membership. The existing seed image still binds every supplied native RAM cell, including shadows, to that Sail state. [RAM transfer and dependent store/load regressions](Tests/WordMemorySailHistory.lean) are checked; the separate architectural projection is checked below. Original LOAD/STORE execution is checked below; physical boot/ROM binding remains open. No expected-read, intermediate-state or final-value premise was added. |
| Architectural shadow erasure | [Projected histories](Airbender/Review/Trace/Families/WordMemory/Projection.lean) preserve Clean consistency/latest values for retained addresses and derive actual Sail transfers without reading shadow bytes. [The separate initializer](Airbender/Review/Helpers/Memory/ShadowImage.lean) obtains architectural seeds from actual Sail reads and retains public canonical native shadow values independently. Clocks, unique addresses, x0 writes and all full native read/write/terminal word bounds are derived. The existing range induction and native write rules are reused unchanged, including erased shadow accesses. [Ordinary/x0 ROM regressions](Tests/WordMemoryProjection.lean) retain every native event while a shadow read fails in Sail and its value differs from the ROM result. These logical seeds do not assert the physical native zero-boot profile; original instruction execution is checked below; ROM-table/boot binding remains open. |
| Projected native row interfaces | [Native effects](Airbender/Review/Trace/Families/WordMemory/Inputs.lean) now derive the complete native address/PC/clock interfaces from the separate initializer and actual public decoding. [Retained-port transport](Airbender/Proofs/Trace/Families/WordMemory/ProjectedPorts.lean) derives actual pre-state reads and final writes; full native constraints place that final port in GPR space or RAM outside the ROM prefix. Ordinary/x0 ROM regressions need no shadow bytes or expected source read; dependent RAM store/load rows use the same generic transport. Native matching still includes every shadow token. These are native and cell-transfer results; original LOAD/STORE execution is checked below; physical boot/ROM binding remains open. |
| Code/ROM preservation under stores | [Initialized ROM preservation](Airbender/Review/Trace/Families/WordMemory/CodeHistory.lean) now derives equality of every byte entry below four MiB from actual projected Sail transfers and the native architectural domain. Missing bytes remain absent; successful public ROM extraction and original source/decoding evidence survive every history prefix. Public indexed setup supplies complete code windows for programs fitting that ROM region. A reversed changing SW/LW history retains both instruction words and their extracted ROM image without later-read/value premises; ordinary/x0 ROM loads retain unreadable shadow bytes and complete native matching. This does not populate Sail boot/padding bytes, bind physical exports or establish original LOAD/STORE execution. |
| Sail platform versus native RAM effects | [Public configuration preservation](Airbender/Review/Trace/Families/WordMemory/Platform.lean) derives retention of actual Machine/PMP/PMA CSRs from initialized projected transfers. [Native RAM transport](Airbender/Proofs/Trace/Families/WordMemory/MemoryTransport.lean) derives actual pre-state reads, final writes and alignment from v2 constraints/history and invokes unchanged pinned Sail translation/permission/platform proofs. The same reversed accepted SW/LW history now derives a real virtual store and subsequent virtual read of 123. Ordinary addresses exclude actual platform MMIO windows; configuration and platform interfaces remain explicit, without desired-read/result premises. Original ROM/RAM clauses are now checked separately below; complete preparation/retirement is checked below; physical boot/export remains open. No v3 implementation finding is inherited. |
| Original ROM LW versus native shadows | [Virtual transport](Airbender/Proofs/Trace/Families/WordMemory/ROMTransport.lean) derives the original memory call from public ROM bytes and actual retained source reads; native ROM bounds discharge ordinary addresses. [Original LW assembly](Airbender/Proofs/Trace/Families/WordMemory/ROMExecution.lean) connects native masked writes to the original clause, retaining original rd=x0. [Initialized ordinary/x0 regressions](Tests/WordMemoryROMTransport.lean) reach the same actual native after-state while full matching retains shadow value 123 and actual ROM bytes read 0xc0001073. Public extraction requires present bytes and does not populate absent padding. No shadow/ROM equivalence, expected read or desired-state premise is used. Original RAM clauses and row retirement are checked below; general word-memory trace composition is checked below; physical boot/export remains open. No native defect is established. |
| Original RAM LW/SW clauses | [RAM assembly](Airbender/Proofs/Trace/Families/WordMemory/RAMExecution.lean) recovers the original store operand from native port 1 and maps masked RAM-load writes to original Sail writes, including x0. Exact public decoder fields derive load/store selectors, original registers and sign extension. Unchanged original Sail virtual-memory and LW/SW clause lemmas reach actual native cell-transfer states under explicit public configuration/ordinary-address conditions. [The same reversed accepted SW/LW fixture](Tests/WordMemorySailHistory.lean) derives the intermediate state, original SW then LW results, later read 123 and actual destination write. No expected operand/read, intermediate state or desired result is supplied. Row preparation/PC retirement is now checked below; general word-memory trace composition is checked below; physical boot/export remains open. No implementation defect or v3 finding is inherited. |
| Native word-memory PC retirement | [Row assembly](Airbender/Proofs/Trace/Families/WordMemory/Execution.lean) derives native effective addresses and modular PC successors from initialized matching and public decoding. [Control transport](Airbender/Proofs/Trace/Families/WordMemory/Retirement.lean) reuses actual histories/configuration/ROM extraction through Sail nextPC preparation and tick_pc. The original dispatcher is copied without v3's LW-to-x0 deviation. Ordinary/x0 ROM fixtures reach native PC 4 with real memory reads, and reversed dependent SW/LW normal steps reach PC 8 and native terminal RAM/x3=123 without intermediate/read/prepared-state/PC-result premises. Local ordinary-RAM and actual extracted-prefix coverage conditions remain explicit. General finite trace/fetch composition is checked below; physical boot/export and cryptographic enforcement remain open; no implementation defect is established. |
| Initialized word-memory finite execution | [Public execution](Airbender/Review/Trace/Families/WordMemory/Theorems.lean) checks actual fetched bytes/original decoding and finite original LW/SW normal steps, deriving exact native terminal PC and architectural cells. Full native matching still retains independent ROM-shadow values; [the observable](Airbender/Review/Trace/Families/WordMemory/Execution.lean) selects architectural terminal tokens explicitly. Public ordinary RAM, configuration, program-in-ROM size and actual ROM-prefix seed coverage remain visible. Accepted matching derives every local address domain, row order, read, range and intermediate state. Reversed SW/LW reaches PC 8 and RAM/x3=123; ordinary/x0 ROM loads and empty traces pass. Physical boot/padding/export and cryptographic enforcement remain open. No native defect or v3 finding is inherited. |
| Fixed native zero boot | [The boot boundary](Airbender/Review/Helpers/Memory/NativeBoot.lean) uses native zero GPR/RAM/shadow tokens, PC zero/time four and the unchanged original Sail initial profile. The [short theorem](Airbender/Review/Trace/Families/WordMemory/NativeBoot.lean) derives complete original execution through the existing initialization boundary, without per-row values, reads or states. [Full native paths](Airbender/Proofs/Trace/Families/WordMemory/BootShadow.lean) keep terminal shadows zero independently of actual ROM bytes. Ordinary/x0 boot fixtures reach native PC four and actual destination values; nonzero public GPRs and invented seeds reject the fixed profile. Native runtime/replayer source hashes are pinned; Rust refinement and physical argument enforcement remain separate. |
| Proving-loader zeros versus raw-table UNIMP | V2 word padding in [the native machine helpers](../../cs/src/machine/machine_configurations/mod.rs), called by [setup padding](../../circuit_defs/setups/src/lib.rs) and [the binary loader](../../execution_utils/src/lib.rs), extends to four MiB with zero. The raw ROM table constructor uses UNIMP only beyond the image it receives. Passing a complete loader-padded image makes that fallback unreachable within ROM. [The padding model](Airbender/Review/Helpers/Tables/WordROMPadding.lean) and [symbolic proofs](Airbender/Proofs/WordMemory/ROMPadding.lean) retain input words and zero the tail without a large evaluated certificate. Existing raw-table models stay unchanged. This is a checked source/model distinction, not an implementation defect. The explicit Sail padding connection is now checked below; Rust/export refinement remains separate. |
| Explicit Sail loader padding | [The constructor](Airbender/Review/Helpers/Tables/PaddedROMImage.lean) reads the actual supplied prefix and explicitly inserts zero bytes to four MiB. [Symbolic proofs](Airbender/Proofs/WordMemory/ROMBytePadding.lean) derive exact full-ROM extraction without evaluating the huge map/list or assuming table equivalence. Prefix/outside bytes, registers, public configuration and the original zero profile survive; actual decoder setup survives under code-prefix inclusion. [Padded boot execution](Airbender/Review/Trace/Families/WordMemory/NativeBoot.lean) derives all shadow coverage and complete original execution. Ordinary/x0 native fixtures, formerly absent zero reads, exact byte boundaries and missing/oversized prefix rejection pass. General Rust/compiler/export refinement and physical argument enforcement remain open; no v3 finding is inherited. |
| Native physical setup geometry and tags | The compiled artifacts have arithmetic/word-memory widths 12/16, scalar columns 0/1, one ten-column decoder group and word-memory's four-column generic group. [Importer guards](Airbender/Import/Parse.lean) now check exact placement, all 62 offsets, native capacity and the dummy-row extent. The native table IDs are 23/24, not v3's ROM tag 34. [The active-row model](Airbender/Review/Helpers/Tables/PhysicalSetup.lean) retains dummy/zero padding and the full tagged ROM/separator regions; symbolic proofs recover exact logical membership. [The short byte-read bridge](Airbender/Review/Trace/Families/WordMemory/Setup.lean) derives actual Sail words after explicit padding. Nonempty original/padded reads, changed ROM data and wrong padding tags are checked. Native source normalizes only the reserved final setup row, which this model excludes; formal Rust/export/normalization/LDE and stage-two enforcement remain open. No implementation defect is established. |
| Actual native regional setup fixture | [The standalone exporter](../native_setup_exporter/README.md) uses actual v2 table-driver, decoder and range APIs. Exhaustive codec checks and exact regeneration retain a four-word LW/SW/x0/UNIMP input, a full zero-padded public image, all native tags/offsets and every unsupported decoder slot. [Kernel certificates](Airbender/Proofs/WordMemory/NativeSetup.lean) check complete ROM/separator/range data and decoder/image tails; actual exported ROM membership supplies original Sail byte reads after loader construction. The explicit UNIMP word remains ROM data while its decoder slot is the all-minus-one sentinel. This is expected native behavior, not a defect. General program/decoder construction, full trace padding/normalization/LDE, parsing/export refinement and argument enforcement remain open. |
| Unsupported interior decoder slots | Native preprocessing continues past unsupported words without compacting their PCs. [The sparse constructor](Airbender/Review/Helpers/Decoder/SparseSetup.lean) now retains these holes, while missing bytes/effectful decoding fail. Native mask equations reject hole/tail lookups and derive source evidence and canonical fields. [A fresh actual export](artifacts/setup/word-memory-holes-native.json) places UNIMP at PC four and supported LW/SW/x0 words at 0/8/12. [Kernel certificates](Airbender/Proofs/WordMemory/NativeSparseSetup.lean) construct actual public Sail data and check every decoder row. A complete native x0-load constraint witness at PC 12 recovers its original source. This is expected native behavior, not a vulnerability. [Sparse initialized execution](Airbender/Review/Trace/Families/WordMemory/SparseExecution.lean) now reuses the same native history, original Sail clause/retirement and terminal proofs. [A real initialized x0-load regression](Tests/SparseExecution.lean) selects actual exported slot three and derives PC 12 to 16, unchanged RAM 123 and x0 zero. Initial PC 12 is public input; no control flow skipping an executed hole is asserted. Native matching retains the actual RAM read despite x0 masking. General Rust decoder refinement, arbitrary-program export certificates and physical argument enforcement remain open. |
| Setup fidelity | [Range definitions](Airbender/Review/Helpers/Tables/Range.lean) use native Clean static tables. [Actual shared scalar data](Airbender/Review/Helpers/Tables/NativeScalarData.lean) now retains every range16/timestamp19 prefix value. The exporter calls the native range16 API and copies the pinned native timestamp clause/constant unchanged; exact clause identity and lossless reproduction pass. [Symbolic proofs](Airbender/Proofs/Tables/NativeScalars.lean) certify every prefix and source-shaped active zero filler, deriving exact original Clean lookup meanings. Filler zero is valid range data and remains in the active domain; unlike decoder sentinels, it need not be excluded. The reserved normalization row, physical multiplicities, Rust trace/LDE refinement and argument enforcement remain separate. No implementation defect is established. |
| Actual arithmetic decoder data | [The actual native export](artifacts/setup/arithmetic-native.json) preserves signed ADDI limbs, original SUB-to-x0 operands/mask, raw U-type funct3 and the indexed ADD at PC 24 after an UNIMP hole at 20. [Kernel certificates](Airbender/Proofs/AddSub/NativeSetup.lean) construct independent original Sail public data and prove every exported slot equals its sparse row. Native packed-mask equations reject holes/tail before [source recovery](Airbender/Review/Trace/Families/AddSub/NativeDecoder.lean); a complete accepted post-hole ADD witness exercises actual membership. These are confirmed native behaviors, not defects. The native family also supports custom modular MOPs, which are outside this concrete five-opcode certificate. General Rust decoder agreement, arbitrary programs and physical trace/argument refinement remain separate; sparse initialized execution is checked below. |
| Sparse initialized arithmetic | [The short execution claim](Airbender/Review/Trace/Families/AddSub/SparseExecution.lean) now composes actual sparse public construction and complete native constraints/state/memory/decoder matching through the existing arithmetic history, original Sail and terminal assembly. Constructor-derived indexed evidence stays under Proofs; the strict public statement is unchanged. [The initialized post-hole regression](Tests/SparseArithmeticExecution.lean) uses actual exported slot six and derives PC 24 to 28 and x1=246 from full aliased-port matching and original public bytes/decoding. Native equations exclude holes/tail; no public per-row read, intermediate state, desired result or table-equivalence premise is added. The UNIMP word at PC 20 remains public data; initial PC 24 does not claim a control-flow skip. General native decoder refinement, arbitrary-program certificates, custom MOPs and physical trace/argument correspondence remain open. No implementation defect is established. |
| Active decoder padding | The native setup assembler calls the same [padding API](../../cs/src/machine/ops/unrolled/decoder/mod.rs) beyond the decoder prefix; both executable paths use all-minus-one values despite a materializer comment mentioning zeros. [The direct native export](artifacts/setup/decoder-padding-native.json) and [symbolic certificate](Airbender/Proofs/Tables/NativeDecoder.lean) check the actual sentinel and all 15,728,639 extra active rows. That sentinel already occurs in each checked native prefix, so full active membership adds no query; no equivalence is assumed. Both compiled placements and active boundaries are checked. [The initialized arithmetic bridge](Airbender/Review/Trace/Families/AddSub/ActiveSetup.lean) derives the real post-hole alias execution through this full domain; native mask equations reject padding. The final normalization row, general Rust trace/LDE refinement and argument enforcement remain separate. This is confirmed native behavior and a source-comment distinction, not an implementation defect. |
| Complete active row layout | [Full row assembly](Airbender/Review/Helpers/Tables/NativeRowsData.lean) now retains actual scalar/decoder data and tagged generic tuples at imported column positions. [Projection proofs](Airbender/Proofs/Tables/NativeRows.lean) derive unchanged Clean scalar/fixed-table meanings and actual decoder membership. [Regressions](Tests/NativeRows.lean) check overlapping decoder filler/ROM regions, mixed final filler values, missing generic groups, truncated windows, scalar overflow and wrong padding tags. [Initialized arithmetic execution](Airbender/Review/Trace/Families/AddSub/PhysicalSetup.lean) uses decoder columns from the complete row and derives the real alias fixture's PC 28/x1=246. This is a source-shaped logical row/column certificate, not Rust trace/normalization/LDE or argument refinement. No defect is established. |
| Native control triples and alignment | [The complete native export](artifacts/setup/jump-control-native.json) has 65,536 cleanup rows tagged 17 and 128 separate flags/funct3/result rows tagged 43, with no added dummy row. [Certificates](Airbender/Proofs/JumpBranchSlt/ControlTables.lean) bind every actual tagged value to original Clean membership. [The native fixed-effects claim](Airbender/Review/Circuits/JumpBranchSlt/Theorems.lean) derives exact key bounds/control/cleanup values from all native constraints. [An active JAL witness](Tests/JumpControl.lean) passes; altered results/out-of-domain flags and an unaligned JAL target reject. Cleanup itself retains bit one, and the native JAL equation excludes it. Public decoding is checked below; initialized original Sail execution remains open and the source terminal-PC finding is assessed below; no v2 vulnerability or copied closure premise is claimed. |
| V3 F01 retested on native v2 control rows | [Native PC bounds](Airbender/Review/Circuits/JumpBranchSlt/Theorems.lean) derive both outgoing limb ranges under explicit supported masks 1/2/4/8/16. Actual Boolean/packed equations derive selector exclusivity; outgoing high equals variable 43, consumed by scalar query index 5. [The local negative-offset row](Tests/JumpPC.lean) accepts canonical target limbs 65532/65535. Its field-minus-one high variant passes every polynomial and the other fifteen native queries, but that actual scalar query rejects it. The v3 F01 witness shape therefore does not reproduce on these native v2 rows. No terminal-PC range or verifier-closure premise is copied. Public-byte decoding is now checked below; initialized original Sail execution and full terminal-history connections remain open; no global closure result or new v2 vulnerability is claimed. |
| V2 public control metadata | [The control projection](Airbender/Review/Circuits/JumpBranchSlt/Decoder.lean) retains actual v2 SLTI/SLTIU mask 8, branch mask 16, original x0 operations and raw JAL encoding funct3. JAL -4 uses tag 7; its source v3 tag-zero convention cannot be copied. [Sparse public construction and native mask proofs](Airbender/Proofs/JumpBranchSlt/Decoder.lean) exclude every hole/tail sentinel, recover original Sail source evidence and derive mask/input/zero-flag facts before outgoing PC bounds. [Actual public-byte tests](Tests/JumpDecoder.lean) construct JAL -4, an interior UNIMP hole and original SLTIU-to-x0 at PC 8. The full native tag-seven JAL passes; the earlier locally valid tag-zero query is rejected by public membership. A malformed high-PC variant keeps actual public membership and all polynomials but fails the native range query. This closes the local logical decoder boundary, without a mask/range/desired-result or closure premise. Actual native program export is certified below for this input; general Rust decoder refinement, initialized original control execution and terminal matching remain open. These are native behavior differences, not a new vulnerability. |
| Actual native control decoder data | [The actual signed native export](artifacts/setup/jump-decoder-native.json) confirms raw JAL -4 funct3 7, the unsupported PC-four hole and original SLTIU-to-x0 mask 8/zero flag 1 at PC eight. [Independent Sail certificates](Airbender/Proofs/JumpBranchSlt/NativeSetup.lean) check every prefix and tail row. The short source/PC claim consumes actual exported membership with all native constraints; its full JAL witness passes, while the prior local tag-zero query fails. Separate arithmetic/control importer profiles reject crossed or unsigned-only data. These are confirmed native behaviors, not implementation defects. Arbitrary-program Rust decoder refinement, initialized original control execution, terminal matching and physical argument enforcement remain separate. |
| Native control readonly aliases | [Actual native clock extraction](Airbender/Proofs/JumpBranchSlt/Timestamp.lean) proves the shared clock contract from control-specific equation/query indices and imported ports. [Public initialized history](Airbender/Review/Trace/Families/JumpBranchSlt/History.lean) derives complete Clean consistency and newest reads from actual Sail seeds/PC and full native matching. [The full JAL -4 fixture](Tests/ControlHistory.lean) retains two x0 reads and the actual x1 link write; the second x0 read consumes the first readonly refresh. Its stale variant passes every local native constraint but fails logical memory matching. This confirms the existing argument boundary, not a v2 implementation defect. The lower 19-bit clock carry is accepted with correct high limb; explicit missing-register data rejects public initialization. Control word/write bounds and Sail cell transfers are checked below; original instruction execution and terminal instruction-state matching remain separate. |
| Native control masked writes and Sail cells | [Write equations](Airbender/Proofs/JumpBranchSlt/Writes.lean) derive actual destination bounds from one-hot selection, ranged jump links and the native one-bit comparison result. Full public decoding supplies masks/zero flags, while initialized induction derives all native read/write/terminal ranges. [x0 and cell realization](Airbender/Review/Trace/Families/JumpBranchSlt/SailHistory.lean) derive every zero-register write and clock-ordered Sail cell transfer from actual masks and complete matching. [The exported-JAL regression](Tests/ControlValues.lean) retains both x0 refreshes and replaces old x1=123 with link four. A malformed zero flag two passes every local native equation/query and yields an unbounded destination, while full decoder membership rejects it. This confirms the explicit external lookup boundary; no accepted-trace defect is established. Original control instructions, terminal instruction-state matching, physical boot and Rust/cryptographic refinement remain open. |
| Native control instruction pre-state reads | [Readonly-prefix transport](Airbender/Proofs/Trace/Families/JumpBranchSlt/PortReads.lean) now binds original decoded GPR reads/writes to actual imported control ports. [Initialized register histories](Airbender/Review/Trace/Families/JumpBranchSlt/Registers.lean) construct all segment states from native clocks/matching and original public decoding: both source reads and the old destination read use the same cell-history pre-state, including aliases. [The exported-JAL regression](Tests/ControlRegisters.lean) derives both x0 reads, old x1=123 and link write four through this claim. No supplied read, segment state, schedule or desired write is used. This is a checked native connection, with no new implementation defect. Original control operation semantics/clauses, PC retirement and terminal instruction-state matching remain open. |
| Native JAL/JALR saved PC+4 | [Native equations and shared modular addition](Airbender/Proofs/JumpBranchSlt/Link.lean) now derive the actual masked link write. Full public decoding supplies both PC limb bounds and the exact x0 flag; native jump masks recover operation selectors. Actual scalar queries zero/one range the saved word, while Boolean assertions 9/5 constrain carries 49/28. [Regressions](Tests/JumpLink.lean) check the exported negative-JAL link, logical odd-source JALR, original JAL-to-x0 with retained raw link twelve, all native constraints for unmasked PC+4 wrap to zero, and altered-link rejection. The wrap case is local, not an initialized/public-decoder trace; the new logical words have no new general native export certificate. No v2 defect or copied terminal-closure assumption is established. Jump targets, comparison/branch semantics, original Sail clauses/retirement and Rust/cryptographic refinement remain separate. |
| Native initialized JAL/JALR targets | [Native arithmetic and cleanup](Airbender/Proofs/JumpBranchSlt/Target.lean) derive both target limbs and alignment from actual v2 equations, carry assertions and range/fixed queries. [The initialized claim](Airbender/Review/Trace/Families/JumpBranchSlt/Targets.lean) derives source bounds through complete native matching and PC/immediate bounds, JAL parity and selectors through original public bytes. The actual candidate-high range removes the source v3 closure premise. [Regressions](Tests/JumpTarget.lean) cover exported negative JAL, initialized aliasing JALR from public x1=257 to target 264, local x0/wrap targets and bit-one rejection despite valid cleanup. No new v2 defect is established; the logical JALR fixture has no new native export certificate, and local wrap is not initialized execution. Original Sail instruction/retirement, comparisons/branches and full terminal instruction-state matching remain open. |
| Native initialized comparison results | [Numerical proofs](Airbender/Proofs/JumpBranchSlt/Comparison.lean) preserve native positive flags 31/33, derive signs from shifted-limb equations and actual scalar bounds, reuse original subtraction/borrow lifting and unchanged signed word ordering, then apply the actual conditional table and masked writes. [The initialized claim](Airbender/Review/Trace/Families/JumpBranchSlt/Comparisons.lean) derives operand ranges from full matching and selectors/signedness/x0 from actual original public decoding. [Four initialized cases](Tests/ControlComparisons.lean) distinguish signed/unsigned -1 versus one and positive 123 versus sign-extended -1, including true SLTIU-to-x0 with a retained readonly refresh and discarded raw one. Its query matches the prior actual native export. A flipped positive flag preserves its field equation only with an out-of-range shifted limb; actual scalar query two rejects it. No v2 defect is established. Logical-program native export, branch semantics, original instruction/PC execution and full terminal instruction-state matching remain separate. |
| Native comparison PC routing | [Actual native equations](Airbender/Proofs/JumpBranchSlt/ComparisonPC.lean) route comparison candidate 42/43 directly to final PC 13/14. Scalar queries four/five derive both limb ranges, Boolean carries retain RV32 wrap, and unchanged modular addition proves PC+4. [The short public claim](Airbender/Review/Trace/Families/JumpBranchSlt/ComparisonPC.lean) obtains incoming bounds/alignment and selectors from original public decoding without a register-image boundary or final-high closure assumption. [Tests](Tests/ComparisonPC.lean) reuse all four initialized comparisons, check full native local wrap and reject altered PC. This is confirmed native behavior, not a defect. Local wrap does not claim initialized execution/new native export; original Sail retirement, branch semantics and complete terminal instruction-state matching remain open. |
| Native initialized branch flags | [Subtraction and inverse proofs](Airbender/Proofs/JumpBranchSlt/Branch.lean) derive unsigned borrow, exact operand equality and native positive flags before the actual conditional lookup resolves all six branch conditions. Actual routing bits are complementary and unused destination writes are zero independently of the external x0 flag. [The initialized claim](Airbender/Review/Trace/Families/JumpBranchSlt/Branches.lean) obtains operand ranges from full matching and exact mask/tags from original public decoding. [Eighteen cases](Tests/Branches.lean) check both outcomes for every opcode, equality and opposite signed/unsigned orderings, retaining the real zero write event. A false equality flag/BEQ answer passes the actual conditional table but fails native inverse equation 16. This confirms enforcement, not a defect. New logical-program native export, branch targets, original Sail retirement and full terminal instruction-state matching remain separate. |
| Native branch PC selection/alignment | [Branch PC calculations](Airbender/Proofs/JumpBranchSlt/BranchPC.lean) derive PC+offset when taken and PC+4 otherwise from actual candidate, carry and routing equations. Both scalar queries bound the output, removing the source final-high premise. Untaken rows use the raw candidate; taken rows use cleanup, while original decoded parity and native assertion 26 exclude low-bit changes. [The initialized claim](Airbender/Review/Trace/Families/JumpBranchSlt/BranchTargets.lean) reuses the checked six conditions and derives all local PC/offset facts from original public bytes. [Tests](Tests/BranchTargets.lean) reuse eighteen initialized cases and check full local negative/taken-wrap/untaken-wrap rows. An ignored untaken offset two is accepted; taken offset two has valid cleanup but fails the bit-one assertion. This confirms native enforcement, not a defect. Local wrap/negative rows are not initialized/public-decoder execution or new exports; original Sail retirement and full terminal instruction-state matching remain separate. |
| Native comparisons versus original Sail retirement | [The native connection](Airbender/Proofs/Trace/Families/JumpBranchSlt/ComparisonExecution.lean) reuses checked comparison results, actual same-pre-state register reads and masked writes, exact public constructors/sign extension and unchanged preparation/retirement. [The public claim](Airbender/Review/Trace/Families/JumpBranchSlt/ComparisonExecution.lean) constructs every history segment and retires its original clause to the native PC. [All four initialized cases](Tests/ComparisonExecution.lean) pass from actual public states; true SLTIU-to-x0 retains source x1=123, stutters in data and retires PC eight to twelve. The source nonzero-rd restriction and final-high closure interface are not carried into this v2 claim. No defect is established. General fetched trace/terminal instruction-state composition, jump/branch CSR clauses and new program-export certificates remain open. |
| Original branches and public ISA state | [The checked native connection](Airbender/Proofs/Trace/Families/JumpBranchSlt/BranchExecution.lean) derives original six-opcode conditions, actual source reads, sign extension and exact aligned native targets before invoking original BTYPE preparation/retirement. [The public claim](Airbender/Review/Trace/Families/JumpBranchSlt/BranchExecution.lean) constructs segment states and explicitly requires an actual initial misa entry, with arbitrary value. Unchanged original CSR frame lemmas transport that entry; the copied Sail control-flow module preserves its real read even on an aligned taken path. [All eighteen native fixtures](Tests/BranchExecution.lean) execute unchanged with only that public CSR entry added, deriving complete data stuttering and targets. Old partial states have no entry and their original accessor cannot succeed. This is a public-state boundary, not a v2 defect or a claimed whole missing-CSR branch exception trace. Original jump CSR effects and full fetched control/terminal instruction-state composition remain open. |
| Original jumps and landing-pad profile | [The native connection](Airbender/Proofs/Trace/Families/JumpBranchSlt/JumpExecution.lean) reuses exact native links/targets, original metadata and same-pre-state reads/writes, then invokes the unchanged original retirement declaration. [The public claim](Airbender/Review/Trace/Families/JumpBranchSlt/JumpExecution.lean) constructs segments and retains actual initial misa readability plus Machine/MLPE-clear security data only when JALR occurs. Unchanged history frames derive all row CSR reads. [Regressions](Tests/JumpExecution.lean) reuse negative exported JAL and logical aliasing JALR, deriving original retirement and actual link writes with the same after-state. JAL has no privilege/security entries; the old partial JALR state cannot supply its original privilege read. This is an explicit original-Sail platform boundary, not a native defect, whole missing-CSR exception trace or new export certificate. Full fetched control/terminal instruction-state composition remains open. |
| Artifact fidelity | [Importer](Airbender/Import/Parse.lean) checks consumed addresses, residue bounds and unsupported features. Hashes pin the inputs; parsing/emission and native metadata interpretation are not formally proved. |
| Complete fetched control execution | [The public claim](Airbender/Review/Trace/Families/JumpBranchSlt/Execution.lean) composes all twelve supported original control constructors using unchanged shared fetch/retirement assembly. Native GPR history preserves public bytes; accepted state/memory matching derives actual order, intermediate states and terminal PC/register reads. Actual scalar candidate queries derive raw terminal PC bounds, including empty traces, without a copied closure premise. Initial misa and conditional JALR Machine/MLPE-clear CSR profile remain explicit. [Existing jump/branch/empty cases](Tests/ControlExecution.lean) and [reversed dependent JAL/JALR](Tests/ControlSequence.lean) pass. The stale-link variant passes all local constraints, public decoding and state matching but fails actual native memory matching. No native defect or new Rust program-export certificate is claimed; whole-machine/protocol/init/teardown and general refinement remain separate. |
| Unsigned mul/div native artifact and byte ranges | [The import](Airbender/Review/Circuits/MulDiv/Artifact.lean) retains all 49 equations and 20 lookups, including six exact paired-byte queries covering eleven native byte columns with odd-column zero padding. [Symbolic certificates](Airbender/Proofs/MulDiv/SmallRange.lean) identify all 65,536 actual exported tagged rows and exact Clean membership; [bounds](Airbender/Proofs/MulDiv/ByteBounds.lean) follow from native queries without supplied ranges. Two native optimized-out variables are scratch metadata only; consuming them as equation/query inputs, overflow/aliasing, malformed pairing/padding and changed table geometry are rejected. Endpoint/overflow/padding/tag regressions pass. This is a checked importer/data boundary, not MUL/DIV instruction correctness, a native defect or inherited v3 coverage. Numerical arithmetic is checked below; public decoding/history and original Sail execution remain open. |
| Native unsigned mul/div arithmetic and discarded writes | [The public local claim](Airbender/Review/Circuits/MulDiv/Theorems.lean) checks MUL/MULHU/DIVU/REMU selected results and actual masked writes. The unchanged shared integer product lemma is connected to native explicit bytes and split carries; accepted constraints derive every intermediate/output bound. [Native division](Airbender/Proofs/MulDiv/Division.lean) uses Mersenne31 inverse 32768, not the source -30720, and derives strict remainder bounds and zero-divisor all-ones quotient/dividend remainder from actual equations. Packed masks are 2/0/3/1 independently of x0. Forty full native assignments cover boundary and discarded-write cases; corruption of actual writes is rejected. This establishes local numerical correctness under explicit packed operation, input limb-bound and destination-zero interfaces, not original public decoding/history/Sail execution or a new native Rust export. No v2 defect is established. |

| Stateful MUL/DIV decoding and initialized numerical interfaces | [The initialized claim](Airbender/Review/Trace/Families/MulDiv/Theorems.lean) derives all numerical inputs from actual public bytes, seed/PC reads and accepted native matching. The original decoder reads misa.M, so a pure-only constructor cannot cover these forms. [Stateful setup](Airbender/Review/Helpers/Decoder/StatefulSetup.lean) preserves the real read and rejects decoder errors; the unchanged shared frame proof preserves state/misa replay. Sixteen nonempty initialized traces cover all four operations, zero divisors and actual x0 writes. Disabling M rejects actual original decoding; locally valid wrong tags and compensating flag-2 writes fail full public membership. This is a checked configuration/argument boundary, not a native defect. Original operation execution/retirement, physical boot/export and cryptographic enforcement remain open. |

| Actual MUL/DIV Sail GPR histories and decoder replay | [The public claim](Airbender/Review/Trace/Families/MulDiv/Registers.lean) constructs all segment states and original same-pre-state register reads/actual masked writes from native matching and public initialization. Native x0 equations retain original discarded opcodes. Actual GPR histories preserve code and misa, so the original stateful decoder replays after real updates. Sixteen initialized cases and a two-MUL source/destination alias sequence pass; the stale old-destination timestamp passes local constraints/decoding/state matching but fails native memory matching. This is a checked logical argument/configuration boundary, not a native defect or full MUL/DIV instruction/PC execution. |

| Original local MUL/DIV execution and native PC wrap | [The public instruction-history claim](Airbender/Review/Trace/Families/MulDiv/Execution.lean) derives original four-operation clauses, actual masked writes and original preparation/retirement from constructed native histories. Actual carry/inverse gates derive bounded modular RV32 PC+4; a full imported row wraps 0xfffffffc to zero. Sixteen initialized cases retain zero divisors and x0 retirement; the actual aliased second MUL retires PC four to eight after a real update. Complete fetched stateful-decoder composition remains unfinished; no native defect, fetched wraparound program or compiler refinement is claimed. |

| Complete fetched unsigned MUL/DIV execution | [The public theorem](Airbender/Review/Trace/Families/MulDiv/FetchedExecution.lean) derives finite original Sail fetch/stateful decoding/preparation/retirement from public initialization and full native matching, including actual terminal PC/register reads and bounds. Actual misa/code frames supply replay; no pure-decoder, extra ISA-read, per-row-step or desired-state premise is supplied. Sixteen complete cases, zero divisors/x0, concrete arithmetic results, a reversed two-MUL alias sequence reaching PC eight/x1=x3=861 and empty execution pass. This closes the family execution connection; no native defect, fetched wraparound fixture, new Rust export or cryptographic/compiler refinement is claimed. |

| Native shift/binop decoder migration differences | [The actual native export](artifacts/setup/shift-decoder-native.json) retains original x0 destinations, full sign-extended 16-bit immediate limbs and SRAI encoded funct7 (shift 31 gives 1055); native masks/tags differ from v3. [Independent original Sail proofs](Airbender/Review/Trace/Families/ShiftBinop/NativeDecoder.lean) connect all twelve ordinary forms, their x0 variants, the unsupported ADD hole and every exported row. Actual Rust runs reproduce empty-CSR filtering and unsupported REV8/rotate/illegal RV32 shift rejection. These are profile differences, not a native defect. This finite decoder-data certificate supplies no shift/binop constraint/execution coverage; dynamic table import/membership and custom CSR/oracle semantics remain separate. |

| Native zero and binary table membership | [The actual native prefix](artifacts/setup/shift-binary-native.json) retains zero and XOR/OR/AND IDs 0/4/6/7 with compiled offsets 0/1/65537/131073. [Public helper claims](Airbender/Review/Helpers/Tables/NativeBinary.lean) connect original Clean membership to every actual native binary row and derive both byte bounds and exact bitwise results. Source literal-block certificates check all 196,608 outputs; symbolic geometry retains actual keys/tags and the zero row. Byte 256 and a changed XOR output reject. An evaluated geometry check hit Lean allocation cap; splitting source-shaped structural geometry resolved it with unchanged ceilings. This is a certified table prerequisite, not shift/binop circuit/execution or general compiler/cryptographic soundness. Large shifts and custom CSR/oracle behavior remain separate; no native defect is established. |

| Native truncation, padding and sign-fill tables | [Actual selected native rows](artifacts/setup/shift-scalars-native.json) retain IDs 47/52/53 and compiled offsets 200705/8654849/10752001 across unexported regions. [Public helper results](Airbender/Review/Helpers/Tables/NativeShiftScalars.lean) derive bounds, truncation, padding and the exact RV32 mask for every row, including all 2,097,152 sign-fill entries. Shift zero fills no bits even for a negative high limb; one/sixteen/31 and positive-boundary fixtures pass. Nonzero padding, changed truncation/sign-fill and oversized keys reject. The combined upper-mask calculation reached the resident ceiling; four independent 16-domain certificates retain fixed caps. Four logical-shift tables and dynamic circuit/execution coverage remain separate; this is supported native behavior, not a defect. |

| Native low-input SRL table | [All actual native rows](artifacts/setup/shift-srl-low-native.json) retain ID 50 and compiled offset 4460545. [Public membership/results](Airbender/Review/Helpers/Tables/NativeSrlLow.lean) derive key/output bounds, zero high output and exact zero-extended RV32 logical shift for all 2,097,152 rows. Six symbolic native-block certificates use unchanged getters and the source block-check framework over all 74 stored blocks. Final-bit and shift-zero/one/fifteen/sixteen/31 fixtures pass; changed outputs, nonzero high padding and oversized packed keys reject. The other three logical-shift tables and full dynamic circuit/execution connection remain separate; no native defect is established. |

| Native high-input SLL table | [All actual native rows](artifacts/setup/shift-sll-high-native.json) retain ID 49 and compiled offset 2363393. [Two public helper claims](Airbender/Review/Helpers/Tables/NativeSllHigh.lean) derive packed-key/output bounds, zero low output and exact wrapped RV32 high-limb shift for every row. Six symbolic partitions retain 74 actual blocks; ten actual templates have structural geometry and 64-query kernel certificates. Generic size/output assembly avoids imported-array normalization after controlled resident/allocation-limit failures, with no surviving owned workers or raised ceilings. Top-bit loss, the final surviving bit, shift sixteen/31 and malformed queries pass. Discarded bits match RV32; no native defect is established. Low-input SLL, high-input SRL and full dynamic circuit/execution coverage remain separate. |

| Native low-input SLL table | [All 2,097,152 actual rows](artifacts/setup/shift-sll-low-native.json) retain ID 48 and compiled offset 266241. [Two public helper claims](Airbender/Review/Helpers/Tables/NativeSllLow.lean) derive packed-key/both-limb bounds and exact reconstructed RV32 logical-left shifts. Checked reuse identifies the full low-output column and 73 high-output blocks with previously certified native SLL-high data; six symbolic prefix partitions cover actual carry values. First-carry, shift-sixteen, final-bit/discard and malformed limb/result/key regressions pass under unchanged caps. Carry and bit discard match RV32; no native defect is established. High-input SRL and the dynamic circuit/execution connection remain separate. |

| Native high-input SRL table | [All 2,097,152 actual rows](artifacts/setup/shift-srl-high-native.json) retain ID 51 and offset 6557697. [Two public helper claims](Airbender/Review/Helpers/Tables/NativeSrlHigh.lean) derive packed-key/both-limb bounds and reconstructed RV32 right shifts. The high column and 73 low-output blocks reuse native SRL-low. All 146 native low-output blocks retain rotated templates, the 65,537-row initial zero block and shortened shift-eleven affine block; bounded stored-template and symbolic certificates prove exact values. Cross-shift/reset, shift-sixteen/31, final-bit and malformed-query regressions pass under unchanged caps. All four logical-shift limb tables now have helper membership/results; no native defect is established. Dynamic circuit import and initialized shift/binop execution remain separate. |
| Compiled shift/binop dynamic selectors and CSR profile | [The native import](Airbender/Review/Circuits/ShiftBinop/Artifact.lean) retains all fifty equations, eight timestamp queries and four physical selector witnesses as evaluated fourth Clean fields. [All twelve actual regions](Airbender/Review/Circuits/ShiftBinop/Tables/Native.lean) retain 10,817,537 tagged rows; [structural proofs](Airbender/Proofs/ShiftBinop/NativeLookup.lean) include every stored native row. The separately configured CSR region uses the exact compilation-test generator (nondeterminism enabled, empty delegation list), ID 25/offset 196609/4096 rows. Native source explicitly requires separately configured proving/setup CSR contents. This is an import/configuration boundary, not a runtime CSR binding, custom CSR/delegation execution claim or native defect. [Regressions](Tests/ShiftArtifact.lean) retain selectors, metadata, the native zero row and actual CSR data; malformed/crossed profile, mapping and offset cases reject. Numerical and initialized shift/binop execution remain open. |

| Accepted native tagged-lookup resolution | [Short native lookup claims](Airbender/Review/Circuits/ShiftBinop/Lookups.lean) extract all four queries and canonical selectors directly from original Clean acceptance. An exhaustive structural partition proves unique tags for all twelve actual regions; selected membership resolves to the existing binary/scalar/four logical-shift helper results with no equivalence premise. Tag zero requires three zero fields; it is not a wildcard. [Regressions](Tests/ShiftLookups.lean) reject wrong results, crossed/unsupported selectors and nonzero inactive data, while retaining boundary rows and canonical field wraparound. This establishes the native lookup connection, not operation routing, numerical circuit soundness or initialized Sail execution. The compilation CSR fixture remains separate from runtime CSR setup/custom instruction semantics. No native defect is established. |

| Decoded native shift/binop routing | [The short public claim](Airbender/Review/Circuits/ShiftBinop/Routing.lean) derives all four table tags, register/immediate operand selection and zero ordinary request multiplicity from original public bytes, native decoder membership and native constraints. Six Boolean bits bound the mask to 63 and exclude sentinel decoder rows. Native SRA uses sign fill before its two logical contributions; SRAI retains its encoded funct7 payload. [Complete row regressions](Tests/ShiftRouting.lean) cover twelve ordinary forms and every x0 variant, with 96 exact native lookup certificates and wrong-tag/operand/CSR-bit rejection. Numerical word results, initialized Sail register/history execution, runtime CSR binding and worker/request protocol enforcement remain separate. This is checked v2 routing, not a native implementation defect. |

| Native binary numerical results | [The short public claim](Airbender/Review/Circuits/ShiftBinop/Binary.lean) derives exact XOR/OR/AND selected RV32 words and actual decoded x0-masked writes from original public bytes, native decoder membership and accepted native constraints. The four byte lookups derive both operand bounds; native inverse-256 equations reconstruct all six input/output limbs. Full word values above Mersenne31 remain intact. [Twelve binary native cases](Tests/ShiftBinary.lean) cover register/immediate/x0 forms, negative immediates and rejected corrupted reconstruction/selected limbs/x0 writes. Native shift arithmetic, initialized register/history transport and original Sail instruction execution remain unfinished. No native implementation defect is established. |

| Native shift contributions | [The short public claim](Airbender/Review/Circuits/ShiftBinop/Shifts.lean) derives low-five-bit truncation, exact canonical packed-key SLL/SRL/sign-fill contributions and actual selected-word assembly from original public bytes, native decoder membership and accepted constraints. Native source/amount field equations, all contribution bounds and literal inactive zero slots are retained. SRA uses sign fill before low/high logical contributions. [Twelve complete native cases](Tests/ShiftContributions.lean) retain SRAI 1055→31, shift-31/x0 boundaries and corrupt key/inactive/missing-fill rejection. Binding packed keys to initialized bounded source reads, canonical selected limbs and architectural shift/Sail execution remains unfinished. This is a checked native contribution connection, not a native defect or a substitute source-bound premise. |

| Native shift/binop initialized history and x0 aliases | [The short public history claim](Airbender/Review/Trace/Families/ShiftBinop/History.lean) connects actual public Sail seeds/PC and native matching to complete Clean history and latest reads for all three native ports. Actual carry/borrow equations and eight timestamp queries derive all row/prior bounds, alignment, four-tick advancement and port order. [Twenty-four complete initialized fixtures](Tests/ShiftHistoryFixture.lean) pass with actual masked writes; six immediate/x0 aliases consume the earlier readonly refresh at time five. Their stale alternatives pass local native constraints but fail full memory matching. This confirms necessary global matching behavior, not a native implementation defect. Source-word bounds, canonical packed-key binding, Sail cell/instruction execution and runtime CSR binding remain separate. |
