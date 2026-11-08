# Actual native reduced trace review

Start with the [regenerated-artifact registry](../../../Helpers/Context/ReducedMachine.lean)
and [short public history claims](History.lean). They use the actual monolithic
117-equation v2 artifact, not the historical shipped JSON or a table-equivalence
premise. The four-field modeled setup table stays explicit.

[Native clock extraction](../../../../Proofs/ReducedMachine/NativeTimestamp.lean)
checks actual Boolean rows27..30, final-clock equations115/116 and all eight
native timestamp queries8..15. [Metadata](../../../../Proofs/ReducedMachine/NativeClockMetadata.lean)
retains the actual three previous-clock pairs, borrow bits and offsets0/1/2.
[Proof assembly](../../../../Proofs/Trace/Families/ReducedMachine/History.lean)
instantiates the unchanged shared clock/history machinery. Public Sail seed/PC
construction and accepted native logical matching derive all local/prior clocks,
strict access order, terminal four-tick row count, complete Clean memory
consistency and newest preceding reads for each native port. Readonly refreshes
and actual mixed addresses/masked writes stay in the relation. Row list order
need not be chronological. No expected read, per-row clock/order or supplied
intermediate-state answer is used.

[Four conditional regressions](../../../../../Tests/NativeReducedHistory.lean)
cover low-clock carry, finite clock-epoch overflow, nonpreceding reads and wrong
terminal row counts. They are not full positive native execution fixtures.

This establishes logical initialized clock/memory history. Word ranges still
need decoded native write preservation and shared range induction; memory
consistency alone does not prove all source limbs bounded. Original public
instruction decoding, canonical source keys, complete word/PC effects and Sail
execution remain open, as do workers/accounting/protocol/padding/terminal/init
and physical enforcement boundaries. Terminal clock counting is not terminal
machine-state soundness. See [current status](../../../../../VERIFICATION_STATUS.md)
and [trust boundaries](../../../../../TRUST_AND_REVIEW.md).

## Original public shift decoding

[The short public decoder claim](Decoder.lean) now recovers the original public
instruction entry and actual native mask/source/rd/x0/immediate/funct3 fields.
[Complete sparse/padded membership](../../../Helpers/Decoder/ReducedMachine.lean)
is checked at the imported native query; original public bytes and stateful Sail
decoding construct its independent table. [Native packing](../../../../Proofs/ReducedMachine/NativeShiftDecoder.lean)
excludes holes/tail, and [trace assembly](../../../../Proofs/Trace/Families/ReducedMachine/Decoder.lean)
keeps calculations under Proofs. The current profile includes only original
SLL/SRL/SRA/register/immediate forms. [Eight regressions](../../../../../Tests/NativeReducedDecoder.lean)
retain all twelve ordinary/x0 forms and reuse only original byte/decode lemmas,
not a split-family native table. This does not establish native Rust preprocessing
exports, universal fixed-ROM binding, other combined operations or a full accepted
execution fixture. Native write preservation, initialized source ranges and
complete instruction/execution effects remain next.

## Initialized word ranges and native source keys

[Concrete fixedData](FixedData.lean) selects the actual native pool while retaining
rows and explicit state/memory boundaries. It assumes no equivalence with another
table. [Native preservation](../../../../Proofs/ReducedMachine/NativeShiftPreservation.lean)
proves readonly refreshes and the actual masked destination write preserve ranges
from earlier reads, using original decoded rd/x0 fields. [Shared range induction](../../../../Proofs/Trace/Families/ReducedMachine/Values.lean)
then derives all native read/write/terminal word bounds from public seeds and
accepted matching; the [public interface](Values.lean) has no per-row range or
preservation-rule premise. [Both source keys](Sources.lean) are now exact natural
limb/amount/direction packings using the derived low source bound. Calculation
proofs stay under Proofs, including all32amounts and the arithmetic zero-shift
exception. [Nine regressions](../../../../../Tests/NativeReducedRanges.lean)
retain shift/sign boundaries, reject oversized actual reads/writes and preserve
bounded x0 source participation. No complete positive117-equation execution
fixture is asserted. Other combined profiles, original Sail GPR/cell/word effects,
numerical PC and preprocessing/physical/protocol/terminal/init remain separate.

## Complete initialized RV32 shift results

[The short public result](Results.lean) now derives canonical complete candidate
words and actual decoded x0-masked writes from public initialization, full
original shift decoding and concrete fixed-pool acceptance. No source range,
result answer or per-row preservation rule is supplied. [Proof assembly](../../../../Proofs/Trace/Families/ReducedMachine/Results.lean)
uses the already derived native read bounds and original entry fields.
[Eight regressions](../../../../../Tests/NativeReducedResults.lean) retain
numerical boundaries, corrupted arithmetic rejection and discarded candidates.
Original Sail cell/GPR transport, native source-two port binding, numerical PC
and instruction execution remain open, as do other combined profiles and
worker/protocol/padding/terminal/init and physical/setup correspondence.

## Original Sail cell/GPR realization

[The public register-history claim](Registers.lean) derives every native-clock-
ordered cell/GPR segment, original source and old-destination reads in one
pre-state, actual masked writes, final matching, preserved code/misa and original
stateful decoder replay. [Observables](../../../Helpers/Memory/ReducedMachine.lean)
keep all states/reads/order/replay as conclusions. [Actual zero rules](../../../../Proofs/Trace/Families/ReducedMachine/ZeroRegister.lean)
and [mixed-port/register-space recovery](../../../../Proofs/ReducedMachine/NativeShiftPorts.lean)
justify reuse of the unchanged shared Clean/Sail history machinery. Explicit
public cell-domain alignment remains an input; local states/read values or
address-space/replay answers do not. [Eight regressions](../../../../../Tests/NativeReducedRegisters.lean)
cover aliases/x0 and malformed mixed fields; the positive group fixture does not
claim full 117-equation acceptance. Selected-operand/clause, PC/fetched execution,
other combined profiles and setup/physical/protocol/terminal/init stay open.

## Retained original Sail shift clauses

[The public clause-history claim](Clauses.lean) derives original clause execution
at the actual native GPR after-state from public seeds/decoder and concrete native
matching. [Observable contracts](../../../Helpers/Memory/ReducedMachineClauses.lean)
add no per-row state/read/result premise. Actual selected operands and source
bounds are derived; original SRAI bits and readonly immediate/x0 aliases stay
intact. [Trace assembly](../../../../Proofs/Trace/Families/ReducedMachine/Clauses.lean)
keeps calculations and sequencing under Proofs. [Eight regression roots](../../../../../Tests/NativeReducedClauses.lean)
include twelve original Sail executions and six state stutters, scoped separately
from a complete positive native 117-equation fixture. Numerical PC/wrap, normal
preparation/retirement/fetched execution, other combined profiles and native
setup/physical/protocol/terminal/init remain open.

## Derived numerical PC successor

[The short PC theorem](PC.lean) derives incoming canonical bounds/alignment and
bounded native final-PC+4 with RV32 wrap from original public image/shift decoding
and actual accepted constraints. [Trace assembly](../../../../Proofs/Trace/Families/ReducedMachine/PC.lean)
discharges the local input bound/alignment from original query membership; native
carries/output ranges are derived from actual polynomials. The modeled fixed table
remains explicit; this table-independent PC theorem implies no physical setup
fidelity. [Eight regressions](../../../../../Tests/NativeReducedPC.lean) retain
carry/corruption/wrap/x0 behavior. Positive fixtures are the exact increment slice,
not full117-equation accepted rows. Normal PC preparation/retirement/fetched
execution, other profiles and protocol/padding/terminal/init remain open.

## Initialized original retired and fetched execution

[Original instruction history](Execution.lean) now derives actual row states and
original nextPC preparation/clause/tick_pc retirement. [Finite fetched execution](FetchedExecution.lean)
composes the derived native-clock/PC chain, original public byte/stateful decoder
replay and local retired steps into actual native terminal PC/cell reads. [Proofs](../../../../Proofs/Trace/Families/ReducedMachine/Composition.lean)
assemble every state/order/read/range/PC internally. Concrete fixedData acceptance,
public initialization/full original shift decoding and aligned tracked cells stay
explicit; no table identity or execution/state answer is a premise. [Six regression roots](../../../../../Tests/NativeReducedExecution.lean)
across the retirement module and [empty-boundary module](../../../../../Tests/NativeReducedFetched.lean)
retain x0/PC wrap, constructed initialized segments, terminal rejection and actual
zero-row acceptance. A complete positive nonempty117-equation native fixture,
other combined profiles and setup/physical/protocol/padding/terminal/init remain
open. Successful ordinary four-byte Sail paths do not include interrupts/exceptions.

## Complete nonempty positive examples

[Two actual native SLL/x0 fixtures](../../../../../Tests/NativeReducedPositive.lean)
now instantiate fetched execution with every modeled interface proved. [Native
witnesses](../../../../../Tests/NativeReducedWitness.lean) check117equations and
22lookups,while [trace/public construction](../../../../../Tests/NativeReducedFixture.lean)
checks activity,state/memory matching,original Sail seed reads and complete
13-slot original sparse/stateful decoding. Actual terminal PC/GPR reads and
candidate/write participation follow. These are nonempty accepted examples,not
local-only execution slices. Other mode/alias/multi-row fixtures,combined
operations and native public/setup/physical/protocol boundaries remain separate.

## Initialized arithmetic profiles

[Original arithmetic decoding](ArithmeticDecoder.lean) derives actual native
ADD/ADDI/SUB/LUI/AUIPC masks/source/rd/x0/immediate/raw funct3. [Word ranges](ArithmeticValues.lean)
follow from original public seeds, native preservation and shared initialized
induction. [Canonical numerical results](ArithmeticResults.lean) derive full
RV32 candidates and actual masked writes, discharging every internal source,
operand, PC and immediate-bound premise. [Proof assembly](../../../../Proofs/Trace/Families/ReducedMachine/ArithmeticResults.lean)
uses explicit modeled setup without a native/arbitrary-table equivalence. These
are arithmetic-profile traces; original GPR/cell history, retained Sail clauses,
PC retirement and fetched execution mixed with shifts remain next. [Source checks](../../../../../Tests/NativeReducedArithmeticDecoder.lean)
and [initialized consequences](../../../../../Tests/NativeReducedArithmeticValues.lean)
are not complete positive117-equation arithmetic execution fixtures. Native public
preprocessing/ROM/physical setup and broader protocol boundaries remain separate.

## Original arithmetic register states

[Arithmetic register history](ArithmeticRegisters.lean) now derives native-clock
row order, original Sail states, all three reads in one pre-state, actual masked
writes, terminal matching, code/misa frames and decoder replay. [Internal assembly](../../../../Proofs/Trace/Families/ReducedMachine/ArithmeticRegisterHistory.lean)
uses new actual arithmetic port/x0 proofs before unchanged shared realization.
[Eight regressions](../../../../../Tests/NativeReducedArithmeticRegisters.lean)
retain immediate/x0 aliases and reject malformed mixed fields; the exact generic
x0 group fixture remains scoped below complete arithmetic acceptance. Original
selected operands/clauses and PC prepare/retire/fetched execution remain next,
including AUIPC's actual incoming PC. Mixed shift/arithmetic and broader physical/
protocol/padding/terminal/init boundaries remain open.

## Original arithmetic initialized execution

[Instruction histories](ArithmeticExecution.lean) and [fetched execution](ArithmeticFetchedExecution.lean)
now derive original normal preparation/clause/retirement, row states and terminal
PC/cell reads from public initialization/decoding and accepted actual native matching.
[Assembly](../../../../Proofs/Trace/Families/ReducedMachine/ArithmeticComposition.lean)
derives both read bounds, numerical PC+4/wrap and original stateful decoder replay.
AUIPC's architectural PC is placed into constructed states and observed internally.
[Six retirement/initialized roots](../../../../../Tests/NativeReducedArithmeticExecution.lean)
and [two empty-execution roots](../../../../../Tests/NativeReducedArithmeticFetched.lean)
retain x0, sign/upper immediates and nonzero-PC AUIPC. They do not certify a positive
nonempty arithmetic 117-equation witness. Separate arithmetic/shift traces are
checked; mixed traces and other combined operations remain next. Exact fixedData
acceptance stays mandatory for shift numerical lookups; public/physical setup,
workers/protocol/padding/terminal/init and completeness remain separate.

## Mixed selected shift/arithmetic execution

[Original source recovery](SupportedDecoder.lean), [common initialized ranges](SupportedValues.lean)
and [finite fetched execution](SupportedExecution.lean) now cover interleaved supported
rows with one original public projection. [Native local transport](../../../../Proofs/ReducedMachine/NativeSupportedLocal.lean)
derives profile-specific preservation/addresses/PC/execution. [Common composition](../../../../Proofs/Trace/Families/ReducedMachine/SupportedExecution.lean)
discharges every read bound/alignment/state/replay input using exact fixedData
acceptance, native matching and original public construction. [Mixed image tests](../../../../../Tests/NativeReducedSupportedDecoder.lean)
retain original shift+ADD bytes/slots/queries; [initialized/empty tests](../../../../../Tests/NativeReducedSupportedExecution.lean)
reject oversized sources/terminal PCs and nonzero x0 events. These do not certify
positive nonempty arithmetic/mixed accepted native witnesses. Other ordinary
profiles, native public/physical fidelity and worker/protocol/padding/terminal/init
boundaries remain open; no parity follows from this selected coverage.

## Bitwise local prerequisite

[Native bitwise numerical roots](../../../Circuits/ReducedMachine/BitwiseTheorems.lean)
now derive source/selected-operand bounds and complete canonical RV32 candidates
from actual byte queries under explicit native33/35mask and funct3tag. [Exact pool](../../../Circuits/ReducedMachine/Tables/NativeBitwiseTheorems.lean)
connections are proved rather than assumed. Original public bitwise decoding,
rd/x0/operand/GPR/clause/PC transport and common preservation/history remain next.
SupportedMode and its initialized execution currently still cover only selected
shifts and ADD/ADDI/SUB/LUI/AUIPC. Positive byte-pool rows do not certify full
117-equation bitwise accepted execution or physical setup.

## Bitwise in common initialized execution (7 November 2026)

[Original bitwise source recovery](BitwiseDecoder.lean) derives actual mask/tag,
rs1/rs2/rd/x0 and sign extension. [New local native execution](../../../../Proofs/ReducedMachine/NativeBitwiseExecution.lean)
binds all actual ports, selected operands, numerical masked writes, original
clauses and bounded PC+4/full RV32 wrap. [Common ranges](SupportedValues.lean) and
[fetched execution](SupportedExecution.lean) now cover interleaved shifts, arithmetic
and bitwise through one derived range/x0/native-clock history and code/misa replay.
No read/range/result/PC/state/profile answer or table equivalence is public. Exact
fixedData acceptance stays explicit. [Original-image regressions](../../../../../Tests/NativeReducedSupportedDecoder.lean)
prove every one of25slots supported; [Sail regressions](../../../../../Tests/NativeReducedBitwiseExecution.lean)
retain ordinary/x0/negative-immediate/wrap behavior. Full nonempty native bitwise/
arithmetic/mixed positive witnesses and other combined/protocol/setup boundaries
remain open. The preceding local-only bitwise snapshot is superseded here.

## Initialized comparison numerical profile

[Original comparison decoding](ComparisonDecoder.lean) derives actual native
masks/tags/rs/rd/x0/sign extension from public bytes/stateful sparse membership.
[All read/write/terminal ranges](ComparisonValues.lean) and [complete RV32 results](ComparisonResults.lean)
now follow from initialized accepted native history and proved write preservation
at exact fixedData, with no local source/range/result/state answer. [Actual resolver](../../../Circuits/ReducedMachine/Tables/NativeConditionalTheorems.lean)
certifies all128native tag22rows, including inconsistent flags. Original GPR/cell/
operand/Sail clause/PC/fetched execution and common supported comparison integration
remain next. [Tests](../../../../../Tests/NativeReducedComparison.lean) are original
source/table/conditional native consequences, not full positive nonempty execution
witnesses. Native public/export/preprocessing/ROM/physical/protocol/completeness
boundaries remain separate.

## Comparisons in common initialized execution (7 November 2026)

[Common original support](../../../Circuits/ReducedMachine/SupportedDecoder.lean)
now includes SLT/SLTU/SLTI/SLTIU. [New local execution](../../../../Proofs/ReducedMachine/NativeComparisonExecution.lean)
binds actual GPR ports, selected operands, retained Sail clauses and bounded
PC+4/full RV32 wrap. [Common local rules](../../../../Proofs/ReducedMachine/NativeSupportedLocal.lean)
justify preservation/x0/register-space/PC transport before unchanged initialized
range/history/code/misa/decoder replay and [fetched composition](SupportedExecution.lean).
Both readonly source bounds and all intermediate states/order/replay are derived
from public construction, exact fixedData acceptance, complete sparse membership
and aligned tracked cells. No expected profile/read/result/PC/state or table
identity is supplied. AUIPC's prepared native PC and immediate readonly rs2/x0
participation remain derived. This supersedes the earlier numerical-only comparison scope.

[Original comparison tests](../../../../../Tests/NativeReducedComparisonExecution.lean)
cover ordinary/x0/sign/negative-immediate/retirement/wrap; [common decoder tests](../../../../../Tests/NativeReducedSupportedDecoder.lean)
add original public SLTIU evidence. These are not complete positive nonempty native
comparison/mixed witnesses. Other ordinary operations, native export/ROM/physical
setup, worker/protocol/padding/terminal/init and completeness remain open.

## Branch local prerequisite

[Native branch routing](../../../Circuits/ReducedMachine/BranchTheorems.lean)
derives actual mask70/all18bits, readonly and present x0 dummy ports, conditional
queries/PC field selection and remainder-zero semantics. Original branch public
decoding, condition/target arithmetic/alignment/GPR/Sail effects and initialized
execution remain open. Current common supported execution still covers only
shifts/arithmetic/bitwise/comparisons. [Five-assertion positive slices](../../../../../Tests/NativeReducedBranchRouting.lean)
are not full117-equation branch acceptance or initialized execution witnesses.

## Branch internal numerical effects

[Actual branch conditions](../../../../Proofs/ReducedMachine/NativeBranchCondition.lean)
and [native target/final PC](../../../../Proofs/ReducedMachine/NativeBranchPC.lean)
now derive full RV32 outcomes, wrap and taken-only alignment from accepted native
constraints and exact table semantics. Both source bounds and original PC/offset
bounds/alignment/parity remain internal obligations for public history/decoding.
Branches are still outside common initialized fetched execution. [Target slices](../../../../../Tests/NativeReducedBranchResults.lean)
cover only four actual assertions, not full accepted native branch instructions.

## Original public initialized branch numerics

[Public branch decoding](BranchDecoder.lean), [all-word ranges](BranchValues.lean)
and [short numerical result](BranchResults.lean) now derive actual native condition,
target/final PC bounds, RV32 wrap and successor alignment from original public
construction, exact fixedData acceptance, full sparse membership and native history.
Both source ranges and original PC/offset bounds/alignment/parity are discharged
internally. [Eight source/initialized checks](../../../../../Tests/NativeReducedBranchDecoder.lean)
include a complete six-word/two-padding original image; these are not full accepted
native branch witnesses. Numerical words are not yet original Sail GPR/branch
clause/fetched execution. Common supported execution still excludes branches.

## Original branch initialized fetched execution

[Public branch register history](BranchRegisters.lean) derives native-clock row
states, all three pre-state reads, present x0 dummy write/data stutter, final
matching, code/misa frames and original decoder replay. [Fetched execution](BranchFetchedExecution.lean)
derives retained BTYPE preparation/clause/tick retirement at the actual incoming
and condition-selected outgoing PC. Both actual source bounds, incoming alignment
and original decoder offset parity are discharged internally. Initial public misa
readability is explicit and its value unrestricted; every row CSR read is derived
through history/control frames. No read/result/target/PC/state/order/replay answer
or arbitrary-table equivalence is public. Exact fixedData acceptance is required.

[Port/history regressions](../../../../../Tests/NativeReducedBranchRegisters.lean),
[retained clause/PC edge regressions](../../../../../Tests/NativeReducedBranchExecution.lean)
and [empty native fixtures](../../../../../Tests/NativeReducedBranchFetched.lean)
are not full positive nonempty117-equation native branches. This closes separate
branch original execution above; common supported execution still excludes branches
until operation-specific PC integration. Native public/physical setup and other
ordinary/protocol/padding/terminal/init/completeness/interrupt scopes stay separate.

## Mixed initialized branch execution

[The common source](SupportedDecoder.lean), [common ranges](SupportedValues.lean)
and [fetched execution](SupportedExecution.lean) now cover branches interleaved
with the four prior profiles. Exact original entry/query transport derives new
branch preservation/x0/register-space prerequisites before shared initialized
Sail states/code/misa/replay. Both source bounds/alignment/original offset parity
are discharged internally. Common PC inputs/final bounds are operation-specific;
ordinary per-profile PC+4/full RV32 wrap proofs remain unchanged. Initial readable
misa is required only if the public program contains BTYPE, value unrestricted;
every local read follows from history. CSR-free empty/ordinary scopes remain.

[Independent mixed public source/configuration tests](../../../../../Tests/NativeReducedSupportedBranches.lean)
construct three original words plus padding, all-slot SourceWith and exact branch
fields, and check unrestricted/missing/unnecessary initial CSR availability.
These do not certify full positive nonempty117-equation native mixed acceptance.
Remaining ordinary/protocol/padding/terminal/init/public/physical/completeness and
interrupt/exception boundaries stay separate. This supersedes the earlier open
common branch integration notes above.

## Jump local prerequisite

[Actual jump routing/output bounds](../../../Circuits/ReducedMachine/JumpTheorems.lean)
now connects native masks257/33025, PC/rs1 base/immediate addition, exact cleanup
query/bit1 exclusion, return candidate, masked destination and final-PC fields.
Output bounds/alignment derive without supplied source ranges. Original public
JAL/JALR decoding/input bounds/GPR/operands/PC return/target/retained clauses and
initialized/fetched support remain next. [Six-assertion positives](../../../../../Tests/NativeReducedJump.lean)
are not complete accepted native jumps. The current five-profile common public
execution includes branches and excludes jumps.

## Original initialized jump numerical results

[Public jump sources](JumpDecoder.lean), [all-word ranges](JumpValues.lean) and
[canonical numerical results](JumpResults.lean) now recover original JAL/JALR
fields, direct parity, PC+4 return/rd-x0 writes and raw/selected targets with full
RV32 wrap/JALR low-bit clearing. Return preservation uses public PC inputs before
induction; actual initialized reads then discharge every raw addition range.
No source/range/return/target/PC/parity/state/table-identity answer is public.
[Ten regressions](../../../../../Tests/NativeReducedJumpDecoder.lean) cover original
three-slot source construction and conditional initialized effects, not complete
nonempty117-equation accepted native jumps. Original GPR/retained clauses/fetched
execution and common jump integration remain next, with physical/setup/compiler/
cryptographic/completeness and interrupt/exception scopes separate.

## Original jump GPR/cell history

[One short root](JumpRegisters.lean) derives all3actual original GPR reads in one
pre-state, masked writes, every chronological native-clock Sail segment/final match,
code/misa frames and original stateful decoder replay. [New port proofs](../../../../Proofs/ReducedMachine/NativeJumpPorts.lean)
use actual jump source/destination equations and original decoded fields before
shared history. JAL x0 reads and JALR aliases/old destination/discarded writes remain.
No initial CSR readability premise is used at this GPR boundary; actual PC control
preparation/retained clauses/normal/fetched/common integration stay separate.
[Eight regressions](../../../../../Tests/NativeReducedJumpRegisters.lean) include
unchanged imported group mechanics, not complete positive native jump acceptance.

[Local retained jump execution](../../../../Proofs/ReducedMachine/NativeJumpExecution.lean)
now binds actual native GPR/return/target words to original JAL/JALR, prepared architectural
PC and normal retirement. Source range/alignment and local CSR/landing-pad reads remain
internal obligations for initialized trace composition. No public initialized/fetched
jump or common jump integration follows yet; no desired local answer is made public.

## Initialized original jump fetched execution

[Public jump execution](JumpFetchedExecution.lean) derives successful original JAL/JALR
fetch/prepare/clause/retire and actual terminal PC/cells. [Composition](../../../../Proofs/Trace/Families/ReducedMachine/JumpComposition.lean)
discharges source/alignment/local CSR reads from original public membership and actual
initialized history, then derives every state/decoder replay/native-clock order/PC chain.
[JumpISA](../../../Helpers/Decoder/ReducedMachineJump.lean) keeps initial reference
configuration conditional on nonempty/JALR public program; empty/direct-only/GPR scopes
stay narrow. [Tests](../../../../../Tests/NativeReducedJumpFetched.lean) cover complete
empty execution at every RV32 PC with no CSR reads, not complete positive nonempty
native jumps. Common mixed jump integration remains next.

## Mixed original jump execution

[public_supported_execution](SupportedExecution.lean) now includes JAL/JALR interleaved
with shifts/arithmetic/bitwise/comparisons/branches. Original PC/byte/query identities
and actual native write/x0/address/PC/clause rules precede common initialized induction.
Jump return alignment derives from original public membership before range induction.
All states/read/write/CSR/replay/order/terminal observations remain derived. [SupportedISA](../../../Helpers/Decoder/ReducedMachineSupported.lean)
restricts initial misa to BTYPE/JAL/JALR and security configuration to JALR, preserving
empty/ordinary/branch-only scopes. [Six tests](../../../../../Tests/NativeReducedSupportedJumps.lean)
check logical original JAL/ADD/JALR image/sources/configuration, not full nonempty
117-equation native mixed acceptance. Remaining ordinary/protocol/physical scopes stay open.

[Word-only memory local foundation](../../../Circuits/ReducedMachine/WordMemoryTheorems.lean) checks explicit1025/16386masks/all18flags/selected operands/port spaces. Current common six-profile execution excludes LW/SW until fresh address/value/ROM/shadow/initialized/code-frame/Sail bindings.

[Word-memory local address/access](../../../Circuits/ReducedMachine/WordMemoryAddressTheorems.lean)
and [exact fixed-table semantics](../../../Circuits/ReducedMachine/Tables/WordMemoryTheorems.lean)
are now checked separately. They do not extend this common trace to LW/SW. Original
public decoding, initialized RAM/ROM reads and write preservation, code nonoverlap,
Sail clauses and mixed history remain open. Preserve actual shadow/OLDREAD events;
current all-events-register-space code frames do not apply to memory stores.

[Word-memory public decoding](WordMemoryDecoder.lean) now recovers original LW/SW
sources and allten actual fields from full sparse/padded membership, with native
packing excluding holes/tail. It does not yet extend this common execution profile:
initialized actual RAM/ROM/shadow values, write preservation and memory-aware code
frames must be derived first. Generic decoder setup is not a fixed-ROM identity.

[Word-memory value bounds](WordMemoryValues.lean) and [numerical effects](WordMemoryResults.lean)
now derive ALL actual reads/writes/terminal ranges, effective addresses, actual mixed
port cells, ROM/RAM/store writes and PC+4/wrap from the explicit ordinary public seed
image and exact native acceptance. No per-row source/range/read/result/state answer.
This is not yet original Sail memory/history or common support. Independent native
ROM-shadow seed ledger, exact fixed-ROM/original bytes and memory-aware code frames
must be constructed before retained LW/SW execution is claimed.

[Independent-shadow initialization](ShadowInputs.lean) now derives native seed clocks,
ranges/uniqueness and exact architectural projection from original cell reads plus
independent public ROM-shadow values. [All word ranges](WordMemoryShadowValues.lean)
and [native numerical effects](WordMemoryShadowResults.lean) follow actual reduced
write preservation/time induction. Missing architectural ROM bytes do not fabricate
shadow reads. Fixed ROM/original bytes, filtered row/Sail states/code-byte frames/
retained execution/common support remain open; this is not physical boot enforcement.

[Exact native ROM construction](ROMImage.lean) now derives the complete original
public extractor, every aligned fixture/padding word read and register/outside-byte
frames. [Actual accepted LW ROM bytes](../../../Circuits/ReducedMachine/WordMemoryROMTheorems.lean)
follow from the freshly checked address/lookup semantics in this constructed
reference state. Shadow values stay independent. Next derive actual event-domain
projection/chronological memory-Sail states/code-byte frames/retained LW/SW/common
execution. No physical public preprocessing/ROM fidelity or full nonempty native
memory witness is claimed.

[Projected LW/SW history](WordMemoryHistory.lean) and [initialized address origins](WordMemoryAddressDomains.lean)
now derive every chronological architectural Sail state/segment, final matching,
ROM-byte/misa frames and stateful source replay from full actual native acceptance
and original public construction. ALL shadow events/timestamps remain native-matched;
SW OLDREAD/unmasked write is retained. Code capacity describes public setup, not
per-row desired windows/frames. Next actual GPR/RAM/ROM transfer and retained original
LOAD/STORE execution; current common six-profile execution excludes memory.

[Original memory transfers](WordMemoryTransfers.lean) now derive all retained
reads/OLDREADs at ONE original pre-state and actual final writes, including
aliases and RAM refreshes. Exact NativeROM input bytes plus past frames derive
ROM reads, independently of native shadow values. Original unmasked load-to-x0
writes discard only after reading memory; SW writes actual RAM from original rs2.
Every local source/range/address/result/PC/state/order/replay obligation is derived
from full public initialization/decoding/native acceptance. No CSR premise at this
transfer boundary. [Eight regressions](../../../../../Tests/NativeReducedWordMemoryTransfers.lean)
are conditional-native/original-accessor/complete-empty evidence, not full positive
nonempty accepted memory witnesses. Retained LOAD/STORE clauses/configuration and
normal/fetched/common memory execution remain next; common six-profile support
still excludes LW/SW.

[Retained original LW/SW clauses](WordMemoryClauses.lean) now execute at actual
projected row states through original virtual/physical access. Every local source/
address/range/read/write/state/result/CSR/permission is derived. Meaningful initial
reference configuration is conditional on nonempty public programs; ordinary RAM
cells exclude pinned CLINT/signature windows. Actual native bounds/matching derive
local ordinary addresses; real history transports initial configuration. No per-row
success/configuration answer or native enforcement claim. [Nine tests](../../../../../Tests/NativeReducedWordMemoryClauses.lean)
include positive ORIGINAL LW-to-x0/SW and a CSR-free complete empty clause scope,
not full nonempty native memory witnesses. Actual PC preparation/normal retirement,
fetched and common mixed memory remain next.

[Original LW/SW normal/fetched execution](WordMemoryFetchedExecution.lean) now
reaches the actual native terminal PC and every architectural terminal cell.
Original stateful decoding replays in actual pre-states; derived PC preparation/
retirement preserves all kept reads/OLDREADs/aliases/unmasked load-x0/SW effects.
Full native matching keeps independent shadows. The [reference conclusion](WordMemoryExecution.lean)
filters architectural terminal observations only. Existing public exact-ROM/
initialization/platform/domain scopes remain; empty programs stay CSR-free.
[Five regression roots](../../../../../Tests/NativeReducedWordMemoryRetirement.lean)
and [empty terminal checks](../../../../../Tests/NativeReducedWordMemoryFetched.lean)
are original-reference/complete-empty evidence, not full nonempty native memory
witnesses. Common mixed memory-aware histories/profile transport remain next.

## Common seven-profile initialized memory-aware history

[Unified decoding](UnifiedDecoder.lean) wraps unchanged SupportedMode plus LW/SW.
[All native read/write/terminal ranges](UnifiedValues.lean) use one shared time
induction after original public decoding selects actual per-profile write laws;
JAL alignment is derived first. [Common history and actual port domains](UnifiedHistory.lean)
derive all projected chronological states/segments/final architectural matching,
ROM-byte/misa frames and original stateful decoder replay. All independent shadow
tokens/timestamps stay native-matched. LW ROM shadow alone filters from Sail;
RAM refreshes and SW OLDREAD/unmasked memory write stay architectural.

No CSR premise, per-row profile/read/range/result/state/PC/order/frame/preservation
answer or table-equivalence premise is added. Existing six-profile arbitrary
source/execution scopes remain unchanged; new arbitrary unified logical images
are not equated with native8wordROM. Common retained/normal/fetched execution is
NEXT after actual local transfers/retirement/configuration bindings. Eighteen
[original-source](../../../../../Tests/NativeReducedUnifiedDecoder.lean)/
[conditional-native and complete-EMPTY tests](../../../../../Tests/NativeReducedUnifiedHistory.lean)
are not full positive NONEMPTY117-equation/22-lookup accepted memory/mixed rows
or physical fidelity/completeness/parity. Earlier six-profile-only snapshots
above retain their historical scope.

## Common seven-profile original fetched execution

[Unified fetched execution](UnifiedFetchedExecution.lean) now closes retained
normal/fetched instruction execution at the common states above, yielding actual
terminal PC and EVERY architectural terminal cell read. [The reference result](UnifiedExecution.lean)
filters only Sail terminal observations; full native matching retains ALL
independent shadow seeds/events/timestamps. Actual supported GPR-row filter
identity and selected memory address origins precede local execution; public
constructor-sensitive initial memory/control configuration and ordinary RAM
domains derive every local CSR/permission through real past/control frames.

Ordinary/empty CSR freedom, branch/JAL unrestricted misa/JALR security, AUIPC PC,
x0/aliases/both readonly refreshes/OLDREAD/unmasked SW and native RV32 wrap remain.
The root explicitly uses exact NativeROM input construction; older arbitrary
ordinary public-code execution roots remain unchanged. Eleven [configuration/domain/native-filter](../../../../../Tests/NativeReducedUnifiedExecution.lean) and
[complete EMPTY fetched tests](../../../../../Tests/NativeReducedUnifiedFetched.lean)
are not complete positive NONEMPTY117-equation/22-lookup memory/mixed witnesses.
The earlier history-only checkpoint is superseded for this execution connection;
remaining MOP/CSR/delegation/protocol/physical/init/completeness/parity stays open.

## MOP remains outside the common execution scope

[Local native MOP arithmetic](../../../Circuits/ReducedMachine/MOPTheorems.lean)
now checks field ADD/SUB/MUL and canonical output, source-port/candidate/rdmask/
default-PC bindings. Native words are not yet original pre-state reads. Original
MOP public decoding, custom-operation reference and initialized/normal/fetched/
common execution remain open, separately from the closed seven-profile roots.
CSR/delegation requests, workers/accounting and protocol/init boundaries remain
next; no upstream Zimop zero-result execution is silently substituted.

## CSR local request scope

[Exact native CSR fixture and request observables](../../../Circuits/ReducedMachine/CSRTheorems.lean)
now derive supported/delegated keys, bounded native oracle, zero delegation return
and masked multiplicity/kind/ABI-high request fields. Imported in-cycle index3
does not establish issuance, worker fulfillment or accounting. Native source
words are not yet initialized original CSR reads; original public decoding/
custom/nondeterminism/privilege/normal/fetched/common execution remains open.
The existing seven-profile execution roots are unchanged and exclude CSR/MOP.

## Runtime CSR setup prerequisite

[A separately exported runtime CSR region](../../../Circuits/ReducedMachine/Tables/RuntimeCSRTheorems.lean)
now has exact native row meaning for1984/1991, distinct from the old full-pool
fixture1988/1989. Bigint1994 is outside this selected runtime target. The regional
certificate does not supply a runtime pool/selected-query/public caller stream or
worker/accounting/original execution connection. Existing execution roots stay
on their unchanged explicit pools. Those native composition obligations remain next.


## Original CSR source and runtime local effects

[CSR source roots](CSRDecoder.lean) derive original public bytes/instruction and
all native mask/operand/rd/x0/unsigned-index fields through full sparse/padded
membership. [The setup-only runtime trace constructor](RuntimeCSRData.lean)
retains every row/boundary/token; public decoding discharges the explicit local
mask before existing native CSR effects. This is a CSR-only source/local connection,
not initialized original execution or request clock/issuance/worker accounting.
The existing seven-profile execution and arbitrary ordinary public-code roots
remain unchanged; original decoder bytes are not equated with the fixed ROM.


## Initialized CSR GPR transfers

[CSR ranges](CSRValues.lean) and [GPR history](CSRRegisters.lean) now derive every
actual read/write/terminal bound, x0 propagation, chronological state/segment,
original same-prestate read/write, byte/misa frame and stateful source replay.
Fresh actual CSR address/write/x0 laws precede unchanged shared induction and
history assembly. Both readonly refreshes/OLDREADs/aliases remain; concrete runtime
roots retain every row/boundary/token. These GPR states do not execute original
CSR or delegated RAM effects. Caller clock/issuance, original CSR/PC execution,
workers/accounting/protocol and general native/physical setup remain open.


[Runtime CSR request observations](CSRRequests.lean) derive original pre-state rs1
words and actual imported request multiplicity/kind/optional ABI-high in the same
complete chronological GPR history. Public inputs remain full original bytes/
membership, ordinary logical seed boundary, runtime acceptance and alignment;
no local value/request/state answer. Natural high half precedes field cast even
above the field modulus. Original CSR execution, actual issuance and worker
fulfillment/accounting remain open; common seven-profile execution is unchanged.


[Runtime CSR local caller projection](CSRCallers.lean) retains full source/request
history and constructs strictly ordered multiplicity-selected caller observations.
The exact imported slot3 timestamp is bounded/nonzero, after every native GPR
access and before next machine clock; request kind1991/ABI bounds and actual row
origins follow constraints/initialization. No caller-stream premise is supplied.
This does not close sequence normalization, actual issuance or worker accounting.


[Runtime CSR caller argument](CSRArgument.lean) retains full initialized source/
request/caller history and derives actual row origins with reviewed stage2/quotient
argument identities. Selected constructor sequence0 contributes no extra high shift;
witness scaling preserves literal offsets/gamma. Unit specialization identifies
keys before compression, without equating all protocol points with unit scaling.
Actual auxiliary/accumulator enforcement and worker ledger/accounting stay open.

[Native precompression/token coding](../../../Circuits/ReducedMachine/MemoryTokenTheorems.lean)
now binds all three original main read/write tokens and retains all43 worker keys
through a lossless field-complement/pair encoding. The bridge supplies no accepted
permutation. These active logical trace histories remain separate from the full
physical ordinary-row domain, inactive argument factors and unproved delegated
actions. Actual global matching/extraction, initialized worker reads and faithful
padding/filter/history are still needed before the trace machinery can apply.

[Joint main arguments](../../../Circuits/ReducedMachine/MainArgumentTheorems.lean)
now share exact body/auxiliary observations across scalar/product conclusions.
No active physical-row filter or global token permutation follows from this
coupling. Existing initialized logical execution remains separate until faithful
full-domain matching, padding and delegated-action histories are connected.

[The nonempty runtime CSR1991/x0 fixture](../../../../../Tests/NativeCSRPositive.lean)
now checks every native body equation/lookup, full active logical state/memory
matching, original independent public program/decoder and actual initialization.
The existing theorem derives GPR/source/request/caller history and clock7. This
executes no original CSR clause or delegated action. A paired inactive BODY
witness still requests and is rejected by the active logical interface; faithful
full-domain padding/filtering and global matching remain open, not native defects.

## Native full-domain logical token boundary

[The native ledger roots](../../../Circuits/ReducedMachine/TokenLedgerTheorems.lean) bind all ordinary main/worker/public
tokens to the checked scalar product and retain exact precompression matching as
an explicit logical trust boundary. Identical inactive incoming port/state tokens
cancel only as duplicate-preserving multisets. Initialization/teardown, every worker
access and caller requests remain. [Controls](../../../../../Tests/NativeTokenLedger.lean) do not establish
initialized worker history, active ranges/key refinement, fulfillment or physical
cryptographic extraction. Original initialized execution interfaces are unchanged.

## Native active main-state path

[The main-state theorem](../../../Circuits/ReducedMachine/MainStateHistoryTheorems.lean) derives actual active main chronology,
clock bounds, four-tick counts and distinct0/1/2 write slots from complete native
body acceptance and the same explicit full token matching. All ordinary main rows
are considered before selecting execute1. Worker/init memory tokens and inactive
caller requests remain in their original ledgers. This is no initialized worker
memory history, CSR/MOP/Sail execution, issuance/accounting or physical extraction
claim. Original initialized execution interfaces are unchanged.

## Native adjacent initialization records

[The initialization ordering roots](../../../Circuits/ReducedMachine/InitializationOrderingTheorems.lean) derive repeated adjacent
actual token-address exclusion from native ordering polynomials, complete body
remainder/borrow checks and unmasked padding. Only zero padding can repeat at
adjacent comparison positions; the last two physical rows are excluded. This
supplies no global uniqueness, address range, public seed image, initialized
worker read or physical extraction. Original initialized execution is unchanged.

## Native initialization-address pair oracles

[The same-main pair roots](../../../Circuits/ReducedMachine/InitializationRangeTheorems.lean) retain all ordinary native rows and
the existing complete body, auxiliary chain, padding and adjacent ordering.
Separate base4/quartic28 observations yield the source pair equation, including
its duplicate-pole limit. Address ranges and logical lookup extraction are still
open; these local relations do not establish initialized worker reads or change
original execution.

## Complete native scalar16 family

[The same-main scalar16 roots](../../../Circuits/ReducedMachine/Scalar16Theorems.lean) derive ordinary auxiliary-sum
equality and reserved-last consistency from the native polynomial divisor.
All four body pairs and the initialization-address pair remain, including every
ordinary row and pole auxiliary. Physical multiplicity/setup observations do not
yet authenticate the public scalar table or extract lookup membership. Address
bounds, combined initialized worker history and accounting remain open.

## Constructed native scalar16 lookup boundary

[The same-main constructed lookup roots](../../../Circuits/ReducedMachine/Scalar16LookupTheorems.lean) retain the complete
source component and derive both initialization-address bounds from ALL actual
family queries on the constructed prefix/zero-tail table. The last normalization
value is derived symbolically. Logical lookup membership remains an explicit
cryptographic extraction boundary; no initialized worker history or accounting
is supplied, and original execution is unchanged.

## Natural initialization sorting

[Actual same-main sorting and nonpadding uniqueness](../../../Circuits/ReducedMachine/InitializationSortedTheorems.lean) follow from
the existing complete source, derived full-family address ranges, native
subtraction and six padding polynomials. All ordinary rows are included; repeated
padding remains. Public windows/image/seeds and combined worker memory history
are separate obligations; original execution is unchanged.
