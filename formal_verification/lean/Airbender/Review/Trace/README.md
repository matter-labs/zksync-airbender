# Whole-trace review

[Native memory soundness](History.lean) is the first v2 initialized logical-history
claim. Its short statement constructs a complete Clean online-consistent memory
history and proves that each actual imported port reads its newest preceding
write. Readonly refreshes and actual masked destination writes participate.

Review the shared [row/token data and acceptance](../Helpers/Context/Model.lean)
and [history meaning](../Helpers/Memory/History.lean). Acceptance checks the
imported native constraints, active rows and logical state/memory permutations.
The public boundary bounds only the starting machine clock and seed timestamps,
with initial four-tick alignment and one seed per address. Every per-row clock,
prior bound and newest-read conclusion is derived. Rows may be unordered.

Calculations and complete-path assembly stay under
[Proofs/Trace](../../Proofs/Trace/MemoryHistory.lean). The
[aliased-register regression](../../../Tests/InitializedHistory.lean) supplies
one native ADD row with both sources and destination at x1. Sequential readonly
refreshes are accepted. Reusing the seed for the second read satisfies local
constraints but fails logical memory matching.

[Public-image memory soundness](Initialization.lean) replaces the clock and
uniqueness premises with [public constructors](../Helpers/Memory/PublicImage.lean).
The original Sail interpreter reads every public tracked cell and the starting
architectural PC. The native initial clock is four; seed clocks are zero. Missing
registers or bytes fail construction. Seed bounds, seed clocks and unique encoded
addresses are derived, without witness-supplied initial read values.

[Public decoder recovery](Decoder.lean) constructs selected arithmetic-profile
setup rows from public bytes and original Sail decoding. Logical lookup membership
includes the native minus-one padding tail. The imported packed-mask equations
exclude that tail, recovering actual decoded public instructions and the zero flag.
Canonical decoder PC/immediate words follow in the proof layer.

[Public-image value bounds](Values.lean) derives all native reads, actual writes
and terminal word bounds from the public seed image, accepted native history and
complete decoder lookup membership. The source's decreasing-time induction is
reused; readonly ports preserve values, while native range/mask equations bound
destination writes after the zero flag is recovered. No per-row bounds are inputs.

[Actual Sail history](SailHistory.lean) realizes every accepted native transfer
from the public initial state. The [shared history representation](../Helpers/Memory/SailHistory.lean)
uses original Sail reads/writes and Clean last-write values. Native v2 mask
equations preserve x0 without NOP preprocessing; only public RAM-cell alignment
is supplied. Clock-derived [row grouping](../../Proofs/Trace/RowHistory.lean) and
[port transport](../../Proofs/Trace/PortReads.lean) recover instruction pre-state
reads and actual masked writes, including aliases. Both the aliased ADD and
[retained SUB-to-x0](../../../Tests/X0History.lean) have nonempty regressions.

[Native PC soundness](PC.lean) derives incoming PC bounds/alignment from public
indexed setup addresses, preserving RV32 truncation. The native carry/wrap
equations prove bounded successors; state matching and the public initial PC
bound the terminal PC, including empty traces. No per-row PC inputs are supplied.

[Decoded arithmetic assembly](../../Proofs/Trace/Arithmetic.lean) now derives
complete local interfaces and original Sail row retirement. The shared
[control transport](../../Proofs/Trace/Retirement.lean) preserves actual cell
reads/writes through PC preparation and retirement; no extra erased-source
readability premises are needed on v2. Concrete alias ADD and actual-byte
SUB-to-x0 regressions reach the original Sail retirement states.

[Complete arithmetic execution](Families/AddSub/Theorems.lean) now proves the
[shared reference relation](Execution.lean): actual Sail code-byte reads and
original decoding precede each normal preparation/execution/retirement step.
Native GPR metadata preserves all code bytes. Pure decoder evidence is extracted
from successful setup construction and replayed in each derived state. Native
state/memory matching derive the terminal PC and exact tracked cells, including
empty traces. The [dependent two-row regression](../../../Tests/ArithmeticExecution.lean)
stores witness rows backwards yet reaches original Sail PC 8 and x2=247.

[Word-memory public decoding](Families/WordMemory/README.md) now has a separate
native registry and short source-recovery theorem. Actual LW/SW bytes build a
complete padded logical table; native equations reject padding and recover exact
zero flags, PC/immediate bounds/alignment and original Sail source evidence,
including loads to x0. [Public ROM extraction](../Helpers/Tables/WordROMImage.lean)
now binds native ROM data to actual Sail bytes in the extracted prefix. A complete
four-MiB extraction covers the native ROM region. Initialized word-memory
[logical history](Families/WordMemory/History.lean) and
[word ranges](Families/WordMemory/Values.lean) now reuse the shared matching/clock
and decreasing-time proofs. Public seeds discharge all initial clock/value inputs;
full decoder membership supplies the zero flag. Every native port participates,
including discarded ROM-shadow reads. [Native-row assembly](Families/WordMemory/Inputs.lean)
now derives effective-address addition, bounded aligned PCs, modular successors
and native clock/port order with no per-row numerical input premises.
[Word-memory Sail cell histories](Families/WordMemory/SailHistory.lean) now derive
actual reads/writes and intermediate states, with clock-derived row grouping and
mixed-port x0 preservation. A reversed store/load pair derives its intermediate
RAM state and the later read. That claim uses the full supplied native cell image.
[Architectural projection](Families/WordMemory/Projection.lean) now uses separate
public architectural and native-shadow seeds. It preserves the full Clean history
while realizing only architectural addresses in Sail, deriving clocks, unique
addresses, x0 preservation and final matching. Ordinary/x0 ROM loads retain native
shadow events despite missing Sail shadow bytes and distinct shadow/ROM values.
[Projected native inputs](Families/WordMemory/Inputs.lean) now derive address
addition, bounded aligned PCs, modular successors and native clock effects.
Retained-port transport recovers actual pre-state reads and final masked writes,
with final-port retention proved from native constraints. Physical native
boot/padding/ROM binding remains separate; original execution is checked below.
[Code/ROM preservation](Families/WordMemory/CodeHistory.lean) now derives equality
of every byte entry below four MiB and retains every successful public ROM
extraction. Public programs fitting the native ROM region preserve original Sail
instruction reads/decoding across every projected prefix, even with changing RAM
stores. Missing bytes remain absent; physical boot/export remains open. Original
LOAD/STORE execution is checked below.

[Public platform configuration](Families/WordMemory/Platform.lean) now survives
initialized projected histories. Eight unchanged source modules supply the
original Sail Machine/PMP/PMA and ordinary-memory interface. Actual native RAM
reads/writes now reach Sail virtual-memory calls on the dependent SW/LW fixture.
[ROM transport](../../Proofs/Trace/Families/WordMemory/ROMTransport.lean) now derives
original virtual reads from actual public bytes; native ROM bounds discharge
ordinary addresses. [Original LW clauses](../../Proofs/Trace/Families/WordMemory/ROMExecution.lean)
reach the actual masked-write after-state, retaining original x0 loads. Initialized
ordinary/x0 regressions retain full shadow matching with distinct shadow/ROM
values. [Original RAM clauses](../../Proofs/Trace/Families/WordMemory/RAMExecution.lean)
now reach actual cell-transfer states using derived selectors, rs2/RAM reads and
native masked writes. The reversed dependent fixture reaches original SW then
LW results without intermediate state/read/result premises.
[Native row retirement](../../Proofs/Trace/Families/WordMemory/Execution.lean) now
composes original preparation/clause/tick_pc using derived native PC successors
and actual history/configuration transport. Ordinary/x0 ROM loads reach native
PC 4; the same reversed SW/LW normal steps reach PC 8 and terminal RAM/x3=123.
Local ordinary-RAM and actual ROM-prefix coverage remain explicit; general
finite trace/fetch composition is now checked by
[the short execution theorem](Families/WordMemory/Theorems.lean). Its
[observable](Families/WordMemory/Execution.lean) retains exact native terminal PC
and architectural cells while full matching retains all shadow tokens. Public
cell/seed domains derive every local ordinary-RAM and ROM-prefix condition;
configuration, program size in ROM and actual extraction remain visible.
Original bytes/decoding, configuration and ROM extraction survive every derived
prefix. The reversed SW/LW trace reaches PC 8 and terminal RAM/x3=123 through the
general relation; ordinary/x0 ROM loads and empty traces also pass.

These are logical selected-profile results. Remaining families and physical
setup/argument fidelity remain in [the plan](../../../FORMAL_VERIFICATION_PLAN.md).
Cryptographic enforcement of the logical permutations remains a separate boundary.
Existing [local circuit claims](../Circuits/README.md) retain their explicit interfaces.

[Fixed word-memory zero boot](Families/WordMemory/NativeBoot.lean) now derives the
same execution contract from original Sail zero-profile reads and fixed native
seeds/PC. Complete native paths preserve shadow zero independently of ROM bytes.
Ordinary/x0 boot regressions derive PC four and actual masked destinations.
The proving loader's zero extension and raw-table UNIMP fallback have separate
[checked models](../Helpers/Tables/WordROMPadding.lean). The [explicit loader](../Helpers/Tables/PaddedROMImage.lean)
now constructs actual Sail zero bytes and derives full ROM extraction plus
setup/profile/configuration preservation. The padded-boot claim derives all ROM
coverage; physical initialization/setup exports remain open.

[The native setup-row read bridge](Families/WordMemory/Setup.lean) now connects
complete tagged ROM membership to actual Sail bytes after explicit padding.
Compiled placement and all table offsets are checked; dummy/wrong-table/zero-padding
rows are distinguished by native tags. Actual Rust column exports, normalization/
LDE refinement and physical argument enforcement remain separate.

[Sparse word-memory execution](Families/WordMemory/SparseExecution.lean) now uses
successful public construction with unsupported interior slots and complete
native matching. The shared history/original Sail/terminal assembly derives the
same exact observable while keeping original PCs and actual bytes unchanged.
The real x0-load regression starts at public PC 12, selects actual exported slot
three after the PC-four hole, and reaches PC 16 with RAM 123 and x0 zero.
General Rust/export and physical argument connections remain separate.

[Shared scalar certificates](../Helpers/Tables/NativeScalars.lean) now connect
actual range16/timestamp19 prefix data and modeled active zero padding to the
unchanged Clean range helpers used by initialized execution. These data/row
claims preserve the existing logical trace boundary; they do not establish
physical lookup multiplicities, normalization/LDE or argument enforcement.

[Actual arithmetic decoder source recovery](Families/AddSub/NativeDecoder.lean)
now certifies every slot of a native export against independent original Sail
public bytes/decoding. Native equations exclude its interior UNIMP hole and full
tail before membership recovers a supported source. The nonempty ADD witness at
PC 24 retains its original index after the hole. General decoder refinement,
custom MOPs and full physical setup/argument connections remain separate.

[Sparse initialized arithmetic execution](Families/AddSub/SparseExecution.lean)
now reuses the existing native history, numerical, original Sail and terminal
proofs. Actual strict/sparse constructors derive [internal indexed evidence](../../Proofs/Trace/ProgramImage.lean);
the strict public statement is unchanged. Complete native membership excludes
holes/tail and retains every original PC/byte. The full initialized alias fixture
selects actual exported slot six at public PC 24 and reaches PC 28 and x1=246.
No indexed-source evidence, per-row bound/read, intermediate state, desired result
or table equivalence is a public premise. Custom MOPs, general decoder/export
refinement and physical argument enforcement remain separate.

[Active setup arithmetic execution](Families/AddSub/ActiveSetup.lean) now consumes
complete active decoder membership over the actual native prefix and padding API
row. [The shared certificate](../Helpers/Tables/NativeDecoder.lean) proves the
full domain adds no query; the same initialized alias witness reaches PC 28 and
x1=246. No padding exclusion or table equivalence is a public premise. Final
normalization, Rust full-trace/LDE and physical argument enforcement remain open.

[Complete-row arithmetic execution](Families/AddSub/PhysicalSetup.lean) now uses
decoder queries at imported columns of [assembled native rows](../Helpers/Tables/NativeRowsData.lean).
All scalar, tagged generic and decoder groups keep their own padding domains;
[projection proofs](../../Proofs/Tables/NativeRows.lean) derive their existing
logical meanings. The real alias fixture still reaches PC 28/x1=246 with native
matching and public byte/Sail construction. Rust trace/normalization/LDE,
arbitrary-program decoder certificates and cryptographic enforcement remain open.

[Jump/branch/SLT fixed effects](../Circuits/JumpBranchSlt/README.md) now have exact
native equations/metadata and complete native fixed-table certificates. A full
active JAL witness and alignment rejection pass. Public decoding/native export and
local outgoing PC bounds are checked in the circuit guide. [Initialized native
control history](Families/JumpBranchSlt/History.lean) now uses its separate imported
clock/port registry and proved shared clock laws. Actual public Sail seeds/PC plus
full matching derive complete Clean history and newest reads, retaining readonly
alias refreshes and actual masked writes. [The full JAL -4 regression](../../../Tests/ControlHistory.lean)
retains both x0 reads and the link write; a stale local read fails matching.
[Control word ranges](Families/JumpBranchSlt/Values.lean) now follow from public
sparse decoding and initialized induction. [Sail cell history](Families/JumpBranchSlt/SailHistory.lean)
uses native x0 masks and shared row grouping to derive actual reads/writes and
intermediate states; the [exported-JAL regression](../../../Tests/ControlValues.lean)
checks the old x1=123 read and actual link write four. Original control instructions
and terminal instruction-state matching remain open. Existing arithmetic and word-memory claims retain their meanings.

[Control register histories](Families/JumpBranchSlt/Registers.lean) now bind every
original decoded source/destination accessor to actual native ports in derived
clock order. The shared readonly-prefix proof keeps all three reads in one
cell-history pre-state; the final masked write reaches the constructed row-after
state. Older/current/newer Sail histories connect every boundary to public
initialization and the full terminal cell history. [The exported-JAL regression](../../../Tests/ControlRegisters.lean)
derives both x0 reads, old x1=123 and link write four without supplied intermediate
states. Original control clauses and native PC/operation semantics remain open.

[Native saved jump links](../Circuits/JumpBranchSlt/Theorems.lean) now derive the
actual masked PC+4 word for public-decoded JAL/JALR rows. Selectors, PC bounds and
the x0 flag come from native constraints and public construction. This numerical
connection complements the checked register histories; jump targets are checked
below, while Sail clauses/PC retirement and complete control execution remain separate. A full
local native wrap regression is checked, without claiming initialized wrap execution.

[Initialized native jump targets](Families/JumpBranchSlt/Targets.lean) now derive
every JAL/JALR target and four-byte alignment from actual public initialization,
complete native matching and original byte decoding. Source ranges come from
shared history; JAL parity comes from the original Sail decoder. [Regressions](../../../Tests/JumpTarget.lean)
retain exported negative JAL and initialize an aliasing JALR with public x1=257,
whose odd sum 265 clears to target 264. No per-row bound, selector, parity, carry
or desired target is supplied. Full original instruction/PC retirement remains open.

[Initialized comparison results](Families/JumpBranchSlt/Comparisons.lean) now
derive all four SLT/SLTU/SLTI/SLTIU actual masked writes. Native matching supplies
operand ranges; original public metadata supplies immediate choice, signedness
and x0. Native equations and actual scalar/fixed queries derive signs and borrow.
[Four independent initialized cases](../../../Tests/ControlComparisons.lean)
cover signed/unsigned disagreement, sign-extended -1 and discarded true SLTIU-to-x0
with its real readonly refresh. No expected read/result, selector or bound is
supplied. Branch semantics and full original instruction/PC execution remain open.

[Comparison PC advancement](Families/JumpBranchSlt/ComparisonPC.lean) now derives
PC+4 and alignment from public decoding and native acceptance. Comparison rows
route the ranged raw candidate directly; no source-register/image premise is
needed. Native carries and both scalar queries retain RV32 wrap.
[All four initialized fixtures](../../../Tests/ComparisonPC.lean) pass; full
native local wrap and altered-PC rejection are also checked. Local wrap is not
an initialized/public-decoder execution. Original Sail instruction retirement,
branches and complete control execution remain open.

[Initialized branch conditions](Families/JumpBranchSlt/Branches.lean) now derive
all six predicates, both routing bits and actual zero writes. Native inverse
equations identify equality; actual scalar/fixed queries resolve signed/unsigned
order. Original public decoding derives branch identity/tags and full matching
supplies both operand ranges, with no per-row flags, bounds or desired result.
[Eighteen initialized cases](../../../Tests/Branches.lean) check both outcomes
for every opcode and retain the real zero destination event. Branch targets and
original Sail clauses/retirement remain separate.

[Initialized branch targets](Families/JumpBranchSlt/BranchTargets.lean) now
follow each checked branch condition to PC+offset or PC+4. Public original
decoding supplies bounds/alignment and derives offset parity through unchanged
Sail lemmas; actual native queries/routing derive exact aligned targets with
RV32 wrap. [All eighteen initialized cases](../../../Tests/BranchTargets.lean)
pass, together with separate full native local negative/wrap and taken-only
misalignment regressions. No per-row decision, carry, parity, bound, expected PC
or final-high closure is supplied. Original Sail retirement remains open.

[Original comparison execution](Families/JumpBranchSlt/ComparisonExecution.lean)
now constructs every initialized native segment and invokes original Sail
SLT/SLTU/SLTI/SLTIU preparation/retirement to its actual output PC. Shared
history supplies both source reads and the actual masked write. Public decoding
supplies exact constructors, indices, immediate sign extension and masks.
[All four unchanged fixtures](../../../Tests/ComparisonExecution.lean) execute
from their actual public states, including retained x1=123 and complete data
stuttering for true SLTIU-to-x0. Full fetched control execution/terminal matching
and original jump/branch clauses remain separate.

[Original branch execution](Families/JumpBranchSlt/BranchExecution.lean) now
constructs all native segment states and retires every original BTYPE clause
to its checked target. Native matching/public decoding derive reads, bounds,
sign extension and decisions. A real initial misa entry is explicit, with
unrestricted value; unchanged CSR frame lemmas transport it through history.
[All eighteen unchanged native cases](../../../Tests/BranchExecution.lean)
execute both outcomes per opcode, preserve the complete data state and reach
the exact target. Missing public CSR/accessor tests retain the original-state
boundary. Original jumps and full fetched control composition remain separate.

[Original jump execution](Families/JumpBranchSlt/JumpExecution.lean) constructs
JAL/JALR segments and retires original clauses to native targets and actual
masked links. Real initial misa is readable; traces containing JALR use actual
Machine/MLPE-clear CSR data, transported through history. JAL needs no landing-
pad entries. [Existing initialized fixtures](../../../Tests/JumpExecution.lean)
execute negative JAL and aliasing JALR with exact native writes. Full fetched
control composition and terminal instruction-state matching remain open.

[Complete fetched control execution](Families/JumpBranchSlt/Execution.lean)
now composes all twelve supported original constructors and derives native
terminal PC/register matching. The unchanged shared composer constructs order,
states, fetch/decoding and retirement; actual GPR history preserves public
bytes. Candidate range queries/state matching bound raw terminal PC limbs,
including empty traces. Initial misa and conditional JALR Machine/MLPE-clear
profile remain explicit. [Existing fixtures](../../../Tests/ControlExecution.lean)
and [reversed dependent JAL/JALR](../../../Tests/ControlSequence.lean) pass;
stale-link data passes local constraints/decoding/state matching and fails
native memory matching. No per-row step, desired state/read/result or terminal
closure premise is supplied. Whole-machine/protocol/init/teardown remain open.

[Unsigned mul/div](../Circuits/MulDiv/README.md) now has checked native
numerical results for all four operations, zero divisors and actual masked x0
writes, using its artifact/paired-byte connection. This adds no trace execution claim:
public decoding, initialized register history and original MUL/DIV retirement
still require native v2 connections. The existing three execution families and
shared logical history definitions are unchanged.

## Initialized unsigned MUL/DIV

[The family guide](Families/MulDiv/README.md) routes complete native Clean history, derived read/write/terminal bounds and the short public numerical result. Actual public bytes and stateful original decoding supply operation/zero metadata. Original instruction execution remains open.

## Original MUL/DIV register histories

[The short public claim](Families/MulDiv/Registers.lean) constructs actual original Sail register transfers, all segment states and code/misa frames. It includes aliases and original x0 writes. Original operation clauses and PC retirement remain unfinished.

## Original local MUL/DIV preparation and retirement

[The short public instruction-history claim](Families/MulDiv/Execution.lean) derives the original four-operation clauses and actual PC retirement over constructed register histories. All sixteen initialized cases, original x0 retirement and actual aliased second-MUL retirement pass. A full native row checks RV32 PC wrap. Complete fetched composition still needs stateful decoder replay.

## Complete fetched unsigned MUL/DIV execution

[The short public execution theorem](Families/MulDiv/FetchedExecution.lean) derives finite original fetch/stateful decoding/preparation/retirement from actual public initialization and native matching, reaching native terminal PC/register reads. [Regressions](../../../Tests/MulDivFetched.lean) cover all sixteen initialized cases, concrete arithmetic outcomes, x0/zero divisors, actual alias execution and empty rows. Shift/binop and subword memory are next; general compiler/cryptographic and whole-machine/protocol boundaries remain separate.

## Native shift/binop decoder checkpoint

[The short data certificate](Families/ShiftBinop/NativeDecoder.lean) checks actual native decoder export against independent public bytes and original Sail decoding. [The family guide](Families/ShiftBinop/README.md) records its twelve ordinary forms, original x0 variants, native immediate/mask differences and complete sentinel tail. Dynamic table import/membership and shift/binop execution are next; this certificate supplies no circuit or initialized trace claim.

## Subword connection boundary

[The native subword local import](../Circuits/SubwordMemory/README.md) retains
actual state/decoder fields, all three memory ports and clocks. Both dynamic
queries are extracted from native acceptance. Generic history machinery has not
yet been instantiated for subword operations: public/native decoding, read/write
bounds, byte-store composition, initialized Sail reads/retirement and complete
family execution remain unfinished. Local import adds no subword trace coverage.

The [subword local connections](../Circuits/SubwordMemory/Lookups.lean) now derive
canonical selectors and resolve all seven native tagged regions to their helpers.
These local results do not add initialized subword history or execution coverage.
Native operation routing, selected limbs and actual read/write effects are still
needed before instantiating the generic history and original Sail transport.

[Subword operation routing](../Circuits/SubwordMemory/Routing.lean) now derives
actual mode tags and query fields from native equations and separator membership.
Six complete local accepted rows cover ROM/RAM loads, x0 and stores, but public
instruction decoding and initialized memory/history are still required before
original Sail transport. The subword family adds no initialized execution claim
at this checkpoint; general numerical effects are the next dependency.

[Subword native values](../Circuits/SubwordMemory/Values.lean) now derive exact
offset/trap controls, bounded load candidates, actual x0 scaling and store
clearing/placement write assembly. The original six full rows support all new
claims nonvacuously. Actual decoder membership, packed-key normalization and
initialized source/old-RAM/whole-write bounds are still required before original
Sail transport. This checkpoint adds no initialized subword execution claim.

[Subword public fields and load writes](../Circuits/SubwordMemory/Decoding.lean)
now derive all native decoder fields and written load bounds from actual public
byte construction, original Sail decoding, complete logical setup membership and
native acceptance. This closes the local Boolean x0 dependency. Native exported
decoder fidelity, raw-key normalization and initialized history still precede
original subword instruction/trace execution and composition.

[Native subword decoder fidelity](Families/SubwordMemory/NativeDecoder.lean)
connects every actual exported row of the thirteen-word fixture to independently
read original Sail setup. Six forms, signed immediate/x0 variants, unused-index
clearing, unsupported LW and full sentinel tail are checked under unchanged limits.
This is a specific Import/data prerequisite; initialized subword history, bounded
source/old-RAM reads, packed-key binding and original execution remain next work.

[Initialized native subword history](Families/SubwordMemory/History.lean)
now constructs complete original Clean history and newest reads for all three
mixed register/RAM ports. Actual public Sail seed reads/PC and native state/memory
matching derive every row/prior clock input. Eight fixtures include ROM shadows,
actual SB/SH writes, x0 and a source/destination readonly-refresh alias. Stale
alias matching rejects, and full native clock carry plus malformed clock
rejections pass. Canonical reads/store bounds, packed-key binding, architectural
ROM projection and original subword instruction execution remain next work.

[Initialized native subword value bounds](Families/SubwordMemory/Values.lean)
derive every actual read/write/terminal payload range from public original
initialization and decoding in the same Sail state, with native matching.
Native packed-key normalization and disjoint byte clearing/placement preserve
merged SB/SH writes using both source and old reads. Eight full fixtures include
actual overlapping instruction/shadow bytes, x0 and readonly alias refreshes.
Address/width/sign/ROM bindings and original subword execution remain next work;
no expected read, result or intermediate state is supplied.

[Initialized subword native addresses](Families/SubwordMemory/Address.lean)
now derive RV32 byte-address addition, offsets, containing aligned words and
actual load/store port addresses from one public state supplying initialization
and original decoding. Established history derives the source bound; decoded
fields derive every remaining numerical interface. Eight unchanged initialized
traces retain all forms, x0 and aliases, while complete native signed/wrap rows
check boundary carries. Original width/sign/byte effects, architectural ROM
projection and instruction execution remain next dependencies.

[Initialized subword load values](Families/SubwordMemory/Loads.lean) now derive
original Sail byte/halfword extension functions and actual masked writes from
one public state supplying initialization and original decoding. The second
native read range, both offset bits and exact ROM index are derived. Eight old
full traces remain unchanged; a ninth full odd LH-to-x0 trace prevents an
unconditional alignment premise. Store byte windows and original architectural
access/exception/retirement/execution remain open.

[Initialized subword store bytes](Families/SubwordMemory/Stores.lean)
derive every SB/SH byte update from the same public state used for initialization
and original sparse decoding. Existing native history supplies both actual
source and old-RAM read bounds. Eight unchanged complete traces retain their
actual matching; SB offset-three and SH halfword replacement preserve all other
old bytes. No per-row expected read/write, range, alignment or intermediate
state is supplied. Architectural read/write/ROM binding and original exception/
retirement behavior remain open dependencies.

## Combined reduced-machine scope

The [combined row intake](../Circuits/ReducedMachine/README.md) is separate from
these standalone execution claims. Native reduced fixed setup and selector/operand
connections precede initialized combined histories and original Sail execution.
The [current v3 adaptation](../../../V3_ADAPTATION.md) keeps compiler, logical
acceptance, initialization and worker boundaries explicit.

## Actual regenerated reduced history

[The native reduced history interface](Families/ReducedMachine/History.lean)
now derives complete logical memory consistency/newest reads and local/prior
clock ordering from actual public seed construction and accepted native matching.
Its [registry](../Helpers/Context/ReducedMachine.lean) binds the independently
regenerated117-equation target, all actual ports and explicit modeled setup,
separately from historical JSON. Terminal clocks count four ticks per native
row; terminal machine/protocol soundness is still separate. Source word bounds,
public decoding and original instruction execution remain open. Review the
[native trace guide](Families/ReducedMachine/README.md) for precise scope.

[Actual reduced LW/SW transfers](Families/ReducedMachine/WordMemoryTransfers.lean)
now derive original same-pre-state GPR/RAM/ROM reads and final writes throughout
projected initialized history. Actual readonly aliases/OLDREADs remain; exact
constructed ROM bytes supply loads independently of matched shadow values.
Original unmasked x0-load writes and unmasked SW memory writes retain their
separate semantics. No expected per-row answer is supplied. Retained LOAD/STORE
virtual-memory/platform/access/privilege clauses, normal/fetched/common memory
execution and physical/global enforcement remain open.

[Actual reduced retained LW/SW clauses](Families/ReducedMachine/WordMemoryClauses.lean)
now execute at derived row states. Initial reference configuration applies only
to nonempty memory programs; public ordinary RAM cells plus actual initialized
origins, or native ROM bounds, derive local address restrictions. Real history
transports every local CSR/permission. Original load-to-x0 reads remain and SW
writes actual RAM. PC preparation/normal/fetched/common memory remains open;
no native enforcement or full positive nonempty memory witness is claimed.

[Separate actual reduced LW/SW fetched execution](Families/ReducedMachine/WordMemoryFetchedExecution.lean)
now proves original byte fetch/stateful decoder/normal PC preparation/clause/
retirement along the native PC chain, with exact terminal architectural readers.
Source/read/write/range/address/configuration/state/order/replay are derived; all
independent shadow tokens stay native-matched. Empty programs retain CSR freedom.
Common mixed supported memory and physical/global boundaries remain separate.

## Common seven-profile native projected history

[Unified original decoding](Families/ReducedMachine/UnifiedDecoder.lean),
[initialized word ranges](Families/ReducedMachine/UnifiedValues.lean) and
[common history/domain roots](Families/ReducedMachine/UnifiedHistory.lean) now
cover six-profile support plus LW/SW through ONE actual initialized chain. All
native shadow tokens remain; only architectural Sail transfers are filtered.
Chronological states, code/misa frames and stateful source replay are derived.
Common retained/normal/fetched instruction execution remains next; arbitrary
logical public source images are not identified with exact native ROM.

## Common original fetched memory execution

[The seven-profile original fetched root](Families/ReducedMachine/UnifiedFetchedExecution.lean)
now connects common initialized projected states to finite normal/fetched
execution and actual terminal PC/architectural readers. All native shadows remain
matched. Exact NativeROM mixed-memory input scope is explicit; existing arbitrary
ordinary-code roots stay unchanged. Local source/profile/configuration/domain/
read/result/order/replay/PC obligations are derived, not public desired answers.
Worker/protocol/padding/terminal/init/teardown and physical/completeness remain open.

The [fresh Blake2 worker checkpoint](../Circuits/Blake2Worker/README.md) checks local row intake/control only. Caller projection and argument references are not a worker stream or an enforced global ledger; no delegated RAM frame or whole execution is inferred.

The [native worker fixed-pool checkpoint](../Circuits/Blake2Worker/README.md) checks all five stored XOR regions. This adds no worker ledger or request/worker fulfillment, converse, accounting or delegated execution claim.

The [worker query connection](../Circuits/Blake2Worker/QueriesTheorems.lean) closes local compiled lookup projection only. Static query counts are not worker issuance/accounting, and no main byte/RAM frame crosses unproved worker actions.

The [native worker ABI-local memory root](../Circuits/Blake2Worker/MemoryTheorems.lean) now derives canonical
pointer alignment/scalar-implied bounds and all43 actual Boolean borrow and
timestamp-difference laws from complete local acceptance. Initialized16bit reads,
raw clocks/processing multiplicity, alltoken matching and issued worker/protocol
accounting remain open. Main histories/frames do not cross unproved worker actions.

The [normalized worker processing root](../Circuits/Blake2Worker/ProcessingTheorems.lean) derives Boolean multiplicity
and allinactive memory-field zeroing under an explicit additional native
individual-convention relation. This relation is separate from the352 local JSON
equations and physical quotient/LDE/last-row enforcement. Worker keys/tokens,
initialized active ranges/clocks, cancellation and issuance/accounting remain open.

The [unused worker memory-key roots](../Circuits/Blake2Worker/MemoryKeysTheorems.lean) retain all43 access/read/write
sides and common processor clock, deriving stage2/quotient-unit reference key
agreement and equal products before division under normalized processing
acceptance. Active initialization/keys, native auxiliaries, full matching and
issuance/accounting remain open; no main frames cross unproved worker actions.

The [worker auxiliary roots](../Circuits/Blake2Worker/AuxiliaryTheorems.lean) now telescope all43 native memory factors
across the selected full domain under an explicit individual normalized auxiliary
acceptance contract and actual first/last public-claim boundaries. Separate typed
quartic slots, no division or terminal claim1. Product balance does not prove
full token matching/initialization or a delegation ledger; active ranges/keys/raw
clocks and issuance/converse/accounting remain open. No main frame crosses an
unproved delegated action, and physical enforcement stays separately scoped.

The [worker delegation sum roots](../Circuits/Blake2Worker/DelegationTheorems.lean) derive ordinary auxiliary sums from
native polynomial divisibility/degree/domain/sample inputs and normalize the
unified statement's returned-claim accumulator component. Main claims remain
opaque until their actual caller auxiliaries are connected; scalar balance is
not issuance/matching/converse/accounting. Physical/global capacity/dispatch/
challenge boundaries and active initialized memory effects remain open.

The [main caller auxiliary roots](../Circuits/ReducedMachine/DelegationTheorems.lean) now derive main claims from all native
ordinary-row auxiliary values and connect them to worker-row scalar sums. Separate
quartic92 and body92 roles remain explicit. Full body acceptance here does not
require every row active; existing initialized logical trace/history roots remain
unchanged. No inactive contribution is discarded, and padding/filter/matching,
global sequence/capacity/dispatch/challenge boundaries and accounting stay open.

The [configured caller/worker component](../Circuits/ReducedMachine/ConfiguredDelegationTheorems.lean) now retains the selected native
sequence/type/setup/shared-challenge checks and configured-slot counter over the
same returned proofs as the full-row scalar balance. Processing acceptance
derives Boolean indicators and an exact canonical multiplicity count below the
field modulus, with at most2048 selected proofs. No inactive auxiliary value is
dropped; capacity is not an issued count or matching/accounting certificate.
Initialized padding/filter/history, full43-token matching, active key/read/clock
refinement and physical/global transcript/setup/dispatch enforcement remain open.

The [native public memory-boundary component](../Circuits/ReducedMachine/MemoryBoundaryTheorems.lean) combines all selected worker
read/write products with the actual returned-main-claim fold and32-register/PC
source contributions. Public full32-bit values split before field casting;
x0 timestamps and PC initial time4 remain. Successful inverse-operation relations
clear only boundary denominators, retaining zero worker factors. Main grand
claims still need actual main state/memory/masking/initialization auxiliary
bindings; product balance does not establish token matching or initialized
histories/active bounds/accounting. Existing logical execution scopes remain.

The [actual main auxiliary component](../Circuits/ReducedMachine/MainAuxiliaryTheorems.lean) now derives returned main claims
from full ordinary-row memory/state/masking/initialization products, preserving
the actual execute polynomial and unmasked initialization. Same returned claims
compose with full worker products and public register/PC contributions without
factor cancellation or an execute-one premise. Token matching, initialization/
active bounds and faithful caller padding/filter/history remain open; existing
logical execution scopes and physical/general refinement boundaries are unchanged.

The [native decoder-access extension](../Circuits/ReducedMachine/DecoderArgumentTheorems.lean)
retains every ordinary physical-domain observation in its normalized source
interface. Complete body plus individual decoder access admits execute0/request1;
it supplies no faithful caller filter or active logical execution trace. Existing
initialized execution/history roots and their explicit scopes remain unchanged;
no Sail frame crosses unproved delegated actions.
