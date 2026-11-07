# Memory helper review

[Ports](Ports.lean) preserves the shared address/value/timestamp interpretation.
Native v2 direct shuffle-RAM ports use two 16-bit words; their metadata is
[resolved from physical columns](../../../Import/Parse.lean) and retained by the
[ADD/SUB artifact](../../Circuits/AddSub/Artifact.lean). The actual destination
write maps to logical variables 37/38, separately from its old value and raw hint.

[History](History.lean) preserves the source's explicit initialization writes and
native transfer events. [Row/token acceptance](../Context/Model.lean) compares
actual native address/time/value tokens, preserving raw field limbs injectively.
The checked [trace claim](../../Trace/History.lean) constructs complete Clean
online consistency and newest preceding reads from matching, initial clock
boundaries and unique seed addresses. No expected read value is supplied.
[Initial image](InitialImage.lean) and [public boundary](PublicImage.lean) now bind
seed values and initial PC to actual Sail reads; missing data rejects construction.
[Image proofs](../../../Proofs/Trace/InitialImage.lean) are copied unchanged and
derive seed bounds, zero clocks, address injectivity and read-state preservation.
[Value proofs](../../../Proofs/Trace/Values.lean) now derive native read/write/terminal
word bounds using initialized history and the decoded zero flag.
The same public seed boundary and generic history induction now support the
[word-memory registry](../../Trace/Families/WordMemory/History.lean), including
all native mixed ports and discarded shadow reads. Its
[write rules](../../../Proofs/Trace/Families/WordMemory/Values.lean) preserve ranges
through RAM copies, ROM data selection and actual x0-masked writes. The separate
[architectural projection](../../Trace/Families/WordMemory/Projection.lean) is now
checked under its own public seed constructor.
[Sail history](SailHistory.lean) retains the shared actual-read/write representation;
[its proof](../../../Proofs/Trace/SailHistory.lean) derives all intermediate states
from Clean consistency and public seeds. V2 masked writes preserve x0; public
RAM alignment supplies byte-window disjointness. [Grouped row reads/writes](../../../Proofs/Trace/PortReads.lean)
transport actual Sail accesses, including readonly alias stutters.
The [word-memory instance](../../Trace/Families/WordMemory/SailHistory.lean) now
uses the same realization/grouping with checked mixed-port x0 preservation. It
recovers actual source-register reads, RAM/register writes and intermediate
states for the full supplied native cell image.
[Whole-address projection](Projection.lean) retains the original full native
history while erasing shadow addresses from architectural transfers.
[Shadow-aware initialization](ShadowImage.lean) reads only architectural cells
and appends independent canonical native shadow seeds. Its
[short trace claim](../../Trace/Families/WordMemory/Projection.lean) derives actual
Sail transfers and final architectural matching, including ROM loads with no
Sail shadow bytes. Clocks, unique addresses and x0 preservation follow from the
constructors and accepted native matching/decoding. The same initializer now
supplies all seed bounds to the existing shared native range induction, deriving
read/write/terminal ranges for retained and erased accesses alike.
[Retained-port transport](../../../Proofs/Trace/PortProjection.lean) now handles
readonly refresh prefixes and aliases after projection. The
[native word-memory instance](../../../Proofs/Trace/Families/WordMemory/ProjectedPorts.lean)
proves final-port retention and derives actual pre-state source reads and masked
writes. Original instruction execution and the fixed logical native zero-boot
connection are now checked; physical argument/ROM enforcement remains separate.
[Indirect descriptors](IndirectPorts.lean) are retained reusable definitions;
v2 batched worker arguments and indirect-port import remain pending.

[Platform](Platform.lean) is copied unchanged from the pinned source. Its public
configuration describes actual Machine CSRs, PMP/PMA permissions, disabled HTIF
and an ordinary-address domain outside CLINT/signature windows. Native projected
histories now [preserve it](../../Trace/Families/WordMemory/Platform.lean), and
actual RAM port effects feed original Sail virtual-memory calls.
[ROM transport](../../../Proofs/Trace/Families/WordMemory/ROMTransport.lean) now
combines actual public extraction with retained reads; native ROM bounds derive
ordinary addresses. Original ROM LW clauses, including x0, reach actual native
after-states without equating shadow and ROM values.
[Original RAM clauses](../../../Proofs/Trace/Families/WordMemory/RAMExecution.lean)
now reuse actual native port effects and public decoder metadata, deriving rs2,
RAM reads, selectors and masked destination effects.
[Row retirement](../../../Proofs/Trace/Families/WordMemory/Retirement.lean) now
reuses actual history/control commutation and unchanged configuration frames;
original preparation and tick_pc preserve these native data effects.
[Native assembly](../../../Proofs/Trace/Families/WordMemory/Execution.lean) derives
exact modular PC successors. Complete finite trace/fetch composition and the
fixed zero-boot profile connection are checked; physical enforcement remains separate.

[Original initialization](Initialization.lean) and its
[proof](../../../Proofs/Trace/Initialization.lean) are copied unchanged. The
[fixed native boundary](NativeBoot.lean) derives architectural zero reads and
independent zero shadow seeds from the original profile and native public domain.
[The short boot theorem](../../Trace/Families/WordMemory/NativeBoot.lean) reuses
complete original execution, while actual native shadow paths force terminal zero.
The v2 runtime/replayer sources are pinned. [Explicit byte padding](BytePadding.lean)
now inserts finite zero bytes using the original Sail map. Exact lookup, actual
zero-word reads, prefix/outside preservation and original boot/configuration
frames are proved symbolically. The [public loader](../Tables/PaddedROMImage.lean)
derives complete ROM extraction and boot execution; physical setup/initialization
enforcement and general Rust refinement remain separate.

## Unsigned MUL/DIV observations

[Register transfer/history observables](MulDiv.lean) describe actual original Sail reads/writes, constructed segment states, final cell matching and code/misa preservation. [The short public claim](../../Trace/Families/MulDiv/Registers.lean) derives them from actual public bytes/seeds and native matching; calculations remain under Proofs.

## Original local MUL/DIV execution observations

[Instruction-history observations](MulDivExecution.lean) combine constructed real register histories, original instruction identity, native successor bounds and original local Sail preparation/retirement. [The short public theorem](../../Trace/Families/MulDiv/Execution.lean) derives all interfaces; complete fetched composition remains separate.

## Ordinary shift/binop register histories

[Actual transfer/history observables](ShiftBinop.lean) retain original Sail
source and old-destination reads in the same pre-state, actual masked writes,
constructed segment states, source replay, code/misa frames and final cell matching.
[The short public claim](../../Trace/Families/ShiftBinop/Registers.lean) derives
these from actual public initialization and complete native matching/decoding.
[Native x0 preservation](../../../Proofs/Trace/Families/ShiftBinop/ZeroRegister.lean)
connects to the unchanged shared cell-history realization; [port transport](../../../Proofs/ShiftBinop/PortReads.lean)
reuses the three original pinned declarations unchanged with checked v2 metadata.
[All twenty-four regressions](../../../../Tests/ShiftRegisters.lean) reach actual
Sail numerical writes and all twelve discarded whole-state stutters. Original
instruction clauses and PC/fetched execution remain separate.

## Ordinary shift/binop original clauses

[Clause-history observables](ShiftBinopClauses.lean) now connect retained original
Sail instructions to the actual native row histories and constructed GPR states.
[The short public claim](../../Trace/Families/ShiftBinop/Clauses.lean) derives
original clause execution, source bounds, selected operands and actual result
writes from initialized native matching and public decoding. [All twenty-four regressions](../../../../Tests/ShiftClauses.lean) execute the original clauses;
all twelve x0 variants preserve the whole data state. PC preparation/retirement
and complete fetched execution remain separate.

## Shift/binop retirement and fetched execution

[Retired-step/history observables](ShiftBinopExecution.lean) retain original
dispatch, actual native pre/post states and the exact bounded successor PC.
[The local claim](../../Trace/Families/ShiftBinop/Execution.lean) derives original
preparation/retirement; [complete fetched execution](../../Trace/Families/ShiftBinop/FetchedExecution.lean)
composes actual original decoding and normal steps through native PC matching.
[All twenty-four cases and empty traces](../../../../Tests/ShiftFetched.lean)
derive terminal PC/cell reads, including twelve x0 PC advances. [Complete native carry fixtures](../../../../Tests/ShiftPC.lean) preserve low carry and RV32 wrap.
Remaining subword, CSR/delegation and unified protocol claims remain separate.

## Actual native reduced original register histories

[Reduced observables](ReducedMachine.lean) retain actual native source, old-
destination and masked-write ports and original selected-shift decoding.
[The short public claim](../../Trace/Families/ReducedMachine/Registers.lean)
derives all original Sail states/GPR transfers, preserved code/misa, original
decoder replay and final cell matching from public seeds and native matching.
[Native mixed-port constraints](../../../Proofs/ReducedMachine/NativeShiftPorts.lean)
prove register space/indices, and [actual x0 preservation](../../../Proofs/Trace/Families/ReducedMachine/ZeroRegister.lean)
feeds unchanged shared induction/realization. Aligned public cell-domain input
remains explicit; no expected read, write, intermediate state or replay result
is supplied. This is not original selected-operand/clause/PC execution or broad
physical/setup/protocol/terminal closure. [Eight regressions](../../../../Tests/NativeReducedRegisters.lean)
distinguish positive imported-port mechanics from complete native acceptance.

## Actual native reduced original clauses

[Reduced clause/history observables](ReducedMachineClauses.lean) retain original
Sail instructions and actual native row states. [The short public claim](../../Trace/Families/ReducedMachine/Clauses.lean)
derives all original shift clause executions, source bounds, selected operands
and actual writes from public initialization/decoder and native matching. No
expected result, read or intermediate state is supplied per row. Actual readonly
rs2/x0 participation is retained on immediate forms. [Eight regressions](../../../../Tests/NativeReducedClauses.lean)
distinguish twelve concrete original Sail executions from full 117-equation
native acceptance. Numerical PC and normal/fetched retirement, other profiles
and setup/physical/protocol/terminal/init remain separate.

## Native reduced original retired/fetched execution

[Small execution observables](ReducedMachineExecution.lean) retain actual original
normal nextPC/clause/tick_pc execution, while [the public fetched claim](../../Trace/Families/ReducedMachine/FetchedExecution.lean)
now derives all states and terminal PC/cell reads from fixedData acceptance and
original public initialization/full shift decoding. [Native proof](../../../Proofs/ReducedMachine/NativeShiftExecution.lean)
transports proved original GPR histories through control-register updates; no
expected reads, source ranges, successors or intermediate states are supplied.
Aligned tracked cells remain meaningful input. Other combined operations and
physical/setup/protocol/padding/terminal/init/completeness remain separate.

[Complete nonempty native SLL/x0 fixtures](../../../../Tests/NativeReducedPositive.lean)
now check all native equations/lookups and actual state/memory matching,including
readonly refreshes and discarded nonzero candidate participation,before deriving
original initialized execution/terminal reads. Original public initialization and
decoder construction are proved;no per-row state/read/result is supplied. Native
public/preprocessing/physical fidelity and other combined profiles remain separate.

## Actual native reduced arithmetic registers

[Small arithmetic history observables](ReducedMachineArithmetic.lean) retain all
original GPR observations and actual masked writes, segment states, final matching
and decoder replay as conclusions. [The public claim](../../Trace/Families/ReducedMachine/ArithmeticRegisters.lean)
uses actual native arithmetic mixed-address/zero proofs before unchanged shared
Sail realization. [Port proofs](../../../Proofs/ReducedMachine/NativeArithmeticPorts.lean)
keep readonly aliases and immediate rs2/x0 participation. Numerical PC and retained
clause execution remain separate, particularly AUIPC's incoming PC observation.

## Original arithmetic preparation and retirement

[Small arithmetic execution observables](ReducedMachineArithmeticExecution.lean)
retain normal row execution and initialized instruction history. [Public execution](../../Trace/Families/ReducedMachine/ArithmeticFetchedExecution.lean)
now derives original successful fetched steps and terminal PC/cell observations.
[Native assembly](../../../Proofs/ReducedMachine/NativeArithmeticExecution.lean)
proves AUIPC's prepared incoming PC read and derives original operands/results
from actual GPR history and initialized ranges. No per-row state/range/read/result
or PC answer is a public input. Generic modeled setup and tracked-cell alignment
remain explicit; mixed profiles/native physical setup/protocol boundaries remain open.

## Mixed supported native history

[Common range induction](../../../Proofs/Trace/Families/ReducedMachine/SupportedValues.lean)
and [x0/state realization](../../../Proofs/Trace/Families/ReducedMachine/SupportedZeroRegister.lean)
now cover interleaved selected shift/arithmetic rows. [Actual local rules](../../../Proofs/ReducedMachine/NativeSupportedLocal.lean)
are derived from original decoded profiles; they are not supplied publicly.
[Code/misa frames](../../../Proofs/Trace/Families/ReducedMachine/SupportedCodeHistory.lean)
and [finite original execution](../../Trace/Families/ReducedMachine/SupportedExecution.lean)
construct all states, decoder replay and terminal observations with exact fixedData
acceptance. Other profiles and native public/physical/protocol boundaries remain open.

## Actual reduced bitwise GPR transport

[BitwiseRegisterTransfer](ReducedMachineBitwise.lean) observes all three original
GPR reads in one pre-state and the actual masked write. [Native port proofs](../../../Proofs/ReducedMachine/NativeBitwisePorts.lean)
derive register addresses and readonly aliases before shared history reuse.
[Common initialized execution](../../Trace/Families/ReducedMachine/SupportedExecution.lean)
constructs the states and order from native matching and public seeds; these
observations are not supplied as public answers.

## Initialized native comparison ranges

[Comparison value bounds](../../Trace/Families/ReducedMachine/ComparisonValues.lean)
use proved native resolver/masked-write preservation in unchanged shared time
induction. Both readonly refreshes and discarded writes remain in native matching.
[Canonical comparison results](../../Trace/Families/ReducedMachine/ComparisonResults.lean)
discharge every internal read bound from those initialized facts. These numerical
read words are not yet original pre-row Sail GPR/clause/fetched execution.

## Original comparison GPR transport

[ComparisonRegisterTransfer](ReducedMachineComparison.lean) observes all three
original reads in one pre-state and actual masked writes. [Native address proofs](../../../Proofs/ReducedMachine/NativeComparisonPorts.lean)
justify shared read/write transport, retaining aliases and readonly immediate
rs2/x0. [Common original execution](../../Trace/Families/ReducedMachine/SupportedExecution.lean)
constructs every state/order and discharges both source bounds from initialized
native history, including comparison rows. These observations are conclusions,
not public row answers. Earlier numerical-only comparison scope is superseded.

[Native branch fields](../../../Proofs/ReducedMachine/NativeBranchFields.lean)
now derive readonly register-space source routing and the present third port at
x0 with zero write. Its old read still participates in matching. Original branch
GPR binding, initialized preservation/history and clause execution remain open;
local address fields do not supply those observations.

[Actual branch condition numerics](../../../Proofs/ReducedMachine/NativeBranchCondition.lean)
now identify operand equality/order with both source bounds kept internal. Common
initialized ranges/GPR state construction has not yet been extended to branch
rows. Public decoding and native zero-write/readonly preservation must justify
that extension before any initialized branch numerical/Sail execution claim.

[Initialized branch ranges](../../Trace/Families/ReducedMachine/BranchValues.lean)
now follow from proved actual zero dummy-write/readonly preservation and shared
public-seed time induction. [Numerical branch assembly](../../Trace/Families/ReducedMachine/BranchResults.lean)
discharges both source bounds internally. Original GPR/cell observations, retained
Sail branch clauses and common mixed execution remain separate next connections.

[Branch register observables](ReducedMachineBranch.lean) now describe all three
original reads in one pre-state, actual zero dummy write and whole-data-state
stutter. [Public history](../../Trace/Families/ReducedMachine/BranchRegisters.lean)
derives every state/order/read/write/final match/code/misa frame and decoder replay.
[Branch fetched execution](../../Trace/Families/ReducedMachine/BranchFetchedExecution.lean)
adds original clauses and actual conditional PC effects; initial misa readability
is explicit, each local read derived. This closes the separate branch GPR/Sail
connection above. Common mixed branch integration and complete positive nonempty
native branch witnesses remain open; port-group fixtures alone do not close them.

[Common mixed history/execution](../../Trace/Families/ReducedMachine/SupportedExecution.lean)
now includes branches after new actual preservation/x0/register-space/profile
transport. All three ports, aliases and dummy x0 old-read/zero-write remain in
one initialized induction/history. Both source bounds, original parity, every row
state/read/result/PC/control and decoder replay are derived. Public initial misa
readability is required only for branch-containing programs; its unrestricted
value is transported to every local read. [Regressions](../../../../Tests/NativeReducedSupportedBranches.lean)
are public source/configuration checks, not full nonempty native mixed witnesses.

[Native jump routing](../../Circuits/ReducedMachine/JumpTheorems.lean) derives
readonly rs2/register-space and masked rd fields, retaining every actual port.
These are not yet original Sail GPR/old-destination observations or initialized
jump histories. Internal base/immediate bounds still need original public input
and history discharge before architectural raw addition/Sail execution. Current
common initialized support excludes jumps; local output PC bounds alone do not
establish that connection.

[Jump write preservation](../../../Proofs/ReducedMachine/NativeJumpPreservation.lean)
now derives bounded PC+4 return writes from original public incoming PC, before
any source-range induction. [All initialized jump ranges](../../Trace/Families/ReducedMachine/JumpValues.lean)
then include both readonly ports, aliases, old-destination/discarded writes and
terminal cells. [Numerical jump results](../../Trace/Families/ReducedMachine/JumpResults.lean)
derive original return/target/cleanup without source-bound answers; original
pre-row Sail GPR/cell observations and clause/fetched execution remain next.

[Jump transfer/history observables](ReducedMachineJump.lean) now name actual
all3port GPR reads/write and chronological initialized states/final matching.
[Fresh port proofs](../../../Proofs/ReducedMachine/NativeJumpPorts.lean) establish
original register cells before shared history lemmas. JAL x0 reads remain despite
PC base; JALR aliases/readonly rs2/old destination/masked writes share one pre-state.
[Public history](../../Trace/Families/ReducedMachine/JumpRegisters.lean) derives
zero preservation/code/misa/decoder replay without supplied state/read/result or
initial CSR-read answers. Retained clauses/PC preparation/fetched support remain next.

[Initialized jump fetched execution](../../Trace/Families/ReducedMachine/JumpFetchedExecution.lean)
now derives all source bounds, states/reads/writes/replay and local CSR observations
through actual history before retained normal retirement. Public initial configuration
is narrow; GPR-only history still needs no CSR premise. Native output bounds and PC
chain determine terminal observations, with no supplied state/read/target answers.

[Common mixed jump execution](../../Trace/Families/ReducedMachine/SupportedExecution.lean)
now uses one initialized range/x0/native-clock GPR/code/CSR/replay history across all
six profiles. Jump return preservation first gets alignment from original public
membership, not a source-range answer. Every source/read/write/state/control/replay/
terminal observation is derived; JAL x0 and readonly inputs/JALR aliases remain present.

[Actual native LW/SW port spaces](../../Circuits/ReducedMachine/WordMemoryTheorems.lean) now show load second port and store third port are memory events. Values/addresses/shadow reads/oldreads and code preservation need new proofs; do not reuse all-events-GPR framing.

[Actual reduced ROM input](ReducedMachineROMImage.lean) now constructs every
original little-endian byte of the native8wordfixture/fullUNIMPtail. [Derived
public facts](../../Trace/Families/ReducedMachine/ROMImage.lean) include full
extraction/every aligned read and register/outside-byte preservation. Actual
native LW ROM output is connected separately; ignored shadow values remain
independent. This does not establish Rust/public/physical setup refinement,
projected initialized row/Sail memory states or retained LOAD/STORE execution.

[Projected word-memory observable](ReducedMachineWordMemoryHistory.lean) now names
actual port domains, complete native matching and derived chronological Sail
segment states/final matching/ROM-byte/misa frames/decoder replay. [Public root](../../Trace/Families/ReducedMachine/WordMemoryHistory.lean)
uses independent public shadow seeds, full original decoding/native acceptance,
aligned cells and meaningful code capacity; no desired reads/states/frames supplied.
Retained LOAD/STORE/normal/fetched/common execution and physical enforcement remain open.

## Common native mixed memory-history observations

[Unified port domains and projected history](ReducedMachineUnified.lean) describe
actual chronological Sail states/segments, final cell matching and code/misa
frames. [The short public roots](../../Trace/Families/ReducedMachine/UnifiedHistory.lean)
derive these from original public setup, independent shadow initialization and
full native matching. Every shadow event remains native-matched; RAM refreshes
and SW OLDREAD/write remain architectural. No CSR premise or desired per-row
profile/read/state/frame answer is public. Retained mixed execution is separate.
