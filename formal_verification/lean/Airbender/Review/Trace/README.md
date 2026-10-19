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
