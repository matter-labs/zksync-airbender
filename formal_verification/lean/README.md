# Circuit verification

The [constructed native decoder setup](Airbender/Review/Circuits/ReducedMachine/PhysicalDecoderSetupTheorems.lean)
now retains the public slice, holes, full ordinary physical tail and separate
normalized last row on the same main observations. Ordinary-table membership
recovers original Sail source evidence; lookup extraction and initialized worker
matching remain open. See the [current status](VERIFICATION_STATUS.md).

The [native decoder table sum](Airbender/Review/Circuits/ReducedMachine/DecoderTableTheorems.lean)
now connects physical witness9, setup6-through15 and quartic88/72 on the same main
observations. Full ordinary auxiliary-sum equality follows from the native
zero/last polynomial boundary; matching/extraction, inactive request filtering
and initialized worker execution remain open. See the [current status](VERIFICATION_STATUS.md).

The [native decoder-access component](Airbender/Review/Circuits/ReducedMachine/DecoderArgumentTheorems.lean)
now binds actual quartic72/execute and all ten decoder fields to the same full-domain
main observations. Complete CSR body plus this individual decoder relation still
admits execute0/request1 for every decoder challenge. This is a local interface
limit; decoder table/global enforcement, initialized worker matching and parity
remain open. See the [current status](VERIFICATION_STATUS.md).

## What is checked

[Verification status](VERIFICATION_STATUS.md) lists v2 coverage and open tasks.
The [findings audit](FINDINGS.md) keeps observed behavior separate from unported
v3 findings and missing proof connections.

The current user priority is the [actual combined reduced machine](../../cs/reduced_machine_preprocessed_layout.json).
Its local row importer now retains the complete native constraints and tagged
queries; fixed setup and global argument connections remain open. No v2
reduced-machine execution theorem is claimed. Existing standalone-family
results are reusable components, not combined-machine coverage. The reduced
machine is word-only for memory operations; subword retirement is not a required
predecessor. See the [active priority and concrete blocker](FORMAL_VERIFICATION_PLAN.md#user-priority-native-reduced-machine-2026-10-21).

The proof path is:

```text
v2 compiled layout JSON → native Clean constraints → original Sail execution
```

This is the v2 backport based on dev revision
67ee094449abaebc77e58435f130ce6ea27721e5. Reused definitions and proofs come from
the original formalization revision 805909325 and the current PR #585 reference
b29277dd895499574e317a994fd89243a72f06cb; see the [adaptation snapshot](V3_ADAPTATION.md).
Exact source identities and hashes are in
[provenance](artifacts/provenance.json). Circuit and runtime Rust are unchanged.

Current execution coverage spans five circuit families:

- [ADD/ADDI/SUB/LUI/AUIPC](Airbender/Review/Trace/Families/AddSub/Theorems.lean):
  complete initialized original Sail execution and native terminal matching.
- [LW/SW](Airbender/Review/Trace/Families/WordMemory/Theorems.lean): original
  fetched Sail execution under the documented ROM/RAM/platform boundaries,
  including x0 loads and retained native shadow events.
- [Jumps, branches and comparisons](Airbender/Review/Circuits/JumpBranchSlt/README.md):
  native JAL/JALR links/targets, all six branch conditions/targets and all four
  comparison results/PCs. All original control clauses and retirement now reach
  native outputs in constructed initialized-history segments, with documented
  public ISA/landing-pad CSR profiles. [Complete fetched control execution](Airbender/Review/Trace/Families/JumpBranchSlt/Execution.lean)
  now derives finite original Sail execution, terminal PC/register matching and
  raw terminal PC bounds from accepted native matching and public inputs.

- [Unsigned MUL/MULHU/DIVU/REMU](Airbender/Review/Trace/Families/MulDiv/FetchedExecution.lean):
  complete initialized fetched execution, stateful original decoding, zero divisors,
  actual x0 writes and terminal matching under the documented misa.M profile.

- [Ordinary SLL/SRL/SRA/XOR/OR/AND](Airbender/Review/Trace/Families/ShiftBinop/FetchedExecution.lean):
  complete initialized original fetched execution for all twelve register/immediate
  forms, actual x0 writes, modular RV32 PC retirement and exact terminal matching.
  Native tagged lookup/helper results and numerical interfaces are derived.

Subword memory, delegation and whole-machine
protocol composition are still unfinished; the [plan](FORMAL_VERIFICATION_PLAN.md)
tracks the remaining dependencies. The checkpoint details below retain their
original snapshot structure.

The [subword offset/trap helper](Airbender/Review/Helpers/Tables/SubwordOffsetTheorems.lean)
now has a complete certificate over its actual 2,097,152 native exported rows,
including the explicit misaligned-load-to-x0 rule. This is the first subword
fixed-table connection; full subword circuit/history/execution remains unfinished.

The [subword load-data helper](Airbender/Review/Helpers/Tables/SubwordLoadTheorems.lean)
now certifies all 2,097,152 actual native load-data rows, including signed/unsigned
byte and halfword outputs, all offsets and retained unused keys. Its small public
claim derives both output bounds from lookup membership. Full subword circuit,
initialized history and original instruction execution remain unfinished.

The [original-RAM-limb clearing helper](Airbender/Review/Helpers/Tables/SubwordStoreClearTheorems.lean)
certifies all 2,097,152 actual native store-clear rows, including both byte masks,
all four offsets and retained unused zero outputs. Written-value placement is also certified; general subword numerical effects,
initialized history and original instruction execution remain unfinished.

The [written-value placement helper](Airbender/Review/Helpers/Tables/SubwordStorePlaceTheorems.lean)
certifies all 2,097,152 actual native placement rows, preserving SB byte positions,
SH full limbs at all raw offsets and unused zero outputs. The actual v2 ROM region, complete native import and operation routing are also
connected; initialized history and original execution remain open.

The [native subword import](Airbender/Review/Circuits/SubwordMemory/README.md)
retains all 51 equations, fourteen queries and actual state/port/decoder/setup
metadata. Its short public claim extracts both evaluated dynamic queries.
V2 has one word-indexed ROM region; v3 byte/halfword ROM regions do not apply.
Subword operation effects, initialized history and original execution remain open.

[Native subword tag resolution](Airbender/Review/Circuits/SubwordMemory/Lookups.lean)
now derives canonical selectors from acceptance and connects all seven regions
to the existing helpers, including exact all-zero disabling and word-indexed ROM.
[Native operation routing](Airbender/Review/Circuits/SubwordMemory/Routing.lean)
now derives all three accepted modes, actual query fields, ROM/RAM/load/store
limb selection and all-zero disabling. Six complete accepted rows and eight
mutation rejections pass. [Native value/write claims](Airbender/Review/Circuits/SubwordMemory/Values.lean)
now derive offset/trap controls, candidate values/bounds, actual masked load writes
and clearing/placement store assembly. Nine new rejection checks pass. Decoded
byte/halfword key normalization, initialized read/write bounds and original Sail
execution remain unfinished.

The arithmetic checkpoint includes complete initialized ADD/ADDI/SUB/LUI/AUIPC normal-path
execution and conditional row soundness, including actual masked destination
writes, original-opcode discarded x0 writes and aligned 32-bit PC wraparound. Native ten-column decoder placement/query order is checked;
public selected-profile setup construction and logical padded membership are now
connected separately from Rust generation/export fidelity.
The local circuit statements expose decoding, input bounds, preprocessing and
actual Sail reads; the initialized assembly below derives those interfaces. Native direct port/state metadata now supports
[initialized logical memory history](Airbender/Review/Trace/History.lean): accepted
state/memory matching and initial clock boundaries derive all row/prior clock
bounds, complete Clean memory consistency and latest reads. [Public Sail image construction](Airbender/Review/Trace/Initialization.lean) now
binds seed tokens and initial PC to actual upstream reads, deriving seed bounds,
clocks and uniqueness. [Public decoder recovery](Airbender/Review/Trace/Decoder.lean)
rejects native minus-one padding from the imported mask equations. Logical decoder
membership and initialized history now derive native read/write/terminal word
bounds. [Native-to-Sail history](Airbender/Review/Trace/SailHistory.lean) now derives
actual cell reads/writes and intermediate states, with native x0 preservation and
clock-derived row grouping. Readonly refreshes preserve the instruction pre-state,
including aliases. The [native PC path](Airbender/Review/Trace/PC.lean) now derives
all incoming bounds/alignment, bounded RV32 successors and the terminal PC bound.
The [decoded row assembly](Airbender/Proofs/Trace/Arithmetic.lean) now derives the
complete local interfaces and original Sail preparation/execution/retirement for
all five arithmetic opcodes. [Complete initialized arithmetic execution](Airbender/Review/Trace/Families/AddSub/Theorems.lean)
now reaches exact native terminal PC/register/RAM values through original Sail
code-byte reads, decoding and normal steps, including empty traces. Reversed
dependent ADD/ADDI witness rows reach PC 8 and x2=247. The [word-memory transfer checkpoint](Airbender/Review/Circuits/WordMemory/README.md)
now imports all native equations/queries and mixed ports. Complete modeled ROM
tables derive address alignment, exact ROM data, RAM/ROM load selection, masked
writes and RAM-only stores. Native Mersenne31 address addition, modular PC
successors and four-tick port scheduling are checked under explicit input bounds
and clock interfaces. [Public LW/SW decoding](Airbender/Review/Trace/Families/WordMemory/Decoder.lean)
now recovers original Sail source evidence, exact zero flags and native
PC/immediate bounds/alignment from complete padded membership, including x0
loads. [ROM extraction](Airbender/Review/Helpers/Tables/WordROMImage.lean) now reads
actual Sail bytes; native ROM query data inside that prefix has an original Sail
read proof. A complete four-MiB extraction covers all native ROM addresses. Physical native
boot/padding/ROM binding remains pending; word-memory execution is checked below.
[Initialized word-memory history](Airbender/Review/Trace/Families/WordMemory/History.lean)
now derives complete Clean consistency, latest native reads and every per-row/prior
clock input from actual public seed reads and accepted matching.
[Read/write/terminal ranges](Airbender/Review/Trace/Families/WordMemory/Values.lean)
follow through actual native load/store/mask rules and full decoder membership,
including discarded shadow reads. [Native-row effects](Airbender/Review/Trace/Families/WordMemory/Inputs.lean)
now derive effective-address addition, bounded aligned PCs, RV32 successors and
native clock/port order without per-row numerical premises.
[Word-memory Sail cell histories](Airbender/Review/Trace/Families/WordMemory/SailHistory.lean)
now derive actual original Sail reads/writes and intermediate states from the
full supplied native image. Mixed-port x0 writes are preserved, and reversed
store/load rows derive their intermediate RAM state and later read. Architectural
ROM-shadow accesses below four MiB are proved value-preserving, with every refresh
token retained in logical matching. [Architectural projection](Airbender/Review/Trace/Families/WordMemory/Projection.lean)
now realizes only GPR/RAM transfers while retaining the complete native history.
A separate public initializer reads architectural cells and independently retains
native shadow seeds. Ordinary/x0 ROM loads derive actual masked Sail writes even
with unreadable shadow locations and distinct shadow/ROM values. The same public
constructor now derives all full native read/write/terminal ranges through the
unchanged shared range induction, including erased shadow accesses.
[Projected native inputs](Airbender/Review/Trace/Families/WordMemory/Inputs.lean)
now derive address addition, bounded aligned PCs, modular successors and clock
laws through the same native calculations. Retained-port transport recovers
actual Sail source reads and masked writes; full constraints keep the final port
architectural. Ordinary/x0 ROM loads and dependent RAM store/load rows are checked.
[Code/ROM preservation](Airbender/Review/Trace/Families/WordMemory/CodeHistory.lean)
now preserves all bytes below four MiB and every successful public ROM extraction.
Public programs fitting that region retain original Sail instruction reads and
decoding through each projected prefix. A changing SW/LW history retains both
instruction words and their ROM image; absent shadow bytes stay absent.
[Platform configuration](Airbender/Review/Trace/Families/WordMemory/Platform.lean)
now survives initialized projected histories. Eight unchanged pinned modules
supply Sail's Machine translation, PMP/PMA and ordinary-memory path. Native RAM
ports derive actual virtual-memory store/load results on the same dependent
SW/LW fixture. [ROM transport and original LW clauses](Airbender/Proofs/Trace/Families/WordMemory/ROMExecution.lean)
now derive actual ROM virtual reads and original instruction-body effects from
public bytes and native history, including original x0. Initialized ordinary/x0
fixtures retain distinct native shadow and ROM values and reach the same actual
after-state. [RAM LW/SW clause assembly](Airbender/Proofs/Trace/Families/WordMemory/RAMExecution.lean)
now reaches the same derived native cell-transfer states. Public decoding derives
selectors/registers/immediates, and retained ports derive actual operand/RAM
reads. The reversed fixture reaches original SW then LW results with actual read
123 and destination write. [Native row retirement](Airbender/Proofs/Trace/Families/WordMemory/Execution.lean)
now derives exact modular native PC successors and composes original Sail
preparation, memory clauses and tick_pc through actual history/configuration
transport. Ordinary/x0 ROM loads reach native PC 4, and reversed SW/LW normal
steps reach PC 8 and actual terminal RAM/x3=123.
[Complete initialized word-memory execution](Airbender/Review/Trace/Families/WordMemory/Theorems.lean)
now composes every native row through actual fetched bytes, original decoding
and normal Sail steps. It derives exact native terminal PC and architectural
cells, retaining full matching for independent shadow tokens. Public ordinary
RAM, configuration, program size in ROM and actual ROM-prefix seed coverage
remain explicit; native matching discharges each local address domain. The
reversed SW/LW fixture reaches PC 8 and RAM/x3=123 through this general relation;
ordinary/x0 ROM loads and empty traces pass. Physical boot/ROM binding remains open.
Remaining families, general Rust
setup generation/export refinement and cryptographic argument soundness remain pending. This checkpoint does not inherit v3's completed coverage.

[Fixed native zero boot](Airbender/Review/Trace/Families/WordMemory/NativeBoot.lean)
now derives the general initialized execution boundary from the unchanged original
Sail zero profile and fixed native seeds/PC. Ordinary/x0 ROM fixtures reach PC
four and their actual destination values from all-zero GPRs; full native paths
keep shadows zero independently of ROM contents. Native word padding was retested:
the proving loader fills its input tail with zero, while the raw table constructor
uses UNIMP only beyond the supplied image. [A separate model](Airbender/Review/Helpers/Tables/WordROMPadding.lean)
proves this padding's extent/prefix/tail symbolically. The explicit
[loader constructor](Airbender/Review/Helpers/Tables/PaddedROMImage.lean) now
inserts actual Sail zero bytes and derives full four-MiB extraction, setup/profile
preservation and complete boot execution without a supplied padding/coverage
premise. Ordinary/x0 regressions retain full native matching; missing/oversized
prefixes reject construction. Physical setup/initialization exports and
Rust/cryptographic enforcement remain open.

[Native physical setup placement](Airbender/Review/Helpers/Tables/SetupColumns.lean)
is now checked for both artifacts, including all offsets and the reserved last
row. The complete [tagged row model](Airbender/Review/Helpers/Tables/PhysicalSetup.lean)
retains dummy/zero padding and native tags 23/24. Symbolic proofs recover exact
ROM/separator membership and actual Sail reads after public loader construction;
nonempty byte fixtures reject altered words and wrong tags. The actual regional
export fixture is checked below; full physical trace assembly, normalization/LDE
refinement and argument enforcement remain open.

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

## Read these first

The [Review guide](Airbender/Review/README.md) has two routes:
[individual circuit review](Airbender/Review/Circuits/README.md) and
[whole-trace review](Airbender/Review/Trace/README.md).

[Properties](Airbender/Review/Helpers/Properties.lean) defines soundness,
completeness and the observable circuit relation. Shared helpers are grouped by
[topic](Airbender/Review/Helpers/README.md). The public ADD/SUB surface is two
theorems in [Theorems](Airbender/Review/Circuits/AddSub/Theorems.lean), with
observables and assumptions in [Model](Airbender/Review/Circuits/AddSub/Model.lean).
Calculations stay in Proofs; Import has its own fidelity boundary.

## Clean and Sail

Dependencies are unchanged: Lean v4.31.0, Clean
1e563b9c27991b3795eb440c1ee0757edb4ce8b1 and the same Mathlib/lean-sail pins.
[Preparation](scripts/prepare_clean.py) guards Clean's original hashes before
applying the existing compatibility fixes. Native Clean expressions, assertions,
static tables and constraint satisfaction remain the only constraint semantics.

The [unchanged upstream Sail sources](vendor/sail-riscv/source/model/extensions/I/base_insts.sail)
and [generated Lean](generated/sail-rv32/SailRV32.lean) retain their original pins.
[Regeneration](generated/sail-rv32/README.md) documents source/compiler provenance.
No local replacement instruction semantics were added. The existing word and
Sail execution lemmas are copied unchanged; the artifact-specific proof is new.
The pinned custom-operation reference is retained for later work; no v2 custom
operation claim is made yet.


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

## Reproduce

Run from formal_verification/lean:

```sh
python3 scripts/prepare_clean.py
python3 scripts/check_resource_guard.py
python3 scripts/check_all.py
```

[The serial verification runner](scripts/check_all.py) checks each module with
one Lean thread and a 3072 MiB Lean allocation cap. The shared
[macOS watchdog](scripts/bounded_fv.py) limits the owned process tree to 3072 MiB
physical footprint, 4096 MiB resident memory and a finite wall budget, kills owned
processes after a violation and confirms termination. It uses a global lock and
rejects multiple Lean workers. These are sampled process measurements, not an OS
hard physical-memory ceiling. Redesign a proof when it exceeds the limits.
Dependency bootstrap also needs these limits; do not launch unbounded proof builds.
The same runner checks the standalone native exporter offline with its isolated
manifest/lock and one Cargo job, then reproduces the pinned fixture and rejects
malformed inputs. Use the repository-pinned Rust nightly alongside Lean.

Importer rejection tests are not a proof of faithful parsing. The
[trust boundaries](TRUST_AND_REVIEW.md) identify what remains external; the
[plan](FORMAL_VERIFICATION_PLAN.md) gives the next backport milestones.

With Lean's editor extension, inspect the embedded constraints with:

```lean
import Airbender.Review.Circuits.AddSub.Artifact
#print Airbender.AddSub.importedConstraints
```

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

[Public subword decoding](Airbender/Review/Circuits/SubwordMemory/Decoding.lean)
now derives all ten native fields for original LB/LH/LBU/LHU/SB/SH and actual
load writes/bounds, including x0. Seven full native rows and original public
byte images support both short claims; five decoder rejections pass. Native
exported decoder fidelity, packed-key normalization and initialized history
remain open before original subword execution and whole-machine composition.

[Actual subword decoder fidelity](Airbender/Review/Trace/Families/SubwordMemory/NativeDecoder.lean)
now connects every native exported decoder row to independently read original
Sail setup for the thirteen-word fixture: all six forms, negative immediates,
x0 loads, unused-index clearing, unsupported LW and complete sentinel tail.
Nineteen new strict importer checks and native binary-text/rejection checks pass.
Initialized history, packed-key binding and original subword execution remain open.

[Initialized native subword history](Airbender/Review/Trace/Families/SubwordMemory/History.lean)
now derives original Clean consistency and latest reads for all three mixed ports
from actual public Sail seeds/PC and native matching. Eight complete traces retain
ROM shadows, x0, SB/SH writes and source/destination alias refreshes; stale alias
matching, nonboolean clock carry and high overflow reject. Full native low-clock
carry is checked. Word/key bounds, architectural ROM projection and original
subword instruction execution remain separate next dependencies.

[Initialized native subword payload bounds](Airbender/Review/Trace/Families/SubwordMemory/Values.lean)
now derive all read/write/terminal ranges from one actual public state supplying
initialization and full original sparse decoding, with native matching. Exact
packed fields and disjoint byte contributions bound merged SB/SH writes without
assuming bounded results. Eight full traces retain actual code/shadow bytes,
x0 and alias refreshes. Address/width/sign/ROM bindings and original subword
instruction execution remain next work.

[Initialized native subword addresses](Airbender/Review/Trace/Families/SubwordMemory/Address.lean)
now derive RV32 source-plus-immediate addition, byte offsets and actual aligned
mixed-port words from the same public initialization/decoding and native matching.
Eight full initialized traces and two full-native signed/wrap boundary rows
exercise the connection. Width/sign/byte effects, architectural ROM projection
and original subword instruction execution remain next work.

[Initialized native subword load values](Airbender/Review/Trace/Families/SubwordMemory/Loads.lean)
now derive original Sail byte/halfword extension functions and actual masked
writes from public initialization/decoding and native matching. The exact native
ROM word index and retained alignment are derived. Nine complete traces include
an odd discarded LH-to-x0 without imposing unconditional alignment. Store byte
windows, architectural ROM/access/exception binding and original execution remain
next work; no confirmed defect or repair is claimed by this value checkpoint.

[Initialized native subword store bytes](Airbender/Review/Trace/Families/SubwordMemory/Stores.lean)
now derive every changed and preserved SB/SH byte from actual initialized reads,
original decoding and native constraints. Exact clearing/placement keys, size,
upper selection and SH alignment are derived. Architectural read/write and ROM
binding, original access/exception behavior and full instruction execution remain
next work; this byte-effect checkpoint adds no confirmed finding.

[Lossless native memory-key/token transport](Airbender/Review/Circuits/ReducedMachine/MemoryTokenTheorems.lean)
now proves the native indicator-to-Clean-space complement and raw-field tuple
injectivity, binds all three main ports and retains all43 worker keys/factors.
Pure permutation transport preserves duplicates. Native token matching and
initialized worker history remain open; scalar products do not supply them.

[Same-main-proof argument composition](Airbender/Review/Circuits/ReducedMachine/MainArgumentTheorems.lean)
now shares body rows, typed auxiliaries and both distinct claims across the checked
scalar/product components and configured worker batch. Matching/extraction and
initialized worker history remain open.

[Complete CSR body and initialized caller checks](Airbender/Review/Circuits/ReducedMachine/BodyPaddingTheorems.lean)
now include a nonempty runtime1991/x0 fixture. Both execute values satisfy the
complete117-equation/22-lookup BODY while retaining a request; body-only inactive
filtering is therefore unavailable. Full physical/global padding remains separate.

## Native full-domain logical token boundary

[The native ledger roots](Airbender/Review/Circuits/ReducedMachine/TokenLedgerTheorems.lean) bind all ordinary main/worker/public
tokens to the checked scalar product and retain exact precompression matching as
an explicit logical trust boundary. Identical inactive incoming port/state tokens
cancel only as duplicate-preserving multisets. Initialization/teardown, every worker
access and caller requests remain. [Controls](Tests/NativeTokenLedger.lean) do not establish
initialized worker history, active ranges/key refinement, fulfillment or physical
cryptographic extraction. Original initialized execution interfaces are unchanged.

## Native active main-state path

[The main-state theorem](Airbender/Review/Circuits/ReducedMachine/MainStateHistoryTheorems.lean) derives actual active main chronology,
clock bounds, four-tick counts and distinct0/1/2 write slots from complete native
body acceptance and the same explicit full token matching. All ordinary main rows
are considered before selecting execute1. Worker/init memory tokens and inactive
caller requests remain in their original ledgers. This is no initialized worker
memory history, CSR/MOP/Sail execution, issuance/accounting or physical extraction
claim. Original initialized execution interfaces are unchanged.

## Native adjacent initialization records

[The initialization ordering roots](Airbender/Review/Circuits/ReducedMachine/InitializationOrderingTheorems.lean) derive repeated adjacent
actual token-address exclusion from native ordering polynomials, complete body
remainder/borrow checks and unmasked padding. Only zero padding can repeat at
adjacent comparison positions; the last two physical rows are excluded. This
supplies no global uniqueness, address range, public seed image, initialized
worker read or physical extraction. Original initialized execution is unchanged.

## Native initialization-address pair oracles

[The same-main pair roots](Airbender/Review/Circuits/ReducedMachine/InitializationRangeTheorems.lean) retain all ordinary native rows and
the existing complete body, auxiliary chain, padding and adjacent ordering.
Separate base4/quartic28 observations yield the source pair equation, including
its duplicate-pole limit. Address ranges and logical lookup extraction are still
open; these local relations do not establish initialized worker reads or change
original execution.
