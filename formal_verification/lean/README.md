# Circuit verification

## What is checked

[Verification status](VERIFICATION_STATUS.md) lists v2 coverage and open tasks.
The [findings audit](FINDINGS.md) keeps observed behavior separate from unported
v3 findings and missing proof connections.

The proof path is:

```text
v2 compiled layout JSON → native Clean constraints → original Sail execution
```

This is the v2 backport based on dev revision
67ee094449abaebc77e58435f130ce6ea27721e5. Reused definitions and proofs come from
formalization revision 805909325; exact source identities and hashes are in
[provenance](artifacts/provenance.json). Circuit and runtime Rust are unchanged.

Current scope includes complete initialized ADD/ADDI/SUB/LUI/AUIPC normal-path
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
