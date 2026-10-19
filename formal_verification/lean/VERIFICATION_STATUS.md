# Verification status

**Checked** means kernel-checked claims over imported v2 native constraints
and logical matching under the explicit Review interfaces. See [trust boundaries](TRUST_AND_REVIEW.md)
and the [backport plan](FORMAL_VERIFICATION_PLAN.md). V3 results are source material,
not completed v2 coverage.

## Checked coverage

| Circuit | Coverage |
| --- | --- |
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
- Extend initialized execution to jump/branch/SLT and the remaining supported families; preserve each native metadata and argument boundary.
- Backport the remaining ordinary circuit families, worker operations, unified machine, full traces and initialization/teardown.
- Retest v3 findings against v2 before carrying over counterexamples or temporary assumptions.
- Prove the deferred import/compiler/cryptographic connections under a separately scoped claim.

No whole-machine or cryptographic soundness is claimed. Completeness is defined
but unproved. Unsupported fixed tables/dynamic selectors, byte ranges and inter-row linkage
are rejected rather than omitted from the local importer target.

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

## Validation

Current checked checkpoint:

- Library, both CLI entrypoints and all sixty-one concrete test modules pass.
- Importer regressions: 202 checks pass.
- Axiom audit: 1189 explicit roots; only propext, Classical.choice and Quot.sound.
- All sixty-nine public Review theorems (eleven circuit claims, forty-nine trace claims and nine helper claims including the two reused port-representation lemmas) have explicit axiom roots; guide references, links and layering checks pass.
- Source provenance: 76 unchanged reused files, four native circuit artifacts, forty native Rust sources, eight native setup artifacts and four exporter source/manifest/lock files.
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
