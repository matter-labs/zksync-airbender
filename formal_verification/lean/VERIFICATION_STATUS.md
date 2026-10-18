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
| Range tables | Native Clean static-table definitions with explicit range semantics; the pinned range16 fixture is certified row by row. General scalar/physical setup correspondence remains open. |

## Remaining work

- Connect sparse decoding to initialized execution, generalize native export certificates to arbitrary public programs, add arithmetic/timestamp exports and full physical trace assembly; connect physical initialization and expand mixed/custom programs.
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
native exports, timestamp19 and full physical trace padding/normalization/LDE
correspondence remain open, as do physical initialization and argument enforcement.

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
post-hole fields are checked separately. These are decoder/source claims; sparse
initialized execution, arbitrary-program Rust decoder refinement and full physical
trace/argument connections remain open.

## Validation

Current checked checkpoint:

- Library, both CLI entrypoints and all twenty-one concrete test modules pass.
- Importer regressions: 84 checks pass.
- Axiom audit: 651 explicit roots; only propext, Classical.choice and Quot.sound.
- All thirty-two public Review theorems (five circuit claims, twenty-five trace claims and two reused port-representation lemmas) have explicit axiom roots; guide references, links and layering checks pass.
- Source provenance: 71 unchanged reused files, two native circuit artifacts, thirty-one native Rust sources, two native setup fixtures and four exporter source/manifest/lock files.
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
- No handwritten project warnings, admitted proofs or project axioms.
- Serial bounded gates pass; parent/child timeout and memory probes confirm termination with no live owned processes.

Run the [reproduction commands](README.md#reproduce) for the current checkpoint.
