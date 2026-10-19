# Trust and review boundaries

## Review entry points

Start with [Properties](Airbender/Review/Helpers/Properties.lean), then the short
[ADD/SUB theorems](Airbender/Review/Circuits/AddSub/Theorems.lean) and their
[Model](Airbender/Review/Circuits/AddSub/Model.lean). The local theorem takes
explicit decoded-input interfaces; it is not an initialized whole-run claim.
The separate short [trace memory theorem](Airbender/Review/Trace/History.lean)
constructs complete Clean memory history and latest reads from native logical
matching and explicit initialization tokens. The
[public-image theorem](Airbender/Review/Trace/Initialization.lean) obtains those
tokens and the initial PC from actual Sail reads of a supplied state/domain.

## Sources and pins

The target is dev revision 67ee094449abaebc77e58435f130ce6ea27721e5. The source
formalization is revision 805909325; [provenance](artifacts/provenance.json)
records its full commit and byte-identical shared modules, generated references,
native Rust source hashes and the v2 JSON identity. Lean, Mathlib, Clean and
lean-sail versions are unchanged. The [Clean preparation](scripts/prepare_clean.py)
is the existing guarded compatibility patch, not a change to its semantics.
The [Sail generation record](generated/sail-rv32/provenance.json) is copied unchanged.

## Import and generation fidelity

Mersenne31 coefficients are non-Montgomery residues in 0..=2147483647; the upper
endpoint is another representation of zero. The [coefficient lemma](Airbender/Import/Coefficients.lean)
proves signed interpretation in the native characteristic. Other generic prime
instances interpret those same signed equations and are not additional native artifacts.

[Native clock/port import](Airbender/Import/Parse.lean) checks two-limb group
extents, physical banks, consecutive port slots and query/borrow counts. Emitted
metadata is pinned by [mechanical bindings](Airbender/Proofs/AddSub/ArtifactChecks.lean).
The [clock proof](Airbender/Proofs/AddSub/Timestamp.lean) derives advancement and
strict access order under local initial/prior clock bounds and alignment.
The [initialized history layer](Airbender/Proofs/Trace/History.lean) discharges
those per-row inputs from logical state/memory matching and public initial clock
bounds. The v2 carry equations need no source-field inverse constant.

[Decoder placement](Airbender/Review/Helpers/Decoder/README.md) now resolves all
ten v2 query columns, including the decoder-owned zero flag and packed mask.
Group extents and memory/witness bank choices are checked; extra unconsumed
funct7/family descriptor fields fail closed. This is metadata interpretation,
separate from the [public selected-profile setup constructor](Airbender/Review/Helpers/Decoder/Setup.lean).
The constructor reads public bytes and original Sail decoding at native PCs 4*i,
retains a power-of-two capacity and the full all-minus-one tail, and rejects
missing/unsupported/effectful entries. It covers the selected five arithmetic
instructions. General Rust generation/export correspondence remains unproved;
no physical exported setup artifact or mixed/custom-opcode coverage is claimed.
Logical membership is explicit over the complete table, with no table-equivalence
premise. Native packed-mask equations exclude padding and recover actual decoded
source evidence, the zero flag and canonical decoder PC/immediate words. The v2 decoder
retains original opcode masks/operands for x0, unlike the source's NOP projection;
the local interface and a nonzero-operand SUB-to-x0 regression now preserve that.

The [schema](Airbender/Import/Schema.lean) is the consumed local-row projection of
the v2 compiled artifact. All linear/quadratic equations and scalar/timestamp
queries are emitted as native Clean operations. Only the two native word-memory
fixed tables are supported, with exactly three columns. Unknown tables, dynamic selectors, malformed arities, byte ranges and
state linkage fail closed. Native stage-two arguments,
public boundary conditions, decoder tables and memory matching are not implied
by this projection. Their remaining work is explicit in the status and plan.

Logical variable IDs are recovered uniquely from physical column placement.
The [named mapping](Airbender/Review/Circuits/AddSub/Model.lean) exposes actual
destination-write variables 37/38 rather than raw arithmetic variables 29/30.
The proof connects both using the imported x0 mask equations. Pinning and parser
regressions check parts of this connection; formal parsing/emission fidelity is
not proved.

The separate [word-memory checkpoint](Airbender/Review/Circuits/WordMemory/Theorems.lean)
imports every native equation/query and all mixed port/decoder metadata. The
[table models](Airbender/Review/Helpers/Tables/WordROM.lean) enumerate the native
four-MiB profile, including every separator row, every aligned ROM row and UNIMP
padding. Both native fixed queries remain unconditional. Membership derives
address alignment, RAM classification and exact public ROM values; equations
derive port selection, actual masked loads and RAM-only stores. The x0 flag
remains visible until public decoding identifies it. Native Mersenne31 address
addition now derives its carries and ranged output under explicit source/immediate
bounds. Native PC bounds/alignment and clock inputs yield modular successors,
four-tick advancement and port order. The initialized word-memory instance now
recovers every per-row/prior clock input from matching and the actual public
seed/PC boundary, reusing the existing shared clock/history proofs. [Public LW/SW decoding](Airbender/Review/Trace/Families/WordMemory/Decoder.lean)
now recovers actual Sail bytes/decoding and native fields from complete padded
membership. Native Boolean store-mask equations reject padding; generic source,
PC/immediate and register-index proofs are reused. Exact zero flags and incoming
alignment are derived, including stores and original loads to x0. The separate
native registry does not extend the arithmetic execution claim.
[Initialized word-memory history](Airbender/Review/Trace/Families/WordMemory/History.lean)
now derives complete Clean online consistency and newest preceding native reads
for all three ports, including readonly ROM-shadow accesses.
[Native value ranges](Airbender/Review/Trace/Families/WordMemory/Values.lean)
reuse the unchanged decreasing-time induction with proved native load/store/mask
rules: stores copy an earlier operand port; loads select canonical ROM data or
bounded RAM reads. Full decoder membership supplies the zero flag. Actual public
seed reads replace all initial values/clocks, deriving every read, actual write
and terminal word bound without per-row answers. This logical result retains
shadow tokens; it does not identify them with architectural ROM contents.
[Initialized native-row assembly](Airbender/Review/Trace/Families/WordMemory/Inputs.lean)
now obtains source bounds from the first actual port, immediate/PC bounds and
alignment from successful public setup, and all clock inputs from matching.
Existing native address/PC/clock proofs are called unchanged, deriving address
addition, bounded aligned PCs, modular PC successors and native access order.
No per-row numerical interface or desired address/PC result is supplied.
[Actual Sail cell histories](Airbender/Review/Trace/Families/WordMemory/SailHistory.lean)
now reuse shared Clean realization and clock-derived row grouping. The native
mixed-port proof preserves x0: readonly ports copy reads, stores address RAM,
and decoded loads to x0 mask the actual write to zero. Original Sail source GPR
reads and the final mixed register/RAM write are recovered in each instruction
pre-state; readonly aliases stutter. Public RAM alignment remains visible.
Reversed dependent store/load rows derive their intermediate state and later
read, with no supplied intermediate/read/result. The full supplied native cell
image still includes shadow cells tracked as RAM; these cell-transfer results
do not establish architectural ROM-shadow projection or original instruction
execution. Physical boot/padding binding and Sail instruction/platform transport
remain open. The [native shadow theorem](Airbender/Review/Circuits/WordMemory/Theorems.lean)
now derives exact raw read/write value-code equality for every imported RAM port
mapped below four MiB. Full native constraints and metadata suffice: the final
port targets registers or RAM outside that prefix; the earlier ports are
readonly refreshes. The native clock tokens still participate in matching.
The separate [architectural projection](Airbender/Review/Trace/Families/WordMemory/Projection.lean)
now erases whole shadow-address domains from Sail transfers while preserving the
complete native Clean history. [Projection calculations](Airbender/Proofs/Trace/Projection.lean)
prove consistency and latest-write preservation without changing Clean semantics.
[The public initializer](Airbender/Review/Helpers/Memory/ShadowImage.lean) reads
only architectural cells, then appends canonical native shadow seeds supplied as
public initialization data. Domain separation/uniqueness and zero seed clocks
are derived; the shared x0 induction now takes its root from architectural seeds
alone. Native matching, decoder membership and derived clocks supply row order,
actual Sail reads/writes and final architectural matching. Neither desired reads,
intermediate states nor shadow/ROM-value equality are inputs. Ordinary/x0 ROM-load
regressions retain the native shadow refresh even when its location has no Sail
bytes and its value differs from the loaded ROM word. These logical public shadow
seeds are not a proof of the physical native zero-boot profile. The
[projected range claim](Airbender/Review/Trace/Families/WordMemory/Projection.lean)
now derives every full native read, actual write and terminal word bound from
canonical seed construction, accepted matching and full decoder membership.
The existing shared decreasing-time induction and native load/store/mask rules
are reused unchanged, retaining all shadow accesses.
[Projected native effects](Airbender/Review/Trace/Families/WordMemory/Inputs.lean)
now recover source bounds from initialized native reads and call the existing
address/PC calculations with actual public decoder facts and derived clocks.
Both initialization boundaries share one numerical assembly; their public
interfaces retain their original meanings. Native PC effects are not Sail
retirement. [Retained-port transport](Airbender/Proofs/Trace/Families/WordMemory/ProjectedPorts.lean)
now recovers actual original Sail pre-state reads and final masked writes.
A shared readonly-prefix induction handles retained aliases and erased ports;
full v2 constraints prove that the final mixed port targets a GPR or RAM outside
the ROM prefix. Decoder indices identify the source GPR without an expected read
premise. Ordinary/x0 ROM loads and reversed dependent RAM store/load regressions
exercise these general lemmas. Original instruction execution/retirement is
checked below; physical boot/padding and ROM-table enforcement remain separate.
[Code/ROM preservation](Airbender/Review/Trace/Families/WordMemory/CodeHistory.lean)
now derives equality of every byte entry below four MiB through actual projected
Sail histories. The checked architectural domain and native final-port retention
exclude actual stores there; byte windows use the unchanged original Sail runtime
write/frame lemmas. Missing bytes and words outside the tracked cell list are
covered. Every successful public ROM extraction survives, including the full
image. For programs fitting the native ROM region, actual indexed setup
construction bounds each complete code window; its checked pure decoder and
original byte reads survive every history prefix. No later fetch, expected ROM
value or table-equivalence premise is added. The changing reversed SW/LW fixture
simultaneously derives terminal RAM 123, unchanged code/ROM extraction and original
source evidence. Physical padding/boot/export and original instruction execution
remain separate.
[Public ROM extraction](Airbender/Review/Helpers/Tables/WordROMImage.lean)
now obtains words by actual original Sail reads. The
[ROM read bridge](Airbender/Review/Trace/Families/WordMemory/ROMImage.lean) recovers
native table data inside the extracted prefix, deriving both data limbs and the
actual effective address. A complete four-MiB extraction discharges prefix
coverage for every native ROM address. Full native UNIMP rows remain present;
missing Sail padding bytes are not filled by extraction. Supplying the actual
Sail boot/padding/shadow state and physical Rust setup/export remain separate.
No expected-read or table-equivalence premise is introduced. The initialized
arithmetic and word-memory registries retain separate selected-profile claims.
[Platform configuration](Airbender/Review/Helpers/Memory/Platform.lean) and seven
Sail platform proof modules are now copied unchanged from the same pinned source.
They specify actual initialized Machine CSRs, disabled PMP entries, an RV32 PMA
region with permissions and ordinary addresses outside CLINT/signature windows;
HTIF is disabled by its public CSR. These are configuration/domain data, not
successful-access or expected-value assumptions. The original MemoryPlatform
interface remains explicit. [Initialized preservation](Airbender/Review/Trace/Families/WordMemory/Platform.lean)
derives the same configuration in every realized native prefix and the final
architectural state. [Native RAM transport](Airbender/Proofs/Trace/Families/WordMemory/MemoryTransport.lean)
derives actual read/write values and byte alignment from v2 equations/ports and
projected histories, then calls unchanged Sail virtual-memory proofs. The
reversed dependent SW/LW regression derives actual virtual store/load results
from the same matched history and public setup; no later read or intermediate
state/result is supplied. This proves the RAM memory-call path.
[ROM transport](Airbender/Proofs/Trace/Families/WordMemory/ROMTransport.lean) now
composes retained source reads, derived address/alignment and actual public ROM
extraction through preserved prefixes into original Sail virtual ROM reads.
Native ROM address bounds discharge the ordinary-address condition, with no extra
MMIO success premise. [Original ROM LW assembly](Airbender/Proofs/Trace/Families/WordMemory/ROMExecution.lean)
uses native masked writes and exact public decoder fields to reach the original
LW clause result in the actual native after-state. Nonzero rd gets the actual
ROM word; the pinned original x0 write discards it, without NOP projection.
[Initialized regressions](Tests/WordMemoryROMTransport.lean) construct actual
ROM/decoder bytes and configuration for both cases. Their native shadow value 123
remains independently initialized and matched while the actual ROM bytes supply
0xc0001073. No expected read, shadow/ROM equivalence or desired intermediate/result
state is supplied. Extraction still requires present bytes and does not create
missing padding.
[RAM clause assembly](Airbender/Proofs/Trace/Families/WordMemory/RAMExecution.lean)
now recovers the actual original rs2 read from the retained native store port,
using native address equations and decoder indices. The actual masked RAM-load
write matches the original unmasked Sail write, including x0. Exact public
fields derive load/store selectors, original registers and sign-extended
immediates. The unchanged original Sail memory and clause lemmas then reach
actual native cell-transfer states, with configuration/ordinary-address domains
still explicit. The same reversed accepted SW/LW fixture derives original SW and
LW results in its realized states, actual later read 123 and the actual register
write. No intermediate state/read or desired result is supplied; previous cell,
code, ROM and virtual-memory regressions remain unchanged. These are original
clause results.
[Original clause dispatch](Airbender/Review/Helpers/Decoder/Instruction.lean) now
copies the pinned original memory/register selector verbatim, omitting the v3
profile that turns LW-to-x0 into a NOP. V2's original x0 memory behavior is retained.
[Retirement transport](Airbender/Proofs/Trace/Families/WordMemory/Retirement.lean)
reuses existing actual history/control commutation and public configuration
frames through Sail's original nextPC preparation. Actual ROM extraction survives
these control-only updates. The derived original clauses and tick_pc reach the
same actual cell state at the modular successor; no prepared read or state is
supplied. [Initialized native row assembly](Airbender/Proofs/Trace/Families/WordMemory/Execution.lean)
derives effective addresses and exact native PC successors, then selects original
RAM LW/SW or ROM LW from actual decoder fields. Local ordinary-RAM and extracted
ROM-prefix coverage conditions remain explicit. The unchanged native fixtures now
also check original normal steps: ordinary/x0 ROM loads retire to native PC 4;
the reversed SW/LW chain starts from its actual public Sail state and reaches
PC 8 and terminal RAM/x3=123 through native terminal matching. No intermediate
state/read or desired PC/value is a premise. General finite trace/fetch composition
is now checked below; physical boot/export and cryptographic enforcement remain open.

[Complete initialized word-memory execution](Airbender/Review/Trace/Families/WordMemory/Theorems.lean)
uses the existing actual fetched/decoded StepWith relation with original LW/SW
clauses. Whole-address [composition](Airbender/Proofs/Trace/ProjectedComposition.lean)
filters only Sail transfers; all native events and matching still derive row
order and PC boundaries. Each prefix preserves actual code bytes, pure decoder
evidence, public configuration and successful ROM extraction. Public ordinary-RAM
and shadow-seed coverage domains root every local address condition through
accepted matching. No per-row range/read/order, intermediate state or desired
result is an assumption.

[Terminal assembly](Airbender/Proofs/Trace/ProjectedTerminal.lean) uses the complete
unfiltered Clean history for latest values. The explicit
[architectural observable](Airbender/Review/Trace/Families/WordMemory/Execution.lean)
requires exact native terminal PC and retained GPR/RAM cells; native shadow values
are independent of actual ROM bytes. Empty traces preserve the actual starting
PC/cells. The general theorem passes the reversed SW/LW trace and derives PC 8,
RAM 123 and x3=123, plus ordinary/x0 ROM and empty-trace regressions. Configuration,
program size in native ROM, ordinary public RAM and successful actual ROM-prefix
extraction/seed coverage remain visible logical inputs. They do not establish
physical zero boot, absent Sail padding, native setup/export fidelity or
cryptographic enforcement. The successful-step relation checks actual code-byte
reads and decoding; architectural fetch permissions, interrupts and exceptions
remain outside this checkpoint.

[Fixed native boot](Airbender/Review/Trace/Families/WordMemory/NativeBoot.lean)
now derives the previous general initializer from the original zero-initialization
profile. The [profile and Sail boot image](Airbender/Review/Helpers/Memory/Initialization.lean)
and [boot-image equivalence proof](Airbender/Proofs/Trace/Initialization.lean) are
copied unchanged. Only the four-MiB limit and native all-zero token constructor
are extracted from the v3 ROM/native modules; their old table-equivalence and
witness-rewrite interfaces are omitted. Native v2 VM/RAM/replayer sources confirm
GPR/RAM zero initialization, PC zero/time four and value-only ROM witness masking;
these sources are pinned separately from formal Rust refinement.

[Boot assembly](Airbender/Proofs/Trace/Families/WordMemory/Boot.lean) uses actual
Sail profile reads to derive the architectural zero image and fixed shadow seeds.
Complete original LW/SW execution then uses the previous theorem unchanged.
[Native shadow paths](Airbender/Proofs/Trace/Families/WordMemory/BootShadow.lean)
recover every actual imported row/port and propagate its checked unchanged raw
value through complete matching to terminal zero. Neither physical ROM bytes nor
a desired terminal value is a premise. Ordinary/x0 fixtures initialize all 32
actual GPR reads to zero and derive PC four, masked destination results and native
shadow zero. Nonzero public GPR data and invented native seeds reject the profile.

The native proving loader calls word padding with zero through the full four-MiB
region. The raw ROM table generator uses UNIMP only past the image it receives;
a complete padded image has no in-region fallback. The separate
[padding definition](Airbender/Review/Helpers/Tables/WordROMPadding.lean) models
this zero extension, with symbolic list proofs of extent, prefix retention and
zero tail. No million-word list is evaluated as a certificate. This definition
does not itself modify Sail state: absent input bytes still fail actual reads.
The added [explicit loader constructor](Airbender/Review/Helpers/Tables/PaddedROMImage.lean)
uses successful original prefix extraction, inserts actual zero bytes into the
remaining finite ROM interval and returns the matching zero-padded native ROM.
[Symbolic byte proofs](Airbender/Proofs/Sail/BytePadding.lean) establish exact
lookup/overwrite behavior, successful zero reads and prefix/outside preservation.
[Extractor assembly](Airbender/Proofs/WordMemory/ROMBytePadding.lean) derives the
complete four-MiB extraction from actual reads, without an evaluated large map/list,
lookup certificate or table-equivalence premise. Missing/oversized prefixes fail.

[Setup transport](Airbender/Proofs/Trace/PaddedSetup.lean) retains actual public
decoding when its code lies in the supplied prefix. Registers, the original boot
profile and Machine/PMP/PMA configuration survive the explicit memory operation.
[Boot composition](Airbender/Proofs/Trace/Families/WordMemory/BootPadding.lean)
feeds the previous initialized execution theorem unchanged; full ROM extraction
and the existing public shadow domain discharge all ROM coverage. The short
public claim adds only constructor success and code-prefix inclusion to the
original boot/configuration/alignment/ordinary-RAM and accepted native interfaces.
No expected padding reads, per-row state or desired result is assumed. Ordinary/x0
fixtures exercise this path while preserving all full native shadow matching.
Physical setup/initialization exports, general Rust/compiler refinement and
cryptographic enforcement remain separately scoped; constructing a Sail model
of the native loader does not formally verify the Rust loader itself.

[Native setup metadata](Airbender/Review/Helpers/Tables/SetupColumns.lean) is now
consumed from both pinned compiled layouts and guarded before emission. The
arithmetic profile has width 12 and decoder start 2; word-memory has width 16,
a generic tuple at 2..5 and decoder start 6. All 62 fixed-table offsets and real
generic-row counts are checked, including the native dummy row. Both traces have
2^24 rows and 2^20 decoder capacity. Unsupported groups, overlaps and extents fail.
Native setup, table/tag and normalization sources are separately hash-pinned.

The [active tagged-row model](Airbender/Review/Helpers/Tables/PhysicalSetup.lean)
copies the source layout: dummy tag zero, separator tag 23 at offset one, word-ROM
tag 24 at offset 65537, then zero tuples through the usable trace. The final row
is reserved for native c0 normalization and is not assigned a lookup meaning by
this model. The Rust source changes that row only; its formal refinement and the
stage-two exclusion/argument connection remain external. No v3 nine-column/tag-34
export certificate is carried onto this v2 model.

[Membership calculations](Airbender/Proofs/WordMemory/PhysicalSetup.lean) prove
that each native tagged region has exactly the unchanged three-column logical
table meaning. All dummy and padding tuples remain present and are excluded by
their tags, rather than filtered out or postulated equivalent. Key/data bounds
and alignment follow from actual modeled rows; original public extraction then
supplies actual Sail bytes. [The short read claim](Airbender/Review/Trace/Families/WordMemory/Setup.lean)
uses explicit loader construction and tagged membership, with no expected-read,
coverage or table-equivalence premise. Nonempty original/padded words and altered
word rejection exercise this bridge. This is a checked source-shaped row model
plus exact compiled placement, not a proof that Rust-generated/exported setup
field values or LDE commitments equal it. The native regional fixture connection
below closes the former data gap for that one exported program. General physical
trace assembly, initialization and cryptographic enforcement remain separate.

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
These certificates cover the pinned word-memory fixture. The arithmetic native
decoder certificate is checked separately below. Arbitrary programs, full physical
trace padding/normalization/LDE, initialization and argument enforcement remain open.

The exporter uses the same pinned native APIs as setup callers, retaining image
and text independently. It copies the pinned lossless column codec, validates
canonical values/coverage and compares every recovered element to native output.
The CLI writes only after those checks and JSON roundtrip. The importer rejects
unknown fields, incompatible versions/fields/families, changed native extents,
missing columns, moved/retagged regions and invalid compressed data. Its literal
emitter reuses the pinned compact-array helpers unchanged. These are executable
checks; neither Rust serialization nor Lean parsing/emission is formally refined.
Kernel proofs certify the emitted data, not the IO path. The native setup artifact,
exporter manifest/lock/sources and reused code are hash-pinned and checked by the
standard gate. No v3 field, tag, decoder filler or physical-layout claim is imported.

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

The sparse constructor supplements the strict selected-profile builder. It reads
actual bytes before deciding whether a pure original Sail result belongs to this
family; it cannot turn a missing/effectful word into a hole. Optional slots retain
all original indexed PCs, and the native query's mask bit excludes unsupported
slots regardless of their position. Shared successful-entry, source, pure-decoder,
indexed-PC and field-query lemmas are reused unchanged. The complete actual native
fixture equality is a kernel theorem over literal rows and constructed public
bytes, not an assumption fed to the source claim. The decoder data still precedes
physical setup padding/normalization/LDE. Native membership enforcement and general
Rust/Sail decoder agreement remain separate; initialized sparse execution is checked below.


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

## Public state, profiles and external inputs

The theorem covers original Sail ADD/ADDI/SUB/LUI/AUIPC execution on the successful
four-byte path, including upstream nextPC initialization and PC retirement.
Public instruction/operand interfaces, actual Sail reads and initial alignment
remain explicit. Selector bits, result bounds, arithmetic and PC effects follow
from the imported constraints. In particular, v2's high-PC wrap is preserved.
The logical history theorem additionally proves newest preceding reads of
injectively encoded native tokens, including readonly timestamp refreshes. Its
initial image may now be constructed from actual public Sail registers/RAM;
missing data fails, and successful reads preserve that state. The supplied public
domain is independent of the witness. This logical image does not yet establish
the physical zero-boot profile or native ROM-shadow interpretation. The [value-bound theorem](Airbender/Review/Trace/Values.lean) now derives native
read/write/terminal bounds. It combines original public seed reads, actual matching,
strict native port order and a zero flag proved from decoder membership. Raw-result
ranges alone do not suffice for a masked write: a concrete bad flag passes local
equations and produces an unbounded write, while full lookup membership rejects it.
The short [Sail-history theorem](Airbender/Review/Trace/SailHistory.lean) now
constructs actual Sail cell transfers and intermediate states. Clean consistency
derives reads from the public seed state; native masked-write equations and the
decoded zero flag preserve hardwired x0, without v3 NOP preprocessing. Alignment
of public RAM cells supplies disjoint byte windows. Native clocks derive complete
row grouping and the PC/state path; readonly refreshes preserve each instruction
pre-state even with aliases. Decoder register indices select original Sail GPR
accessors. These cell transfers do not yet establish instruction execution or
retirement by themselves. The [row assembly](Airbender/Proofs/Trace/Arithmetic.lean)
now derives the complete five-opcode local interfaces and applies original Sail
preparation, execution and retirement. Actual control-register commutation
transports cell histories and supplies rebased PC reads. The resulting state is
the actual masked native write followed by original Sail control updates,
including retained SUB-to-x0. Complete arithmetic trace composition is checked
below. The
[native PC theorem](Airbender/Review/Trace/PC.lean) now derives all incoming PC
bounds/alignment from public indexed setup PCs through RV32 truncation. Native
v2 carry/wrap equations derive bounded outgoing successors. State matching and
the actual public initial PC bound the external terminal PC, including empty
traces. This PC-path result does not establish Sail retirement or whole execution.
[Complete arithmetic execution](Airbender/Review/Trace/Families/AddSub/Theorems.lean)
now composes every native row, in derived clock order, into the original Sail
normal-path relation. The [reference relation](Airbender/Review/Trace/Execution.lean)
checks actual sequential Sail code-byte reads, original decoding, matching PC and
normal preparation/execution/retirement. Native register-space metadata and actual
history prove that all code bytes survive, including bytes outside the tracked
cell domain. Successful selected setup construction retains the actual pure
decoder term, allowing replay in each derived state without a new decoding
premise. State/memory matching derive exact terminal PC/cells, including empty
traces. No row order, intermediate state/read, desired terminal value or table
equivalence is assumed. The reversed dependent ADD/ADDI regression reaches PC 8
and x2=247. Architectural fetch permissions, exceptions, interrupts, other ISA
families, completeness and cryptographic soundness remain outside this checkpoint. The copied custom-operation specification
has no checked v2 consumer yet.

## Verification resources

The [bounded runner](scripts/check_all.py) compiles project modules in dependency
order and caches source/dependency fingerprints. Each proof process and each gate
runs under the shared [macOS watchdog](scripts/bounded_fv.py) with one Lean worker,
Lean -j1/-M3072, physical-footprint ceiling 3072 MiB, resident ceiling 4096 MiB and
finite wall limits. The watchdog is copied from the validated v3 incident response;
it is sampled, not an OS hard ceiling. Small parent/child timeout and allocation
probes verify termination. No native circuit, field or dependency pin changed.

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
