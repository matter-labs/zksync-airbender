# Word-memory trace review

## Checked decoder connection

[Theorem](Decoder.lean) recovers actual public LW/SW bytes, original Sail decoding
and native metadata from the full padded logical decoder table. The
[constructor](../../../Helpers/Decoder/WordMemory.lean) keeps sign-extended
immediates, funct3=2, the native store bit, the separate x0 flag and original x0
loads. It clears only the unused rs2 on loads or rd on stores. Missing bytes,
unsupported/effectful instructions and insufficient capacity fail construction.

The separate [native registry](../../../Helpers/Context/WordMemory.lean) selects
the actual v2 artifact, all three ports, ten decoder columns and ROM tables.
Acceptance has the existing native constraint/active/state/memory meaning.
The [proof assembly](../../../../Proofs/Trace/Families/WordMemory/Decoder.lean)
rejects every minus-one padding row with the native Boolean store-mask equation.
It then derives exact zero flags, register indices, canonical PC/immediate bounds,
incoming alignment and original pure-decoder evidence. No per-row answer or table
equivalence is supplied.

[Regressions](../../../../../Tests/WordMemory.lean) construct real LW/SW bytes and
nonempty accepted native traces, including LW to x0. Negative immediates, excluded
subword/unsigned constructors, missing bytes and bad capacity are checked. A bad
zero flag passes all native constraints but full lookup membership rejects it.
This validates the separate decoder boundary; it is not an implementation defect.

## Checked initialized history

[Memory soundness](History.lean) constructs complete Clean online consistency
and newest preceding reads from the actual public seed image and accepted native
state/memory matching. The existing [public boundary](../../../Helpers/Memory/PublicImage.lean)
now works for either native registry with the same fields and constructors.
The [clock instance](../../../../Proofs/Trace/Families/WordMemory/History.lean)
discharges the shared laws from actual v2 equations and port metadata. Initial
clock four and seed clocks zero derive all per-row/prior ranges, alignment,
four-tick advancement and strict port order. No row ordering is supplied.

[Word bounds](Values.lean) derive every native read, actual masked write and
terminal word range. The [write rule](../../../../Proofs/Trace/Families/WordMemory/Values.lean)
uses earlier port reads for RAM loads/stores and canonical table words for ROM
loads. Full decoder membership supplies the zero flag. The existing decreasing-time
induction is reused unchanged, including every discarded native read.

[Initialized regressions](../../../../../Tests/WordMemoryHistory.lean) build
actual public LW/SW bytes, source registers, RAM cells and initial PC. Nonempty
RAM loads/stores have complete histories; masked x0 ROM loads retain newest-read
and range guarantees for the shadow RAM port. Omitting its seed fails actual
logical matching. This fixture explicitly initializes the native shadow cell;
the separate architectural projection below now avoids that Sail shadow read.

## Checked native-row inputs

[Native effects](Inputs.lean) derive effective-address addition, bounded aligned
incoming PCs, bounded modular PC successors and native clock/port order from the
same public image, actual decoder setup and accepted matching. The
[assembly](../../../../Proofs/Trace/Families/WordMemory/Inputs.lean) obtains the
source word from the first actual port and its initialized range proof. It calls
the existing native address, PC and clock calculations unchanged. No per-row
range, carry, PC, clock or desired-effect premise is supplied. The initialized
LW/SW/x0/ROM-shadow fixtures exercise the complete assembly.

## Checked Sail cell histories

[Cell-history theorem](SailHistory.lean) constructs actual original Sail cell
reads/writes and every intermediate state in derived native clock order. Its
public inputs remain the existing seed/PC construction, accepted matching, full
decoder membership and alignment of the public RAM-cell domain. The
[x0 proof](../../../../Proofs/Trace/Families/WordMemory/ZeroRegister.lean) handles
mixed ports directly: readonly ports preserve reads, stores select RAM, and
loads to rd=0 receive the decoded native zero mask. No NOP projection, per-row
read, desired intermediate state or x0 answer is supplied.

Shared Clean-to-Sail realization and grouping are reused unchanged. The
[port transport](../../../../Proofs/Trace/Families/WordMemory/PortReads.lean)
recovers every read in the instruction pre-state and the final actual mixed
register/RAM write. Decoder indices identify the actual original Sail source GPR.
Readonly refreshes stutter, including aliases and discarded shadow accesses.

[Single-row regressions](../../../../../Tests/WordMemoryHistory.lean) derive
actual Sail source reads, RAM-load register writes, RAM-store byte writes and
x0/ROM-shadow cell stuttering. A [reversed dependent store/load](../../../../../Tests/WordMemorySailHistory.lean)
builds both public decoder instructions and derives the intermediate store state,
the later read of 123 and the destination write from native history. None is an
input premise.

This theorem realizes the full supplied native cell domain. In particular, its
existing public image binds shadow cells as tracked RAM. It does not solve the
projection from a physical native shadow image to architectural ROM contents,
or prove execution of original LOAD/STORE instruction clauses.

## Remaining connection

[Public ROM extraction](../../../Helpers/Tables/WordROMImage.lean) now obtains
ROM words from actual Sail bytes. The short [read theorem](ROMImage.lean) binds
native ROM query data inside the extracted prefix; a complete extracted four-MiB
image covers every ROM address. Full native UNIMP padding remains represented.
The constructor does not fill absent padding bytes in Sail state.
[Native shadow value preservation](../../../Circuits/WordMemory/Theorems.lean)
now shows every RAM access below four MiB only refreshes its existing value.
The complete native history still retains those accesses and their timestamps.

## Checked architectural projection

[Projected cell histories](Projection.lean) now erase whole shadow-address domains
from Sail transfers while preserving the complete accepted native history.
[Clean projection](../../../../Proofs/Trace/Projection.lean) preserves online
consistency and newest writes at every retained address, with the original Clean
semantics unchanged. Native clocks still derive complete row order.

[The separate public initializer](../../../Helpers/Memory/ShadowImage.lean) reads
architectural GPR/RAM cells from Sail and appends independent canonical native
shadow seeds. Domain uniqueness and initial clocks are derived; the shared x0
induction uses only the architectural register seed. Native matching, full decoder
membership and public RAM alignment derive actual reads/writes, intermediate
states and final architectural matching. Shadow cells need no Sail bytes or
shadow/ROM-value equality. Calculations stay in
[the assembly](../../../../Proofs/Trace/Families/WordMemory/ShadowImage.lean).

[Ordinary/x0 ROM-load regressions](../../../../../Tests/WordMemoryProjection.lean)
build actual instruction bytes and accepted native rows. The shadow location is
unreadable in Sail and its native value differs from the loaded ROM word. Full
native history still contains its refresh; the projected transfer history derives
the actual masked Sail register write.

[Projected native bounds](Projection.lean) also derive every native read, actual
write and terminal word range from this initializer. Canonical architectural and
shadow seed words root the existing shared decreasing-time induction; native
load/store/mask rules and decoder flag recovery are reused unchanged. Discarded
shadow accesses retain their full native bounds even when Sail has no shadow
bytes. Both ordinary and x0 ROM-load regressions check these ranges without any
per-row or per-port bound premise.

[Projected native inputs](Inputs.lean) now derive effective-address addition,
bounded aligned native PCs, modular successors and clock/port effects from the
same separate initializer and actual public decoder. Both boundaries use one
[numerical assembly](../../../../Proofs/Trace/Families/WordMemory/Inputs.lean);
[the projected wrapper](../../../../Proofs/Trace/Families/WordMemory/ProjectedInputs.lean)
discharges source ranges and clocks without reading shadow bytes.

[Shared retained-port transport](../../../../Proofs/Trace/PortProjection.lean)
proves that readonly refresh prefixes stutter and all retained reads use the
instruction pre-state, including aliases. The
[native instance](../../../../Proofs/Trace/Families/WordMemory/ProjectedPorts.lean)
proves final-port retention from actual v2 constraints: loads write GPRs and
stores target RAM outside the ROM prefix. It derives the actual final masked
write and original Sail source-GPR read from decoder metadata. No shadow read,
expected source value or intermediate state is supplied. Ordinary/x0 ROM loads
with absent shadow bytes and the reversed dependent RAM store/load regression
exercise the general retained-port lemmas.

## Checked code and ROM preservation

[The short public claim](CodeHistory.lean) adds equality of every byte entry below
four MiB and preservation of every successful public ROM extraction to initialized
projected histories. Actual native stores target RAM above this region. The
[shared byte frame](../../../../Proofs/Trace/CodeHistory.lean) uses original Sail
register and byte-write lemmas; it covers missing bytes and code outside the
tracked cell domain. The [native assembly](../../../../Proofs/Trace/Families/WordMemory/CodeHistory.lean)
reuses public initialization, full matching and projected realization unchanged.

For public programs fitting the native ROM region, actual indexed setup
construction bounds each complete instruction window. Original byte reads and
checked pure Sail decoding survive every projected prefix. No expected later
fetch or table-equivalence premise is supplied. The
[reversed changing SW/LW regression](../../../../../Tests/WordMemorySailHistory.lean)
derives terminal RAM 123 from an initial zero while retaining both instruction
words, their extracted two-word ROM and original source evidence. Ordinary/x0 ROM
loads also preserve missing shadow bytes while full native matching retains their
refreshes. This frame neither creates absent padding bytes nor proves original
LOAD/STORE execution/retirement.

## Checked platform and RAM transport

[The public preservation claim](Platform.lean) retains the actual Machine/PMP/PMA
configuration through initialized projected histories, with full native matching.
[Configuration and ordinary-address definitions](../../../Helpers/Memory/Platform.lean)
are copied unchanged. Seven unchanged pinned Sail proof modules discharge original
translation, permissions, byte encoding and platform helpers. Ordinary addresses
exclude actual CLINT/signature windows; the public CSR image disables HTIF.
No successful-access or desired-value condition is hidden in the configuration.

[Native transport](../../../../Proofs/Trace/Families/WordMemory/MemoryTransport.lean)
derives effective-address alignment and actual RAM reads/writes from v2 equations
and retained ports. The existing public initialized assembly discharges source
and address facts; actual histories derive intermediate states. These facts now
feed original Sail virtual-memory calls under the explicit public configuration,
ordinary-address and MemoryPlatform interfaces. The same reversed SW/LW fixture
initializes real CSRs and derives a virtual store and subsequent read of 123,
while all existing cell, code and ROM-preservation regressions still pass.

## Checked ROM virtual transport and LW clauses

[ROM transport](../../../../Proofs/Trace/Families/WordMemory/ROMTransport.lean)
now composes retained source reads and native address/alignment with actual
public ROM extraction. Preserved prefixes retain the extraction and public
configuration. Native ROM bounds derive the ordinary-address condition. The
original Sail virtual read returns the actual ROM word without a shadow read or
expected-value premise.

[Original LW assembly](../../../../Proofs/Trace/Families/WordMemory/ROMExecution.lean)
then connects the actual native masked write to the original unmasked Sail
instruction effect. Exact native decoder fields recover original registers and
sign extension. For rd=x0, the pinned original write discards either value; the
original instruction is retained without NOP preprocessing. Calculations and
clause assembly remain entirely under Proofs.

[Initialized ordinary/x0 regressions](../../../../../Tests/WordMemoryROMTransport.lean)
construct actual ROM bytes, original decoder bytes and public configuration, then
derive original virtual reads, actual masked writes and original LW clause
results in the same native after-state. Full native matching retains shadow
value 123 independently of the actual ROM word 0xc0001073. Successful extraction
requires present bytes; absent padding is not filled.

## Checked original RAM LW/SW clauses

[RAM clause assembly](../../../../Proofs/Trace/Families/WordMemory/RAMExecution.lean)
reuses the original LW assembly with the actual retained RAM read. Native masks
match original destination writes, including x0 without NOP projection. For
stores, native equations select the retained rs2 GPR on port 1; decoder metadata
identifies the original register and the history derives its actual pre-state
read, including aliases and x0. Exact public fields derive load/store selectors
and sign-extended immediates. Unchanged original Sail memory and clause lemmas
reach the actual states supplied by native cell realization.

[The existing reversed dependent fixture](../../../../../Tests/WordMemorySailHistory.lean)
now reaches original SW then LW results in those same derived states, with actual
later read 123 and actual destination write. Public configuration and ordinary
addresses remain explicit; no expected operand/read, intermediate state or
desired result is supplied. Existing cell/code/ROM/virtual-memory tests remain
unchanged. The public Review theorem surface is unchanged; the assembly remains
under Proofs.

## Checked native row retirement

[Original clause selection](../../../Helpers/Decoder/Instruction.lean) copies
only the pinned original memory/register dispatcher. The v3 discarded-load
profile and exclusions are omitted; original LW-to-x0 still performs its actual
memory read. No unused v3 execution theorem is imported.

[Retirement transport](../../../../Proofs/Trace/Families/WordMemory/Retirement.lean)
reuses the existing actual cell/history commutation with PC and nextPC, plus
unchanged public configuration frames. Original Sail nextPC preparation leaves
native GPR/RAM effects and actual ROM extraction intact. The checked original
clauses run in these derived prepared states, and tick_pc reaches the same actual
cell state at the modular successor. No prepared read/state is supplied.

[Initialized row assembly](../../../../Proofs/Trace/Families/WordMemory/Execution.lean)
recovers effective addresses and exact native PC successors from accepted matching
and public decoding. It selects RAM LW/SW or ROM LW and reaches that native
outgoing PC under local ordinary-RAM and actual extracted-prefix coverage domains.
The latter does not populate missing Sail padding bytes.

[Reversed SW/LW normal steps](../../../../../Tests/WordMemorySailHistory.lean)
now start from the actual public Sail state and reach PC 8, terminal RAM 123 and
x3=123 from native matching. Both [ordinary/x0 ROM fixtures](../../../../../Tests/WordMemoryROMTransport.lean)
retain all earlier results and now retire to native PC 4 with original memory
behavior. No intermediate state/read or desired PC/value is an input. The public
Review adds only the small original-clause reference; all assembly stays under
Proofs.

## Checked finite original execution

[The short public theorem](Theorems.lean) proves the explicit
[reference and terminal observable](Execution.lean). Every native row becomes an
actual fetched/decoded original LW/SW normal step. Exact terminal PC and
architectural cells follow from full native history; shadow values remain
independent matched native data. The original x0 load still reads memory.

[Address domains](../../../../Proofs/Trace/Families/WordMemory/AddressDomain.lean)
root effective RAM addresses in actual public cells and ROM addresses in separate
public shadow seeds. Public ordinary RAM and coverage by the actual extracted ROM
prefix discharge every local access domain. Public configuration and program
size within the native ROM region remain visible. No per-row range, source/read,
order, intermediate state or desired result is supplied.

[Composition](../../../../Proofs/Trace/Families/WordMemory/Composition.lean) reuses
the existing native row induction, control rebasing and terminal assembly with
whole-address filtering. Code reads, pure decoding, configuration and successful
ROM extraction survive each realized prefix. The reversed dependent SW/LW fixture
now reaches PC 8 and native terminal RAM/x3=123 through this general relation;
ordinary/x0 ROM loads and an empty native trace also pass. The public Review adds
one short execution theorem; calculations remain under Proofs.

The general public shadow seeds describe a logical initialized native image.
The fixed native zero-profile and explicit Sail padding connections are checked
below; physical initialization and ROM-table exports remain open. Complete original word-memory execution/retirement
is checked above under the explicit logical public domains.
The existing arithmetic execution registry and its claims retain their scope. Physical setup
export, mixed/custom programs and cryptographic argument enforcement are separate.

## Checked fixed native zero boot

[The small public theorem](NativeBoot.lean) retains the same finite original Sail
execution and architectural terminal observable. [Fixed boot data](../../../Helpers/Memory/NativeBoot.lean)
uses zero native GPR/RAM/shadow values, PC zero/time four and the unchanged
[original Sail profile](../../../Helpers/Memory/Initialization.lean). Actual
initial reads and public geometry derive the prior general initializer;
[the assembly](../../../../Proofs/Trace/Families/WordMemory/Boot.lean) supplies no
per-row range/read/state/result premises. Configuration, alignment, ordinary RAM
and actual extracted-ROM coverage stay explicit. [Full native shadow paths](../../../../Proofs/Trace/Families/WordMemory/BootShadow.lean)
keep terminal values zero independently of actual ROM bytes.

[Ordinary/x0 boot regressions](../../../../../Tests/WordMemoryNativeBoot.lean)
initialize all original Sail GPR reads to zero, build actual instruction/ROM bytes
and reach native PC four and actual masked destinations. Invented seeds and an
actual nonzero public GPR are rejected. [The padding model](../../../Helpers/Tables/WordROMPadding.lean)
reflects v2's proving-loader zero extension; the raw table constructor still uses
UNIMP beyond its supplied image. Symbolic proofs distinguish those paths without
evaluating a million words, and missing Sail padding bytes remain failures.
The [explicit loader constructor](../../../Helpers/Tables/PaddedROMImage.lean)
now fills actual Sail tail bytes. [Symbolic lookup/extraction](../../../../Proofs/WordMemory/ROMBytePadding.lean)
derives full ROM extraction; prefix/outside bytes and original zero-profile/
configuration registers survive. [Decoder transport](../../../../Proofs/Trace/PaddedSetup.lean)
retains the actual public setup when its code fits the supplied prefix.

The added padded-boot claim in the same small public file feeds the previous
execution theorem unchanged. Full-ROM extraction and the existing public shadow
domain derive all coverage; no expected padding read or per-row state is supplied.
Ordinary/x0 native boot fixtures pass complete original execution from the padded
state, including exact byte boundaries and missing/oversized prefix rejection.
Physical initialization/setup exports and Rust/cryptographic enforcement remain open.

## Checked physical setup-row model

[The short read claim](Setup.lean) binds native-shaped tagged ROM membership to
actual Sail bytes after successful explicit loader construction. [Imported placement](../../../Helpers/Tables/SetupColumns.lean)
checks the exact 16-column artifact, all offsets and active/reserved extents.
[The complete tagged model](../../../Helpers/Tables/PhysicalSetup.lean) retains
native dummy/zero-padding tuples, separator tag 23 and word-ROM tag 24.
[Calculations](../../../../Proofs/WordMemory/PhysicalSetup.lean) derive exact
logical membership, key/data bounds and actual reads; no table equivalence or
expected value/read is supplied. [Nonempty regressions](../../../../../Tests/PhysicalSetup.lean)
recover original/padded words and reject altered ROM data and wrong padding tags.
Actual Rust-generated scalar/decoder/generic exports, normalization/LDE refinement,
physical initialization and argument enforcement remain separate.

[The setup bridge](Setup.lean) also accepts actual tagged ROM rows from the pinned
native fixture. The sole public byte condition is the successful four-word Sail
prefix extraction; explicit loader padding and symbolic complete-row certificates
derive the read. [The data entry point](../../../Circuits/WordMemory/Tables/NativeSetupData.lean)
keeps actual native values visible, while all calculations remain in Proofs.
General native program/decoder and full physical argument connections stay open.

[Sparse decoder claims](SparseDecoder.lean) recover original public Sail sources
when supported instructions are separated by unsupported pure words. Native mask
equations exclude holes and the full tail. Shared query calculations derive all
canonical decoder inputs without per-row bounds/flags. [An actual native export](../../../Circuits/WordMemory/Tables/NativeSparseData.lean)
has a complete row certificate from original public bytes and a full native
x0-load witness at PC 12. This decoder connection still needs integration with
initialized whole execution; no whole mixed-program claim is made.
