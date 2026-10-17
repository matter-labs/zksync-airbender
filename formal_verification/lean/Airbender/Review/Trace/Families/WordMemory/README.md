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

The public shadow seeds describe a logical initialized native image. Binding them
to physical native zero boot, Sail boot/padding state, actual ROM-table binding
and original instruction execution/retirement remain open. The existing
arithmetic execution registry and its claims retain their scope. Physical setup
export, mixed/custom programs and cryptographic argument enforcement are separate.
