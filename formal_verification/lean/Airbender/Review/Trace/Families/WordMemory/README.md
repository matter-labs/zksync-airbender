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
its projection into architectural ROM state remains separate.

## Checked native-row inputs

[Native effects](Inputs.lean) derive effective-address addition, bounded aligned
incoming PCs, bounded modular PC successors and native clock/port order from the
same public image, actual decoder setup and accepted matching. The
[assembly](../../../../Proofs/Trace/Families/WordMemory/Inputs.lean) obtains the
source word from the first actual port and its initialized range proof. It calls
the existing native address, PC and clock calculations unchanged. No per-row
range, carry, PC, clock or desired-effect premise is supplied. The initialized
LW/SW/x0/ROM-shadow fixtures exercise the complete assembly.

## Remaining connection

[Public ROM extraction](../../../Helpers/Tables/WordROMImage.lean) now obtains
ROM words from actual Sail bytes. The short [read theorem](ROMImage.lean) binds
native ROM query data inside the extracted prefix; a complete extracted four-MiB
image covers every ROM address. Full native UNIMP padding remains represented.
The constructor does not fill absent padding bytes in Sail state.

Actual intermediate Sail source/port reads, Sail boot/padding state, discarded
ROM-shadow access projection and original Sail execution/retirement remain open. The existing
arithmetic execution registry and its claims retain their scope. Physical setup
export, mixed/custom programs and cryptographic argument enforcement are separate.
