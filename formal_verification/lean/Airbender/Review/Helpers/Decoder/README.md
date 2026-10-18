# Decoder helper review

[Columns](Columns.lean) describes v2's ten native decoder columns, including the
separate destination-zero flag and already-packed family mask. The
[native query](NativeData.lean) preserves DecoderTableEntry.flatten order: two PC
limbs, rs1/rs2/rd, rd-is-zero, two immediate limbs, funct3 and mask.

[Import resolution](../../../Import/Parse.lean) uses the native state descriptor's
memory/witness bank choice, group extents and unique physical-to-logical mapping.
[Mechanical ADD/SUB binding](../../../Proofs/AddSub/ArtifactChecks.lean) fixes the
consumed IDs. The importer rejects unsupported nonempty funct7/family descriptor
fields rather than dropping them. The native preprocessor and padding sources
are pinned in [provenance](../../../../artifacts/provenance.json).

[Regression](../../../../Tests/NativeDecoderMetadata.lean) checks the full query
order. [Public program construction](Program.lean) reads actual Sail bytes and invokes
the pinned original decoder for ADD/ADDI/SUB/LUI/AUIPC. The selected-profile
[logical setup](Setup.lean) retains a power-of-two native-shaped capacity and
its complete all-minus-one tail. Missing, unsupported or effectful entries fail.
General Rust generation/export fidelity remains separate; this is not an imported
physical setup artifact or coverage of mixed/custom-opcode programs.

[Decoder recovery](../../../Proofs/Trace/DecoderSetup.lean) combines actual native
equations with logical membership over that full padded table. The packed-mask
bound excludes padding, then actual public Sail source evidence and the zero flag
are recovered. No table-equivalence or expected per-row metadata premise is used.
Cryptographic enforcement of membership remains separate. V2 keeps original opcode masks and operands when rd=x0;
only the destination write is masked. The local row interface preserves this.
When constructing public tables, retain raw opcode funct3 bits even for U-type
instructions and native minus-one padding; the source's nine-column projection
cannot be copied unchanged.

[Word-memory decoding](WordMemory.lean) uses the same generic original-byte/Sail
construction for LW/SW, with its own native registry and complete minus-one tail.
It retains sign extension, funct3=2, original x0 loads and the separate zero flag.
The [word-memory proof](../../../Proofs/Trace/Families/WordMemory/Decoder.lean)
rejects padding using the native Boolean store mask, then derives actual source
evidence, exact zero flags and PC/immediate bounds/alignment. A local native row
with flag 2 is rejected by full decoder membership. This is not yet initialized
word-memory execution or a public ROM-byte binding.

Successful construction also retains its exact indexed PC sequence. The
[PC composition](../../../Proofs/Trace/PC.lean) derives all incoming bounds and
alignment through RV32 truncation before applying native carry/wrap equations.

[Original clause selection](Instruction.lean) copies the pinned memory/register
dispatcher, selecting original Sail LOAD/STORE clauses. The v3 discarded-load
profile and its exclusions are omitted: v2 original LW-to-x0 memory behavior is
retained. [Native word-memory row assembly](../../../Proofs/Trace/Families/WordMemory/Execution.lean)
now uses actual decoding to select checked preparation/clause/retirement paths;
all calculations remain under Proofs. General finite trace/fetch composition
and physical setup/export remain separate.

[Setup placement](../Tables/SetupColumns.lean) now imports and guards the ten-wide
physical decoder group at column 2 for arithmetic or 6 for word-memory, with
native capacity 2^20 in a 2^24-row setup trace. Tagged generic tuples occupy
word-memory columns 2..5, including the native table ID. This checks compiled
placement; actual Rust-generated decoder columns, unsupported-slot materialization
and physical export/argument fidelity remain separate.

[Sparse construction](SparseSetup.lean) also retains unsupported pure words as
indexed holes. Missing bytes/effectful decoding fail; supported PCs remain 4*i.
[The word-memory interface](WordMemorySparse.lean) reuses the original projection.
[Calculations](../../../Proofs/Trace/Families/WordMemory/SparseDecoder.lean) derive
hole/tail exclusion from native equations and recover actual Sail sources,
canonical words/alignment and the exact zero flag. The [actual interior-hole export](../../Circuits/WordMemory/Tables/NativeSparseData.lean)
has a [complete kernel certificate](../../../Proofs/WordMemory/NativeSparseSetup.lean)
from original public bytes. [Public claims](../../Trace/Families/WordMemory/SparseDecoder.lean)
remain short. [Sparse initialized execution](../../Trace/Families/WordMemory/SparseExecution.lean)
now derives actual construction evidence internally and reuses the strict
history/retirement/terminal assembly. Original slots, PCs and bytes remain intact.
General Rust decoder agreement and full physical setup/argument correspondence
remain separate.

[Actual native arithmetic data](../../Circuits/AddSub/Tables/NativeSetupData.lean)
now reuses this generic sparse constructor. Its [complete certificate](../../../Proofs/AddSub/NativeSetup.lean)
checks every exported row against original Sail public bytes, with signed ADDI,
original SUB-to-x0, raw U-type funct3 and a supported word after an interior hole.
Native packed-mask equations exclude both hole/tail sentinels; [the source claim](../../Trace/Families/AddSub/NativeDecoder.lean)
adds no table-equivalence premise. This concrete export does not establish general
Rust decoder agreement or custom MOP semantics.

[Arithmetic sparse membership](ArithmeticSparse.lean) now feeds the
[short initialized execution claim](../../Trace/Families/AddSub/SparseExecution.lean).
[Proof-internal evidence](../../../Proofs/Trace/ProgramImage.lean) is derived from
actual strict/sparse construction, including original bytes, pure decoding and
indexed PC locations. Native mask equations reject unsupported slots before the
same arithmetic history/retirement/terminal assembly runs. The physical sparse
table keeps all holes/tail; its supported list is only an internal proof index.
General Rust/export and physical argument correspondence remain separate.

[The complete active decoder domain](../Tables/NativeDecoder.lean) now extends
actual native prefixes with the actual native minus-one padding API row. A
literal-data certificate proves repeated filler adds no query, retaining every
active row and excluding final normalization. [The arithmetic execution bridge](../../Trace/Families/AddSub/ActiveSetup.lean)
uses that membership directly; native mask equations still reject sentinels.
General Rust trace/export/LDE and cryptographic enforcement remain separate.

[Control decoding](../../Circuits/JumpBranchSlt/Decoder.lean) reuses sparse public
construction with v2's five packed masks and ten-column native query. Original
SLT/SLTI and jumps to x0 remain intact; SLTI uses mask 8, branches 16, and JAL
retains raw encoding funct3. [Native calculations](../../../Proofs/JumpBranchSlt/Decoder.lean)
exclude all sentinels before recovering original Sail source fields, canonical
words/alignment and the exact zero flag, then derive outgoing PC bounds without
a supplied mask. [The public-byte fixture](../../../../Tests/JumpDecoder.lean)
uses JAL -4 with tag 7, an UNIMP hole and original SLTIU-to-x0. [Actual native export](../../Circuits/JumpBranchSlt/Tables/NativeSetupData.lean)
now has a [complete independent Sail certificate](../../../Proofs/JumpBranchSlt/NativeSetup.lean).
Every prefix/tail row matches the public construction, feeding the short exported
source/PC claim without a table-equivalence premise. General Rust decoder agreement,
initialized control execution and physical argument refinement remain open.
