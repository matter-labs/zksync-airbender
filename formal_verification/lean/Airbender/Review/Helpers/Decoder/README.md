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
remain short; general Rust decoder agreement, sparse initialized execution and
full physical setup/argument correspondence remain separate.
