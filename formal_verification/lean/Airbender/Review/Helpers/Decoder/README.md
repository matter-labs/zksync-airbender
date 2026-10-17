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
order. Placement is separate from public program/table construction and logical
membership; neither expected decoder fields nor cryptographic enforcement follow
from these definitions. V2 keeps original opcode masks and operands when rd=x0;
only the destination write is masked. The local row interface preserves this.
When constructing public tables, retain raw opcode funct3 bits even for U-type
instructions and native minus-one padding; the source's nine-column projection
cannot be copied unchanged.
