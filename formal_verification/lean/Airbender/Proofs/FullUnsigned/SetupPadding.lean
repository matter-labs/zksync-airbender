import Airbender.Proofs.FullUnsigned.SetupValidation
import Airbender.Proofs.Tables.BlockRanges

namespace Airbender.Setup
set_option warningAsError true
set_option Elab.async false

/-- Successful parsing already proves complete physical column coverage. -/
theorem parsed_column_length {source : String} {artifact : Artifact}
    (parsed : parse source = .ok artifact) {column : Column} (member : column ∈ artifact.columns) :
    (column.blocks.toList.map Block.length).sum = artifact.trace_len :=
  column.length_of_validate artifact.trace_len artifact.field_modulus
    (artifact.columns_of_validate (validate_of_parse parsed) column member)

/-- Exact coverage locates a final zero block without expanding its prefix. -/
theorem Column.zero_tail (column : Column) (length tail index : Nat)
    (covered : (column.blocks.toList.map Block.length).sum = length)
    (last : column.blocks.toList.getLast? = some (.affine tail 0 0))
    (lower : length - tail ≤ index) (upper : index < length) :
    column.get? index = some 0 := by
  obtain ⟨front, same⟩ := List.getLast?_eq_some_iff.mp last
  have total := covered
  rw [same] at total
  simp only [List.map_append, List.map_singleton, List.sum_append,
    List.sum_singleton, Block.length] at total
  have offset : (front.map Block.length).sum = length - tail := by omega
  have splitIndex : index = (front.map Block.length).sum +
      (index - (front.map Block.length).sum) := by omega
  change getFromBlocks column.blocks.toList index = some 0
  rw [same, splitIndex, Proofs.skip_blocks]
  have inside : index - (front.map Block.length).sum < tail := by omega
  simp [getFromBlocks, Block.get?, Block.length, inside]

/-- Parsing supplies coverage. Only the exact final block must be certified. -/
theorem parsed_column_zero_tail {source : String} {artifact : Artifact}
    (parsed : parse source = .ok artifact) {column : Column} (member : column ∈ artifact.columns)
    (tail index : Nat) (last : column.blocks.toList.getLast? = some (.affine tail 0 0))
    (lower : artifact.trace_len - tail ≤ index) (upper : index < artifact.trace_len) :
    column.get? index = some 0 :=
  column.zero_tail artifact.trace_len tail index (parsed_column_length parsed member) last lower upper

end Airbender.Setup
