import Airbender.Proofs.GKRProtocol.MaterializedSetup
import Airbender.Proofs.BabyBear

namespace Airbender.Compiler
set_option warningAsError true

/-- Piecewise constant physical tag columns retain their complete row domain,
including decoder and zero-padding regions. -/
def constantTagValue : List (Nat × Nat) → Nat → Source.BaseField
  | [], _ => 0
  | (length, tag) :: rest, index =>
      if index < length then tag else constantTagValue rest (index - length)

theorem constant_tag_blocks (segments : List (Nat × Nat)) (index : Nat) :
    (((Setup.getFromBlocks (segments.map (fun entry => Setup.Block.affine entry.1 entry.2 0)) index).getD 0) : Source.BaseField) =
      constantTagValue segments index := by
  induction segments generalizing index with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨length, tag⟩ := entry
    simp only [List.map_cons, Setup.getFromBlocks, Setup.Block.length, constantTagValue]
    by_cases bounded : index < length
    · simp [Setup.Block.get?, Setup.Block.length, bounded]
    · simp only [if_neg bounded]
      exact ih _

theorem MaterializedLookupSetup.constant_tag_value (model : MaterializedLookupSetup width)
    (column : Fin width) (segments : List (Nat × Nat))
    (shape : (model.imported.data.columns[column.val]).blocks.toList =
      segments.map (fun entry => Setup.Block.affine entry.1 entry.2 0))
    (row : Fin model.imported.data.length) :
    model.value row (.generic column.val) =
      constantTagValue segments (model.imported.data.offset + row.val) := by
  rw [model.value_generic]
  simp only [Setup.TableData.row, Vector.getElem_map]
  change (Setup.signedValue (((model.imported.data.columns[column.val]).get?
    (model.imported.data.offset + row.val)).getD 0) : Source.BaseField) = _
  rw [Setup.signedValue_cast]
  change (((Setup.getFromBlocks (model.imported.data.columns[column.val]).blocks.toList
    (model.imported.data.offset + row.val)).getD 0) : Source.BaseField) = _
  rw [shape]
  exact constant_tag_blocks segments _

end Airbender.Compiler
