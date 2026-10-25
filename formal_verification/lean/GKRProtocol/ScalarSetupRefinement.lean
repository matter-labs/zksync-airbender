import GKRProtocol.CleanRange

namespace Airbender.Compiler
set_option warningAsError true

/-- A literal increasing prefix followed by zero padding has the same values
on every shared row domain, regardless of the padding extent. -/
theorem scalar_row_affine_padded (data : Setup.TableData 1) (limit padding : Nat)
    (offset : data.offset = 0)
    (shape : data.columns[0].blocks.toList = [.affine limit 0 1, .affine padding 0 0])
    (index : Fin data.length) :
    ((data.row index)[0] : Source.BaseField) =
      if index.val < limit then (index.val : Source.BaseField) else 0 := by
  by_cases bounded : index.val < limit
  · rw [if_pos bounded]
    exact scalar_row_affine_prefix data limit offset [.affine padding 0 0] shape index bounded
  · rw [if_neg bounded]
    simp only [Setup.TableData.row, Vector.getElem_map]
    change (Setup.signedValue (((data.columns[0]).get? (data.offset + index.val)).getD 0) : Source.BaseField) = 0
    rw [Setup.signedValue_cast, offset]
    by_cases padded : index.val - limit < padding
    · simp [Setup.Column.get?, shape, Setup.getFromBlocks, Setup.Block.length, Setup.Block.get?, bounded, padded]
    · simp [Setup.Column.get?, shape, Setup.getFromBlocks, Setup.Block.length, bounded, padded]

/-- Transfer scalar membership into the retained Clean table by embedding its
actual row into that table's larger native domain. -/
theorem scalar_table_refinement (source target : Setup.TableData 1) (limit sourcePadding targetPadding : Nat)
    (sourceOffset : source.offset = 0) (targetOffset : target.offset = 0)
    (sourceShape : source.columns[0].blocks.toList = [.affine limit 0 1, .affine sourcePadding 0 0])
    (targetShape : target.columns[0].blocks.toList = [.affine limit 0 1, .affine targetPadding 0 0])
    (domain : source.length ≤ target.length) (value : Source.BaseField)
    (member : ∃ row : Fin source.length, value = ((source.row row)[0] : Source.BaseField))
    (name : String) (provided : Array Source.BaseField) :
    (target.scalarTable (p := babyBearModulus) name).Contains provided value := by
  obtain ⟨row, same⟩ := member
  let targetRow : Fin target.length := row.castLE domain
  change ∃ index : Fin target.length, value = ((target.row index)[0] : Source.BaseField)
  refine ⟨targetRow, ?_⟩
  rw [same, scalar_row_affine_padded source limit sourcePadding sourceOffset sourceShape,
    scalar_row_affine_padded target limit targetPadding targetOffset targetShape]
  rfl

end Airbender.Compiler
