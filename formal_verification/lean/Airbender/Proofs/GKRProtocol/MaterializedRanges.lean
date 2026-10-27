import Airbender.Proofs.GKRProtocol.MaterializedSetup
import Airbender.Proofs.BabyBear

namespace Airbender.Compiler
set_option warningAsError true

/-- A literal affine prefix in the imported column supplies the corresponding
integer range, without enumerating its large native trace domain. -/
theorem scalar_row_affine_prefix (data : Setup.TableData 1) (limit : Nat)
    (offset : data.offset = 0) (rest : List Setup.Block)
    (initialBlocks : (data.columns[0]).blocks.toList = .affine limit 0 1 :: rest)
    (index : Fin data.length) (bounded : index.val < limit) :
    ((data.row index)[0] : Source.BaseField) = (index.val : Source.BaseField) := by
  simp only [Setup.TableData.row, Vector.getElem_map]
  change (Setup.signedValue (((data.columns[0]).get? (data.offset + index.val)).getD 0) : Source.BaseField) = _
  rw [Setup.signedValue_cast, offset]
  simp [Setup.Column.get?, initialBlocks, Setup.getFromBlocks, Setup.Block.length, Setup.Block.get?, bounded]

theorem MaterializedLookupSetup.range_contains (model : MaterializedLookupSetup width)
    (offset : model.imported.range16.offset = 0) (rest : List Setup.Block)
    (initialBlocks : (model.imported.range16.columns[0]).blocks.toList = .affine 65536 0 1 :: rest)
    (domain : 65536 ≤ model.imported.data.length) (value : Source.BaseField)
    (bounded : value.val < 65536) : model.Contains [.range16] [value] := by
  let row : Fin model.imported.data.length := ⟨value.val, lt_of_lt_of_le bounded domain⟩
  refine ⟨row, ?_⟩
  change [value] = [((model.imported.range16.row _)[0] : Source.BaseField)]
  rw [scalar_row_affine_prefix model.imported.range16 65536 offset rest initialBlocks _ bounded]
  exact congrArg (fun entry : Source.BaseField => [entry]) (ZMod.natCast_zmod_val value).symm

theorem MaterializedLookupSetup.timestamp_contains (model : MaterializedLookupSetup width)
    (offset : model.imported.timestampRange.offset = 0) (rest : List Setup.Block)
    (initialBlocks : (model.imported.timestampRange.columns[0]).blocks.toList = .affine 524288 0 1 :: rest)
    (domain : 524288 ≤ model.imported.data.length) (value : Source.BaseField)
    (bounded : value.val < 524288) : model.Contains [.timestamp] [value] := by
  let row : Fin model.imported.data.length := ⟨value.val, lt_of_lt_of_le bounded domain⟩
  refine ⟨row, ?_⟩
  change [value] = [((model.imported.timestampRange.row _)[0] : Source.BaseField)]
  rw [scalar_row_affine_prefix model.imported.timestampRange 524288 offset rest initialBlocks _ bounded]
  exact congrArg (fun entry : Source.BaseField => [entry]) (ZMod.natCast_zmod_val value).symm

/-- A range prefix followed by zero padding contains no out-of-range values.
This checks the complete literal column shape, including its padding. -/
theorem scalar_row_range_zero_padding (data : Setup.TableData 1) (limit padding : Nat)
    (positive : 0 < limit)
    (shape : (data.columns[0]).blocks.toList =
      [.affine limit 0 1, .affine padding 0 0]) (index : Fin data.length) :
    ((data.row index)[0] : Source.BaseField).val < limit := by
  simp only [Setup.TableData.row, Vector.getElem_map]
  change (Setup.signedValue (((data.columns[0]).get? (data.offset + index.val)).getD 0) : Source.BaseField).val < limit
  rw [Setup.signedValue_cast]
  simp only [Setup.Column.get?, shape, Setup.getFromBlocks, Setup.Block.length]
  split
  next bounded =>
    simp [Setup.Block.get?, Setup.Block.length, bounded, ZMod.val_natCast]
    exact lt_of_le_of_lt (Nat.mod_le _ _) bounded
  next outside =>
    split <;> simp [Setup.Block.get?, Setup.Block.length, *]

theorem MaterializedLookupSetup.timestamp_bounded (model : MaterializedLookupSetup width)
    (padding : Nat)
    (shape : (model.imported.timestampRange.columns[0]).blocks.toList =
      [.affine 524288 0 1, .affine padding 0 0])
    (value : Source.BaseField) (member : model.Contains [.timestamp] [value]) :
    value.val < 524288 := by
  obtain ⟨row, same⟩ := member
  have scalar : value = ((model.imported.timestampRange.row
      ⟨row.val, by rw [model.timestampDomain]; exact row.isLt⟩)[0] : Source.BaseField) :=
    List.singleton_inj.mp same
  rw [scalar]
  exact scalar_row_range_zero_padding model.imported.timestampRange 524288 padding (by decide) shape _

end Airbender.Compiler
