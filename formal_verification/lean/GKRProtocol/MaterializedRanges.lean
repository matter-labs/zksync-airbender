import GKRProtocol.MaterializedSetup
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

end Airbender.Compiler
