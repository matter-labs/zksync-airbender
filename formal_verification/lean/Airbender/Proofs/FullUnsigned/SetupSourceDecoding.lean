import Airbender.Import.SetupSourceColumns
import Airbender.Proofs.FullUnsigned.SetupSourceArrays

namespace Airbender.Setup.SourceDecoding
open Lean SourceProofs
set_option warningAsError true
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option Elab.async false

/-- Use full transparency for this definitional goal conversion.
The kernel checks the completed theorem term. -/
elab "setup_decode_change " target:term : tactic => do
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let type ← Lean.Elab.Term.elabTerm target (some (Lean.mkSort Lean.Level.zero))
    let changed ← Lean.Meta.withTransparency .all <| goal.change type
    Lean.Elab.Tactic.replaceMainGoal [changed]

theorem decode_natural (n : Nat) :
    (fromJson? (.num ⟨n, 0⟩) : Except String Nat) = .ok n := by setup_source_rfl

theorem decode_integer (n : Int) :
    (fromJson? (.num ⟨n, 0⟩) : Except String Int) = .ok n := by setup_source_rfl

theorem decode_naturals (values : Array Nat) :
    (fromJson? (.arr (values.map fun n : Nat => Json.num ⟨n, 0⟩)) : Except String (Array Nat)) =
      .ok values := by
  have h := decode_array_family (fun n : Nat => Json.num ⟨n, 0⟩) id decode_natural values.toList
  simpa only [← List.map_toArray, Array.toArray_toList, List.map_id_fun, id] using h

theorem decode_block (block : Block) :
    (fromJson? (SourceData.blockJson block) : Except String Block) = .ok block := by
  cases block with
  | affine length first step => setup_source_rfl
  | dense values =>
    setup_decode_change (do
      let decoded ← (fromJson? (.arr (values.map fun n : Nat => Json.num ⟨n, 0⟩)) : Except String (Array Nat))
      pure (Block.dense decoded)) = Except.ok (Block.dense values)
    rw [decode_naturals]
    rfl
  | periodic repetitions stride values =>
    setup_decode_change (do
      let decoded ← (fromJson? (.arr (values.map fun n : Nat => Json.num ⟨n, 0⟩)) : Except String (Array Nat))
      pure (Block.periodic repetitions stride decoded)) = Except.ok (Block.periodic repetitions stride values)
    rw [decode_naturals]
    rfl

/-- Decode every RLE block once. Preserve its position in the column. -/
theorem decode_column (column : Column) :
    (fromJson? (SourceData.columnJson column) : Except String Column) = .ok column := by
  have decoded := decode_blocks_object_family SourceData.blockJson id decode_block column.blocks.toList
  simpa only [SourceData.columnJson, ← List.map_toArray, Array.toArray_toList,
    List.map_id_fun, id] using decoded

/-- Decode the complete physical column array. No row is selected or removed. -/
theorem decode_columns (columns : Array Column) :
    (fromJson? (SourceData.columnsJson columns) : Except String (Array Column)) = .ok columns := by
  have decoded := decode_array_family SourceData.columnJson id decode_column columns.toList
  simpa only [SourceData.columnsJson, ← List.map_toArray, Array.toArray_toList,
    List.map_id_fun, id] using decoded

/-- An exact retained column field supplies the artifact decoder's field value. -/
theorem columns_field {json : Json} {columns : Array Column}
    (field : json.getObjVal? "columns" = .ok (SourceData.columnsJson columns)) :
    json.getObjValAs? (Array Column) "columns" = .ok columns := by
  unfold Json.getObjValAs? Json.getObjValD
  rw [field]
  exact decode_columns columns

end Airbender.Setup.SourceDecoding
