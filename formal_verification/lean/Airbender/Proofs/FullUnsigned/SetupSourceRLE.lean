import Airbender.Proofs.FullUnsigned.SetupSourceBank
import Airbender.Proofs.FullUnsigned.SetupSourceDecoding

namespace Airbender.Setup.SourceDecoding
open Lean SourceProofs SourceBank
set_option warningAsError true
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option Elab.async false

structure NaturalAt (strings : Nat → String) (tokens : Nat → SourceData.NumberToken) (bank : Bank)
    (fuel index value : Nat) : Prop where
  value : (evaluate strings tokens bank fuel index).value = .num ⟨value, 0⟩

theorem NaturalAt.choose {strings tokens bank fuel leftIndex rightIndex leftValue rightValue}
    (condition : Prop) [Decidable condition]
    (left : NaturalAt strings tokens bank fuel leftIndex leftValue)
    (right : NaturalAt strings tokens bank fuel rightIndex rightValue) :
    NaturalAt strings tokens bank fuel (if condition then leftIndex else rightIndex)
      (if condition then leftValue else rightValue) := by
  split <;> assumption

structure NaturalsAt (strings : Nat → String) (tokens : Nat → SourceData.NumberToken) (bank : Bank)
    (fuel index : Nat) (values : Array Nat) : Prop where
  value : (evaluate strings tokens bank fuel index).value =
    .arr (values.map fun value : Nat => .num ⟨value, 0⟩)

theorem naturals_at (strings : Nat → String) (tokens : Nat → SourceData.NumberToken) (bank : Bank)
    (fuel arrayIndex : Nat) (children values : Nat → Nat) (entries : List Nat)
    (selected : bank.get arrayIndex = .indexedArray children entries)
    (checked : ∀ index, NaturalAt strings tokens bank fuel (children index) (values index)) :
    NaturalsAt strings tokens bank (fuel + 1) arrayIndex (entries.map values).toArray := by
  constructor
  have same : (fun index => (evaluate strings tokens bank fuel (children index)).value) =
      (fun index => Json.num ⟨values index, 0⟩) := funext (fun index => (checked index).value)
  simp only [evaluate, selected, sharedArrayNode_eq, SourceData.arrayNode, same,
    List.map_toArray, List.map_map, Function.comp_def]

theorem block_array_template (block : Block) :
    SourceData.blockJson block = SourceData.blockArrayTemplate block
      (.arr ((SourceData.blockValues block).map fun value : Nat => .num ⟨value, 0⟩)) := by
  cases block <;> setup_source_rfl

/-- A source node has the exact JSON value of one retained RLE block. -/
structure BlockAt (strings : Nat → String) (tokens : Nat → SourceData.NumberToken) (bank : Bank)
    (fuel index : Nat) (block : Block) : Prop where
  value : (evaluate strings tokens bank fuel index).value = SourceData.blockJson block

theorem BlockAt.decode {strings tokens bank fuel index block}
    (checked : BlockAt strings tokens bank fuel index block) :
    (fromJson? (evaluate strings tokens bank fuel index).value : Except String Block) = .ok block := by
  rw [checked.value]
  exact decode_block block

theorem BlockAt.choose {strings tokens bank fuel leftIndex rightIndex leftBlock rightBlock}
    (condition : Prop) [Decidable condition]
    (left : BlockAt strings tokens bank fuel leftIndex leftBlock)
    (right : BlockAt strings tokens bank fuel rightIndex rightBlock) :
    BlockAt strings tokens bank fuel (if condition then leftIndex else rightIndex)
      (if condition then leftBlock else rightBlock) := by
  split <;> assumption

theorem BlockAt.of_naturals (strings : Nat → String) (tokens : Nat → SourceData.NumberToken) (bank : Bank)
    (blockFuel arrayFuel blockIndex arrayIndex : Nat) (block : Block)
    (checked : NaturalsAt strings tokens bank arrayFuel arrayIndex (SourceData.blockValues block))
    (shape : (evaluate strings tokens bank blockFuel blockIndex).value =
      SourceData.blockArrayTemplate block (evaluate strings tokens bank arrayFuel arrayIndex).value) :
    BlockAt strings tokens bank blockFuel blockIndex block := by
  constructor
  rw [shape, checked.value, ← block_array_template]

/-- The decoder returns every retained block of the source column. -/
structure ColumnAt (strings : Nat → String) (tokens : Nat → SourceData.NumberToken) (bank : Bank)
    (fuel index : Nat) (column : Column) : Prop where
  decoded : (fromJson? (evaluate strings tokens bank fuel index).value : Except String Column) = .ok column

theorem ColumnAt.choose {strings tokens bank fuel leftIndex rightIndex leftColumn rightColumn}
    (condition : Prop) [Decidable condition]
    (left : ColumnAt strings tokens bank fuel leftIndex leftColumn)
    (right : ColumnAt strings tokens bank fuel rightIndex rightColumn) :
    ColumnAt strings tokens bank fuel (if condition then leftIndex else rightIndex)
      (if condition then leftColumn else rightColumn) := by
  split <;> assumption

theorem column_of_blocks (strings : Nat → String) (tokens : Nat → SourceData.NumberToken) (bank : Bank)
    (fuel columnIndex keyIndex arrayIndex : Nat) (children : Nat → Nat) (blocks : Nat → Block)
    (entries : List Nat)
    (columnSelected : bank.get columnIndex = .object [(keyIndex, arrayIndex)])
    (keySelected : strings keyIndex = "blocks")
    (arraySelected : bank.get arrayIndex = .indexedArray children entries)
    (checked : ∀ index, BlockAt strings tokens bank fuel (children index) (blocks index)) :
    ColumnAt strings tokens bank (fuel + 2) columnIndex ⟨(entries.map blocks).toArray⟩ := by
  constructor
  have shape : (evaluate strings tokens bank (fuel + 2) columnIndex).value =
      Json.mkObj [("blocks", .arr (entries.map
        (fun index => (evaluate strings tokens bank fuel (children index)).value)).toArray)] := by
    simp only [evaluate, columnSelected, arraySelected, sharedObjectNode_eq, sharedArrayNode_eq,
      SourceData.objectNode, SourceData.arrayNode, List.map_cons, List.map_nil, keySelected]
  rw [shape]
  exact decode_blocks_object_family _ blocks (fun index => (checked index).decode) entries

theorem columns_at (strings : Nat → String) (tokens : Nat → SourceData.NumberToken) (bank : Bank)
    (fuel arrayIndex : Nat) (children : Nat → Nat) (columns : Nat → Column) (entries : List Nat)
    (selected : bank.get arrayIndex = .indexedArray children entries)
    (checked : ∀ index, ColumnAt strings tokens bank fuel (children index) (columns index)) :
    (fromJson? (evaluate strings tokens bank (fuel + 1) arrayIndex).value :
      Except String (Array Column)) = .ok (entries.map columns).toArray := by
  simp only [evaluate, selected, sharedArrayNode_eq, SourceData.arrayNode]
  exact decode_array_family _ columns (fun index => (checked index).decoded) entries

theorem columns_field_of_value {json value : Json} {columns : Array Column}
    (field : json.getObjValD "columns" = value)
    (decoded : (fromJson? value : Except String (Array Column)) = .ok columns) :
    json.getObjValAs? (Array Column) "columns" = .ok columns := by
  unfold Json.getObjValAs?
  rw [field]
  exact decoded

end Airbender.Setup.SourceDecoding
