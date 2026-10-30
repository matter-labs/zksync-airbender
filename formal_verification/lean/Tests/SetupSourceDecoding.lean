import Airbender.Proofs.FullUnsigned.SetupSourceDecoding

namespace Tests.SetupSourceDecoding
open Lean Airbender.Setup Airbender.Setup.SourceProofs Airbender.Setup.SourceDecoding
set_option warningAsError true
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option Elab.async false

private def column : Column := ⟨#[.affine 3 5 (-2), .dense #[0, 2013265920],
  .periodic 2 (-1) #[3, 7]]⟩

theorem mixed_column_decoded :
    (fromJson? (SourceData.columnJson column) : Except String Column) = .ok column :=
  decode_column column

theorem mixed_row_order (index : Fin 9) :
    column.get? index.val = (#[5, 3, 1, 0, 2013265920, 3, 7, 2, 6] : Array Nat)[index.val]? := by
  decide +kernel +revert

theorem physical_end : column.get? 9 = none := by setup_source_rfl

theorem repeated_columns_decoded :
    (fromJson? (SourceData.columnsJson #[column, column, ⟨#[]⟩]) :
      Except String (Array Column)) = .ok #[column, column, ⟨#[]⟩] :=
  decode_columns #[column, column, ⟨#[]⟩]

theorem empty_columns_decoded :
    (fromJson? (SourceData.columnsJson #[]) : Except String (Array Column)) = .ok #[] :=
  decode_columns #[]

theorem zero_repetitions_preserved :
    (fromJson? (SourceData.blockJson (.periodic 0 7 #[9])) : Except String Block) =
      .ok (.periodic 0 7 #[9]) := decode_block _

theorem negative_first_rejected :
    (fromJson? (Json.mkObj [("kind", .str "affine"), ("length", .num ⟨3, 0⟩),
      ("first", .num ⟨-1, 0⟩), ("step", .num ⟨1, 0⟩)]) : Except String Block).toOption = none := by
  setup_source_rfl

theorem negative_dense_rejected :
    (fromJson? (Json.mkObj [("kind", .str "dense"),
      ("values", .arr #[.num ⟨-1, 0⟩])]) : Except String Block).toOption = none := by
  setup_source_rfl

theorem fractional_stride_rejected :
    (fromJson? (Json.mkObj [("kind", .str "periodic"), ("repetitions", .num ⟨3, 0⟩),
      ("stride", .num ⟨3, 1⟩), ("values", .arr #[.num ⟨5, 0⟩])]) :
      Except String Block).toOption = none := by setup_source_rfl

theorem missing_blocks_rejected :
    (fromJson? (Json.mkObj [("block", .arr #[])]) : Except String Column).toOption = none := by
  setup_source_rfl

theorem field_decoded :
    (Json.mkObj [("circuit", .null), ("columns", SourceData.columnsJson #[column, column])]).getObjValAs?
      (Array Column) "columns" = .ok #[column, column] :=
  columns_field (by setup_source_rfl)

end Tests.SetupSourceDecoding
