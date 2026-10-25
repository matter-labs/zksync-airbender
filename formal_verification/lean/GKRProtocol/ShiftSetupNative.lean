import GKRProtocol.ShiftPrefixNative.Column0
import GKRProtocol.ShiftPrefixNative.Column1
import GKRProtocol.ShiftPrefixNative.Column2
import GKRProtocol.ShiftPrefixNative.Column3
import GKRProtocol.ShiftPrefixNative.Column4
import GKRProtocol.ShiftPrefixNative.Column5
import GKRProtocol.ShiftPrefixNative.Column6
import GKRProtocol.ShiftPrefixNative.Column7
import GKRProtocol.ShiftPrefixNative.Column8
import GKRProtocol.ShiftPrefixNative.Column9
import GKRProtocol.CleanGenericSetup
import GKRProtocol.TaggedSetup
import GKRProtocol.MaterializedNative.ShiftBinopUncached

namespace Airbender.Compiler.ShiftSetupNative
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

abbrev nativeSetup := MaterializedNative.ShiftBinopUncached.native.model

theorem padding_shape : nativeSetup.imported.data.columns[(8 : Nat)].blocks.toList =
    [(Setup.Block.affine 524545 0 0), .affine 1048576 2013265920 0, .affine 15204095 0 0] := by rfl

theorem padding_domain (row : Fin nativeSetup.imported.data.length)
    (selected : nativeSetup.value row (.generic 8) = 0) :
    row.val < 524545 ∨ 1573121 ≤ row.val := by
  have bridge := nativeSetup.constant_tag_value (⟨8, by decide⟩ : Fin 10)
    [(524545, 0), (1048576, 2013265920), (15204095, 0)] padding_shape row
  simp only [show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add] at bridge
  rw [bridge] at selected
  simp only [constantTagValue] at selected
  split_ifs at selected
  all_goals first
    | omega
    | exact False.elim ((by decide +kernel : (2013265920 : Source.BaseField) ≠ 0) selected)

theorem prefix_row (row : Fin nativeSetup.imported.data.length) (bounded : row.val < 524545) :
    (nativeSetup.imported.data.row row).map (fun entry : Int => (entry : Source.BaseField)) =
      (Verification.shiftBinopRow ⟨row.val, bounded⟩).map (fun entry : Nat => (entry : Source.BaseField)) := by
  apply Vector.ext
  intro column wide
  simp only [Vector.getElem_map]
  rw [← nativeSetup.value_generic row (⟨column, wide⟩ : Fin 10)]
  rw [nativeSetup.generic_cell_value row (⟨column, wide⟩ : Fin 10),
    show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]
  change (((Data.GKRSetup.ShiftBinop.setup.data.columns[column]).get? row.val).getD 0 : Source.BaseField) = _
  have small : column < 10 := wide
  interval_cases column
  · exact congrArg (fun entry : Nat => (entry : Source.BaseField)) (ShiftPrefixNative.Column0.clean_value ⟨row.val, bounded⟩)
  · exact congrArg (fun entry : Nat => (entry : Source.BaseField)) (ShiftPrefixNative.Column1.clean_value ⟨row.val, bounded⟩)
  · exact congrArg (fun entry : Nat => (entry : Source.BaseField)) (ShiftPrefixNative.Column2.clean_value ⟨row.val, bounded⟩)
  · exact congrArg (fun entry : Nat => (entry : Source.BaseField)) (ShiftPrefixNative.Column3.clean_value ⟨row.val, bounded⟩)
  · exact congrArg (fun entry : Nat => (entry : Source.BaseField)) (ShiftPrefixNative.Column4.clean_value ⟨row.val, bounded⟩)
  · exact congrArg (fun entry : Nat => (entry : Source.BaseField)) (ShiftPrefixNative.Column5.clean_value ⟨row.val, bounded⟩)
  · exact congrArg (fun entry : Nat => (entry : Source.BaseField)) (ShiftPrefixNative.Column6.clean_value ⟨row.val, bounded⟩)
  · exact congrArg (fun entry : Nat => (entry : Source.BaseField)) (ShiftPrefixNative.Column7.clean_value ⟨row.val, bounded⟩)
  · exact congrArg (fun entry : Nat => (entry : Source.BaseField)) (ShiftPrefixNative.Column8.clean_value ⟨row.val, bounded⟩)
  · exact congrArg (fun entry : Nat => (entry : Source.BaseField)) (ShiftPrefixNative.Column9.clean_value ⟨row.val, bounded⟩)

theorem dummy_row_zero : Verification.shiftBinopRow 0 = Vector.replicate 10 0 := by decide +kernel

theorem padding_row (row : Fin nativeSetup.imported.data.length) (lower : 1573121 ≤ row.val) :
    (nativeSetup.imported.data.row row).map (fun entry : Int => (entry : Source.BaseField)) =
      (Verification.shiftBinopRow 0).map (fun entry : Nat => (entry : Source.BaseField)) := by
  rw [dummy_row_zero]
  apply Vector.ext
  intro column wide
  simp only [Vector.getElem_map, Vector.getElem_replicate]
  rw [← nativeSetup.value_generic row (⟨column, wide⟩ : Fin 10)]
  rw [nativeSetup.generic_cell_value row (⟨column, wide⟩ : Fin 10),
    show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]
  change (((Data.GKRSetup.ShiftBinop.setup.data.columns[column]).get? row.val).getD 0 : Source.BaseField) = _
  have small : column < 10 := wide
  interval_cases column
  · rw [show (Data.GKRSetup.ShiftBinop.setup.data.columns[(0 : Nat)]) = Data.GKRSetup.ShiftBinop.setupColumn0 from rfl, ShiftPrefixNative.Column0.padding_value row lower]
    rfl
  · rw [show (Data.GKRSetup.ShiftBinop.setup.data.columns[(1 : Nat)]) = Data.GKRSetup.ShiftBinop.setupColumn1 from rfl, ShiftPrefixNative.Column1.padding_value row lower]
    rfl
  · rw [show (Data.GKRSetup.ShiftBinop.setup.data.columns[(2 : Nat)]) = Data.GKRSetup.ShiftBinop.setupColumn2 from rfl, ShiftPrefixNative.Column2.padding_value row lower]
    rfl
  · rw [show (Data.GKRSetup.ShiftBinop.setup.data.columns[(3 : Nat)]) = Data.GKRSetup.ShiftBinop.setupColumn3 from rfl, ShiftPrefixNative.Column3.padding_value row lower]
    rfl
  · rw [show (Data.GKRSetup.ShiftBinop.setup.data.columns[(4 : Nat)]) = Data.GKRSetup.ShiftBinop.setupColumn4 from rfl, ShiftPrefixNative.Column4.padding_value row lower]
    rfl
  · rw [show (Data.GKRSetup.ShiftBinop.setup.data.columns[(5 : Nat)]) = Data.GKRSetup.ShiftBinop.setupColumn5 from rfl, ShiftPrefixNative.Column5.padding_value row lower]
    rfl
  · rw [show (Data.GKRSetup.ShiftBinop.setup.data.columns[(6 : Nat)]) = Data.GKRSetup.ShiftBinop.setupColumn6 from rfl, ShiftPrefixNative.Column6.padding_value row lower]
    rfl
  · rw [show (Data.GKRSetup.ShiftBinop.setup.data.columns[(7 : Nat)]) = Data.GKRSetup.ShiftBinop.setupColumn7 from rfl, ShiftPrefixNative.Column7.padding_value row lower]
    rfl
  · rw [show (Data.GKRSetup.ShiftBinop.setup.data.columns[(8 : Nat)]) = Data.GKRSetup.ShiftBinop.setupColumn8 from rfl, ShiftPrefixNative.Column8.padding_value row lower]
    rfl
  · rw [show (Data.GKRSetup.ShiftBinop.setup.data.columns[(9 : Nat)]) = Data.GKRSetup.ShiftBinop.setupColumn9 from rfl, ShiftPrefixNative.Column9.padding_value row lower]
    rfl

/-- Full exported rows accepted by a Shift lookup refine the retained fixed
rows. The actual zero padding operand excludes the decoder region. -/
theorem clean_contains (value : Vector Source.BaseField 10)
    (member : nativeSetup.Contains ((List.range 10).map SourceSetupColumn.generic) value.toList)
    (padding : value[8] = 0) (provided : Array (Vector Source.BaseField 10)) :
    (Verification.shiftBinopTable (p := babyBearModulus)).Contains provided value := by
  obtain ⟨row, same⟩ := member
  rw [nativeSetup.generic_fields row] at same
  have equality := Vector.toList_inj.mp same
  have selected : nativeSetup.value row (.generic 8) = 0 := by
    rw [equality] at padding
    rw [nativeSetup.value_generic row (⟨8, by decide⟩ : Fin 10)]
    simpa only [Vector.getElem_map] using padding
  change ∃ index : Fin 524545, value = (Verification.shiftBinopRow index).map (fun entry : Nat => (entry : Source.BaseField))
  rcases padding_domain row selected with bounded | lower
  · exact ⟨⟨row.val, bounded⟩, equality.trans (prefix_row row bounded)⟩
  · exact ⟨0, equality.trans (padding_row row lower)⟩

end Airbender.Compiler.ShiftSetupNative
