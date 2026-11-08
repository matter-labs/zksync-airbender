import Airbender.Proofs.FullUnsigned.ThetaControlSuffixes
import Airbender.Proofs.FullUnsigned.SourceColumnRanges
import Airbender.Proofs.FullUnsigned.SourceColumnCoverage
import Airbender.Proofs.FullUnsigned.ChiSourceController
import Airbender.Data.Setup.Keccak.ThetaRhoPhysical

namespace Airbender.Setup.SourceCaptureThetaProofs
open Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
-- Each controller or slot check has 121 rows and nine fields.
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private noncomputable def sourceColumn (column : Fin 9) : Column :=
  (SourceCaptureTheta.columns[column.val]?).getD ⟨#[]⟩

private noncomputable def sourceBinding (column : Fin 9) : SourceBank.ColumnBinding :=
  (SourceCaptureTheta.columnBindings[column.val]'(by change column.val < 9; exact column.isLt)).1

private noncomputable def sourceEntries (column : Fin 9) : List Nat :=
  match column.val with
  | 0 => SourceCaptureTheta.entries_7040
  | 1 => SourceCaptureTheta.entries_7064
  | 2 => SourceCaptureTheta.entries_8478
  | 3 => SourceCaptureTheta.entries_9296
  | 4 => SourceCaptureTheta.entries_10186
  | 5 => SourceCaptureTheta.entries_10204
  | 6 => SourceCaptureTheta.entries_10212
  | 7 => SourceCaptureTheta.entries_10220
  | _ => SourceCaptureTheta.entries_10225

private noncomputable def tailEntries (column : Fin 9) : List Nat :=
  match column.val with
  | 0 => ThetaControlSuffix.Column0.entries
  | 1 => ThetaControlSuffix.Column1.entries
  | 2 => ThetaControlSuffix.Column2.entries
  | 3 => ThetaControlSuffix.Column3.entries
  | 4 => ThetaControlSuffix.Column4.entries
  | 5 => ThetaControlSuffix.Column5.entries
  | 6 => ThetaControlSuffix.Column6.entries
  | 7 => ThetaControlSuffix.Column7.entries
  | _ => ThetaControlSuffix.Column8.entries

private noncomputable def tailSkip (column : Fin 9) : Nat :=
  match column.val with
  | 0 => ThetaControlSuffix.Column0.skip
  | 1 => ThetaControlSuffix.Column1.skip
  | 2 => ThetaControlSuffix.Column2.skip
  | 3 => ThetaControlSuffix.Column3.skip
  | 4 => ThetaControlSuffix.Column4.skip
  | 5 => ThetaControlSuffix.Column5.skip
  | 6 => ThetaControlSuffix.Column6.skip
  | 7 => ThetaControlSuffix.Column7.skip
  | _ => ThetaControlSuffix.Column8.skip

private noncomputable def tailLength (column : Fin 9) : Nat :=
  match column.val with
  | 0 => 4194304
  | 1 => 4194304
  | 2 => 4150064
  | 3 => 3782400
  | 4 => 3627552
  | 5 => 4194304
  | 6 => 4194304
  | 7 => 4194304
  | _ => 4194304

private noncomputable def tailBlocks (column : Fin 9) : List Block :=
  (tailEntries column).map (sourceBinding column).blocks

private theorem source_column_binding (column : Fin 9) :
    sourceColumn column = (sourceBinding column).column := by
  fin_cases column <;> simp only [sourceBinding, SourceCaptureTheta.columnBindings,
    List.getElem_cons_zero, List.getElem_cons_succ] <;> rfl

private theorem binding_entries (column : Fin 9) :
    (sourceBinding column).entries = sourceEntries column := by
  fin_cases column <;> simp only [sourceBinding, SourceCaptureTheta.columnBindings,
    List.getElem_cons_zero, List.getElem_cons_succ, sourceEntries] <;> source_record_entries

private theorem source_suffix (column : Fin 9) :
    (sourceColumn column).blocks.toList.drop (tailSkip column) = tailBlocks column := by
  rw [source_column_binding]
  simp only [SourceBank.ColumnBinding.column, List.toList_toArray, ← List.map_drop]
  unfold tailBlocks
  apply congrArg (fun entries : List Nat => entries.map (sourceBinding column).blocks)
  rw [binding_entries]
  fin_cases column
  · simpa only [sourceEntries, tailSkip, tailEntries] using ThetaControlSuffix.Column0.matches
  · simpa only [sourceEntries, tailSkip, tailEntries] using ThetaControlSuffix.Column1.matches
  · simpa only [sourceEntries, tailSkip, tailEntries] using ThetaControlSuffix.Column2.matches
  · simpa only [sourceEntries, tailSkip, tailEntries] using ThetaControlSuffix.Column3.matches
  · simpa only [sourceEntries, tailSkip, tailEntries] using ThetaControlSuffix.Column4.matches
  · simpa only [sourceEntries, tailSkip, tailEntries] using ThetaControlSuffix.Column5.matches
  · simpa only [sourceEntries, tailSkip, tailEntries] using ThetaControlSuffix.Column6.matches
  · simpa only [sourceEntries, tailSkip, tailEntries] using ThetaControlSuffix.Column7.matches
  · simpa only [sourceEntries, tailSkip, tailEntries] using ThetaControlSuffix.Column8.matches

private theorem tail_length (column : Fin 9) :
    ((tailBlocks column).map Block.length).sum = tailLength column := by
  fin_cases column <;> setup_source_rfl

private theorem tail_cut : ∀ column : Fin 9, 4194304 - tailLength column ≤ 589824 := by decide +kernel

private theorem source_covered {artifact : Artifact} (parsed : parse SourceCaptureTheta.source = .ok artifact)
    (column : Fin 9) : ((sourceColumn column).blocks.toList.map Block.length).sum = 4194304 := by
  have bound : column.val < SourceCaptureTheta.columns.size := by change column.val < 9; exact column.isLt
  have member : sourceColumn column ∈ SourceCaptureTheta.columns := by
    unfold sourceColumn
    rw [Array.getElem?_eq_getElem bound, Option.getD_some]
    simp
  exact source_column_lengths SourceCaptureThetaProofs.parsed trace_len_decoded columns_decoded parsed _ member

-- Keep each closed computation within one 121-row column during kernel replay.

private def controllerValueCorrect (index : Fin 121) (column : Fin 9) : Prop :=
    signedValue ((getFromBlocks (tailBlocks column)
      (589824 + index.val - (4194304 - tailLength column))).getD 0) =
      signedValue ((Airbender.Keccak.Split.Native.Fixed.thetaRhoControl.columns[column.val].get? index.val).getD 0)

private theorem controllerValues0 : ∀ index : Fin 121,
    controllerValueCorrect index ⟨0, by decide⟩ := by
  unfold controllerValueCorrect
  decide +kernel

private theorem controllerValues1 : ∀ index : Fin 121,
    controllerValueCorrect index ⟨1, by decide⟩ := by
  unfold controllerValueCorrect
  decide +kernel

private theorem controllerValues2 : ∀ index : Fin 121,
    controllerValueCorrect index ⟨2, by decide⟩ := by
  unfold controllerValueCorrect
  decide +kernel

private theorem controllerValues3 : ∀ index : Fin 121,
    controllerValueCorrect index ⟨3, by decide⟩ := by
  unfold controllerValueCorrect
  decide +kernel

private theorem controllerValues4 : ∀ index : Fin 121,
    controllerValueCorrect index ⟨4, by decide⟩ := by
  unfold controllerValueCorrect
  decide +kernel

private theorem controllerValues5 : ∀ index : Fin 121,
    controllerValueCorrect index ⟨5, by decide⟩ := by
  unfold controllerValueCorrect
  decide +kernel

private theorem controllerValues6 : ∀ index : Fin 121,
    controllerValueCorrect index ⟨6, by decide⟩ := by
  unfold controllerValueCorrect
  decide +kernel

private theorem controllerValues7 : ∀ index : Fin 121,
    controllerValueCorrect index ⟨7, by decide⟩ := by
  unfold controllerValueCorrect
  decide +kernel

private theorem controllerValues8 : ∀ index : Fin 121,
    controllerValueCorrect index ⟨8, by decide⟩ := by
  unfold controllerValueCorrect
  decide +kernel

private theorem controller_values : ∀ index : Fin 121, ∀ column : Fin 9,
    signedValue ((getFromBlocks (tailBlocks column)
      (589824 + index.val - (4194304 - tailLength column))).getD 0) =
      signedValue ((Airbender.Keccak.Split.Native.Fixed.thetaRhoControl.columns[column.val].get? index.val).getD 0) := by
  intro index column
  change controllerValueCorrect index column

  by_cases h0 : column.val = 0
  · have same : column = ⟨0, by decide⟩ := Fin.ext h0
    subst column
    exact controllerValues0 index

  by_cases h1 : column.val = 1
  · have same : column = ⟨1, by decide⟩ := Fin.ext h1
    subst column
    exact controllerValues1 index

  by_cases h2 : column.val = 2
  · have same : column = ⟨2, by decide⟩ := Fin.ext h2
    subst column
    exact controllerValues2 index

  by_cases h3 : column.val = 3
  · have same : column = ⟨3, by decide⟩ := Fin.ext h3
    subst column
    exact controllerValues3 index

  by_cases h4 : column.val = 4
  · have same : column = ⟨4, by decide⟩ := Fin.ext h4
    subst column
    exact controllerValues4 index

  by_cases h5 : column.val = 5
  · have same : column = ⟨5, by decide⟩ := Fin.ext h5
    subst column
    exact controllerValues5 index

  by_cases h6 : column.val = 6
  · have same : column = ⟨6, by decide⟩ := Fin.ext h6
    subst column
    exact controllerValues6 index

  by_cases h7 : column.val = 7
  · have same : column = ⟨7, by decide⟩ := Fin.ext h7
    subst column
    exact controllerValues7 index

  have same : column = ⟨8, by decide⟩ := by
    apply Fin.ext
    change column.val = 8
    have bound := column.isLt
    omega
  subst column
  exact controllerValues8 index

private def slotValueCorrect (index : Fin 121) (column : Fin 9) : Prop :=
    signedValue ((getFromBlocks (tailBlocks column)
      (589945 + index.val - (4194304 - tailLength column))).getD 0) =
      signedValue ((Airbender.Keccak.Split.Native.Fixed.thetaRhoSlots.columns[column.val].get? index.val).getD 0)

private theorem slotValues0 : ∀ index : Fin 121,
    slotValueCorrect index ⟨0, by decide⟩ := by
  unfold slotValueCorrect
  decide +kernel

private theorem slotValues1 : ∀ index : Fin 121,
    slotValueCorrect index ⟨1, by decide⟩ := by
  unfold slotValueCorrect
  decide +kernel

private theorem slotValues2 : ∀ index : Fin 121,
    slotValueCorrect index ⟨2, by decide⟩ := by
  unfold slotValueCorrect
  decide +kernel

private theorem slotValues3 : ∀ index : Fin 121,
    slotValueCorrect index ⟨3, by decide⟩ := by
  unfold slotValueCorrect
  decide +kernel

private theorem slotValues4 : ∀ index : Fin 121,
    slotValueCorrect index ⟨4, by decide⟩ := by
  unfold slotValueCorrect
  decide +kernel

private theorem slotValues5 : ∀ index : Fin 121,
    slotValueCorrect index ⟨5, by decide⟩ := by
  unfold slotValueCorrect
  decide +kernel

private theorem slotValues6 : ∀ index : Fin 121,
    slotValueCorrect index ⟨6, by decide⟩ := by
  unfold slotValueCorrect
  decide +kernel

private theorem slotValues7 : ∀ index : Fin 121,
    slotValueCorrect index ⟨7, by decide⟩ := by
  unfold slotValueCorrect
  decide +kernel

private theorem slotValues8 : ∀ index : Fin 121,
    slotValueCorrect index ⟨8, by decide⟩ := by
  unfold slotValueCorrect
  decide +kernel

private theorem slot_values : ∀ index : Fin 121, ∀ column : Fin 9,
    signedValue ((getFromBlocks (tailBlocks column)
      (589945 + index.val - (4194304 - tailLength column))).getD 0) =
      signedValue ((Airbender.Keccak.Split.Native.Fixed.thetaRhoSlots.columns[column.val].get? index.val).getD 0) := by
  intro index column
  change slotValueCorrect index column

  by_cases h0 : column.val = 0
  · have same : column = ⟨0, by decide⟩ := Fin.ext h0
    subst column
    exact slotValues0 index

  by_cases h1 : column.val = 1
  · have same : column = ⟨1, by decide⟩ := Fin.ext h1
    subst column
    exact slotValues1 index

  by_cases h2 : column.val = 2
  · have same : column = ⟨2, by decide⟩ := Fin.ext h2
    subst column
    exact slotValues2 index

  by_cases h3 : column.val = 3
  · have same : column = ⟨3, by decide⟩ := Fin.ext h3
    subst column
    exact slotValues3 index

  by_cases h4 : column.val = 4
  · have same : column = ⟨4, by decide⟩ := Fin.ext h4
    subst column
    exact slotValues4 index

  by_cases h5 : column.val = 5
  · have same : column = ⟨5, by decide⟩ := Fin.ext h5
    subst column
    exact slotValues5 index

  by_cases h6 : column.val = 6
  · have same : column = ⟨6, by decide⟩ := Fin.ext h6
    subst column
    exact slotValues6 index

  by_cases h7 : column.val = 7
  · have same : column = ⟨7, by decide⟩ := Fin.ext h7
    subst column
    exact slotValues7 index

  have same : column = ⟨8, by decide⟩ := by
    apply Fin.ext
    change column.val = 8
    have bound := column.isLt
    omega
  subst column
  exact slotValues8 index

private theorem source_tail_get {artifact : Artifact}
    (parsed : parse SourceCaptureTheta.source = .ok artifact) (index : Fin 242) (column : Fin 9) :
    signedValue ((((SourceCaptureTheta.columns[column.val]?).getD ⟨#[]⟩).get?
      (589824 + index.val)).getD 0) =
      if early : index.val < 121 then
        (Airbender.Keccak.Split.Native.Fixed.thetaRhoControl.row ⟨index.val, by change index.val < 121; exact early⟩)[column.val]
      else (Airbender.Keccak.Split.Native.Fixed.thetaRhoSlots.row ⟨index.val - 121, by change index.val - 121 < 121; omega⟩)[column.val] := by
  change signedValue (((sourceColumn column).get? (589824 + index.val)).getD 0) = _
  have lower : 4194304 - (((sourceColumn column).blocks.toList.drop (tailSkip column)).map Block.length).sum ≤
      589824 + index.val := by
    rw [source_suffix, tail_length]
    have cut := tail_cut column
    omega
  have selected := column_suffix_get (sourceColumn column) (tailSkip column) 4194304
    (589824 + index.val) (source_covered parsed column) lower
  rw [source_suffix, tail_length] at selected
  rw [selected]
  split_ifs with early
  · simp only [TableData.row, Vector.getElem_map]
    change _ = signedValue ((Airbender.Keccak.Split.Native.Fixed.thetaRhoControl.columns[column.val].get? (0 + index.val)).getD 0)
    simpa only [Nat.zero_add] using controller_values ⟨index.val, early⟩ column
  · have late : index.val - 121 < 121 := by omega
    have position : 589945 + (index.val - 121) = 589824 + index.val := by omega
    simp only [TableData.row, Vector.getElem_map]
    change _ = signedValue ((Airbender.Keccak.Split.Native.Fixed.thetaRhoSlots.columns[column.val].get? (0 + (index.val - 121))).getD 0)
    simpa only [Nat.zero_add, position] using slot_values ⟨index.val - 121, late⟩ column

/-- The complete source controller and slot rows equal their physical reference rows. -/
theorem source_control_slot_rows {artifact : Artifact}
    (parsed : parse SourceCaptureTheta.source = .ok artifact) (index : Fin 242) :
    (Vector.ofFn fun column : Fin 9 => signedValue
      ((((SourceCaptureTheta.columns[column.val]?).getD ⟨#[]⟩).get? (589824 + index.val)).getD 0)) =
      Airbender.Keccak.Split.Native.Fixed.thetaRhoPhysicalGenericRow ⟨589824 + index.val, by
        change 589824 + index.val < 4194304
        have bound := index.isLt
        omega⟩ := by
  have first : ¬ 589824 + index.val < 65536 := by omega
  have second : ¬ 589824 + index.val < 589824 := by omega
  have final : 589824 + index.val < 590066 := by have bound := index.isLt; omega
  by_cases early : index.val < 121
  · have controller : 589824 + index.val < 589945 := by omega
    simp only [Airbender.Keccak.Split.Native.Fixed.thetaRhoPhysicalGenericRow,
      dif_neg first, dif_neg second, dif_pos controller]
    apply Vector.ext
    intro column bound
    simp only [Vector.getElem_ofFn]
    have value := source_tail_get parsed index ⟨column, bound⟩
    rw [dif_pos early] at value
    simpa only [Fin.getElem_fin, Nat.add_sub_cancel_left] using value
  · have controller : ¬ 589824 + index.val < 589945 := by omega
    simp only [Airbender.Keccak.Split.Native.Fixed.thetaRhoPhysicalGenericRow,
      dif_neg first, dif_neg second, dif_neg controller, dif_pos final]
    apply Vector.ext
    intro column bound
    simp only [Vector.getElem_ofFn]
    have value := source_tail_get parsed index ⟨column, bound⟩
    rw [dif_neg early] at value
    have position : 589824 + index.val - 589945 = index.val - 121 := by omega
    simpa only [Fin.getElem_fin, position] using value

end Airbender.Setup.SourceCaptureThetaProofs

namespace Airbender.Compiler.MachineTargets.Proofs
open Airbender.Setup
set_option warningAsError true
set_option Elab.async false

/-- Canonical source membership is proved for both theta/rho control regions. -/
theorem theta_source_control_slot_member [Fact babyBearModulus.Prime] {artifact : Artifact}
    (parsed : parse SourceCaptureTheta.source = .ok artifact) (_shape : artifact.columns.size = 9)
    (index : Fin artifact.trace_len) (lower : 589824 ≤ index.val) (upper : index.val < 590066)
    (row : Vector F 9)
    (values : ∀ column : Fin 9,
      row[column] = (signedValue
        ((((artifact.columns[column.val]?).getD ⟨#[]⟩).get? index.val).getD 0) : F)) :
    Keccak.Split.Native.Fixed.thetaRhoPhysicalGenericTable.toRaw.Contains #[] row := by
  have decoded := fields_of_parse SourceCaptureThetaProofs.parsed parsed
  have sameColumns : artifact.columns = SourceCaptureTheta.columns :=
    Except.ok.inj (decoded.2.symm.trans SourceCaptureThetaProofs.columns_decoded)
  have sameRow : row = (Vector.ofFn (fun column : Fin 9 =>
      signedValue ((((SourceCaptureTheta.columns[column.val]?).getD ⟨#[]⟩).get? index.val).getD 0))).map
      (fun value : Int => (value : F)) := by
    apply Vector.ext
    intro column bound
    simpa only [Vector.getElem_map, Vector.getElem_ofFn, Fin.getElem_fin, sameColumns] using values ⟨column, bound⟩
  change ∃ nativeIndex : Fin Keccak.Split.Native.Fixed.thetaRhoPhysicalGenericLength,
    row = (Keccak.Split.Native.Fixed.thetaRhoPhysicalGenericRow nativeIndex).map (fun value : Int => (value : F))
  refine ⟨⟨index.val, by change index.val < 4194304; omega⟩, ?_⟩
  rw [sameRow]
  let localIndex : Fin 242 := ⟨index.val - 589824, by omega⟩
  have position : 589824 + localIndex.val = index.val := by dsimp [localIndex]; omega
  have reference := congrArg (fun actual : Vector Int 9 => actual.map (fun value : Int => (value : F)))
    (SourceCaptureThetaProofs.source_control_slot_rows parsed localIndex)
  simpa only [position] using reference

end Airbender.Compiler.MachineTargets.Proofs
