import Airbender.Proofs.FullUnsigned.ChiControllerSuffixes
import Airbender.Proofs.FullUnsigned.SourceColumnRanges
import Airbender.Proofs.FullUnsigned.SourceColumnCoverage
import Airbender.Proofs.Keccak.SplitChiControlRegion

namespace Airbender.Setup.SourceCaptureChiProofs
open Airbender.Setup.Proofs
open Lean
set_option warningAsError true
set_option Elab.async false
-- The controller slice has 121 rows. Each retained suffix has at most 122 blocks.
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private noncomputable def sourceColumn (column : Fin 11) : Column :=
  (SourceCaptureChi.columns[column.val]?).getD ⟨#[]⟩

private noncomputable def sourceBinding (column : Fin 11) : SourceBank.ColumnBinding :=
  (SourceCaptureChi.columnBindings[column.val]'(by change column.val < 11; exact column.isLt)).1

private noncomputable def sourceEntries (column : Fin 11) : List Nat :=
  match column.val with
  | 0 => SourceCaptureChi.entries_2452
  | 1 => SourceCaptureChi.entries_2458
  | 2 => SourceCaptureChi.entries_2579
  | 3 => SourceCaptureChi.entries_2619
  | 4 => SourceCaptureChi.entries_2645
  | 5 => SourceCaptureChi.entries_2715
  | 6 => SourceCaptureChi.entries_2804
  | 7 => SourceCaptureChi.entries_2871
  | 8 => SourceCaptureChi.entries_3333
  | 9 => SourceCaptureChi.entries_3369
  | _ => SourceCaptureChi.entries_3373

private noncomputable def controllerEntries (column : Fin 11) : List Nat :=
  match column.val with
  | 0 => ChiControllerSuffix.Column0.entries
  | 1 => ChiControllerSuffix.Column1.entries
  | 2 => ChiControllerSuffix.Column2.entries
  | 3 => ChiControllerSuffix.Column3.entries
  | 4 => ChiControllerSuffix.Column4.entries
  | 5 => ChiControllerSuffix.Column5.entries
  | 6 => ChiControllerSuffix.Column6.entries
  | 7 => ChiControllerSuffix.Column7.entries
  | 8 => ChiControllerSuffix.Column8.entries
  | 9 => ChiControllerSuffix.Column9.entries
  | _ => ChiControllerSuffix.Column10.entries

private noncomputable def controllerSkip (column : Fin 11) : Nat :=
  match column.val with
  | 0 => ChiControllerSuffix.Column0.skip
  | 1 => ChiControllerSuffix.Column1.skip
  | 2 => ChiControllerSuffix.Column2.skip
  | 3 => ChiControllerSuffix.Column3.skip
  | 4 => ChiControllerSuffix.Column4.skip
  | 5 => ChiControllerSuffix.Column5.skip
  | 6 => ChiControllerSuffix.Column6.skip
  | 7 => ChiControllerSuffix.Column7.skip
  | 8 => ChiControllerSuffix.Column8.skip
  | 9 => ChiControllerSuffix.Column9.skip
  | _ => ChiControllerSuffix.Column10.skip

private noncomputable def controllerLength (column : Fin 11) : Nat :=
  match column.val with
  | 0 => 4194304
  | 1 => 4194304
  | 2 => 3440640
  | 3 => 3584000
  | 4 => 4194304
  | 5 => 3147176
  | 6 => 3155424
  | 7 => 3300864
  | 8 => 3538944
  | 9 => 4194304
  | _ => 4194304

private noncomputable def controllerBlocks (column : Fin 11) : List Block :=
  (controllerEntries column).map (sourceBinding column).blocks

private theorem source_column_binding (column : Fin 11) :
    sourceColumn column = (sourceBinding column).column := by
  fin_cases column <;> simp only [sourceBinding, SourceCaptureChi.columnBindings, List.getElem_cons_zero, List.getElem_cons_succ] <;> rfl


private theorem binding_entries_of_literal (binding : SourceBank.ColumnBinding)
    (index key array : Nat) (children : Nat → Nat) (blocks : Nat → Block) (entries : List Nat)
    (same : binding = ⟨index, key, array, children, blocks, entries⟩) :
    binding.entries = entries := by
  cases same
  rfl

/-- Read the record before projecting its long index list. All proposed
record values and the resulting theorem enter the kernel. -/
elab "source_record_entries" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target ← goal.getType
  unless target.isAppOf ``Eq do throwError "expected source entries equality"
  let left := target.getAppArgs[1]!
  let binding ← match left with
    | .proj _ 5 binding => pure binding
    | _ =>
      unless left.isAppOf ``SourceBank.ColumnBinding.entries do
        throwError "expected source binding entries"
      pure left.getAppArgs[0]!
  let body ← Lean.Meta.withTransparency .all <| Lean.Meta.whnf binding
  unless body.isAppOf ``SourceBank.ColumnBinding.mk do throwError "expected source binding record"
  let same ← Lean.Meta.mkEqRefl binding
  let proof := mkAppN (mkConst ``binding_entries_of_literal) (#[binding] ++ body.getAppArgs ++ #[same])
  goal.assign proof
  Lean.Elab.Tactic.replaceMainGoal []

private theorem binding_entries (column : Fin 11) :
    (sourceBinding column).entries = sourceEntries column := by
  fin_cases column <;> simp only [sourceBinding, SourceCaptureChi.columnBindings, List.getElem_cons_zero, List.getElem_cons_succ, sourceEntries] <;> source_record_entries


private theorem controller_suffix (column : Fin 11) :
    (sourceColumn column).blocks.toList.drop (controllerSkip column) = controllerBlocks column := by
  rw [source_column_binding]
  simp only [SourceBank.ColumnBinding.column, List.toList_toArray, ← List.map_drop]
  unfold controllerBlocks
  apply congrArg (fun entries : List Nat => entries.map (sourceBinding column).blocks)
  rw [binding_entries]
  fin_cases column
  · simpa only [sourceEntries, controllerSkip, controllerEntries] using ChiControllerSuffix.Column0.matches
  · simpa only [sourceEntries, controllerSkip, controllerEntries] using ChiControllerSuffix.Column1.matches
  · simpa only [sourceEntries, controllerSkip, controllerEntries] using ChiControllerSuffix.Column2.matches
  · simpa only [sourceEntries, controllerSkip, controllerEntries] using ChiControllerSuffix.Column3.matches
  · simpa only [sourceEntries, controllerSkip, controllerEntries] using ChiControllerSuffix.Column4.matches
  · simpa only [sourceEntries, controllerSkip, controllerEntries] using ChiControllerSuffix.Column5.matches
  · simpa only [sourceEntries, controllerSkip, controllerEntries] using ChiControllerSuffix.Column6.matches
  · simpa only [sourceEntries, controllerSkip, controllerEntries] using ChiControllerSuffix.Column7.matches
  · simpa only [sourceEntries, controllerSkip, controllerEntries] using ChiControllerSuffix.Column8.matches
  · simpa only [sourceEntries, controllerSkip, controllerEntries] using ChiControllerSuffix.Column9.matches
  · simpa only [sourceEntries, controllerSkip, controllerEntries] using ChiControllerSuffix.Column10.matches


private theorem controller_length (column : Fin 11) :
    ((controllerBlocks column).map Block.length).sum = controllerLength column := by
  fin_cases column <;> setup_source_rfl


private theorem controller_cut : ∀ column : Fin 11, 4194304 - controllerLength column ≤ 1048576 := by
  decide +kernel

private theorem source_covered {artifact : Artifact} (parsed : parse SourceCaptureChi.source = .ok artifact)
    (column : Fin 11) : ((sourceColumn column).blocks.toList.map Block.length).sum = 4194304 := by
  have bound : column.val < SourceCaptureChi.columns.size := by
    change column.val < 11
    exact column.isLt
  have member : sourceColumn column ∈ SourceCaptureChi.columns := by
    unfold sourceColumn
    rw [Array.getElem?_eq_getElem bound, Option.getD_some]
    simp
  exact source_column_lengths SourceCaptureChiProofs.parsed trace_len_decoded columns_decoded parsed _ member

-- Keep each closed computation within one controller column during kernel replay.

private def controllerValueCorrect (index : Fin 121) (column : Fin 11) : Prop :=
    signedValue ((getFromBlocks (controllerBlocks column)
      (1048576 + index.val - (4194304 - controllerLength column))).getD 0) =
      signedValue ((Airbender.Keccak.Split.Native.Fixed.chi5Control.columns[column.val].get? index.val).getD 0)

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

private theorem controllerValues9 : ∀ index : Fin 121,
    controllerValueCorrect index ⟨9, by decide⟩ := by
  unfold controllerValueCorrect
  decide +kernel

private theorem controllerValues10 : ∀ index : Fin 121,
    controllerValueCorrect index ⟨10, by decide⟩ := by
  unfold controllerValueCorrect
  decide +kernel

private theorem controller_values : ∀ index : Fin 121, ∀ column : Fin 11,
    signedValue ((getFromBlocks (controllerBlocks column)
      (1048576 + index.val - (4194304 - controllerLength column))).getD 0) =
      signedValue ((Airbender.Keccak.Split.Native.Fixed.chi5Control.columns[column.val].get? index.val).getD 0) := by
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

  by_cases h8 : column.val = 8
  · have same : column = ⟨8, by decide⟩ := Fin.ext h8
    subst column
    exact controllerValues8 index

  by_cases h9 : column.val = 9
  · have same : column = ⟨9, by decide⟩ := Fin.ext h9
    subst column
    exact controllerValues9 index

  have same : column = ⟨10, by decide⟩ := by
    apply Fin.ext
    change column.val = 10
    have bound := column.isLt
    omega
  subst column
  exact controllerValues10 index

/-- Every parsed source controller field equals its original native reference. -/
theorem source_controller_get {artifact : Artifact}
    (parsed : parse SourceCaptureChi.source = .ok artifact) (index : Fin 121) (column : Fin 11) :
    signedValue ((((SourceCaptureChi.columns[column.val]?).getD ⟨#[]⟩).get?
      (1048576 + index.val)).getD 0) =
      (Airbender.Keccak.Split.Native.Fixed.chi5Control.row ⟨index.val, index.isLt⟩)[column.val] := by
  change signedValue (((sourceColumn column).get? (1048576 + index.val)).getD 0) = _
  have lower : 4194304 - (((sourceColumn column).blocks.toList.drop (controllerSkip column)).map Block.length).sum ≤
      1048576 + index.val := by
    rw [controller_suffix, controller_length]
    have cut := controller_cut column
    omega
  have selected := column_suffix_get (sourceColumn column) (controllerSkip column) 4194304
    (1048576 + index.val) (source_covered parsed column) lower
  rw [controller_suffix, controller_length] at selected
  rw [selected]
  have values := controller_values index column
  simp only [TableData.row, Vector.getElem_map]
  change _ = signedValue ((Airbender.Keccak.Split.Native.Fixed.chi5Control.columns[column.val].get?
    (0 + index.val)).getD 0)
  simpa only [Nat.zero_add] using values

/-- The complete parsed controller row equals its row in the original
canonical generic table. The original parse premise supplies coverage. -/
theorem source_controller_rows {artifact : Artifact}
    (parsed : parse SourceCaptureChi.source = .ok artifact) (index : Fin 121) :
    (Vector.ofFn fun column : Fin 11 =>
      signedValue ((((SourceCaptureChi.columns[column.val]?).getD ⟨#[]⟩).get?
        (1048576 + index.val)).getD 0)) =
      Airbender.Keccak.Split.Native.Fixed.chi5Generic.row ⟨1048576 + index.val, by
        have bound := index.isLt
        change 1048576 + index.val < 1048697
        omega⟩ := by
  have native := Airbender.Keccak.Split.Native.Fixed.Proofs.chi5_controller_rows_equal
    (⟨index.val, index.isLt⟩ : Fin Airbender.Keccak.Split.Native.Fixed.chi5Control.length)
  refine Eq.trans ?_ native.symm
  apply Vector.ext
  intro column bound
  simpa only [Vector.getElem_ofFn, Fin.getElem_fin] using source_controller_get parsed index ⟨column, bound⟩

end Airbender.Setup.SourceCaptureChiProofs

namespace Airbender.Compiler.MachineTargets.Proofs
open Airbender.Setup
set_option warningAsError true
set_option Elab.async false

/-- The original parsed-source premise supplies canonical membership for
all chi5 controller rows. The complete row values stay explicit. -/
theorem chi_source_controller_member [Fact babyBearModulus.Prime] {artifact : Artifact}
    (parsed : parse SourceCaptureChi.source = .ok artifact) (_shape : artifact.columns.size = 11)
    (index : Fin artifact.trace_len) (lower : 1048576 ≤ index.val) (upper : index.val < 1048697)
    (row : Vector F 11)
    (values : ∀ column : Fin 11,
      row[column] = (signedValue
        ((((artifact.columns[column.val]?).getD ⟨#[]⟩).get? index.val).getD 0) : F)) :
    (Keccak.Split.Native.Fixed.chi5Generic.table "Airbender.SplitChi5Generic").toRaw.Contains #[] row := by
  let localIndex : Fin 121 := ⟨index.val - 1048576, by omega⟩
  have globalIndex : 1048576 + localIndex.val = index.val := by dsimp [localIndex]; omega
  have decoded := fields_of_parse SourceCaptureChiProofs.parsed parsed
  have sameColumns : artifact.columns = SourceCaptureChi.columns :=
    Except.ok.inj (decoded.2.symm.trans SourceCaptureChiProofs.columns_decoded)
  have sameRow : row = (Vector.ofFn (fun column : Fin 11 =>
      signedValue ((((SourceCaptureChi.columns[column.val]?).getD ⟨#[]⟩).get? index.val).getD 0))).map
      (fun value : Int => (value : F)) := by
    apply Vector.ext
    intro column bound
    simpa only [Vector.getElem_map, Vector.getElem_ofFn, Fin.getElem_fin, sameColumns]
      using values ⟨column, bound⟩
  change ∃ nativeIndex : Fin Keccak.Split.Native.Fixed.chi5Generic.length,
    row = (Keccak.Split.Native.Fixed.chi5Generic.row nativeIndex).map (fun value : Int => (value : F))
  refine ⟨⟨index.val, upper⟩, ?_⟩
  rw [sameRow]
  have reference := congrArg (fun actual : Vector Int 11 => actual.map (fun value : Int => (value : F)))
    (SourceCaptureChiProofs.source_controller_rows parsed localIndex)
  simpa only [globalIndex] using reference

end Airbender.Compiler.MachineTargets.Proofs
