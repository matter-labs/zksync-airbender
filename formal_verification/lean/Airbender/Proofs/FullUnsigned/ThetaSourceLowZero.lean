import Airbender.Proofs.FullUnsigned.SourceBlockWindows
import Airbender.Proofs.FullUnsigned.ThetaSourceXorOutput
import Airbender.Proofs.FullUnsigned.ThetaLowZeroIndices
import Airbender.Proofs.FullUnsigned.SourceBlockAgreement

namespace Airbender.Setup.SourceCaptureThetaProofs
open Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
-- Only the two leading blocks differ from the proved byte-XOR source column.
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

/-- Propose reflexivity without elaborator normalization. The ordinary
kernel conversion check must accept the complete theorem term. -/
elab "low_source_kernel_rfl" : tactic => do
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let type ← goal.getType
    unless type.isAppOf ``Eq do throwError "expected equality"
    let proof ← Lean.Meta.mkEqRefl type.getAppArgs[1]!
    goal.assign proof
    Lean.Elab.Tactic.replaceMainGoal []

private noncomputable def lowColumn : Column := (SourceCaptureTheta.columns[3]?).getD ⟨#[]⟩
private noncomputable def byteColumn : Column := (SourceCaptureTheta.columns[2]?).getD ⟨#[]⟩
private noncomputable def lowBinding : SourceBank.ColumnBinding :=
  (SourceCaptureTheta.columnBindings[3]'(by change 3 < 9; decide +kernel)).1
private noncomputable def byteBinding : SourceBank.ColumnBinding :=
  (SourceCaptureTheta.columnBindings[2]'(by change 2 < 9; decide +kernel)).1
private noncomputable def lowBody : List Block := (lowColumn.blocks.toList.drop 2).take 897
private noncomputable def byteBody : List Block := (byteColumn.blocks.toList.drop 1).take 897

private theorem first_two : lowColumn.blocks.toList.take 2 =
    [.affine 65537 0 0, .affine 255 1 1] := by setup_source_rfl

private theorem low_offset : ((lowColumn.blocks.toList.take 2).map Block.length).sum = 65792 := by
  rw [first_two]
  rfl

private theorem byte_offset : ((byteColumn.blocks.toList.take 1).map Block.length).sum = 256 := by
  setup_source_rfl

private theorem low_column_binding : lowColumn = lowBinding.column := by
  simp only [lowBinding, SourceCaptureTheta.columnBindings, List.getElem_cons_zero, List.getElem_cons_succ]
  rfl

private theorem byte_column_binding : byteColumn = byteBinding.column := by
  simp only [byteBinding, SourceCaptureTheta.columnBindings, List.getElem_cons_zero, List.getElem_cons_succ]
  rfl

private theorem low_entries : lowBinding.entries = SourceCaptureTheta.entries_9296 := by
  simp only [lowBinding, SourceCaptureTheta.columnBindings, List.getElem_cons_zero, List.getElem_cons_succ]
  low_source_kernel_rfl

private theorem byte_entries : byteBinding.entries = SourceCaptureTheta.entries_8478 := by
  simp only [byteBinding, SourceCaptureTheta.columnBindings, List.getElem_cons_zero, List.getElem_cons_succ]
  low_source_kernel_rfl

private theorem map_window (ids : List Nat) (block : Nat → Block) (first count : Nat) :
    ((ids.map block).drop first).take count = ((ids.drop first).take count).map block := by
  rw [← List.map_drop, ← List.map_take]

private theorem body_nodes :
    ThetaLowZeroIndices.entries.map SourceCaptureTheta.select_9296 =
      ((SourceCaptureTheta.entries_8478.drop 1).take 897).map SourceCaptureTheta.select_8478 := by
  decide +kernel

/-- Reuse the existing checked source-decoder callbacks. The resulting term
applies the generic node-agreement theorem and enters the ordinary kernel. -/
elab "low_body_node_transport" : tactic => do
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let target ← goal.getType
    let sides := target.getAppArgs
    let left := sides[1]!.getAppArgs
    let right := sides[2]!.getAppArgs
    let moduleName := `Airbender.Proofs.FullUnsigned.Source.Theta
    let base := `Airbender.Setup.SourceCaptureThetaProofs
    let lname := Lean.mkPrivateNameCore moduleName (base.str "rle_blocks_9297")
    let rname := Lean.mkPrivateNameCore moduleName (base.str "rle_blocks_8479")
    let info ← Lean.getConstInfo lname
    let (context, ln) ← Lean.Meta.forallTelescope info.type fun _ body => do
      let fields := body.getAppArgs
      pure (fields.extract 0 4, fields[4]!.getAppFn)
    let other ← Lean.getConstInfo rname
    let rn ← Lean.Meta.forallTelescope other.type fun _ body => pure body.getAppArgs[4]!.getAppFn
    let proof := Lean.mkAppN (Lean.mkConst ``SourceDecoding.blocks_equal_of_nodes)
      (context ++ #[ln, rn, left[2]!, right[2]!, left[3]!, right[3]!,
        Lean.mkConst lname, Lean.mkConst rname, Lean.mkConst ``body_nodes])
    goal.assign proof
    Lean.Elab.Tactic.replaceMainGoal []

private theorem body_equal : lowBody = byteBody := by
  unfold lowBody byteBody
  conv_lhs => rw [low_column_binding]
  conv_rhs => rw [byte_column_binding]
  simp only [SourceBank.ColumnBinding.column, List.toList_toArray]
  conv_lhs => rw [map_window]
  conv_rhs => rw [map_window]
  conv_lhs => rw [low_entries, ThetaLowZeroIndices.source_slice]
  conv_rhs => rw [byte_entries]
  low_body_node_transport
private theorem body_length : (lowBody.map Block.length).sum = 65280 := by
  unfold lowBody
  rw [low_column_binding]
  simp only [SourceBank.ColumnBinding.column, List.toList_toArray]
  rw [map_window]
  rw [low_entries, ThetaLowZeroIndices.source_slice]
  low_source_kernel_rfl

private theorem leading_get (index : Fin 256) : lowColumn.get? (65536 + index.val) = some index.val := by
  change getFromBlocks _ (65536 + index.val) = _
  rw [getFromBlocks_take _ 2 _ (by rw [first_two]; change 65536 + index.val < 65792; omega), first_two]
  rw [getFromBlocks]
  by_cases zero : index.val = 0
  · simp only [zero]
    rw [if_pos (by change 65536 < 65537; decide +kernel)]
    exact constant_affine_get _ _ _ (by decide +kernel)
  · have outside : ¬ 65536 + index.val < (Block.affine 65537 0 0).length := by
      change ¬ 65536 + index.val < 65537
      omega
    have offset : 65536 + index.val - 65537 = index.val - 1 := by omega
    rw [if_neg outside]
    simp only [Block.length]
    rw [offset, getFromBlocks]
    have inside : index.val - 1 < (Block.affine 255 1 1).length := by
      change index.val - 1 < 255
      have bound := index.isLt
      omega
    rw [if_pos inside]
    simp only [Block.get?, if_pos inside, Int.natCast_one]
    have value : (1 : Int) + 1 * (index.val - 1 : Nat) = (index.val : Int) := by omega
    rw [value, if_pos (Int.natCast_nonneg _), Int.toNat_natCast]

/-- The zero-shift source fragment reuses the complete proved byte-XOR column. -/
theorem source_split_low_zero_get (index : Fin 65536) :
    ((SourceCaptureTheta.columns[3]?).getD ({ blocks := #[] } : Column)).get? (65536 + index.val) =
      some ((index.val / 256 % 256) ^^^ (index.val % 256)) := by
  change lowColumn.get? (65536 + index.val) = _
  by_cases early : index.val < 256
  · have selected := leading_get ⟨index.val, early⟩
    have high : index.val / 256 % 256 = 0 := by omega
    have low : index.val % 256 = index.val := Nat.mod_eq_of_lt early
    simpa only [high, low, Nat.zero_xor] using selected
  · have lower : 256 ≤ index.val := by omega
    have inside : index.val - 256 < (lowBody.map Block.length).sum := by
      rw [body_length]
      have upper := index.isLt
      omega
    have source := getFromBlocks_window lowColumn.blocks.toList 2 897 65792 (index.val - 256) low_offset inside
    have native := getFromBlocks_window byteColumn.blocks.toList 1 897 256 (index.val - 256) byte_offset
      (by change index.val - 256 < (byteBody.map Block.length).sum; rw [← body_equal]; exact inside)
    have sourcePosition : 65792 + (index.val - 256) = 65536 + index.val := by omega
    have bytePosition : 256 + (index.val - 256) = index.val := by omega
    change lowColumn.get? _ = getFromBlocks lowBody _ at source
    change byteColumn.get? _ = getFromBlocks byteBody _ at native
    rw [sourcePosition, body_equal] at source
    rw [bytePosition] at native
    exact (source.trans native.symm).trans (source_xor_output_get index)

end Airbender.Setup.SourceCaptureThetaProofs
