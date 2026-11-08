module
public import Slop.Trace.RVValues
public import Slop.JumpBranchSlt.RVDecoder
public import Slop.JumpBranchSlt.Branch
public import Slop.JumpBranchSlt.Jump
public import Slop.JumpBranchSlt.Trace

@[expose] public section

/-! JumpBranchSlt row facts of the RV value-bounds law (`RVValuesPooled`): destination bounds and write sources
    from the RV projection equation. -/

namespace Airbender.JumpBranchSlt.Proofs
open Arithmetic Trace

private theorem rv_comparison_destination_bounds {p : Nat} [Fact p.Prime]
    (hp : 4194304 ≤ p) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 11 = 0 ∧ w 12 = 0 ∧ w 13 = 1 ∧ w 15 = 0) :
    (⟨(w 30).val, (w 31).val⟩ : Word).Bounded := by
  obtain ⟨jal, jalr, comparison, mask⟩ := selected
  have low := Verification.assertion_of_holds h
    ⟨8, by simp [importedConstraints, FlatOperation.constraints]⟩
  have high := Verification.assertion_of_holds h
    ⟨9, by simp [importedConstraints, FlatOperation.constraints]⟩
  have outputLow := Verification.assertion_of_holds h
    ⟨10, by simp [importedConstraints, FlatOperation.constraints]⟩
  have outputHigh := Verification.assertion_of_holds h
    ⟨11, by simp [importedConstraints, FlatOperation.constraints]⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, jal, jalr, comparison] at low high
  have lo : w 47 = w 44 := by linear_combination -low
  have hi : w 48 = 0 := high
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, mask, lo, hi] at outputLow outputHigh
  have written : w 30 = w 44 := by linear_combination -outputLow
  have resolved := (lookup_values hp h).2.2.1
  rw [show w 31 = 0 by exact outputHigh, written, resolved]
  constructor
  · have bounded (bit : Bool) :
        (((if bit then 1 else 0 : Nat) : ZMod p)).val < limbBase := by
      cases bit <;> simp [limbBase, ZMod.val_one'' (by omega : p ≠ 1)]
    exact bounded _
  · simp [limbBase]

/-- `destination_bounds` with the Sail `Fetched` replaced by the projection equation and the selector facts. -/
theorem rv_destination_bounds {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    {i : RV.Instr} {data : DecoderData Unit}
    (fields : rvDecoderFields i = some data)
    (flags : ∀ i : Fin 5,
      w importedConstraintsDecoderColumns.flags[i] = if data.mask.testBit i.val then 1 else 0)
    (initialLo : (w 0).val < limbBase) :
    (⟨(w 30).val, (w 31).val⟩ : Word).Bounded := by
  have f0 := flags ⟨0, by decide⟩
  have f1 := flags ⟨1, by decide⟩
  have f2 := flags ⟨2, by decide⟩
  have f3 := flags ⟨3, by decide⟩
  have f4 := flags ⟨4, by decide⟩
  rcases rv_decoder_masks fields with m | m | m | m | m | m
  all_goals simp [importedConstraintsDecoderColumns, m, Nat.testBit] at f0 f1 f2 f3 f4
  · exact (jump_link hp (initial := ⟨(w 0).val, (w 1).val⟩) h
      (by simp [f0, f1]) ⟨f2, f3⟩ ⟨rfl, rfl⟩ initialLo).2
  · exact (jump_link hp (initial := ⟨(w 0).val, (w 1).val⟩) h
      (by simp [f0, f1]) ⟨f2, f3⟩ ⟨rfl, rfl⟩ initialLo).2
  · exact rv_comparison_destination_bounds hp h ⟨f0, f1, f2, f4⟩
  all_goals
    obtain ⟨low, high⟩ := masked_destination h f4
    simp [low, high, Word.Bounded, limbBase]

/-- `row_write_sources` with the Sail `Fetched` replaced by the projection equation and the selector facts. -/
theorem rv_row_write_sources {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    (row : Row p TraceKind)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) importedConstraints)
    {i : RV.Instr} {data : DecoderData Unit}
    (fields : rvDecoderFields i = some data)
    (flags : ∀ i : Fin 5, row.assignment importedConstraintsDecoderColumns.flags[i] =
      if data.mask.testBit i.val then 1 else 0)
    (initialLo : (row.assignment 0).val < limbBase) : Trace.Proofs.RowWriteSources row := by
  intro port present
  simp [Row.ports, importedConstraintsMemoryPorts] at present
  rcases present with rfl | rfl | rfl
  · exact Or.inr ⟨_, by simp [Row.ports, importedConstraintsMemoryPorts], rfl, le_rfl⟩
  · exact Or.inr ⟨_, by simp [Row.ports, importedConstraintsMemoryPorts], rfl, le_rfl⟩
  · left
    simpa [Trace.Proofs.write_word, importedConstraintsMemoryPorts] using
      rv_destination_bounds hp h fields flags initialLo

end Airbender.JumpBranchSlt.Proofs
