import GKRProtocol.TaggedSetup

namespace Airbender.Compiler
set_option warningAsError true

/-- Native tag encodings may keep the initial disabled zero row as a dense
block. The remaining constant segments retain their literal physical extent. -/
theorem dense_zero_tag (segments : List (Nat × Nat)) (index : Nat) :
    (((Airbender.Setup.getFromBlocks
      (.dense #[0] :: segments.map (fun entry => Airbender.Setup.Block.affine entry.1 entry.2 0)) index).getD 0) : Source.BaseField) =
      if index < 1 then 0 else constantTagValue segments (index - 1) := by
  by_cases leading : index < 1
  · have zero : index = 0 := by omega
    subst index
    rfl
  · simp only [Airbender.Setup.getFromBlocks, Airbender.Setup.Block.length,
      show (#[0] : Array Nat).size = 1 from rfl, if_neg leading]
    exact constant_tag_blocks segments (index - 1)


theorem constant_tag_skip (length value : Nat) (rest : List (Nat × Nat))
    (index : Nat) (expected : Source.BaseField)
    (different : (value : Source.BaseField) ≠ expected)
    (selected : constantTagValue ((length, value) :: rest) index = expected) :
    length ≤ index ∧ constantTagValue rest (index - length) = expected := by
  by_cases inside : index < length
  · change (if index < length then _ else _) = _ at selected
    rw [if_pos inside] at selected
    exact False.elim (different selected)
  · refine ⟨by omega, ?_⟩
    change (if index < length then _ else _) = expected at selected
    rw [if_neg inside] at selected
    exact selected

theorem constant_tag_avoids (segments : List (Nat × Nat)) (expected : Source.BaseField)
    (zero : (0 : Source.BaseField) ≠ expected)
    (different : segments.all (fun entry => decide ((entry.2 : Source.BaseField) ≠ expected)) = true)
    (index : Nat) : constantTagValue segments index ≠ expected := by
  induction segments generalizing index with
  | nil => exact zero
  | cons entry rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at different
    have head : (entry.2 : Source.BaseField) ≠ expected := of_decide_eq_true different.1
    change (if index < entry.1 then _ else _) ≠ expected
    by_cases inside : index < entry.1
    · rw [if_pos inside]
      exact head
    · rw [if_neg inside]
      exact ih different.2 _

theorem constant_tag_head_bounded (length value : Nat) (rest : List (Nat × Nat))
    (index : Nat) (expected : Source.BaseField)
    (zero : (0 : Source.BaseField) ≠ expected)
    (different : rest.all (fun entry => decide ((entry.2 : Source.BaseField) ≠ expected)) = true)
    (selected : constantTagValue ((length, value) :: rest) index = expected) : index < length := by
  by_contra outside
  change (if index < length then _ else _) = expected at selected
  rw [if_neg outside] at selected
  exact constant_tag_avoids rest expected zero different _ selected

end Airbender.Compiler
