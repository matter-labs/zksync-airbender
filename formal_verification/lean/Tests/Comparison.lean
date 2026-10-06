import Airbender.Review.JumpBranchSlt.Theorems

namespace Tests.Comparison
open Airbender

/-- A selected SLTU row with zero operands and correct lookup results, but an
    unbounded final-PC high limb. This is a local-interface counterexample, not a
    claim that the full decoder/ROM/execution arguments accept the row. -/
private def row : Nat → ZMod babyBearModulus
  | 4 | 7 | 13 | 40 | 41 => 1
  | 10 => 3
  | 16 | 18 | 36 => 4
  | 17 => 2013200385
  | _ => 0

theorem unboundedFinalPCSatisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment row)
      JumpBranchSlt.importedConstraints := by
  simp [JumpBranchSlt.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Expression.eval, Verification.environment, row]
  repeat' apply And.intro
  all_goals first
    | (apply Verification.range16_contains; decide)
    | (with_unfolding_all change ∃ i : Fin 131072,
         ((0, 1) : fieldPair (ZMod babyBearModulus)) = ((i.val : ZMod babyBearModulus), ((if i.val = 0 then 1 else 0 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨0, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 65536,
         ((0, 0) : fieldPair (ZMod babyBearModulus)) = ((i.val : ZMod babyBearModulus), ((i.val / 32768 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨0, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 4194304,
         ((1835008, 0) : fieldPair (ZMod babyBearModulus)) = ((i.val : ZMod babyBearModulus), (Verification.conditionalValue i.val : ZMod babyBearModulus))
       exact ⟨⟨1835008, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 65536,
         ((4, 0, 4) : fieldTriple (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((i.val / 2 % 2 : Nat) : ZMod babyBearModulus), ((i.val - i.val % 4 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨4, by decide⟩, rfl⟩)
    | decide

example : ¬ ((⟨4, (row 17).val⟩ : Arithmetic.Word).toBitVec =
    (⟨0, 0⟩ : Arithmetic.Word).toBitVec + 4) := by decide

private def edgeRow : Nat → ZMod babyBearModulus
  | 4 | 7 | 13 | 30 | 34 | 37 | 38 | 44 | 47 => 1
  | 10 => 3
  | 16 | 18 | 36 => 4
  | 26 | 27 | 43 => 65535
  | _ => 0

private theorem edgeSatisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment edgeRow)
      JumpBranchSlt.importedConstraints := by
  simp [JumpBranchSlt.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Expression.eval, Verification.environment, edgeRow]
  repeat' apply And.intro
  all_goals first
    | (apply Verification.range16_contains; decide)
    | (with_unfolding_all change ∃ i : Fin 131072,
         ((1, 0) : fieldPair (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((if i.val = 0 then 1 else 0 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨1, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 65536,
         ((0, 0) : fieldPair (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((i.val / 32768 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨0, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 4194304,
         ((1769471, 1) : fieldPair (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), (Verification.conditionalValue i.val : ZMod babyBearModulus))
       exact ⟨⟨1769471, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 65536,
         ((4, 0, 4) : fieldTriple (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((i.val / 2 % 2 : Nat) : ZMod babyBearModulus),
             ((i.val - i.val % 4 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨4, by decide⟩, rfl⟩)
    | decide

/-- Unsigned 0 < 0xffffffff requires both subtraction borrows and resolves to one. -/
example : (⟨(edgeRow 30).val, (edgeRow 31).val⟩ : Arithmetic.Word).value = 1 := by
  have result := JumpBranchSlt.unsigned_destination (p := babyBearModulus) (by decide)
    (left := ⟨0, 0⟩) (right := ⟨65535, 65535⟩) edgeSatisfies
    rfl ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl⟩ rfl rfl ⟨rfl, rfl, rfl, rfl⟩
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
  simpa [Arithmetic.Word.value, Arithmetic.limbBase] using result

end Tests.Comparison
