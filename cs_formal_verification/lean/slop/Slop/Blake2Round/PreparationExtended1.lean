module
public import Slop.Blake2Round.PreparationBase
public import Slop.Blake2Round.ArtifactChecks
public import Slop.Blake2Round.OpIndex
public import Slop.Constraints
public import Mathlib.Tactic.LinearCombination
public import Slop.CleanCore.Circuit.Operations
public import Slop.Defs.Circuits.Blake2Round.Artifact
public import Slop.Defs.Circuits.Blake2Round.Preparation

@[expose] public section

namespace Airbender.Blake2Round.Preparation.Proofs
open Arithmetic

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- The `extended` output words 4..8 (indices 4 to 8). Per-word proof, split out of
`extended` so each range builds in its own module. -/
theorem extended_eqs_1 {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 6)}
    {w : Nat → ZMod p} (first compression : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (firstFlag : w 142 = if first then 1 else 0)
    (compressionFlag : w 141 = if compression then 1 else 0)
    (normalFlag : w 153 = (if first then 1 else 0) * (1 - if compression then 1 else 0))
    (i : Fin 16) (lowerIndex : 4 ≤ i.val) (upperIndex : i.val < 8) :
    w Variables.preparedState[i].1 = ((extendedExpected first compression w)[i].lo : ZMod p) ∧
      w Variables.preparedState[i].2 = ((extendedExpected first compression w)[i].hi : ZMod p) := by
  have lo := Verification.assertion_of_holds h ⟨loIdx[i],
    by rw [constraint_count]; exact loIdx_lt i⟩
  have high := Verification.assertion_of_holds h ⟨hiIdx[i],
    by rw [constraint_count]; exact hiIdx_lt i⟩
  fin_cases i <;> try (simp at lowerIndex upperIndex; done)
  all_goals simp only [loIdx, hiIdx, Fin.getElem_fin, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ] at lo high
  all_goals op_index at lo high
  all_goals simp [Expression.eval, Verification.environment] at lo high
  all_goals cases first <;> cases compression
  all_goals simp only [extendedExpected, Bool.false_eq_true, ↓reduceIte]
  all_goals simp only [Fin.getElem_fin, get_append8]
  all_goals simp [firstFlag, words,
    Variables.preparedState, Variables.chainingInputs, Variables.extendedReads] at lo high ⊢
  all_goals constructor
  all_goals first | linear_combination -lo | linear_combination -high

end Airbender.Blake2Round.Preparation.Proofs
