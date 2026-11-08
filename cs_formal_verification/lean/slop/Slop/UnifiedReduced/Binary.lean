import Slop.UnifiedReduced.ArtifactChecks
import Human.Circuits.UnifiedReduced.Artifact
import Slop.Constraints
import Slop.Arithmetic.Bytes
import Human.Circuits.UnifiedReduced.Tables.Setup
import Slop.ShiftBinop.Lookups

namespace Airbender.UnifiedReduced.Proofs
open Arithmetic Verification
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

def leftByte {p : Nat} (w : Nat → ZMod p) (i : Fin 4) : ZMod p :=
  match i.val with
  | 0 => w 74 | 1 => -7864320 * (w 36 - w 74)
  | 2 => w 75 | _ => -7864320 * (w 37 - w 75)

def rightByte {p : Nat} (w : Nat → ZMod p) (i : Fin 4) : ZMod p :=
  match i.val with
  | 0 => w 76 | 1 => -7864320 * (w 42 - w 76)
  | 2 => w 77 | _ => -7864320 * (w 43 - w 77)

def immediateByte {p : Nat} (w : Nat → ZMod p) (i : Fin 4) : ZMod p :=
  if i.val = 0 then w 8 else if i.val = 1 then w 9 else w 57

theorem binary_wiring [Fact p.Prime] {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w 26 = 0 ∧ w 27 = 1) (other : w 21 = 0 ∧ w 22 = 0 ∧ w 23 = 0 ∧ w 24 = 0)
    (i : Fin 4) :
    w (86 + 9 * i.val) = w 10 ∧
      w (87 + 9 * i.val) = leftByte w i ∧
      w (88 + 9 * i.val) = rightByte w i + immediateByte w i ∧
      (∀ j : Fin 4, w (89 + 9 * i.val + j.val) = w (58 + 4 * i.val + j.val)) ∧
      w (93 + 9 * i.val) = 0 ∧ w (94 + 9 * i.val) = 0 := by
  have h (j : Fin 9) := Verification.assertion_of_holds holds
    ⟨49 + 9 * i.val + j.val, by rw [constraint_count]; have := i.isLt; have := j.isLt; omega⟩
  fin_cases i
  all_goals
    have t := h 0; have a := h 1; have b := h 2
    have c := h 3; have d := h 4; have e := h 5; have f := h 6
    have g := h 7; have k := h 8
    simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment,
      selected.1, selected.2, other.1, other.2.1, other.2.2.1, other.2.2.2,
      leftByte, rightByte, immediateByte] at t a b c d e f g k ⊢
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · linear_combination t
    · linear_combination a
    · linear_combination b
    · intro j; fin_cases j
      all_goals norm_num only
      all_goals first | linear_combination c | linear_combination d | linear_combination e | linear_combination f
    · exact g
    · exact k

end Airbender.UnifiedReduced.Proofs
