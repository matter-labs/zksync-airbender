import Airbender.Proofs.UnifiedReduced.ArtifactChecks
import Airbender.Proofs.UnifiedReduced.BinaryLookups
import Airbender.Proofs.UnifiedReduced.ShiftLookups
import Airbender.Review.Circuits.UnifiedReduced.Artifact
import Airbender.Proofs.Constraints
import Airbender.Proofs.Arithmetic.Bytes

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
    w (92 + 9 * i.val) = w 10 ∧
      w (93 + 9 * i.val) = leftByte w i ∧
      w (94 + 9 * i.val) = rightByte w i + immediateByte w i ∧
      (∀ j : Fin 4, w (95 + 9 * i.val + j.val) = w (58 + 4 * i.val + j.val)) ∧
      w (99 + 9 * i.val) = 0 ∧ w (100 + 9 * i.val) = 0 := by
  have h (j : Fin 9) := Verification.assertion_of_holds holds
    ⟨52 + 9 * i.val + j.val, by rw [constraint_count]; have := i.isLt; have := j.isLt; omega⟩
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

theorem binary_query_values [Fact p.Prime] (hp : 256 < p)
    {before : Reference.RiscV.Sail.State} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints (Setup.table before)))
    (selected : w 26 = 0 ∧ w 27 = 1) (other : w 21 = 0 ∧ w 22 = 0 ∧ w 23 = 0 ∧ w 24 = 0)
    (tag : Nat) (valid : tag = 4 ∨ tag = 6 ∨ tag = 7) (funct3 : w 10 = (Setup.binaryTag tag : ZMod p))
    (i : Fin 4) :
    (leftByte w i).val < 256 ∧ (rightByte w i + immediateByte w i).val < 256 ∧
      (w (58 + 4 * i.val)).val < 256 ∧
      BitVec.ofNat 8 (w (58 + 4 * i.val)).val = byteOperation tag
        (BitVec.ofNat 8 (leftByte w i).val) (BitVec.ofNat 8 (rightByte w i + immediateByte w i).val) ∧
      ∀ j : Fin 3, w (59 + 4 * i.val + j.val) = 0 := by
  have wires := binary_wiring holds selected other i
  have query := Verification.lookup_of_holds holds
    ⟨14 + i.val, by rw [lookup_count]; have := i.isLt; omega⟩
  fin_cases i
  all_goals
    norm_num only at wires
    have result := Setup.Proofs.wide_lookup hp query tag valid
      (by simpa [Expression.eval, Verification.environment] using wires.1.trans funct3)
    have a := wires.2.1
    have b := wires.2.2.1
    have c := wires.2.2.2.1 ⟨0, by decide⟩
    have d := wires.2.2.2.1 ⟨1, by decide⟩
    have e := wires.2.2.2.1 ⟨2, by decide⟩
    have f := wires.2.2.2.1 ⟨3, by decide⟩
    norm_num only at a b c d e f
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [Expression.eval, Verification.environment, a] using result.1
    · simpa [Expression.eval, Verification.environment, b] using result.2.1
    · simpa [Expression.eval, Verification.environment, c] using result.2.2.1
    · simpa [Expression.eval, Verification.environment, a, b, c] using result.2.2.2.1
    · intro j; fin_cases j
      all_goals first
        | simpa [Expression.eval, Verification.environment, d] using result.2.2.2.2 0
        | simpa [Expression.eval, Verification.environment, e] using result.2.2.2.2 1
        | simpa [Expression.eval, Verification.environment, f] using result.2.2.2.2 2

end Airbender.UnifiedReduced.Proofs
