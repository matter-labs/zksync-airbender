import Airbender.Review.Circuits.ReducedMachine.Tables.ShiftImplementation
import Airbender.Proofs.Tables.SllLowMath
import Airbender.Proofs.Tables.SllHighMath
import Airbender.Proofs.Tables.SrlLowMath
import Airbender.Proofs.Tables.SrlHighMath

namespace Airbender.ReducedMachine.NativeShiftArithmeticProofs
open Verification NativeFixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

-- These calculations have no imported getter equalities in their local contexts.
theorem right_index (i : Fin 4194304) : i.val - 2097152 < 2097152 := by
  have := i.isLt
  omega

theorem branches (p : Prop) [Decidable p] (a b c d : Option Nat)
    (yes : p → a = c) (no : ¬ p → b = d) :
    (if p then a else b) = (if p then c else d) := by
  by_cases h : p
  · rw [if_pos h,if_pos h]
    exact yes h
  · rw [if_neg h,if_neg h]
    exact no h

private theorem pair_first {α : Type} (a b : α) : (#v[a,b])[0] = a := rfl
private theorem pair_second {α : Type} (a b : α) : (#v[a,b])[1] = b := rfl

theorem low_option (n : Nat) :
    (if n < 2097152 then some (sllHighOutput n)
      else some (srlLowOutput (n - 2097152))) = some (shiftOutputs n)[0] := by
  unfold shiftOutputs
  split
  · exact congrArg some (pair_first (sllHighOutput n) (sllLowHighOutput n)).symm
  · exact congrArg some (pair_first (srlLowOutput (n - 2097152))
      (srlHighLowOutput (n - 2097152))).symm

theorem high_option (n : Nat) :
    (if n < 2097152 then some (sllLowHighOutput n)
      else some (srlHighLowOutput (n - 2097152))) = some (shiftOutputs n)[1] := by
  unfold shiftOutputs
  split
  · exact congrArg some (pair_second (sllHighOutput n) (sllLowHighOutput n)).symm
  · exact congrArg some (pair_second (srlLowOutput (n - 2097152))
      (srlHighLowOutput (n - 2097152))).symm

theorem output_bounds (key : Nat) :
    (shiftOutputs key)[0] < 65536 ∧ (shiftOutputs key)[1] < 65536 := by
  unfold shiftOutputs
  split
  · rw [pair_first,pair_second]
    exact ⟨SllHighProofs.high_bound key,SllLowProofs.high_bound key⟩
  · rw [pair_first,pair_second]
    exact ⟨SrlLowProofs.low_bound _,SrlHighProofs.low_bound _⟩

end Airbender.ReducedMachine.NativeShiftArithmeticProofs
