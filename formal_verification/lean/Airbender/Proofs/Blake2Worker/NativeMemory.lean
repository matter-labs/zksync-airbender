import Airbender.Proofs.Blake2Worker.NativeMemoryProjection
import Airbender.Proofs.Blake2Worker.NativeQueryResults
import Airbender.Proofs.Arithmetic.Lemmas

namespace Airbender.Blake2Worker.MemoryProofs
open Verification Native QueryArtifact
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Pure canonical inverse calculation. No raw read bound is an input. -/
theorem unscale {factor inverse : Nat} {x : ZMod mersenne31Modulus}
    (positive : 0 < factor) (capacity : factor*65536 < mersenne31Modulus)
    (identity : (factor : ZMod mersenne31Modulus)*inverse = 1)
    (bounded : ((inverse : ZMod mersenne31Modulus)*x).val < 65536) :
    x.val = factor*((inverse : ZMod mersenne31Modulus)*x).val := by
  have small : factor*((inverse : ZMod mersenne31Modulus)*x).val < mersenne31Modulus :=
    lt_trans (Nat.mul_lt_mul_of_pos_left bounded positive) capacity
  have same : x = ((factor*((inverse : ZMod mersenne31Modulus)*x).val : Nat) : ZMod mersenne31Modulus) := by
    simp only [Nat.cast_mul,ZMod.natCast_zmod_val]
    calc
      x = 1*x := by ring
      _ = ((factor : ZMod mersenne31Modulus)*inverse)*x := by rw [identity]
      _ = _ := by ring
  calc
    x.val = (((factor*((inverse : ZMod mersenne31Modulus)*x).val : Nat) : ZMod mersenne31Modulus)).val := congrArg ZMod.val same
    _ = _ := by rw [ZMod.val_natCast,Nat.mod_eq_of_lt small]

theorem state_quotient {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Fixed.table)) :
    (w 2).val = 128*(16777216*w 2).val := by
  have bounded := (QueryProofs.lookup_effects holds).scalars ⟨0,by decide⟩
  simp [queryScalars,Expression.eval,environment] at bounded
  exact unscale (by decide) (by decide) (by decide +kernel) bounded

theorem message_quotient {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Fixed.table)) :
    (w 100).val = 64*(33554432*w 100).val := by
  have bounded := (QueryProofs.lookup_effects holds).scalars ⟨1,by decide⟩
  simp [queryScalars,Expression.eval,environment] at bounded
  exact unscale (by decide) (by decide) (by decide +kernel) bounded

theorem local_effects {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Fixed.table)) : LocalMemoryEffects w := by
  have state := state_quotient holds
  have message := message_quotient holds
  have scalar0 := (QueryProofs.lookup_effects holds).scalars ⟨0,by decide⟩
  have scalar1 := (QueryProofs.lookup_effects holds).scalars ⟨1,by decide⟩
  simp [queryScalars,Expression.eval,environment] at scalar0 scalar1
  refine ⟨state,?_,?_,message,?_,?_,?_,?_,?_⟩
  · rw [state]; simp
  · omega
  · rw [message]; simp
  · omega
  · intro slot
    exact mul_eq_zero.mp (borrow_boolean holds slot) |>.imp id sub_eq_zero.mp
  · intro slot
    have bound := (QueryProofs.lookup_effects holds).clocks ⟨2*slot.val,by have := slot.isLt; omega⟩
    rw [low_expression] at bound
    exact bound
  · intro slot
    have bound := (QueryProofs.lookup_effects holds).clocks ⟨2*slot.val+1,by have := slot.isLt; omega⟩
    rw [high_expression] at bound
    exact bound

end Airbender.Blake2Worker.MemoryProofs
