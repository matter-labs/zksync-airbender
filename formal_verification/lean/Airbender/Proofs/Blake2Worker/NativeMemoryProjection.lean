import Airbender.Review.Circuits.Blake2Worker.Memory
import Airbender.Proofs.Blake2Worker.NativeQueryProjection
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

namespace Airbender.Blake2Worker.MemoryProofs
open Verification Native QueryArtifact
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem access_geometry : memoryAccesses.size = 43 ∧
    (memoryAccesses.filter fun access => access.writeValue.isSome).size = 25 := by decide +kernel

theorem clock_columns (slot : Fin 43) :
    clockBorrowColumn slot = 742+3*slot.val ∧
    (memoryAccess slot).readTime = #v[743+3*slot.val,744+3*slot.val] := by
  fin_cases slot <;> decide +kernel

private def term {p : Nat} (coefficient : ZMod p) (column : Nat) : Expression (ZMod p) :=
  .mul (.mul (.const 1) (.const coefficient)) (.var ⟨column⟩)

private def lowSyntax {p : Nat} (slot : Fin 43) : Expression (ZMod p) :=
  .add (.add (.add (.add (.const 0) (.const 0)) (term (-1) 740))
    (term 524288 (742+3*slot.val))) (term 1 (743+3*slot.val))

private def highSyntax {p : Nat} (slot : Fin 43) : Expression (ZMod p) :=
  .add (.add (.add (.add (.add (.const 0) (.const 0)) (term 524288 0))
    (term (-1) 741)) (term (-1) (742+3*slot.val))) (term 1 (744+3*slot.val))

private theorem low_shape (slot : Fin 43) :
    clockExpression ⟨2*slot.val,by have := slot.isLt; omega⟩ = (lowSyntax slot : Expression (ZMod mersenne31Modulus)) := by
  fin_cases slot <;> rfl

private theorem high_shape (slot : Fin 43) :
    clockExpression ⟨2*slot.val+1,by have := slot.isLt; omega⟩ = (highSyntax slot : Expression (ZMod mersenne31Modulus)) := by
  fin_cases slot <;> rfl

theorem low_expression (w : Nat → ZMod mersenne31Modulus) (slot : Fin 43) :
    (clockExpression ⟨2*slot.val,by have := slot.isLt; omega⟩).eval (environment w) = lowClockDifference w slot := by
  rw [low_shape]
  obtain ⟨borrow,read⟩ := clock_columns slot
  simp [lowSyntax,term,Expression.eval,environment,lowClockDifference,borrow,read,constraintsABI]
  ring

theorem high_expression (w : Nat → ZMod mersenne31Modulus) (slot : Fin 43) :
    (clockExpression ⟨2*slot.val+1,by have := slot.isLt; omega⟩).eval (environment w) = highClockDifference w slot := by
  rw [high_shape]
  obtain ⟨borrow,read⟩ := clock_columns slot
  simp [highSyntax,term,Expression.eval,environment,highClockDifference,borrow,read,constraintsABI]
  ring

private theorem block1 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) :
    FlatOperation.ConstraintsHoldFlat (environment w) (constraintsBlock1 setup) := by
  apply holds_of_sublist holds
  have base : (constraintsBlock1 setup).Sublist ([] ++ constraintsBlock0 setup ++ constraintsBlock1 setup) := List.sublist_append_right _ _
  exact (((((((((base.trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _))

private theorem block2 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) :
    FlatOperation.ConstraintsHoldFlat (environment w) (constraintsBlock2 setup) := by
  apply holds_of_sublist holds
  have base : (constraintsBlock2 setup).Sublist ([] ++ constraintsBlock0 setup ++ constraintsBlock1 setup ++ constraintsBlock2 setup) := List.sublist_append_right _ _
  exact ((((((((base.trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _))

private def booleanSyntax (column : Nat) : Expression (ZMod mersenne31Modulus) :=
  .add (.add (.const 0) (.add (.add (.const 0) (.const 0)) (term (-1) column)))
    (.mul (.mul (.mul (.const 1) (.const 1)) (.var ⟨column⟩)) (.var ⟨column⟩))

private theorem bits1_shape (setup : Table (ZMod mersenne31Modulus) (fields 4)) (slot : Fin 3) :
    (FlatOperation.constraints (constraintsBlock1 setup)).get ⟨61+slot.val,by change 61+slot.val < 64; omega⟩ =
      booleanSyntax (742+3*slot.val) := by
  fin_cases slot <;> rfl

private theorem bits2_shape (setup : Table (ZMod mersenne31Modulus) (fields 4)) (slot : Fin 40) :
    (FlatOperation.constraints (constraintsBlock2 setup)).get ⟨slot.val,by change slot.val < 64; omega⟩ =
      booleanSyntax (742+3*(3+slot.val)) := by
  fin_cases slot <;> rfl

theorem borrow_boolean {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) (slot : Fin 43) :
    w (clockBorrowColumn slot) * (w (clockBorrowColumn slot)-1) = 0 := by
  have equation : (booleanSyntax (742+3*slot.val)).eval (environment w) = 0 := by
    by_cases first : slot.val < 3
    · have eq := assertion_of_holds (block1 holds) ⟨61+slot.val,by change 61+slot.val < 64; omega⟩
      rw [bits1_shape setup ⟨slot.val,first⟩] at eq
      exact eq
    · have eq := assertion_of_holds (block2 holds) ⟨slot.val-3,by change slot.val-3 < 64; have := slot.isLt; omega⟩
      rw [bits2_shape setup ⟨slot.val-3,by have := slot.isLt; omega⟩] at eq
      simpa only [show 3+(slot.val-3) = slot.val by omega] using eq
  rw [(clock_columns slot).1]
  simp [booleanSyntax,term,Expression.eval,environment] at equation
  linear_combination equation

end Airbender.Blake2Worker.MemoryProofs
