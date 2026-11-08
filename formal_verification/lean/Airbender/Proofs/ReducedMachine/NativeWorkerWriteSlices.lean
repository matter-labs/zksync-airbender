import Airbender.Review.Circuits.ReducedMachine.WorkerWriteSlices
import Airbender.Proofs.ReducedMachine.NativeLatestReads
import Airbender.Proofs.Blake2Worker.NativeQueryResults
import Airbender.Proofs.Blake2Worker.NativeControl
import Mathlib.Tactic.FinCases

namespace Airbender.NativeWorkerWriteSliceProofs
open Airbender.NativeWorkerWriteSlices
open Airbender.Blake2Worker.Native Airbender.Blake2Worker.QueryArtifact
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary Verification
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Abstract canonical field reconstruction BEFORE query/native data. -/
theorem reconstruct (a b : F) (scale : Nat) (small : a.val+scale*b.val < 65536) :
    (a+(scale : F)*b).val < 65536 := by
  have same : ((a.val+scale*b.val : Nat) : F) = a+(scale : F)*b := by simp
  rw [← same,ZMod.val_natCast_of_lt (show a.val+scale*b.val < mersenne31Modulus by
    exact small.trans (by decide +kernel))]
  exact small

private theorem reconstruct512 {a b : F} (low : a.val < 512) (high : b.val < 128) :
    (a+512*b).val < 65536 := reconstruct a b 512 (by omega)
private theorem reconstruct128 {a b : F} (low : a.val < 128) (high : b.val < 512) :
    (a+128*b).val < 65536 := reconstruct a b 128 (by omega)
private theorem reconstruct256 {a b : F} (low : a.val < 256) (high : b.val < 256) :
    (a+256*b).val < 65536 := reconstruct a b 256 (by omega)

private theorem bit_of_val (x : F) (small : x.val ≤ 1) : x = 0 ∨ x = 1 := by
  have cast : (x.val : F) = x := ZMod.natCast_zmod_val x
  rcases (show x.val = 0 ∨ x.val = 1 by omega) with zero | one
  · left; rw [zero] at cast; exact cast.symm
  · right; rw [one] at cast; exact cast.symm

private theorem or_bit {a b c product result : F}
    (aBit : a = 0 ∨ a = 1) (bBit : b = 0 ∨ b = 1) (cBit : c = 0 ∨ c = 1)
    (mul : a*b-product = 0) (combine : -c*product+c+product-result = 0) : result = 0 ∨ result = 1 := by
  have resultEq : result = c+a*b-c*(a*b) := by
    linear_combination -combine-(1-c)*mul
  rw [resultEq]
  rcases aBit with rfl | rfl <;> rcases bBit with rfl | rfl <;> rcases cBit with rfl | rfl <;> simp

private theorem block2 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) :
    FlatOperation.ConstraintsHoldFlat (environment w) (constraintsBlock2 setup) := by
  apply holds_of_sublist holds
  have base : (constraintsBlock2 setup).Sublist ([] ++ constraintsBlock0 setup ++ constraintsBlock1 setup ++ constraintsBlock2 setup) := List.sublist_append_right _ _
  exact ((((((((base.trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _))

private theorem block4 {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) :
    FlatOperation.ConstraintsHoldFlat (environment w) (constraintsBlock4 setup) := by
  apply holds_of_sublist holds
  have base : (constraintsBlock4 setup).Sublist ([] ++ constraintsBlock0 setup ++ constraintsBlock1 setup ++ constraintsBlock2 setup ++ constraintsBlock3 setup ++ constraintsBlock4 setup) := by
    exact List.sublist_append_right _ _
  exact ((((((base.trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _))


private def directColumns : Vector Nat 32 := #v[625,626,529,530,627,624,531,528,493,494,573,574,495,492,575,572,537,538,617,618,539,536,619,616,581,582,485,486,583,580,487,484]
private def directQuery (piece : Fin 32) : Fin 208 := ⟨176+piece.val,by have := piece.isLt; omega⟩
private def finishQuery (piece : Fin 32) : Fin 208 :=
  ⟨(if piece.val < 16 then 146+4*(piece.val/2) else 178+4*(piece.val/2-8))+piece.val%2,
    by have := piece.isLt; split <;> omega⟩
private def finishColumn (piece : Fin 32) := 633+7*(piece.val/2)+piece.val%2

/-- Bind actual query SYNTAX before any witness evaluation. -/
private theorem direct_shape (piece : Fin 32) :
    (fixedExpressions (directQuery piece) : Vector (Expression F) 4)[0] = .var ⟨directColumns[piece]⟩ := by
  fin_cases piece <;> rfl
private theorem finish_shape (piece : Fin 32) :
    (fixedExpressions (finishQuery piece) : Vector (Expression F) 4)[2] = .var ⟨finishColumn piece⟩ := by
  fin_cases piece <;> rfl

private theorem direct_bounds {w : Nat → F} (effects : LookupEffects w) (piece : Fin 32) :
    (w directColumns[piece]).val < (fixedKind (directQuery piece)).bound := by
  have shape := direct_shape piece
  have query : (fixedQuery w (directQuery piece))[0] = w directColumns[piece] := by
    simpa [fixedQuery,Expression.eval,environment] using congrArg (Expression.eval (environment w)) shape
  rw [← query]
  exact effects.leftBounds _

private theorem finish_bounds {w : Nat → F} (effects : LookupEffects w) (piece : Fin 32) :
    (w (finishColumn piece)).val < (fixedKind (finishQuery piece)).bound := by
  have shape := finish_shape piece
  have query : (fixedQuery w (finishQuery piece))[2] = w (finishColumn piece) := by
    simpa [fixedQuery,Expression.eval,environment] using congrArg (Expression.eval (environment w)) shape
  rw [← query]
  exact effects.outputBounds _

theorem finalization_bit {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) : w 152 = 0 ∨ w 152 = 1 := by
  have product := assertion_of_holds (block2 holds) ⟨40,by change 40 < 64; decide +kernel⟩
  have combine := assertion_of_holds (block2 holds) ⟨41,by change 41 < 64; decide +kernel⟩
  simp [constraintsBlock2,FlatOperation.constraints,Expression.eval,environment] at product combine
  apply or_bit (a := w 138) (b := w 147) (c := w 150) (product := w 151) (result := w 152) (bit_of_val _ (Airbender.Blake2Worker.NativeProofs.bit_bounds holds ⟨0,by decide +kernel⟩))
    (bit_of_val _ (Airbender.Blake2Worker.NativeProofs.bit_bounds holds ⟨9,by decide +kernel⟩))
    (bit_of_val _ (Airbender.Blake2Worker.NativeProofs.bit_bounds holds ⟨12,by decide +kernel⟩))
  · linear_combination product
  · linear_combination combine

private def directStart (limb : Fin 16) : Fin 32 :=
  ⟨if limb.val < 8 then 4*limb.val else 2+4*(limb.val-8),by have := limb.isLt; split <;> omega⟩
private def directNext (limb : Fin 16) : Fin 32 :=
  ⟨(directStart limb).val+1,by have := limb.isLt; simp only [directStart]; split <;> omega⟩
private def directWrite (limb : Fin 16) :=
  if limb.val < 8 then 54+4*(limb.val/2)+limb.val%2 else 86+4*((limb.val-8)/2)+limb.val%2

private theorem direct_first {setup : Table F (fields 4)}
    {w : Nat → F} (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) (limb : Fin 8) :
    w (directWrite (⟨limb.val,by have := limb.isLt; omega⟩ : Fin 16)) = w directColumns[directStart (⟨limb.val,by have := limb.isLt; omega⟩ : Fin 16)] +
      (if ((⟨limb.val,by have := limb.isLt; omega⟩ : Fin 16) : Fin 16).val < 8 then 512 else 256)*w directColumns[directNext (⟨limb.val,by have := limb.isLt; omega⟩ : Fin 16)] := by
  have eq := assertion_of_holds (block4 holds) ⟨56+limb.val,by change 56+limb.val < 64; have := limb.isLt; omega⟩
  fin_cases limb
  all_goals
    simp [directWrite,directColumns,directStart,directNext,constraintsBlock4,FlatOperation.constraints,Expression.eval,environment] at eq ⊢
    linear_combination -eq

private theorem direct_second {setup : Table F (fields 4)}
    {w : Nat → F} (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) (limb : Fin 8) :
    w (directWrite (⟨8+limb.val,by have := limb.isLt; omega⟩ : Fin 16)) = w directColumns[directStart (⟨8+limb.val,by have := limb.isLt; omega⟩ : Fin 16)] +
      (if ((⟨8+limb.val,by have := limb.isLt; omega⟩ : Fin 16) : Fin 16).val < 8 then 512 else 256)*w directColumns[directNext (⟨8+limb.val,by have := limb.isLt; omega⟩ : Fin 16)] := by
  have eq := assertion_of_holds (Airbender.Blake2Worker.QueryProofs.block5 holds)
    ⟨8+limb.val,by change 8+limb.val < 32; have := limb.isLt; omega⟩
  fin_cases limb
  all_goals
    simp [directWrite,directColumns,directStart,directNext,constraintsBlock5,FlatOperation.constraints,Expression.eval,environment] at eq ⊢
    linear_combination -eq

private theorem direct_equation {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) (limb : Fin 16) :
    w (directWrite limb) = w directColumns[directStart limb] +
      (if (limb : Fin 16).val < 8 then 512 else 256)*w directColumns[directNext limb] := by
  by_cases first : limb.val < 8
  · exact direct_first holds ⟨limb.val,first⟩
  · have equation := direct_second holds ⟨limb.val-8,by have := limb.isLt; omega⟩
    have same : (⟨8+(limb.val-8),by have := limb.isLt; omega⟩ : Fin 16) = limb := by
      apply Fin.ext
      change 8+(limb.val-8) = limb.val
      omega
    have index : 8+(limb.val-8) = limb.val := by omega
    simpa only [same,index] using equation

theorem direct_words {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) (limb : Fin 16) :
    (w (directWrite limb)).val < 65536 := by
  have lookup := Airbender.Blake2Worker.QueryProofs.lookup_effects holds
  have low := direct_bounds lookup (directStart limb)
  have high := direct_bounds lookup (directNext limb)
  rw [direct_equation holds limb]
  fin_cases limb
  all_goals
    simp [directStart,directNext,directQuery,directColumns,fixedKind,Airbender.Blake2Worker.Fixed.Kind.bound] at low high ⊢
    first | exact reconstruct512 low high | exact reconstruct256 low high

private theorem finish_equation {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) (limb : Fin 16) :
    w (6+4*(limb.val/2)+limb.val%2) =
      (w (633+7*limb.val)+(if limb.val < 8 then 128 else 256)*w (634+7*limb.val))*w 152 +
      w (4+4*(limb.val/2)+limb.val%2)*(1-w 152) := by
  have eq := assertion_of_holds (block4 holds) ⟨29+limb.val,by change 29+limb.val < 64; have := limb.isLt; omega⟩
  fin_cases limb <;> simp [constraintsBlock4,FlatOperation.constraints,Expression.eval,environment] at eq ⊢
  all_goals linear_combination -eq

theorem finish_written {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) (limb : Fin 16)
    (enabled : w 152 = 1) : (w (6+4*(limb.val/2)+limb.val%2)).val < 65536 := by
  have lookup := Airbender.Blake2Worker.QueryProofs.lookup_effects holds
  have low := finish_bounds lookup ⟨2*limb.val,by have := limb.isLt; omega⟩
  have high := finish_bounds lookup ⟨2*limb.val+1,by have := limb.isLt; omega⟩
  rw [finish_equation holds limb,enabled]
  simp only [mul_one,sub_self,mul_zero,add_zero]
  fin_cases limb
  all_goals
    simp [finishColumn,finishQuery,fixedKind,Airbender.Blake2Worker.Fixed.Kind.bound] at low high ⊢
    first | exact reconstruct128 low high | exact reconstruct256 low high

private def pairLimb (word : Fin 8) (limb : Fin 2) : Fin 16 :=
  ⟨2*word.val+limb.val,by have := word.isLt; have := limb.isLt; omega⟩
private def finishSlot (word : Fin 8) : Fin 43 := ⟨1+word.val,by have := word.isLt; omega⟩
private def directSlot (word : Fin 8) : Fin 43 :=
  ⟨if word.val < 4 then 13+word.val else 17+word.val,by have := word.isLt; split <;> omega⟩

/-- Kernel-check descriptor coordinates BEFORE mapping any witness values. -/
private theorem finish_columns (word : Fin 8) :
    (memoryAccess (finishSlot word)).readValue = #v[4+4*word.val,5+4*word.val] ∧
    (memoryAccess (finishSlot word)).writeValue = some #v[6+4*word.val,7+4*word.val] := by
  fin_cases word <;> decide +kernel

private theorem direct_columns (word : Fin 8) :
    (memoryAccess (directSlot word)).writeValue = some #v[
      directWrite (pairLimb word 0),directWrite (pairLimb word 1)] := by
  fin_cases word <;> decide +kernel

private theorem finish_value (w : Nat → F) (word : Fin 8) (write : Bool) (limb : Fin 2) :
    (keyValue w (finishSlot word) write)[limb] = w ((if write then 6 else 4)+4*word.val+limb.val) := by
  have columns := finish_columns word
  cases write <;> fin_cases limb <;> simp [keyValue,columns.1,columns.2,Nat.add_assoc]
  all_goals exact congrArg w (by omega)

private theorem direct_value (w : Nat → F) (word : Fin 8) (limb : Fin 2) :
    (keyValue w (directSlot word) true)[limb] = w (directWrite (pairLimb word limb)) := by
  have columns := direct_columns word
  fin_cases limb <;> simp [keyValue,columns]

private theorem finish_port {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table))
    (word : Fin 8) : PortEffect w (finishSlot word) := by
  rcases finalization_bit holds with disabled | enabled
  · right
    apply Vector.ext
    intro i bound
    let limb : Fin 2 := ⟨i,bound⟩
    change (keyValue w (finishSlot word) true)[limb] = (keyValue w (finishSlot word) false)[limb]
    rw [finish_value,finish_value]
    have eq := finish_equation holds (pairLimb word limb)
    have divide : (2*word.val+limb.val)/2 = word.val := by have := limb.isLt; omega
    have residue : (2*word.val+limb.val)%2 = limb.val := by have := limb.isLt; omega
    simpa [pairLimb,disabled,divide,residue] using eq
  · left
    intro limb
    rw [finish_value]
    have bounded := finish_written holds (pairLimb word limb) enabled
    have divide : (2*word.val+limb.val)/2 = word.val := by have := limb.isLt; omega
    have residue : (2*word.val+limb.val)%2 = limb.val := by have := limb.isLt; omega
    simpa [pairLimb,divide,residue] using bounded

private theorem direct_port {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table))
    (word : Fin 8) : PortEffect w (directSlot word) := by
  left
  intro limb
  rw [direct_value]
  exact direct_words holds (pairLimb word limb)

private theorem readonly_columns (slot : Fin 43)
    (copy : slot.val = 0 ∨ (25 ≤ slot.val ∧ slot.val < 42)) :
    (memoryAccess slot).writeValue = none := by
  fin_cases slot <;> norm_num at copy <;> decide +kernel

/-- Readonly values are copied; their actual refresh timestamps are retained. -/
theorem readonly_values (w : Nat → F) (slot : Fin 43)
    (copy : slot.val = 0 ∨ (25 ≤ slot.val ∧ slot.val < 42)) :
    keyValue w slot true = keyValue w slot false := by
  simp [keyValue,readonly_columns slot copy]

private theorem control_port {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) :
    PortEffect w 42 := by
  have control := Airbender.Blake2Worker.NativeProofs.effects holds
  have columns : (memoryAccess 42).writeValue = some #v[136,137] := by decide +kernel
  left
  intro limb
  fin_cases limb
  · simp [keyValue,columns] 
    rw [control.lowCleared]
    decide +kernel
  · simp [keyValue,columns]
    exact control.outputBounded.trans (by decide +kernel)

/-- FULL native BODY/queries derive bounded-or-copy writes at35 actual ports.
    The remaining eight arithmetic state ports are not filtered or assumed. -/
theorem local_effects {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) :
    LocalEffects w := by
  refine ⟨finalization_bit holds,?_⟩
  intro slot covered
  fin_cases slot
  · exact Or.inr (readonly_values w 0 (by decide +kernel))
  · exact finish_port holds ⟨0,by decide +kernel⟩
  · exact finish_port holds ⟨1,by decide +kernel⟩
  · exact finish_port holds ⟨2,by decide +kernel⟩
  · exact finish_port holds ⟨3,by decide +kernel⟩
  · exact finish_port holds ⟨4,by decide +kernel⟩
  · exact finish_port holds ⟨5,by decide +kernel⟩
  · exact finish_port holds ⟨6,by decide +kernel⟩
  · exact finish_port holds ⟨7,by decide +kernel⟩
  · simp [Covered] at covered
  · simp [Covered] at covered
  · simp [Covered] at covered
  · simp [Covered] at covered
  · exact direct_port holds ⟨0,by decide +kernel⟩
  · exact direct_port holds ⟨1,by decide +kernel⟩
  · exact direct_port holds ⟨2,by decide +kernel⟩
  · exact direct_port holds ⟨3,by decide +kernel⟩
  · simp [Covered] at covered
  · simp [Covered] at covered
  · simp [Covered] at covered
  · simp [Covered] at covered
  · exact direct_port holds ⟨4,by decide +kernel⟩
  · exact direct_port holds ⟨5,by decide +kernel⟩
  · exact direct_port holds ⟨6,by decide +kernel⟩
  · exact direct_port holds ⟨7,by decide +kernel⟩
  · exact Or.inr (readonly_values w 25 (by decide +kernel))
  · exact Or.inr (readonly_values w 26 (by decide +kernel))
  · exact Or.inr (readonly_values w 27 (by decide +kernel))
  · exact Or.inr (readonly_values w 28 (by decide +kernel))
  · exact Or.inr (readonly_values w 29 (by decide +kernel))
  · exact Or.inr (readonly_values w 30 (by decide +kernel))
  · exact Or.inr (readonly_values w 31 (by decide +kernel))
  · exact Or.inr (readonly_values w 32 (by decide +kernel))
  · exact Or.inr (readonly_values w 33 (by decide +kernel))
  · exact Or.inr (readonly_values w 34 (by decide +kernel))
  · exact Or.inr (readonly_values w 35 (by decide +kernel))
  · exact Or.inr (readonly_values w 36 (by decide +kernel))
  · exact Or.inr (readonly_values w 37 (by decide +kernel))
  · exact Or.inr (readonly_values w 38 (by decide +kernel))
  · exact Or.inr (readonly_values w 39 (by decide +kernel))
  · exact Or.inr (readonly_values w 40 (by decide +kernel))
  · exact Or.inr (readonly_values w 41 (by decide +kernel))
  · exact control_port holds

theorem effects {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity proofs batch) : Effects proofs batch inputs := by
  have processing := Airbender.NativeActiveWorkerClockProofs.worker_processing embed memory ch pc gamma config accepted
  exact ⟨Airbender.NativeLatestReadsProofs.effects embed memory ch pc gamma config accepted identity,
    fun w member => local_effects (processing w member).body⟩

theorem counted {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainBatch.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainBatch.SourceAccepted embed memory ch pc gamma config batch workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.proofs workers) :
    Airbender.NativeMainBatch.Effects batch ∧ Effects batch.proofs workers inputs :=
  ⟨Airbender.NativeMainBatchProofs.effects batch accepted.counter,
    effects embed memory ch pc gamma config accepted.component identity⟩

end Airbender.NativeWorkerWriteSliceProofs
