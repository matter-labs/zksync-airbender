import Airbender.Proofs.Blake2Worker.NativeQueryFixed0
import Airbender.Proofs.Blake2Worker.NativeQueryFixed1
import Airbender.Proofs.Blake2Worker.NativeQueryFixed2
import Airbender.Proofs.Blake2Worker.NativeQueryFixed3
import Airbender.Proofs.Blake2Worker.NativeQueryFixed4
import Airbender.Proofs.Blake2Worker.NativeQueryRanges
import Airbender.Review.Circuits.Blake2Worker.TablesTheorems

namespace Airbender.Blake2Worker.QueryProofs
open Verification Native QueryArtifact
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

private theorem fin_index {α : Type} {n : Nat} (values : Vector α n) (slot : Fin n) :
    values[slot] = values.get slot := rfl

theorem fixed_membership {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Fixed.table))
    (slot : Fin 208) : Fixed.table.Contains #[] (fixedQuery w slot) := by
  unfold fixedQuery fixedExpressions
  split
  · simpa only [fin_index] using fixed0 holds ⟨slot.val,by omega⟩
  split
  · exact fixed1 holds _
  split
  · exact fixed2 holds _
  split
  · exact fixed3 holds _
  exact fixed4 holds _

theorem fixed_tags (w : Nat → ZMod mersenne31Modulus) (slot : Fin 208) :
    (fixedQuery w slot)[3] = ((fixedKind slot).tag : ZMod mersenne31Modulus) := by
  unfold fixedQuery fixedExpressions
  split
  · have result := tag0 w ⟨slot.val,by omega⟩
    have position : (⟨0+slot.val,by have := slot.isLt; omega⟩ : Fin 208) = slot := Fin.ext (Nat.zero_add _)
    rw [position] at result
    simpa only [fin_index] using result
  split
  · have result := tag1 w ⟨slot.val-8,by omega⟩
    have same : 8+(slot.val-8) = slot.val := by omega
    have position : (⟨8+(slot.val-8),by omega⟩ : Fin 208) = slot := Fin.ext same
    rw [position] at result
    exact result
  split
  · have result := tag2 w ⟨slot.val-72,by omega⟩
    have same : 72+(slot.val-72) = slot.val := by omega
    have position : (⟨72+(slot.val-72),by omega⟩ : Fin 208) = slot := Fin.ext same
    rw [position] at result
    exact result
  split
  · have result := tag3 w ⟨slot.val-136,by omega⟩
    have same : 136+(slot.val-136) = slot.val := by omega
    have position : (⟨136+(slot.val-136),by omega⟩ : Fin 208) = slot := Fin.ext same
    rw [position] at result
    exact result
  have result := tag4 w ⟨slot.val-200,by omega⟩
  have same : 200+(slot.val-200) = slot.val := by omega
  have position : (⟨200+(slot.val-200),by omega⟩ : Fin 208) = slot := Fin.ext same
  rw [position] at result
  exact result

private theorem kind_injective : Function.Injective Fixed.Kind.tag := by
  intro a b equal
  cases a <;> cases b <;> simp_all [Fixed.Kind.tag]

private def width : Fixed.Kind → Nat
  | .byte => 8 | .three => 3 | .four => 4 | .seven => 7 | .nine => 9

private theorem xor_bound (kind : Fixed.Kind) (a b : Nat)
    (left : a < kind.bound) (right : b < kind.bound) : a ^^^ b < kind.bound := by
  have power : 2^(width kind) = kind.bound := by cases kind <;> rfl
  have same : ((BitVec.ofNat (width kind) a) ^^^ (BitVec.ofNat (width kind) b)).toNat = a ^^^ b := by
    simp [power,Nat.mod_eq_of_lt left,Nat.mod_eq_of_lt right]
  rw [← same,← power]
  exact BitVec.isLt _

theorem pooled_result (kind : Fixed.Kind) (query : Vector (ZMod mersenne31Modulus) 4)
    (member : Fixed.table.Contains #[] query)
    (selected : query[3] = (kind.tag : ZMod mersenne31Modulus)) :
    query[0].val < kind.bound ∧ query[1].val < kind.bound ∧ query[2].val < kind.bound ∧
      query[2].val = query[0].val ^^^ query[1].val := by
  obtain ⟨other,tag,left,right⟩ := Fixed.input_properties query member
  have tagBound : kind.tag < mersenne31Modulus := by cases kind <;> decide
  have equal : other.tag = kind.tag := by rw [← tag,selected,ZMod.val_natCast_of_lt tagBound]
  have kinds := kind_injective equal
  subst other
  have result : query[2].val = query[0].val ^^^ query[1].val := by
    cases kind with
    | byte =>
      obtain ⟨a,b,c,result⟩ := Fixed.byte_xor query member selected
      have natural := congrArg BitVec.toNat result
      simpa [byteOperation,Nat.mod_eq_of_lt a,Nat.mod_eq_of_lt b,Nat.mod_eq_of_lt c] using natural
    | three => exact Fixed.three_xor query member selected
    | four => exact Fixed.four_xor query member selected
    | seven => exact Fixed.seven_xor query member selected
    | nine => exact Fixed.nine_xor query member selected
  have output : query[2].val < kind.bound := by
    rw [result]
    exact xor_bound kind _ _ left right
  exact ⟨left,right,output,result⟩

theorem clock_bounds {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Fixed.table))
    (slot : Fin 86) : ((clockExpression slot).eval (environment w)).val < 524288 := by
  unfold clockExpression
  split
  · exact clocks0 holds _
  · exact clocks1 holds _

theorem lookup_effects {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Fixed.table)) : LookupEffects w := by
  have result := fun slot => pooled_result (fixedKind slot) (fixedQuery w slot)
    (fixed_membership holds slot) (fixed_tags w slot)
  exact ⟨scalars holds,clock_bounds holds,fixed_tags w,
    fun slot => (result slot).1,fun slot => (result slot).2.1,
    fun slot => (result slot).2.2.1,fun slot => (result slot).2.2.2⟩

end Airbender.Blake2Worker.QueryProofs
