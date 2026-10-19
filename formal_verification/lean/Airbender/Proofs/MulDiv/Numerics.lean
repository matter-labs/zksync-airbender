import Airbender.Review.Circuits.MulDiv.Model
import Airbender.Proofs.MulDiv.ByteBounds
import Airbender.Proofs.Arithmetic.Multiplication
import Mathlib.Tactic.LinearCombination

namespace Airbender.MulDiv.Proofs
open Arithmetic Verification

variable {w : Nat → ZMod mersenne31Modulus}

def rawLow (w : Nat → ZMod p) : Word := ⟨(w 23).val,(w 24).val⟩
def rawHigh (w : Nat → ZMod p) : Word := ⟨(w 25).val,(w 26).val⟩
def factor (w : Nat → ZMod p) : Word :=
  ⟨(w 35).val + 256 * (w 36).val,(w 37).val + 256 * (w 38).val⟩
def addend (w : Nat → ZMod p) : Word := ⟨(w 29).val,(w 30).val⟩
def productLow (w : Nat → ZMod p) : Word := ⟨(w 31).val,(w 32).val⟩
def productHigh (w : Nat → ZMod p) : Word := ⟨(w 33).val,(w 34).val⟩
def carry (w : Nat → ZMod p) : Fin 3 → Nat
  | 0 => (w 44).val + 256 * (w 43).val
  | 1 => (w 47).val + 256 * (w 45).val + 512 * (w 46).val
  | 2 => (w 49).val + 256 * (w 48).val

theorem local_ranges (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints) :
    ∀ column ∈ [23,24,25,26,55,56], (w column).val < limbBase := by
  have b0 := range16_bound (lookup_of_holds holds ⟨0, by rw [lookup_count]; decide⟩)
  have b1 := range16_bound (lookup_of_holds holds ⟨1, by rw [lookup_count]; decide⟩)
  have b2 := range16_bound (lookup_of_holds holds ⟨2, by rw [lookup_count]; decide⟩)
  have b3 := range16_bound (lookup_of_holds holds ⟨3, by rw [lookup_count]; decide⟩)
  have b4 := range16_bound (lookup_of_holds holds ⟨4, by rw [lookup_count]; decide⟩)
  have b5 := range16_bound (lookup_of_holds holds ⟨5, by rw [lookup_count]; decide⟩)
  intro column member
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact b0
  · exact b1
  · exact b2
  · exact b3
  · exact b4
  · exact b5

theorem boolean_values (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints) :
    ∀ column ∈ [17,18,43,45,46,48,57], (w column).val ≤ 1 := by
  have e0 := assertion_of_holds holds ⟨0,by rw [constraint_count]; decide⟩
  have b0 : (w 17).val ≤ 1 := by
    simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e0
    obtain ⟨n,small,same⟩ := boolean_nat (x := w 17) (by linear_combination e0)
    rw [same]
    exact le_trans (Nat.mod_le _ _) small
  have e1 := assertion_of_holds holds ⟨1,by rw [constraint_count]; decide⟩
  have b1 : (w 18).val ≤ 1 := by
    simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e1
    obtain ⟨n,small,same⟩ := boolean_nat (x := w 18) (by linear_combination e1)
    rw [same]
    exact le_trans (Nat.mod_le _ _) small
  have e2 := assertion_of_holds holds ⟨2,by rw [constraint_count]; decide⟩
  have b2 : (w 43).val ≤ 1 := by
    simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e2
    obtain ⟨n,small,same⟩ := boolean_nat (x := w 43) (by linear_combination e2)
    rw [same]
    exact le_trans (Nat.mod_le _ _) small
  have e3 := assertion_of_holds holds ⟨3,by rw [constraint_count]; decide⟩
  have b3 : (w 45).val ≤ 1 := by
    simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e3
    obtain ⟨n,small,same⟩ := boolean_nat (x := w 45) (by linear_combination e3)
    rw [same]
    exact le_trans (Nat.mod_le _ _) small
  have e4 := assertion_of_holds holds ⟨4,by rw [constraint_count]; decide⟩
  have b4 : (w 46).val ≤ 1 := by
    simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e4
    obtain ⟨n,small,same⟩ := boolean_nat (x := w 46) (by linear_combination e4)
    rw [same]
    exact le_trans (Nat.mod_le _ _) small
  have e5 := assertion_of_holds holds ⟨5,by rw [constraint_count]; decide⟩
  have b5 : (w 48).val ≤ 1 := by
    simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e5
    obtain ⟨n,small,same⟩ := boolean_nat (x := w 48) (by linear_combination e5)
    rw [same]
    exact le_trans (Nat.mod_le _ _) small
  have e6 := assertion_of_holds holds ⟨6,by rw [constraint_count]; decide⟩
  have b6 : (w 57).val ≤ 1 := by
    simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e6
    obtain ⟨n,small,same⟩ := boolean_nat (x := w 57) (by linear_combination e6)
    rw [same]
    exact le_trans (Nat.mod_le _ _) small
  intro column member
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact b0
  · exact b1
  · exact b2
  · exact b3
  · exact b4
  · exact b5
  · exact b6

theorem selected_flags (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (operation : Operation) (selected : (w 12).val = operation.nativeMask) :
    w 17 = (if operation.division then 1 else 0) ∧
      w 18 = (if operation.lowHalf then 1 else 0) := by
  have fieldSize : 65536 < mersenne31Modulus := by decide
  have b0 := boolean_values holds 17 (by simp)
  have b1 := boolean_values holds 18 (by simp)
  have packed := assertion_of_holds holds ⟨43,by rw [constraint_count]; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at packed
  have natural : (w 17).val + 2 * (w 18).val = (w 12).val := by
    apply bounded_nat_eq (F := ZMod mersenne31Modulus) (p := mersenne31Modulus)
      (by omega) (ZMod.val_lt _)
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,ZMod.natCast_zmod_val]
    linear_combination packed
  rw [selected] at natural
  have first : (w 17).val = (if operation.division then 1 else 0) := by
    cases operation <;> simp only [Operation.nativeMask,Operation.division,Bool.false_eq_true,if_false,if_true] at natural ⊢ <;> omega
  have second : (w 18).val = (if operation.lowHalf then 1 else 0) := by
    cases operation <;> simp only [Operation.nativeMask,Operation.division,Operation.lowHalf,Bool.false_eq_true,if_false,if_true] at natural first ⊢ <;> omega
  constructor
  · rw [← ZMod.natCast_zmod_val (w 17),first]
    cases operation <;> rfl
  · rw [← ZMod.natCast_zmod_val (w 18),second]
    cases operation <;> rfl

/-- Byte-pair values are canonical before invoking the shared product theorem. -/
theorem byte_words (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints) :
    (factor w).Bounded ∧ (right w).Bounded ∧
      (right w).lo = (w 39).val + 256 * (w 40).val ∧
      (right w).hi = (w 41).val + 256 * (w 42).val := by
  have fieldSize : 65536 < mersenne31Modulus := by decide
  have bytes := native_byte_bounds holds
  have b35 := bytes 35 (by simp); have b36 := bytes 36 (by simp)
  have b37 := bytes 37 (by simp); have b38 := bytes 38 (by simp)
  have b39 := bytes 39 (by simp); have b40 := bytes 40 (by simp)
  have b41 := bytes 41 (by simp); have b42 := bytes 42 (by simp)
  have e0 := assertion_of_holds holds ⟨44,by rw [constraint_count]; decide⟩
  have e1 := assertion_of_holds holds ⟨45,by rw [constraint_count]; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e0 e1
  have lo : (w 21).val = (w 39).val + 256 * (w 40).val := by
    apply bounded_nat_eq (F := ZMod mersenne31Modulus) (p := mersenne31Modulus)
      (ZMod.val_lt _) (by omega)
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,ZMod.natCast_zmod_val]
    linear_combination -e0
  have hi : (w 22).val = (w 41).val + 256 * (w 42).val := by
    apply bounded_nat_eq (F := ZMod mersenne31Modulus) (p := mersenne31Modulus)
      (ZMod.val_lt _) (by omega)
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,ZMod.natCast_zmod_val]
    linear_combination -e1
  exact ⟨⟨by dsimp [factor,Word.Bounded,limbBase]; omega,by dsimp [factor,Word.Bounded,limbBase]; omega⟩,
    ⟨by dsimp [right,Word.Bounded,limbBase]; omega,by dsimp [right,Word.Bounded,limbBase]; omega⟩,lo,hi⟩

theorem carry_bounds (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints) :
    ∀ i, carry w i < 8192 := by
  have bytes := native_byte_bounds holds
  have bits := boolean_values holds
  have b44 := bytes 44 (by simp); have b47 := bytes 47 (by simp); have b49 := bytes 49 (by simp)
  have b43 := bits 43 (by simp); have b45 := bits 45 (by simp)
  have b46 := bits 46 (by simp); have b48 := bits 48 (by simp)
  intro i
  fin_cases i <;> dsimp [carry] <;> omega

end Airbender.MulDiv.Proofs
