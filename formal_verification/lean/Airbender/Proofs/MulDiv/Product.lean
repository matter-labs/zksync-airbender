import Airbender.Proofs.MulDiv.Numerics

namespace Airbender.MulDiv.Proofs
open Arithmetic Verification

variable {w : Nat → ZMod mersenne31Modulus}

private def roleSources : Bool → Vector (Option Nat) 8
  | false => #v[some 19,some 20,none,none,some 23,some 24,some 25,some 26]
  | true => #v[some 23,some 24,some 25,some 26,some 19,some 20,none,none]

private def roleValues (w : Nat → ZMod p) : Vector (ZMod p) 8 :=
  #v[w 35 + 256 * w 36,w 37 + 256 * w 38,w 29,w 30,w 31,w 32,w 33,w 34]

private theorem role_wiring
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (division : Bool) (flag : w 17 = if division then 1 else 0) :
    ∀ i : Fin 8, (roleValues w).get i =
      match (roleSources division).get i with | some v => w v | none => 0 := by
  intro i
  have equation := assertion_of_holds holds
    ⟨14 + i.val,by rw [constraint_count]; have := i.isLt; omega⟩
  cases division <;> fin_cases i <;>
    simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment,
      roleSources,roleValues,Vector.get] at flag equation ⊢ <;>
    rw [flag] at equation <;> first | linear_combination equation | linear_combination -equation

private theorem canonical_pair {x : Word} (bounded : x.Bounded)
    {a b : ZMod mersenne31Modulus}
    (lo : (x.lo : ZMod mersenne31Modulus) = a)
    (hi : (x.hi : ZMod mersenne31Modulus) = b) : x = ⟨a.val,b.val⟩ := by
  have size : 65536 < mersenne31Modulus := by decide
  have low : x.lo = a.val := bounded_nat_eq (F := ZMod mersenne31Modulus)
    (p := mersenne31Modulus) (by have := bounded.1; unfold limbBase at this; omega)
    (ZMod.val_lt _) (by simpa using lo)
  have high : x.hi = b.val := bounded_nat_eq (F := ZMod mersenne31Modulus)
    (p := mersenne31Modulus) (by have := bounded.2; unfold limbBase at this; omega)
    (ZMod.val_lt _) (by simpa using hi)
  cases x
  simp_all

/-- The actual packed division bit wires the shared product roles. -/
theorem word_wiring
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (division : Bool) (flag : w 17 = if division then 1 else 0) :
    factor w = (if division then rawLow w else left w) ∧
    addend w = (if division then rawHigh w else ⟨0,0⟩) ∧
    productLow w = (if division then left w else rawLow w) ∧
    productHigh w = (if division then ⟨0,0⟩ else rawHigh w) := by
  have roles := role_wiring holds division flag
  have e0 := roles 0; have e1 := roles 1
  have e2 := roles 2; have e3 := roles 3
  have e4 := roles 4; have e5 := roles 5
  have e6 := roles 6; have e7 := roles 7
  have factorBound := (byte_words holds).1
  cases division <;>
    dsimp [roleSources,roleValues,Vector.get] at e0 e1 e2 e3 e4 e5 e6 e7 ⊢
  all_goals
    constructor
    · apply canonical_pair factorBound
      · simpa [factor] using e0
      · simpa [factor] using e1
    · repeat' apply And.intro
      all_goals
        apply congrArg₂ Word.mk
        all_goals first |
          (simpa [addend,productLow,productHigh,rawLow,rawHigh,left] using congrArg ZMod.val e2) |
          (simpa [addend,productLow,productHigh,rawLow,rawHigh,left] using congrArg ZMod.val e3) |
          (simpa [addend,productLow,productHigh,rawLow,rawHigh,left] using congrArg ZMod.val e4) |
          (simpa [addend,productLow,productHigh,rawLow,rawHigh,left] using congrArg ZMod.val e5) |
          (simpa [addend,productLow,productHigh,rawLow,rawHigh,left] using congrArg ZMod.val e6) |
          (simpa [addend,productLow,productHigh,rawLow,rawHigh,left] using congrArg ZMod.val e7)

/-- Exact integer product with an optional division remainder. Every byte,
    carry and output bound comes from accepted native constraints; only the
    register input's two-limb bound remains an external row interface. -/
theorem product_with_remainder
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (leftBound : (left w).Bounded) :
    (factor w).value * (right w).value + (addend w).value =
      (productLow w).value + wordModulus * (productHigh w).value := by
  have bytes := native_byte_bounds holds
  have pair := byte_words holds
  have ranges := local_ranges holds
  have lowBound : (rawLow w).Bounded := ⟨ranges 23 (by simp),ranges 24 (by simp)⟩
  have highBound : (rawHigh w).Bounded := ⟨ranges 25 (by simp),ranges 26 (by simp)⟩
  have zeroBound : (⟨0,0⟩ : Word).Bounded := by constructor <;> decide
  have flagBound := boolean_values holds 17 (by simp)
  have flag : w 17 = 0 ∨ w 17 = 1 := by
    have either : (w 17).val = 0 ∨ (w 17).val = 1 := by omega
    rcases either with zero | one
    · left; rw [← ZMod.natCast_zmod_val (w 17),zero]; rfl
    · right; rw [← ZMod.natCast_zmod_val (w 17),one]; rfl
  have bounds : (addend w).Bounded ∧ (productLow w).Bounded ∧ (productHigh w).Bounded := by
    rcases flag with flag | flag
    · have roles := word_wiring holds false flag
      rw [roles.2.1,roles.2.2.1,roles.2.2.2]
      exact ⟨zeroBound,lowBound,highBound⟩
    · have roles := word_wiring holds true flag
      rw [roles.2.1,roles.2.2.1,roles.2.2.2]
      exact ⟨highBound,leftBound,zeroBound⟩
  have b35 := bytes 35 (by simp); have b36 := bytes 36 (by simp)
  have b37 := bytes 37 (by simp); have b38 := bytes 38 (by simp)
  have b39 := bytes 39 (by simp); have b40 := bytes 40 (by simp)
  have b41 := bytes 41 (by simp); have b42 := bytes 42 (by simp)
  have q0 : (factor w).lo % 256 = (w 35).val := by dsimp [factor]; omega
  have q1 : (factor w).lo / 256 = (w 36).val := by dsimp [factor]; omega
  have q2 : (factor w).hi % 256 = (w 37).val := by dsimp [factor]; omega
  have q3 : (factor w).hi / 256 = (w 38).val := by dsimp [factor]; omega
  have d0 : (right w).lo % 256 = (w 39).val := by rw [pair.2.2.1]; omega
  have d1 : (right w).lo / 256 = (w 40).val := by rw [pair.2.2.1]; omega
  have d2 : (right w).hi % 256 = (w 41).val := by rw [pair.2.2.2]; omega
  have d3 : (right w).hi / 256 = (w 42).val := by rw [pair.2.2.2]; omega
  apply product_of_columns (F := ZMod mersenne31Modulus) (by decide)
    (factor w) (right w) (addend w) (productLow w) (productHigh w) (carry w)
    pair.1 pair.2.1 bounds.1 bounds.2.1 bounds.2.2 (carry_bounds holds)
  intro i
  have equation := assertion_of_holds holds
    ⟨22 + i.val,by rw [constraint_count]; have := i.isLt; omega⟩
  fin_cases i <;>
    simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at equation
  all_goals
    dsimp [productColumns,productColumnOutputs]
    simp only [q0,q1,q2,q3,d0,d1,d2,d3]
    dsimp [addend,productLow,productHigh,carry]
    push_cast
    simp only [ZMod.natCast_zmod_val]
    linear_combination equation

end Airbender.MulDiv.Proofs
