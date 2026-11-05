import Human.Circuits.MulDiv.Operation
import Human.ISA.RV32
import Slop.MulDiv.Product

/-! Row-level MUL/MULHU/DIVU/REMU result in RV32 terms: the imported constraints with one selected operation force
    the destination word to be `RV.alu` of the operand words (DIVU by zero = all ones, REMU by zero = the dividend).
    Sail-free: reuses the row calculation lemmas of `Slop/MulDiv.lean` and `Slop/MulDiv/Product.lean`. -/

namespace Airbender.MulDiv

/-- The `RV.Op` of each circuit operation. -/
def Operation.rvOp : Operation → RV.Op
  | .mul => .mul | .mulhu => .mulhu | .divu => .divu | .remu => .remu

end Airbender.MulDiv

namespace Airbender.MulDiv.Proofs
open Airbender.Arithmetic

/-- As the private `division_destination` of `Soundness.lean`. -/
theorem rv_division_destination {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p)
    (inverse : (-30720 : ZMod p) * 65536 = 1) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (remainder : Bool)
    (selected : w 12 = (if remainder then 0 else 1) ∧ w 13 = (if remainder then 1 else 0))
    (other : w 10 = 0 ∧ w 11 = 0)
    (leftBound : (w 20).val < limbBase ∧ (w 21).val < limbBase) :
    (⟨(w 28).val, (w 29).val⟩ : Word).toBitVec = BitVec.ofNat 32
      (if (⟨(w 24).val, (w 25).val⟩ : Word).value = 0 then
        if remainder then (⟨(w 20).val, (w 21).val⟩ : Word).value else 4294967295
      else if remainder then (⟨(w 20).val, (w 21).val⟩ : Word).value %
        (⟨(w 24).val, (w 25).val⟩ : Word).value
      else (⟨(w 20).val, (w 21).val⟩ : Word).value /
        (⟨(w 24).val, (w 25).val⟩ : Word).value) := by
  by_cases zero : (⟨(w 24).val, (w 25).val⟩ : Word).value = 0
  · have zeroFields : w 24 = 0 ∧ w 25 = 0 := by
      simpa [Word.value, limbBase, ZMod.val_eq_zero] using zero
    have value := division_by_zero (by omega) remainder h selected other zeroFields
    cases remainder <;> simpa [zero, Word.toBitVec] using value
  · have value := division_nonzero hp inverse h remainder selected other leftBound zero
    simp only [ite_eq_right zero, Word.toBitVec, value]

theorem rv_mul_bits (a b : Nat) :
    BitVec.ofNat 32 ((a * b) % wordModulus) = BitVec.ofNat 32 a * BitVec.ofNat 32 b := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofNat, BitVec.toNat_mul, wordModulus, Nat.mul_mod]

theorem rv_mulhu_bits {a b : Nat} (ha : a < wordModulus) (hb : b < wordModulus) :
    BitVec.ofNat 32 ((a * b) / wordModulus) =
      ((BitVec.ofNat 32 a).zeroExtend 64 * (BitVec.ofNat 32 b).zeroExtend 64).extractLsb' 32 32 := by
  apply BitVec.eq_of_toNat_eq
  unfold wordModulus at ha hb ⊢
  have product : a * b < 2 ^ 64 := by
    calc a * b < 4294967296 * 4294967296 := Nat.mul_lt_mul'' ha hb
      _ = 2 ^ 64 := by norm_num
  simp only [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, BitVec.toNat_mul, BitVec.toNat_setWidth,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (show a < 2 ^ 32 by omega), Nat.mod_eq_of_lt (show b < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt product]

theorem rv_divu_bits {a b : Nat} (ha : a < wordModulus) (hb : b < wordModulus) :
    BitVec.ofNat 32 (if b = 0 then 4294967295 else a / b) =
      if BitVec.ofNat 32 b = 0 then -1 else BitVec.ofNat 32 a / BitVec.ofNat 32 b := by
  unfold wordModulus at ha hb
  have zero : BitVec.ofNat 32 b = 0 ↔ b = 0 := by
    rw [← BitVec.toNat_inj]
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
  by_cases hz : b = 0
  · simp only [hz, ite_true]
    rfl
  · have hz' : ¬BitVec.ofNat 32 b = 0 := fun e => hz (zero.mp e)
    simp only [hz, hz', ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat, BitVec.toNat_udiv, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
      Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self a b) ha)]

theorem rv_remu_bits {a b : Nat} (ha : a < wordModulus) (hb : b < wordModulus) :
    BitVec.ofNat 32 (if b = 0 then a else a % b) =
      if BitVec.ofNat 32 b = 0 then BitVec.ofNat 32 a else BitVec.ofNat 32 a % BitVec.ofNat 32 b := by
  unfold wordModulus at ha hb
  have zero : BitVec.ofNat 32 b = 0 ↔ b = 0 := by
    rw [← BitVec.toNat_inj]
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
  by_cases hz : b = 0
  · simp [hz]
  · have hz' : ¬BitVec.ofNat 32 b = 0 := fun e => hz (zero.mp e)
    simp only [hz, hz', ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat, BitVec.toNat_umod, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
      Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.mod_le a b) ha)]

/-- One selected operation: the destination word is `RV.alu` of the two operand words. The left operand's limb
    bounds are the only operand premise (the divisor's come from its byte lookups). -/
theorem rv_row_result {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p)
    (inverse : (-30720 : ZMod p) * 65536 = 1) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (operation : Operation)
    (selected : ∀ i : Fin 4, w (10 + i.val) = if i = operation.selector then 1 else 0)
    (leftBound : (w 20).val < limbBase ∧ (w 21).val < limbBase) :
    (⟨(w 28).val, (w 29).val⟩ : Word).toBitVec =
      RV.alu operation.rvOp (⟨(w 20).val, (w 21).val⟩ : Word).toBitVec
        (⟨(w 24).val, (w 25).val⟩ : Word).toBitVec := by
  have bytes := byte_values (by omega) h
  have leftWord : (⟨(w 20).val, (w 21).val⟩ : Word).Bounded := leftBound
  have rightWord : (⟨(w 24).val, (w 25).val⟩ : Word).Bounded :=
    ⟨(bytes ⟨0, by decide⟩).1, (bytes ⟨1, by decide⟩).1⟩
  have la := Word.value_lt leftWord
  have rb := Word.value_lt rightWord
  have s0 := selected ⟨0, by decide⟩
  have s1 := selected ⟨1, by decide⟩
  have s2 := selected ⟨2, by decide⟩
  have s3 := selected ⟨3, by decide⟩
  cases operation
  · have value := multiplication_result hp inverse h false (fun i => by rw [selected i]; fin_cases i <;> simp [Operation.selector])
      leftBound
    simp only [Bool.false_eq_true, ite_false] at value
    simp only [Word.toBitVec, value, Operation.rvOp, RV.alu]
    exact rv_mul_bits _ _
  · have value := multiplication_result hp inverse h true (fun i => by rw [selected i]; fin_cases i <;> simp [Operation.selector])
      leftBound
    simp only [ite_true] at value
    simp only [Word.toBitVec, value, Operation.rvOp, RV.alu]
    exact rv_mulhu_bits la rb
  · have value := rv_division_destination hp inverse h false
      ⟨by simpa [Operation.selector] using s2, by simpa [Operation.selector] using s3⟩
      ⟨by simpa [Operation.selector] using s0, by simpa [Operation.selector] using s1⟩ leftBound
    simp only [Bool.false_eq_true, ite_false] at value
    rw [value]
    simp only [Word.toBitVec, Operation.rvOp, RV.alu]
    exact rv_divu_bits la rb
  · have value := rv_division_destination hp inverse h true
      ⟨by simpa [Operation.selector] using s2, by simpa [Operation.selector] using s3⟩
      ⟨by simpa [Operation.selector] using s0, by simpa [Operation.selector] using s1⟩ leftBound
    simp only [ite_true] at value
    rw [value]
    simp only [Word.toBitVec, Operation.rvOp, RV.alu]
    exact rv_remu_bits la rb

end Airbender.MulDiv.Proofs
