import Human.Circuits.InitsTeardowns.Theorems

/-! Window arithmetic of the inits/teardowns sets, for layouts with two word bits and `2 ^ 23` or
    `2 ^ 24` rows (the unified and standalone artifacts). -/

namespace Airbender.InitsTeardowns.Proofs
open Trace Arithmetic

/-- The layouts these proofs cover. -/
structure Shape (layout : Layout) : Prop where
  wordBits : layout.wordBits = 2
  traceLog : layout.traceLog = 23 ∨ layout.traceLog = 24

theorem window_lt {layout : Layout} (shape : Shape layout) {top row : Nat} (htop : top < maxTopBit)
    (hrow : row < 2 ^ layout.traceLog) : windowAddress layout top row < 2 ^ 32 := by
  obtain ⟨hw, hT⟩ := shape
  unfold windowAddress maxTopBit at *
  rw [hw]
  rcases hT with h | h <;> rw [h] at hrow ⊢ <;> norm_num at hrow ⊢ <;> omega

theorem window_aligned {layout : Layout} (shape : Shape layout) {top row : Nat} (htop : top < maxTopBit)
    (hrow : row < 2 ^ layout.traceLog) : (Cell.ram (BitVec.ofNat 32 (windowAddress layout top row))).Aligned := by
  have hlt := window_lt shape htop hrow
  obtain ⟨hw, hT⟩ := shape
  simp only [Cell.Aligned, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  unfold windowAddress
  rw [hw]
  rcases hT with h | h <;> rw [h] <;> norm_num <;> omega

theorem natCast_val {n : Nat} (h : n < babyBearModulus) : ((n : ZMod babyBearModulus)).val = n := by
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt h]

/-- The circuit's limbs are the two 16-bit halves of the window address. -/
theorem limbs {T top row : Nat} (hT : T = 23 ∨ T = 24) (htop : top < 64) (hrow : row < 2 ^ T) :
    row * 2 ^ 2 % 2 ^ 16 = (top * 2 ^ (T + 2) + row * 2 ^ 2) % 65536 ∧
    row / 2 ^ (16 - 2) + (top <<< (T + 2 - 16)) % 2 ^ 32 = (top * 2 ^ (T + 2) + row * 2 ^ 2) / 65536 ∧
    (top * 2 ^ (T + 2) + row * 2 ^ 2) / 65536 < 65536 := by
  rcases hT with rfl | rfl <;> simp only [Nat.shiftLeft_eq] <;> norm_num at hrow ⊢ <;> omega

theorem addressCode_eq {layout : Layout} (shape : Shape layout) {top row : Nat} (htop : top < maxTopBit)
    (hrow : row < 2 ^ layout.traceLog) :
    addressCode (p := babyBearModulus) layout top row =
      (Cell.ram (BitVec.ofNat 32 (windowAddress layout top row))).addressCode := by
  have hlt := window_lt shape htop hrow
  obtain ⟨hw, hT⟩ := shape
  obtain ⟨h1, h2, h3⟩ := limbs hT htop hrow
  unfold addressCode addressLimbs setupLow setupHigh topShift
  simp only [Cell.addressCode, Word.ofBitVec, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, limbBase]
  unfold windowAddress at hlt ⊢
  rw [hw] at hlt ⊢
  rw [← Nat.cast_add, natCast_val (by unfold babyBearModulus; omega),
    natCast_val (by unfold babyBearModulus; omega), h1, h2]

end Airbender.InitsTeardowns.Proofs
