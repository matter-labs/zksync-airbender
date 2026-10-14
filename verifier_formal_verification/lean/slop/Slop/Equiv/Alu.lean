import Slop.Equiv.Regs

/-! Sail's ALU helpers = our `RV.alu` operations (pure bit-vector facts). -/

open Sail SailRV32 SailRV32.Functions

namespace Slop.Equiv

theorem shamt_eq (y : BitVec 32) :
    (Sail.BitVec.extractLsb y ((↑Functions.log2_xlen : Int) - 1).toNat 0).toNat = (y.setWidth 5).toNat := by
  simp [Sail.BitVec.extractLsb, BitVec.extractLsb, Functions.log2_xlen, Functions.xlen]

theorem sll_eq (x y : BitVec 32) :
    shift_bits_left x (Sail.BitVec.extractLsb y ((↑Functions.log2_xlen : Int) - 1).toNat 0) = x <<< (y.setWidth 5).toNat := by
  simp only [shift_bits_left, BitVec.shiftLeft_eq', shamt_eq]

theorem srl_eq (x y : BitVec 32) :
    shift_bits_right x (Sail.BitVec.extractLsb y ((↑Functions.log2_xlen : Int) - 1).toNat 0) = x >>> (y.setWidth 5).toNat := by
  simp only [shift_bits_right, BitVec.ushiftRight_eq', shamt_eq]

theorem sra_eq (x y : BitVec 32) :
    shift_bits_right_arith x (Sail.BitVec.extractLsb y ((↑Functions.log2_xlen : Int) - 1).toNat 0) = x.sshiftRight (y.setWidth 5).toNat := by
  simp only [shift_bits_right_arith, BitVec.toNatInt, shamt_eq]
  rfl

theorem slt_eq (x y : BitVec 32) :
    zero_extend (m := 32) (bool_to_bit (zopz0zI_s x y)) = if x.slt y = true then 1 else 0 := by
  simp only [zopz0zI_s, BitVec.slt_iff_toInt_lt]
  by_cases h : x.toInt < y.toInt <;> simp [h, bool_to_bit, zero_extend] <;> rfl

theorem sltu_eq (x y : BitVec 32) :
    zero_extend (m := 32) (bool_to_bit (zopz0zI_u x y)) = if x.ult y = true then 1 else 0 := by
  simp only [zopz0zI_u, BitVec.toNatInt, BitVec.ult]
  by_cases h : x.toNat < y.toNat <;> simp [h, bool_to_bit, zero_extend] <;> rfl

theorem shamt6_eq (y : BitVec 32) :
    (Sail.BitVec.extractLsb (BitVec.extractLsb' 0 6 y) ((↑Functions.log2_xlen : Int) - 1).toNat 0).toNat =
      (y.setWidth 5).toNat := by
  simp [Sail.BitVec.extractLsb, BitVec.extractLsb, Functions.log2_xlen]

theorem sll6_eq (x y : BitVec 32) :
    shift_bits_left x (Sail.BitVec.extractLsb (BitVec.extractLsb' 0 6 y) ((↑Functions.log2_xlen : Int) - 1).toNat 0) =
      x <<< (y.setWidth 5).toNat := by
  simp only [shift_bits_left, BitVec.shiftLeft_eq', shamt6_eq]

theorem srl6_eq (x y : BitVec 32) :
    shift_bits_right x (Sail.BitVec.extractLsb (BitVec.extractLsb' 0 6 y) ((↑Functions.log2_xlen : Int) - 1).toNat 0) =
      x >>> (y.setWidth 5).toNat := by
  simp only [shift_bits_right, BitVec.ushiftRight_eq', shamt6_eq]

theorem sra6_eq (x y : BitVec 32) :
    shift_bits_right_arith x (Sail.BitVec.extractLsb (BitVec.extractLsb' 0 6 y) ((↑Functions.log2_xlen : Int) - 1).toNat 0) =
      x.sshiftRight (y.setWidth 5).toNat := by
  simp only [shift_bits_right_arith, BitVec.toNatInt, shamt6_eq]
  rfl

/-! M extension: Sail computes through `Int`; these are the same values. -/

theorem mulhu_nat (x y : BitVec 32) :
    (((x.toNat : Int) * (y.toNat : Int) % 36893488147419103232).toNat >>> 32) % 4294967296 =
      ((x.toNat * y.toNat % 18446744073709551616) >>> 32) % 4294967296 := by
  have hx := x.isLt; have hy := y.isLt
  have hp : x.toNat * y.toNat < 18446744073709551616 := by
    calc x.toNat * y.toNat < 4294967296 * 4294967296 := Nat.mul_lt_mul'' hx hy
      _ = 18446744073709551616 := by norm_num
  rw [Nat.mod_eq_of_lt hp, ← Int.natCast_mul, Int.emod_eq_of_lt (by positivity) (by omega), Int.toNat_natCast]

theorem divu_nat (x y : BitVec 32) :
    ((if y.toNat = 0 then -1 else (x.toNat : Int) / (y.toNat : Int)) % 8589934592).toNat % 4294967296 =
      BitVec.toNat (if y = 0#32 then 4294967295#32 else x / y) := by
  by_cases h : y = 0#32
  · subst h; simp
  · have hy : y.toNat ≠ 0 := by intro h'; apply h; exact BitVec.eq_of_toNat_eq (by simpa using h')
    have hx := x.isLt
    simp only [hy, h, ↓reduceIte, BitVec.toNat_udiv]
    rw [← Int.natCast_ediv, Int.emod_eq_of_lt (by positivity) (by have := Nat.div_le_self x.toNat y.toNat; omega),
      Int.toNat_natCast, Nat.mod_eq_of_lt (by have := Nat.div_le_self x.toNat y.toNat; omega)]

theorem remu_nat (x y : BitVec 32) :
    ((if y.toNat = 0 then (x.toNat : Int) else Int.tmod (x.toNat : Int) (y.toNat : Int)) % 8589934592).toNat % 4294967296 =
      BitVec.toNat (if y = 0#32 then x else x % y) := by
  have hx := x.isLt
  by_cases h : y = 0#32
  · subst h
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, ↓reduceIte]
    rw [Int.emod_eq_of_lt (by positivity) (by omega), Int.toNat_natCast, Nat.mod_eq_of_lt hx]
  · have hy : y.toNat ≠ 0 := by intro h'; apply h; exact BitVec.eq_of_toNat_eq (by simpa using h')
    simp only [hy, h, ↓reduceIte, BitVec.toNat_umod]
    rw [Int.tmod_eq_emod_of_nonneg (by positivity), ← Int.natCast_emod,
      Int.emod_eq_of_lt (by positivity) (by have := Nat.mod_lt x.toNat (Nat.pos_of_ne_zero hy); omega),
      Int.toNat_natCast, Nat.mod_eq_of_lt (by have := Nat.mod_lt x.toNat (Nat.pos_of_ne_zero hy); omega)]

theorem mul_int (x y : BitVec 32) :
    ((x.toInt * y.toInt % 36893488147419103232).toNat) % 4294967296 = x.toNat * y.toNat % 4294967296 := by
  have hx : x.toInt % 4294967296 = (x.toNat : Int) % 4294967296 := by
    rw [BitVec.toInt_eq_toNat_cond]; split <;> omega
  have hy : y.toInt % 4294967296 = (y.toNat : Int) % 4294967296 := by
    rw [BitVec.toInt_eq_toNat_cond]; split <;> omega
  have h1 : (x.toInt * y.toInt % 36893488147419103232) % 4294967296 = (x.toInt * y.toInt) % 4294967296 :=
    Int.emod_emod_of_dvd _ (by norm_num)
  have h2 : (x.toInt * y.toInt) % 4294967296 = ((x.toNat * y.toNat : Nat) : Int) % 4294967296 := by
    rw [Int.mul_emod, hx, hy, ← Int.mul_emod]; push_cast; rfl
  have hnn : 0 ≤ x.toInt * y.toInt % 36893488147419103232 := Int.emod_nonneg _ (by norm_num)
  omega

end Slop.Equiv
