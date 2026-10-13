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

end Slop.Equiv
