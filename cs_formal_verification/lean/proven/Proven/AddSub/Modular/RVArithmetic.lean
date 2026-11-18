module
public import Proven.AddSub.Modular.Result
public import Mathlib.Data.ZMod.Basic

@[expose] public section

namespace Airbender.AddSub.Modular

/-- Nat subtraction with one modulus represents the field difference. -/
theorem sub_val (left right : Nat) :
    ((left : ZMod babyBearModulus) - right).val =
      (left % babyBearModulus + babyBearModulus - right % babyBearModulus) % babyBearModulus := by
  have small := Nat.mod_lt right (by decide : 0 < babyBearModulus)
  have bound : right % babyBearModulus ≤ left % babyBearModulus + babyBearModulus := by omega
  have cast : ((left % babyBearModulus + babyBearModulus - right % babyBearModulus : Nat) :
      ZMod babyBearModulus) = (left : ZMod babyBearModulus) - right := by
    rw [Nat.cast_sub bound]
    simp
  simpa only [ZMod.val_natCast] using (congrArg ZMod.val cast).symm

/-- The field calculation is the shared RV spec's Montgomery operation. -/
theorem arithmeticResult_rv (opcode : Opcode) (left right old : BitVec 32) :
    BitVec.ofNat 32 (arithmeticResult opcode left right old).val =
      RV.mopVal opcode.rvOp left right old := by
  have inverse : (4294967296 : ZMod babyBearModulus)⁻¹ = (943718400 : ZMod babyBearModulus) := by
    decide +kernel
  have inverseValue : (943718400 : ZMod babyBearModulus).val = 943718400 := by decide +kernel
  cases opcode <;>
    simp [arithmeticResult, Opcode.rvOp, RV.mopVal, RV.BabyBearP, RV.RINV, montgomeryInverse,
      inverse, inverseValue, ZMod.val_add, sub_val, ZMod.val_mul, ZMod.val_natCast, Nat.mul_mod, Nat.add_mod]

end Airbender.AddSub.Modular
