import Airbender.Proofs.SubwordMemory.OffsetValues

namespace Airbender.SubwordMemory.Proofs
open Verification Arithmetic
set_option autoImplicit false

/-- Native packing has no carry between its 16-bit limb, two offset bits and
    three raw funct3 bits. These are derived ranges at the integrated boundary. -/
theorem packed_parts {limb offset funct3 : Nat}
    (limbBound : limb < 65536) (offsetBound : offset < 4) (functBound : funct3 < 8) :
    (limb + 65536 * offset + 262144 * funct3) % 65536 = limb ∧
    (limb + 65536 * offset + 262144 * funct3) / 65536 % 4 = offset ∧
    (limb + 65536 * offset + 262144 * funct3) / 262144 % 8 = funct3 := by
  omega

theorem native_data_key {w : Nat → ZMod mersenne31Modulus} {limb : ZMod mersenne31Modulus}
    (limbBound : limb.val < 65536) (offsetBound : (w 22).val < 4)
    (functBound : (w 11).val < 8) :
    (dataKey w limb).val = limb.val + 65536 * (w 22).val + 262144 * (w 11).val := by
  have field : dataKey w limb =
      ((limb.val + 65536 * (w 22).val + 262144 * (w 11).val : Nat) : ZMod mersenne31Modulus) := by
    simp [dataKey]
  rw [field,ZMod.val_natCast_of_lt (by change _ < 2147483647; omega)]

theorem selected_limb_bound {rom : WordROM} {w : Nat → ZMod mersenne31Modulus}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    {low high : Nat} (bounds : (⟨(w low).val,(w high).val⟩ : Word).Bounded) :
    (selectedLimb w low high).val < 65536 := by
  rcases upper_bit native with lower | upper
  · simpa only [selectedLimb,lower,sub_zero,one_mul,zero_mul,add_zero,limbBase] using bounds.1
  · simpa only [selectedLimb,upper,sub_self,zero_mul,one_mul,zero_add,limbBase] using bounds.2

end Airbender.SubwordMemory.Proofs
