import Airbender.Review.Helpers.Tables.SubwordOffsetTheorems

namespace Airbender.Tests.SubwordOffset
open Verification
set_option autoImplicit false

/-- All native keys, including every high address-bit pattern, keep the exact tag. -/
theorem complete_native_rows (key : Fin 2097152) :
    NativeSubwordOffset.data.rowNat key = (Verification.SubwordOffset.row key).push 44 := by
  exact Airbender.SubwordMemory.Proofs.native_offset_rows key

/-- Actual native literals distinguish misaligned LH, waived x0 LH and the high limb. -/
theorem halfword_trap : (NativeSubwordOffset.data.rowNat ⟨589825, by decide⟩)[2] = 5 := by decide +kernel
theorem halfword_x0_waiver : (NativeSubwordOffset.data.rowNat ⟨1638401, by decide⟩)[2] = 1 := by decide +kernel
theorem high_halfword_trap : (NativeSubwordOffset.data.rowNat ⟨589827, by decide⟩)[2] = 7 := by decide +kernel
theorem high_halfword_x0_waiver : (NativeSubwordOffset.data.rowNat ⟨1638403, by decide⟩)[2] = 3 := by decide +kernel

/-- Byte offsets are admitted, word misalignment traps and invalid encodings stay invalid. -/
theorem high_byte : (NativeSubwordOffset.data.rowNat ⟨524291, by decide⟩)[2] = 3 := by decide +kernel
theorem word_trap : (NativeSubwordOffset.data.rowNat ⟨655361, by decide⟩)[2] = 4 := by decide +kernel
theorem word_x0_waiver : (NativeSubwordOffset.data.rowNat ⟨1703937, by decide⟩)[2] = 0 := by decide +kernel
theorem invalid_x0_still_traps : (NativeSubwordOffset.data.rowNat ⟨1769472, by decide⟩)[2] = 4 := by decide +kernel
theorem stores_have_no_x0_waiver : (NativeSubwordOffset.data.rowNat ⟨1114113, by decide⟩)[2] = 5 := by decide +kernel

/-- A changed offset is rejected by actual native membership, not by a row premise. -/
theorem wrong_offset_rejected :
    ¬ Verification.SubwordOffset.table.Contains #[]
      (#v[589825, 0, 5] : Vector (ZMod mersenne31Modulus) 3) := by
  intro member
  have values := Verification.SubwordOffset.native_values member
  have wrong := values.2.1
  change (0 : ZMod mersenne31Modulus) = 1 at wrong
  exact zero_ne_one wrong

theorem wrong_trap_rejected :
    ¬ Verification.SubwordOffset.table.Contains #[]
      (#v[589825, 1, 1] : Vector (ZMod mersenne31Modulus) 3) := by
  intro member
  have values := Verification.SubwordOffset.native_values member
  have wrong := values.2.2
  change (1 : ZMod mersenne31Modulus) = 5 at wrong
  exact (by decide +kernel : (1 : ZMod mersenne31Modulus) ≠ 5) wrong

end Airbender.Tests.SubwordOffset
