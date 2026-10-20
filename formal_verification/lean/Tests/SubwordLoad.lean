import Airbender.Review.Helpers.Tables.SubwordLoadTheorems

namespace Airbender.Tests.SubwordLoad
open Verification
set_option autoImplicit false

/-- Every key and tag is checked against the actual native literal data. -/
theorem complete_native_rows (key : Fin 2097152) :
    NativeSubwordLoad.data.rowNat key = (Verification.SubwordLoad.row key).push 45 := by
  exact Airbender.SubwordMemory.LoadProofs.native_load_rows key

/-- Boundary and offset regressions use the complete native certificate. -/
theorem signed_byte_positive :
    NativeSubwordLoad.data.rowNat ⟨127, by decide⟩ = #v[127, 127, 0, 45] := by
  rw [Airbender.SubwordMemory.LoadProofs.native_load_rows]
  decide +kernel

theorem signed_byte_negative :
    NativeSubwordLoad.data.rowNat ⟨128, by decide⟩ = #v[128, 65408, 65535, 45] := by
  rw [Airbender.SubwordMemory.LoadProofs.native_load_rows]
  decide +kernel

theorem signed_byte_minus_one :
    NativeSubwordLoad.data.rowNat ⟨255, by decide⟩ = #v[255, 65535, 65535, 45] := by
  rw [Airbender.SubwordMemory.LoadProofs.native_load_rows]
  decide +kernel

theorem signed_high_byte :
    NativeSubwordLoad.data.rowNat ⟨98304, by decide⟩ = #v[98304, 65408, 65535, 45] := by
  rw [Airbender.SubwordMemory.LoadProofs.native_load_rows]
  decide +kernel

theorem signed_top_byte :
    NativeSubwordLoad.data.rowNat ⟨261888, by decide⟩ = #v[261888, 65535, 65535, 45] := by
  rw [Airbender.SubwordMemory.LoadProofs.native_load_rows]
  decide +kernel

theorem signed_half_positive :
    NativeSubwordLoad.data.rowNat ⟨294911, by decide⟩ = #v[294911, 32767, 0, 45] := by
  rw [Airbender.SubwordMemory.LoadProofs.native_load_rows]
  decide +kernel

theorem signed_half_negative :
    NativeSubwordLoad.data.rowNat ⟨294912, by decide⟩ = #v[294912, 32768, 65535, 45] := by
  rw [Airbender.SubwordMemory.LoadProofs.native_load_rows]
  decide +kernel

theorem signed_high_half :
    NativeSubwordLoad.data.rowNat ⟨458751, by decide⟩ = #v[458751, 65535, 65535, 45] := by
  rw [Airbender.SubwordMemory.LoadProofs.native_load_rows]
  decide +kernel

theorem odd_signed_half_zero :
    NativeSubwordLoad.data.rowNat ⟨393215, by decide⟩ = #v[393215, 0, 0, 45] := by
  rw [Airbender.SubwordMemory.LoadProofs.native_load_rows]
  decide +kernel

theorem unsigned_byte :
    NativeSubwordLoad.data.rowNat ⟨1048831, by decide⟩ = #v[1048831, 255, 0, 45] := by
  rw [Airbender.SubwordMemory.LoadProofs.native_load_rows]
  decide +kernel

theorem unsigned_high_byte :
    NativeSubwordLoad.data.rowNat ⟨1146880, by decide⟩ = #v[1146880, 128, 0, 45] := by
  rw [Airbender.SubwordMemory.LoadProofs.native_load_rows]
  decide +kernel

theorem unsigned_top_byte :
    NativeSubwordLoad.data.rowNat ⟨1310719, by decide⟩ = #v[1310719, 255, 0, 45] := by
  rw [Airbender.SubwordMemory.LoadProofs.native_load_rows]
  decide +kernel

theorem unsigned_half :
    NativeSubwordLoad.data.rowNat ⟨1376255, by decide⟩ = #v[1376255, 65535, 0, 45] := by
  rw [Airbender.SubwordMemory.LoadProofs.native_load_rows]
  decide +kernel

theorem odd_unsigned_half_zero :
    NativeSubwordLoad.data.rowNat ⟨1572863, by decide⟩ = #v[1572863, 0, 0, 45] := by
  rw [Airbender.SubwordMemory.LoadProofs.native_load_rows]
  decide +kernel

theorem unused_word_key :
    NativeSubwordLoad.data.rowNat ⟨589823, by decide⟩ = #v[589823, 0, 0, 45] := by
  rw [Airbender.SubwordMemory.LoadProofs.native_load_rows]
  decide +kernel

theorem invalid_funct3_key :
    NativeSubwordLoad.data.rowNat ⟨2097151, by decide⟩ = #v[2097151, 0, 0, 45] := by
  rw [Airbender.SubwordMemory.LoadProofs.native_load_rows]
  decide +kernel

/-- A changed low output is rejected by native membership itself. -/
theorem wrong_low_rejected :
    ¬ Verification.SubwordLoad.table.Contains #[]
      (#v[128, 1, 65535] : Vector (ZMod mersenne31Modulus) 3) := by
  intro member
  have values := Verification.SubwordLoad.native_values member
  have wrong := values.2.1
  change (1 : ZMod mersenne31Modulus) = 65408 at wrong
  exact (by decide +kernel : (1 : ZMod mersenne31Modulus) ≠ 65408) wrong

/-- A changed sign-extension limb is also rejected. -/
theorem wrong_high_rejected :
    ¬ Verification.SubwordLoad.table.Contains #[]
      (#v[128, 65408, 0] : Vector (ZMod mersenne31Modulus) 3) := by
  intro member
  have values := Verification.SubwordLoad.native_values member
  have wrong := values.2.2.1
  change (0 : ZMod mersenne31Modulus) = 65535 at wrong
  exact (by decide +kernel : (0 : ZMod mersenne31Modulus) ≠ 65535) wrong

end Airbender.Tests.SubwordLoad
