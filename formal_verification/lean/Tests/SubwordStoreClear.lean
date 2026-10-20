import Airbender.Review.Helpers.Tables.SubwordStoreClearTheorems

namespace Airbender.Tests.SubwordStoreClear
open Verification
set_option autoImplicit false

/-- Every actual native row retains its original table tag. -/
theorem complete_native_rows (key : Fin 2097152) :
    NativeSubwordStoreClear.data.rowNat key = (Verification.SubwordStoreClear.row key).push 54 := by
  exact Airbender.SubwordMemory.StoreClearProofs.native_store_clear_rows key

theorem zero_limb :
    NativeSubwordStoreClear.data.rowNat ⟨0, by decide⟩ = #v[0, 0, 0, 54] := by
  rw [Airbender.SubwordMemory.StoreClearProofs.native_store_clear_rows]
  decide +kernel

theorem low_byte_removed :
    NativeSubwordStoreClear.data.rowNat ⟨255, by decide⟩ = #v[255, 0, 0, 54] := by
  rw [Airbender.SubwordMemory.StoreClearProofs.native_store_clear_rows]
  decide +kernel

theorem high_byte_retained :
    NativeSubwordStoreClear.data.rowNat ⟨65280, by decide⟩ = #v[65280, 65280, 0, 54] := by
  rw [Airbender.SubwordMemory.StoreClearProofs.native_store_clear_rows]
  decide +kernel

theorem all_bits_even :
    NativeSubwordStoreClear.data.rowNat ⟨65535, by decide⟩ = #v[65535, 65280, 0, 54] := by
  rw [Airbender.SubwordMemory.StoreClearProofs.native_store_clear_rows]
  decide +kernel

theorem all_bits_odd :
    NativeSubwordStoreClear.data.rowNat ⟨131071, by decide⟩ = #v[131071, 255, 0, 54] := by
  rw [Airbender.SubwordMemory.StoreClearProofs.native_store_clear_rows]
  decide +kernel

theorem high_byte_removed :
    NativeSubwordStoreClear.data.rowNat ⟨130816, by decide⟩ = #v[130816, 0, 0, 54] := by
  rw [Airbender.SubwordMemory.StoreClearProofs.native_store_clear_rows]
  decide +kernel

theorem offset_two :
    NativeSubwordStoreClear.data.rowNat ⟨175053, by decide⟩ = #v[175053, 43776, 0, 54] := by
  rw [Airbender.SubwordMemory.StoreClearProofs.native_store_clear_rows]
  decide +kernel

theorem offset_three :
    NativeSubwordStoreClear.data.rowNat ⟨240589, by decide⟩ = #v[240589, 205, 0, 54] := by
  rw [Airbender.SubwordMemory.StoreClearProofs.native_store_clear_rows]
  decide +kernel

theorem halfword_zero :
    NativeSubwordStoreClear.data.rowNat ⟨327679, by decide⟩ = #v[327679, 0, 0, 54] := by
  rw [Airbender.SubwordMemory.StoreClearProofs.native_store_clear_rows]
  decide +kernel

theorem word_zero :
    NativeSubwordStoreClear.data.rowNat ⟨589823, by decide⟩ = #v[589823, 0, 0, 54] := by
  rw [Airbender.SubwordMemory.StoreClearProofs.native_store_clear_rows]
  decide +kernel

theorem unused_key_zero :
    NativeSubwordStoreClear.data.rowNat ⟨2097151, by decide⟩ = #v[2097151, 0, 0, 54] := by
  rw [Airbender.SubwordMemory.StoreClearProofs.native_store_clear_rows]
  decide +kernel

/-- Clearing a retained high byte incorrectly is rejected by membership. -/
theorem wrong_cleared_rejected :
    ¬ Verification.SubwordStoreClear.table.Contains #[]
      (#v[65535, 0, 0] : Vector (ZMod mersenne31Modulus) 3) := by
  intro member
  have values := Verification.SubwordStoreClear.native_values member
  have wrong := values.2.1
  change (0 : ZMod mersenne31Modulus) = 65280 at wrong
  exact (by decide +kernel : (0 : ZMod mersenne31Modulus) ≠ 65280) wrong

/-- The unused field is constrained to the actual native zero output. -/
theorem wrong_unused_rejected :
    ¬ Verification.SubwordStoreClear.table.Contains #[]
      (#v[170, 0, 1] : Vector (ZMod mersenne31Modulus) 3) := by
  intro member
  have values := Verification.SubwordStoreClear.native_values member
  have wrong := values.2.2.1
  change (1 : ZMod mersenne31Modulus) = 0 at wrong
  exact one_ne_zero wrong

end Airbender.Tests.SubwordStoreClear
