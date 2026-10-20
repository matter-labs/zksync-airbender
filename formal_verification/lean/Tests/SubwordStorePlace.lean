import Airbender.Review.Helpers.Tables.SubwordStorePlaceTheorems

namespace Airbender.Tests.SubwordStorePlace
open Verification
set_option autoImplicit false

/-- Complete actual native placement rows retain their original table tag. -/
theorem complete_native_rows (key : Fin 2097152) :
    NativeSubwordStorePlace.data.rowNat key = (Verification.SubwordStorePlace.row key).push 55 := by
  exact Airbender.SubwordMemory.StorePlaceProofs.native_store_place_rows key

theorem zero_limb :
    NativeSubwordStorePlace.data.rowNat ⟨0, by decide⟩ = #v[0, 0, 0, 55] := by
  rw [Airbender.SubwordMemory.StorePlaceProofs.native_store_place_rows]
  decide +kernel

theorem low_byte_placed :
    NativeSubwordStorePlace.data.rowNat ⟨255, by decide⟩ = #v[255, 255, 0, 55] := by
  rw [Airbender.SubwordMemory.StorePlaceProofs.native_store_place_rows]
  decide +kernel

theorem high_source_byte_ignored :
    NativeSubwordStorePlace.data.rowNat ⟨65280, by decide⟩ = #v[65280, 0, 0, 55] := by
  rw [Airbender.SubwordMemory.StorePlaceProofs.native_store_place_rows]
  decide +kernel

theorem all_bits_even :
    NativeSubwordStorePlace.data.rowNat ⟨65535, by decide⟩ = #v[65535, 255, 0, 55] := by
  rw [Airbender.SubwordMemory.StorePlaceProofs.native_store_place_rows]
  decide +kernel

theorem all_bits_odd :
    NativeSubwordStorePlace.data.rowNat ⟨131071, by decide⟩ = #v[131071, 65280, 0, 55] := by
  rw [Airbender.SubwordMemory.StorePlaceProofs.native_store_place_rows]
  decide +kernel

theorem zero_low_byte_odd :
    NativeSubwordStorePlace.data.rowNat ⟨130816, by decide⟩ = #v[130816, 0, 0, 55] := by
  rw [Airbender.SubwordMemory.StorePlaceProofs.native_store_place_rows]
  decide +kernel

theorem offset_two :
    NativeSubwordStorePlace.data.rowNat ⟨175053, by decide⟩ = #v[175053, 205, 0, 55] := by
  rw [Airbender.SubwordMemory.StorePlaceProofs.native_store_place_rows]
  decide +kernel

theorem offset_three :
    NativeSubwordStorePlace.data.rowNat ⟨240589, by decide⟩ = #v[240589, 52480, 0, 55] := by
  rw [Airbender.SubwordMemory.StorePlaceProofs.native_store_place_rows]
  decide +kernel

theorem halfword_full_limb :
    NativeSubwordStorePlace.data.rowNat ⟨327679, by decide⟩ = #v[327679, 65535, 0, 55] := by
  rw [Airbender.SubwordMemory.StorePlaceProofs.native_store_place_rows]
  decide +kernel

theorem halfword_odd_key :
    NativeSubwordStorePlace.data.rowNat ⟨371661, by decide⟩ = #v[371661, 43981, 0, 55] := by
  rw [Airbender.SubwordMemory.StorePlaceProofs.native_store_place_rows]
  decide +kernel

theorem word_zero :
    NativeSubwordStorePlace.data.rowNat ⟨589823, by decide⟩ = #v[589823, 0, 0, 55] := by
  rw [Airbender.SubwordMemory.StorePlaceProofs.native_store_place_rows]
  decide +kernel

theorem unused_key_zero :
    NativeSubwordStorePlace.data.rowNat ⟨2097151, by decide⟩ = #v[2097151, 0, 0, 55] := by
  rw [Airbender.SubwordMemory.StorePlaceProofs.native_store_place_rows]
  decide +kernel

theorem wrong_placed_rejected :
    ¬ Verification.SubwordStorePlace.table.Contains #[]
      (#v[131071, 255, 0] : Vector (ZMod mersenne31Modulus) 3) := by
  intro member
  have values := Verification.SubwordStorePlace.native_values member
  have wrong := values.2.1
  change (255 : ZMod mersenne31Modulus) = 65280 at wrong
  exact (by decide +kernel : (255 : ZMod mersenne31Modulus) ≠ 65280) wrong

theorem wrong_unused_rejected :
    ¬ Verification.SubwordStorePlace.table.Contains #[]
      (#v[170, 170, 1] : Vector (ZMod mersenne31Modulus) 3) := by
  intro member
  have values := Verification.SubwordStorePlace.native_values member
  have wrong := values.2.2.1
  change (1 : ZMod mersenne31Modulus) = 0 at wrong
  exact one_ne_zero wrong

end Airbender.Tests.SubwordStorePlace
