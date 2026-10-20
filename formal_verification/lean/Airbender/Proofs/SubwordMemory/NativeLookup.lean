import Airbender.Review.Circuits.SubwordMemory.Tables.Native
import Airbender.Proofs.Mersenne31

namespace Airbender.SubwordMemory.NativeLookupProofs
open Verification
set_option autoImplicit false

theorem zero_region (rom : WordROM) (i : Fin 1) :
    (NativeSubwordLookup.table (p := mersenne31Modulus) rom).Contains #[]
      (NativeBinary.dataZero.row i) := by
  have hi : i.val < 1 := i.isLt
  refine ⟨⟨i.val, by change i.val < 9502721; omega⟩, ?_⟩
  change (NativeBinary.dataZero.rowNat i).map Nat.cast =
    (NativeSubwordLookup.rowNat rom ⟨i.val, _⟩).map Nat.cast
  have selected : i.val < 1 := by omega
  rw [NativeSubwordLookup.rowNat, dif_pos selected]
  cases i
  rfl

theorem separator_region (rom : WordROM) (i : Fin 65536) :
    (NativeSubwordLookup.table (p := mersenne31Modulus) rom).Contains #[]
      (((romSeparatorRow i).map Nat.cast).push 23) := by
  have hi : i.val < 65536 := i.isLt
  refine ⟨⟨i.val + 1, by change i.val + 1 < 9502721; omega⟩, ?_⟩
  change ((romSeparatorRow i).map Nat.cast).push 23 =
    (NativeSubwordLookup.rowNat rom ⟨i.val + 1, _⟩).map Nat.cast
  have h0 : ¬ i.val + 1 < 1 := by omega
  have selected : i.val + 1 < 65537 := by omega
  rw [NativeSubwordLookup.rowNat, dif_neg h0, dif_pos selected]
  simp only [Nat.add_sub_cancel_right, Vector.map_push, Nat.cast_ofNat]

theorem offset_region (rom : WordROM) (i : Fin 2097152) :
    (NativeSubwordLookup.table (p := mersenne31Modulus) rom).Contains #[]
      (NativeSubwordOffset.data.row i) := by
  have hi : i.val < 2097152 := i.isLt
  refine ⟨⟨i.val + 65537, by change i.val + 65537 < 9502721; omega⟩, ?_⟩
  change (NativeSubwordOffset.data.rowNat i).map Nat.cast =
    (NativeSubwordLookup.rowNat rom ⟨i.val + 65537, _⟩).map Nat.cast
  have h0 : ¬ i.val + 65537 < 1 := by omega
  have h1 : ¬ i.val + 65537 < 65537 := by omega
  have selected : i.val + 65537 < 2162689 := by omega
  rw [NativeSubwordLookup.rowNat, dif_neg h0, dif_neg h1, dif_pos selected]
  simp only [Nat.add_sub_cancel_right]
  cases i
  rfl

theorem load_region (rom : WordROM) (i : Fin 2097152) :
    (NativeSubwordLookup.table (p := mersenne31Modulus) rom).Contains #[]
      (NativeSubwordLoad.data.row i) := by
  have hi : i.val < 2097152 := i.isLt
  refine ⟨⟨i.val + 2162689, by change i.val + 2162689 < 9502721; omega⟩, ?_⟩
  change (NativeSubwordLoad.data.rowNat i).map Nat.cast =
    (NativeSubwordLookup.rowNat rom ⟨i.val + 2162689, _⟩).map Nat.cast
  have h0 : ¬ i.val + 2162689 < 1 := by omega
  have h1 : ¬ i.val + 2162689 < 65537 := by omega
  have h2 : ¬ i.val + 2162689 < 2162689 := by omega
  have selected : i.val + 2162689 < 4259841 := by omega
  rw [NativeSubwordLookup.rowNat, dif_neg h0, dif_neg h1, dif_neg h2, dif_pos selected]
  simp only [Nat.add_sub_cancel_right]
  cases i
  rfl

theorem rom_region (rom : WordROM) (i : Fin 1048576) :
    (NativeSubwordLookup.table (p := mersenne31Modulus) rom).Contains #[]
      (((rom.alignedRow i).map Nat.cast).push 46) := by
  have hi : i.val < 1048576 := i.isLt
  refine ⟨⟨i.val + 4259841, by change i.val + 4259841 < 9502721; omega⟩, ?_⟩
  change ((rom.alignedRow i).map Nat.cast).push 46 =
    (NativeSubwordLookup.rowNat rom ⟨i.val + 4259841, _⟩).map Nat.cast
  have h0 : ¬ i.val + 4259841 < 1 := by omega
  have h1 : ¬ i.val + 4259841 < 65537 := by omega
  have h2 : ¬ i.val + 4259841 < 2162689 := by omega
  have h3 : ¬ i.val + 4259841 < 4259841 := by omega
  have selected : i.val + 4259841 < 5308417 := by omega
  rw [NativeSubwordLookup.rowNat, dif_neg h0, dif_neg h1, dif_neg h2, dif_neg h3, dif_pos selected]
  simp only [Nat.add_sub_cancel_right, Vector.map_push, Nat.cast_ofNat]

theorem store_clear_region (rom : WordROM) (i : Fin 2097152) :
    (NativeSubwordLookup.table (p := mersenne31Modulus) rom).Contains #[]
      (NativeSubwordStoreClear.data.row i) := by
  have hi : i.val < 2097152 := i.isLt
  refine ⟨⟨i.val + 5308417, by change i.val + 5308417 < 9502721; omega⟩, ?_⟩
  change (NativeSubwordStoreClear.data.rowNat i).map Nat.cast =
    (NativeSubwordLookup.rowNat rom ⟨i.val + 5308417, _⟩).map Nat.cast
  have h0 : ¬ i.val + 5308417 < 1 := by omega
  have h1 : ¬ i.val + 5308417 < 65537 := by omega
  have h2 : ¬ i.val + 5308417 < 2162689 := by omega
  have h3 : ¬ i.val + 5308417 < 4259841 := by omega
  have h4 : ¬ i.val + 5308417 < 5308417 := by omega
  have selected : i.val + 5308417 < 7405569 := by omega
  rw [NativeSubwordLookup.rowNat, dif_neg h0, dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4, dif_pos selected]
  simp only [Nat.add_sub_cancel_right]
  cases i
  rfl

theorem store_place_region (rom : WordROM) (i : Fin 2097152) :
    (NativeSubwordLookup.table (p := mersenne31Modulus) rom).Contains #[]
      (NativeSubwordStorePlace.data.row i) := by
  have hi : i.val < 2097152 := i.isLt
  refine ⟨⟨i.val + 7405569, by change i.val + 7405569 < 9502721; omega⟩, ?_⟩
  change (NativeSubwordStorePlace.data.rowNat i).map Nat.cast =
    (NativeSubwordLookup.rowNat rom ⟨i.val + 7405569, _⟩).map Nat.cast
  have h0 : ¬ i.val + 7405569 < 1 := by omega
  have h1 : ¬ i.val + 7405569 < 65537 := by omega
  have h2 : ¬ i.val + 7405569 < 2162689 := by omega
  have h3 : ¬ i.val + 7405569 < 4259841 := by omega
  have h4 : ¬ i.val + 7405569 < 5308417 := by omega
  have h5 : ¬ i.val + 7405569 < 7405569 := by omega
  rw [NativeSubwordLookup.rowNat, dif_neg h0, dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4, dif_neg h5]
  simp only [Nat.add_sub_cancel_right]
  cases i
  rfl

end Airbender.SubwordMemory.NativeLookupProofs
