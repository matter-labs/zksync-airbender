import Airbender.Proofs.SubwordMemory.NativeRegions
import Airbender.Proofs.SubwordMemory.Offset
import Airbender.Proofs.SubwordMemory.Load
import Airbender.Proofs.SubwordMemory.StoreClear
import Airbender.Proofs.SubwordMemory.StorePlace
import Mathlib.Tactic.IntervalCases

namespace Airbender.SubwordMemory.NativeLookupProofs
open Verification
set_option autoImplicit false

private theorem pushed_membership {n : Nat}
    (rows : Fin n → Vector (ZMod mersenne31Modulus) 3)
    (query : Vector (ZMod mersenne31Modulus) 3) (tag : ZMod mersenne31Modulus) :
    (∃ i, query.push tag = (rows i).push tag) ↔ ∃ i, query = rows i := by
  constructor
  · rintro ⟨i, same⟩
    refine ⟨i, ?_⟩
    apply Vector.ext
    intro lane bound
    have selected := congrArg (fun v : Vector (ZMod mersenne31Modulus) 4 => v[lane]) same
    simpa only [Vector.getElem_push, bound, ↓reduceDIte] using selected
  · rintro ⟨i, rfl⟩
    exact ⟨i, rfl⟩

theorem separator_membership (rom : WordROM) (query : Vector (ZMod mersenne31Modulus) 3) :
    (NativeSubwordLookup.table rom).Contains #[] (query.push 23) ↔
      romSeparatorTable.Contains #[] query := by
  rw [show (23 : ZMod mersenne31Modulus) = Region.separator.tag by rfl,
    selected_membership]
  exact pushed_membership _ _ _

theorem offset_membership (rom : WordROM) (query : Vector (ZMod mersenne31Modulus) 3) :
    (NativeSubwordLookup.table rom).Contains #[] (query.push 44) ↔
      SubwordOffset.table.Contains #[] query :=
  (selected_membership rom .offset query).trans (Proofs.offset_lookup query).symm

theorem load_membership (rom : WordROM) (query : Vector (ZMod mersenne31Modulus) 3) :
    (NativeSubwordLookup.table rom).Contains #[] (query.push 45) ↔
      SubwordLoad.table.Contains #[] query :=
  (selected_membership rom .load query).trans (LoadProofs.load_lookup query).symm

theorem rom_membership (rom : WordROM) (query : Vector (ZMod mersenne31Modulus) 3) :
    (NativeSubwordLookup.table rom).Contains #[] (query.push 46) ↔
      (romAlignedWordTable rom).Contains #[] query := by
  rw [show (46 : ZMod mersenne31Modulus) = Region.rom.tag by rfl, selected_membership]
  exact pushed_membership _ _ _

theorem store_clear_membership (rom : WordROM) (query : Vector (ZMod mersenne31Modulus) 3) :
    (NativeSubwordLookup.table rom).Contains #[] (query.push 54) ↔
      SubwordStoreClear.table.Contains #[] query :=
  (selected_membership rom .storeClear query).trans (StoreClearProofs.store_clear_lookup query).symm

theorem store_place_membership (rom : WordROM) (query : Vector (ZMod mersenne31Modulus) 3) :
    (NativeSubwordLookup.table rom).Contains #[] (query.push 55) ↔
      SubwordStorePlace.table.Contains #[] query :=
  (selected_membership rom .storePlace query).trans (StorePlaceProofs.store_place_lookup query).symm

/-- A native disabled query is exactly the existing all-zero row. -/
theorem zero_membership (rom : WordROM) (query : Vector (ZMod mersenne31Modulus) 3) :
    (NativeSubwordLookup.table rom).Contains #[] (query.push 0) ↔
      query = #v[0,0,0] := by
  have membership := selected_membership rom .zero query
  simp only [Region.tag, Nat.cast_zero] at membership
  rw [membership]
  constructor
  · rintro ⟨i, same⟩
    have hi : i = ⟨0, by decide⟩ := by
      apply Fin.ext
      change i.val = 0
      have bound : i.val < 1 := i.isLt
      omega
    subst i
    have actual : (NativeBinary.dataZero.row ⟨0, by decide⟩ : Vector (ZMod mersenne31Modulus) 4) =
        #v[0,0,0,0] := by decide +kernel
    change query.push 0 = NativeBinary.dataZero.row ⟨0, _⟩ at same
    rw [actual] at same
    ext lane bound
    have selected := congrArg (fun v : Vector (ZMod mersenne31Modulus) 4 => v[lane]) same
    interval_cases lane <;> simpa using selected
  · rintro rfl
    refine ⟨⟨0, by decide⟩, ?_⟩
    change #v[0,0,0,0] = NativeBinary.dataZero.row ⟨0, _⟩
    decide +kernel

end Airbender.SubwordMemory.NativeLookupProofs
