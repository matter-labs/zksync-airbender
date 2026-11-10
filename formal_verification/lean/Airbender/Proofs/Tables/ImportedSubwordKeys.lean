import Airbender.Data.Tables.SubwordData
import Mathlib.Tactic.FinCases

namespace Airbender.Verification.SubwordFixed
open Setup
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

private theorem constant_get (length value n : Nat) (bound : n < length) :
    (Column.mk #[.affine length value 0]).get? n = some value := by
  simp [Column.get?, getFromBlocks, Block.get?, Block.length, bound]

theorem fixed_key (kind : Fin 4) (n : Nat) (bound : n < (subwordFixedData kind).length) :
    (subwordFixedData kind).columns[0].get? n = some n := by
  have shape : (subwordFixedData kind).columns[0] =
      Column.mk #[.affine (subwordFixedData kind).length 0 1] := by
    fin_cases kind <;> rfl
  rw [shape]
  simp [Column.get?, getFromBlocks, Block.get?, Block.length, bound]

theorem fixed_padding (kind : Fin 4) (lane : Fin 5) (n : Nat)
    (bound : n < (subwordFixedData kind).length) :
    (subwordFixedData kind).columns[lane.val + 3].get? n = some 0 := by
  have shape : (subwordFixedData kind).columns[lane.val + 3] =
      Column.mk #[.affine (subwordFixedData kind).length 0 0] := by
    fin_cases kind <;> fin_cases lane <;> rfl
  rw [shape]
  exact constant_get _ _ _ bound

theorem store_high (kind : Fin 2) (n : Nat) (bound : n < 131072) :
    (#v[storePlaceData, storeClearData][kind]).columns[2].get? n = some 0 := by
  have shape : (#v[storePlaceData, storeClearData][kind]).columns[2] =
      Column.mk #[.affine 131072 0 0] := by fin_cases kind <;> rfl
  rw [shape]
  exact constant_get _ _ _ bound

theorem fixed_tag (kind : Fin 4) (n : Nat) (bound : n < (subwordFixedData kind).length) :
    (subwordFixedData kind).columns[8].get? n = some (subwordFixedRegion kind).id := by
  have shape : (subwordFixedData kind).columns[8] =
      Column.mk #[.affine (subwordFixedData kind).length (subwordFixedRegion kind).id 0] := by
    fin_cases kind <;> rfl
  rw [shape]
  exact constant_get _ _ _ bound

theorem fixed_geometry (kind : Fin 4) :
    (subwordFixedData kind).offset = 0 ∧
      (subwordFixedData kind).length = (subwordFixedRegion kind).length := by
  fin_cases kind <;> exact ⟨rfl, rfl⟩

end Airbender.Verification.SubwordFixed
