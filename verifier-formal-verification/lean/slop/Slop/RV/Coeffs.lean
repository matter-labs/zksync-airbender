import Slop.RV.PolyLoop
import Slop.RV.Code.COEFFS

/-! Facts about this program's coefficient table (the only place its values are used besides `PolyZMod`). -/

namespace RV

theorem coeffs_length : Code.COEFFS.length = 100 := by decide

theorem coeffs_check : (List.range 100).all (fun i => decide ((Code.COEFFS[i]!).toNat ≤ P)) = true := by
  decide +kernel

theorem coeffs_le (i : Nat) (h : i < Code.COEFFS.length) : (Code.COEFFS[i]).toNat ≤ P := by
  have := List.all_eq_true.mp coeffs_check i (List.mem_range.mpr (coeffs_length ▸ h))
  rw [decide_eq_true_eq, getElem!_pos Code.COEFFS i h] at this
  exact this

end RV
