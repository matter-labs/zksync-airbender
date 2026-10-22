import HumanSail.Theorems
import Slop.RV.NonVacuous
import Slop.Equiv.Agree

/-! `Airbender.NonVacuousOf`: for any image that fits in ROM, Sail's reset state with the PC at 0 and the image at
address 0 (zero elsewhere), and the inputs of `RV.nonvacuous_of`. -/

open Sail SailRV32 Human Spec

namespace Slop.Equiv

/-- Sail's reset state, PC 0, the image at address 0 and zero elsewhere. -/
noncomputable def imageSail (bytes : Array (BitVec 8)) : SailState :=
  { Airbender.resetState.set .PC 0 with mem := fun a => if h : a < bytes.size then bytes[a] else 0 }

theorem imageSail_assumptions (bytes : Array (BitVec 8)) (hrom : bytes.size ≤ RV.ROM_END) :
    Airbender.Assumptions bytes (imageSail bytes) 0 0 0 0 0 [] := by
  simp only [RV.ROM_END] at hrom
  refine ⟨fun r hr => ?_, by simp, set_regs_self (σ := Airbender.resetState) .PC 0,
    fun i hi => by simp [imageSail, hi], fun a h1 _ => ?_, by decide, by decide, by decide, by decide, by decide⟩
  · exact set_regs_ne Airbender.resetState .PC r 0 (by rintro rfl; cases hr)
  · simp only [RV.ROM_END] at h1
    simp [imageSail, show ¬ a < bytes.size by omega]

/-- The final theorem's assumptions on the Airbender machine can be met, with a right and with a wrong claim and
path. -/
theorem nonvacuous_of (bytes : Array (BitVec 8)) (hrom : bytes.size ≤ RV.ROM_END) : Airbender.NonVacuousOf bytes := by
  obtain ⟨v0, v1, v2, v3, hv⟩ := RV.exists_claim #v[0, 0, 0, 0, 0]
  exact ⟨⟨_, 0, 0, 0, 0, 0, v0, v1, v2, v3, _, [], imageSail_assumptions bytes hrom, hv, RV.pathOK_nil _⟩,
    ⟨_, 0, 0, 0, 0, 0, v0, v1, v2, v3, _, [], imageSail_assumptions bytes hrom, fun h => RV.not_pathOK_nil _ h.2⟩⟩

end Slop.Equiv
