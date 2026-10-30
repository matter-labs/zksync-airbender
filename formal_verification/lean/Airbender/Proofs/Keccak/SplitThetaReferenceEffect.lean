import Airbender.Proofs.Keccak.SplitThetaLaneOperation

namespace Airbender.Keccak.Split.Native.Proofs
open Trace
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

/-- All seven actual native theta/rho memory lanes. -/
def thetaReferenceLanes (cached writing : Bool) (w : Nat → ZMod babyBearModulus) : Vector Nat 7 :=
  Vector.ofFn (thetaLaneValue cached writing w)

variable [Fact babyBearModulus.Prime]

/-- The complete actual theta/rho output equals the unchanged blessed call reference. -/
theorem theta_native_reference_result (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable
        else ThetaRho.clockConstraints thetaRhoFixedTable)) (index : Fin 361)
    (kind : kindAt index.val = .thetaRho)
    (flags : ∀ selected : Fin 5, thetaColumnFlag cached w selected = if selected.val = index.val % 5 then 1 else 0)
    (bounds : ∀ limb : Fin 4, (thetaLaneLimb cached false w 6 limb).val < 65536) :
    Call.result index (thetaReferenceLanes cached false w) = thetaReferenceLanes cached true w := by
  let column : Fin 5 := ⟨index.val % 5, Nat.mod_lt _ (by decide)⟩
  have selected : ∀ flag : Fin 5, thetaColumnFlag cached w flag = if flag.val = column.val then 1 else 0 := flags
  simp only [Call.result, kind]
  apply Vector.ext
  intro lane bound
  by_cases live : lane < 5
  · simp only [Vector.getElem_ofFn, live, ↓reduceDIte, thetaReferenceLanes, Fin.getElem_fin]
    exact (theta_native_lane_operation cached w holds column ⟨lane, live⟩ selected bounds).symm
  · have laneIndex : 5 + (lane - 5) = lane := by omega
    have same := theta_readonly_lane cached w ⟨lane - 5, by omega⟩
    simp only [thetaReferenceLanes, Vector.getElem_ofFn, Fin.getElem_fin, live, ↓reduceDIte]
    simpa only [laneIndex] using same.symm

/-- An active native row binds the original theta/rho transition, all physical slots and its full lane result. -/
theorem theta_native_reference_schedule (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable
        else ThetaRho.clockConstraints thetaRhoFixedTable)) (active : w 0 = 1)
    (bounds : ∀ limb : Fin 4, (thetaLaneLimb cached false w 6 limb).val < 65536) :
    ∃ index : Fin 361, kindAt index.val = .thetaRho ∧
      (thetaQueryRow cached w 9)[0] = (controlAt index.val : ZMod babyBearModulus) ∧
      (thetaQueryRow cached w 9)[2] = (bump (controlAt index.val) : ZMod babyBearModulus) ∧
      (∀ lane : Fin 7, (thetaQueryRow cached w 0)[1 + lane.val] =
        ((Call.slots index)[lane.val].val : ZMod babyBearModulus)) ∧
      Call.result index (thetaReferenceLanes cached false w) = thetaReferenceLanes cached true w := by
  obtain ⟨index, kind, before, after, flags⟩ := theta_native_controller_schedule cached w holds active
  exact ⟨index, kind, before, after, theta_native_slots cached w holds active index before,
    theta_native_reference_result cached w holds index kind flags bounds⟩

end Airbender.Keccak.Split.Native.Proofs
