import Airbender.Proofs.Keccak.SplitChiMemoryEffect
import Airbender.Proofs.Keccak.SplitChiPortEnumeration

namespace Airbender.Keccak.Split.Native.Proofs
open Trace
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

/-- Actual native lane values, padded only in the two slots unused by chi5. -/
def chi5ReferenceLanes (cached writing : Bool) (w : Nat → ZMod babyBearModulus) : Vector Nat 7 :=
  Vector.ofFn fun lane => if active : lane.val < 5 then
    chi5LaneValue cached writing w ⟨lane.val, active⟩ else 0

variable [Fact babyBearModulus.Prime]

/-- The native lane output is exactly the unchanged blessed chi5 reference result. -/
theorem chi5_native_reference_result (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then Chi5Cached.clockConstraints chi5FixedTable else Chi5.clockConstraints chi5FixedTable))
    (index : Fin 361) (kind : kindAt index.val = .chi5) :
    Call.result index (chi5ReferenceLanes cached false w) = chi5ReferenceLanes cached true w := by
  apply Vector.ext
  intro lane bound
  simp only [Call.result, kind, chi5ReferenceLanes, Fin.getElem_fin, Vector.getElem_ofFn]
  by_cases live : lane < 5
  · simp only [dif_pos live]
    have first : (lane + 1) % 5 < 5 := Nat.mod_lt _ (by decide)
    have second : (lane + 2) % 5 < 5 := Nat.mod_lt _ (by decide)
    simp only [dif_pos first, dif_pos second]
    exact (chi5_native_lane_operation cached w holds ⟨lane, live⟩).symm
  · simp only [dif_neg live]

end Airbender.Keccak.Split.Native.Proofs
