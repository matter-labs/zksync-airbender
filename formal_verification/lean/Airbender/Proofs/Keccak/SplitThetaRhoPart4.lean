import Airbender.Proofs.Keccak.SplitThetaRhoPart4First
import Airbender.Proofs.Keccak.SplitThetaRhoPart4Second

namespace Airbender.Keccak.Split.Call.Proofs
open Specs.Keccak256
set_option warningAsError true

namespace ThetaRhoPart4

/-- Four split phases match the unchanged original Keccak reference. -/
theorem reference (part : Fin 4) (state : LaneState) :
    logicalLanes (16 + part.val + 1)
      (thetaRhoPhase ⟨16 + part.val, by omega⟩ state) =
      rhoPi (thetaXor (logicalLanes (16 + part.val) state)
        (thetaD (Vector.ofFn fun column : Fin 5 => state ⟨25 + column.val, by omega⟩))) := by
  fin_cases part
  · exact First.reference 0 state
  · exact First.reference 1 state
  · exact Second.reference 0 state
  · exact Second.reference 1 state

end ThetaRhoPart4
end Airbender.Keccak.Split.Call.Proofs
