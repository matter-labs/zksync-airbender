import Airbender.Proofs.Keccak.SplitLayout
import Airbender.Proofs.Keccak.DeferredIota
import Airbender.Proofs.Keccak.LayoutReduction

namespace Airbender.Keccak.Split.Call.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Call 360 applies the last original iota constant to the final lane layout. -/
theorem final_iota_reference (state : LaneState) :
    logicalLanes 24 (microStep 360 state) =
      iota (logicalLanes 24 state) roundConstants[23] := by
  apply Vector.ext
  intro lane bound
  interval_cases lane <;> rfl'

/-- The twenty-four Pi renamings return to the original logical lane layout. -/
theorem logical_final_layout (state : LaneState) : logicalLanes 24 state = logicalLanes 0 state := by
  apply Vector.ext
  intro lane bound
  simp only [logicalLanes, Vector.getElem_ofFn, Airbender.Keccak.Proofs.physical_cached]
  rfl

end Airbender.Keccak.Split.Call.Proofs
