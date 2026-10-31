import Airbender.Proofs.FullUnsigned.ParityOutputIntervals

namespace Airbender.Setup.SourceCaptureParityProofs.OutputGroup16
open Airbender.Setup.Proofs OutputIntervals
set_option warningAsError true
set_option Elab.async false
-- The final bounded interval retains the original output formula.
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private theorem part0 : IntervalFact 65 := by
  constructor
  · decide +kernel
  · decide +kernel

/-- Every interval in this source partition group is kernel checked. -/
theorem facts (index : Fin 1) : IntervalFact (1 + 64 + index.val) := by
  fin_cases index
  · exact part0

end Airbender.Setup.SourceCaptureParityProofs.OutputGroup16
