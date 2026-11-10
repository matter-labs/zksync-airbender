import Airbender.Proofs.FullUnsigned.ParityOutputIntervals

namespace Airbender.Setup.SourceCaptureParityProofs.OutputGroup7
open Airbender.Setup.Proofs OutputIntervals
set_option warningAsError true
set_option Elab.async false
-- Four bounded intervals retain the original output formula.
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private theorem part0 : IntervalFact 29 := by
  constructor
  · decide +kernel
  · decide +kernel

private theorem part1 : IntervalFact 30 := by
  constructor
  · decide +kernel
  · decide +kernel

private theorem part2 : IntervalFact 31 := by
  constructor
  · decide +kernel
  · decide +kernel

private theorem part3 : IntervalFact 32 := by
  constructor
  · decide +kernel
  · decide +kernel

/-- Every interval in this source partition group is kernel checked. -/
theorem facts (index : Fin 4) : IntervalFact (1 + 28 + index.val) := by
  fin_cases index
  · exact part0
  · exact part1
  · exact part2
  · exact part3

end Airbender.Setup.SourceCaptureParityProofs.OutputGroup7
