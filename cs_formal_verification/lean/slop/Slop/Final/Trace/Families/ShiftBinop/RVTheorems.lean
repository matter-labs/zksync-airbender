import Human.Trace.Families.ShiftBinop.RVTheorems
import Slop.ShiftBinop.RVTraceExecution

namespace Airbender.ShiftBinop

/-- Publicly fetched bitwise/shift/REV8 rows, in native time order, are a run of `RV.step` from the public starting
    state reaching the terminal PC and cell values. -/
theorem rv_trace_soundness : RVTraceSoundnessClaim := by
  intro p _ hp inverse clockInverse trace initial cells program inputs accepted decoded
  exact Proofs.rv_trace_execution hp inverse clockInverse inputs accepted decoded

end Airbender.ShiftBinop
