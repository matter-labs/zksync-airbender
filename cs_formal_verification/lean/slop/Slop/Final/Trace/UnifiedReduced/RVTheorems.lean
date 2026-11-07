import Human.Trace.UnifiedReduced.RVTheorems
import Slop.UnifiedReduced.RV.Execution

namespace Airbender.UnifiedReduced

/-- Every admitted unified row, in its history-derived order, is one `RV.step` of our RV32 spec from the public
    starting state; the final PC and every tracked cell match the trace's terminal tokens (ROM shadows read as the
    public bytes). -/
theorem rv_execution_soundness : RVExecutionSoundnessClaim := by
  intro p _ hp clockInverse byteInverse trace initial cells program inputs accepted decoded
  exact Proofs.RV.rv_trace_execution hp clockInverse byteInverse inputs accepted decoded

end Airbender.UnifiedReduced
