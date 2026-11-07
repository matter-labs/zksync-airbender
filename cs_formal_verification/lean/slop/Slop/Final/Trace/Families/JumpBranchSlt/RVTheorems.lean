import Human.Trace.Families.JumpBranchSlt.RVTheorems
import Slop.JumpBranchSlt.RVTraceExecution

namespace Airbender.JumpBranchSlt

/-- Accepted comparison, branch and jump rows, in native time order, are a run of `RV.step` from the public starting
    state reaching the terminal PC and register/cell values. -/
theorem rv_trace_soundness : RVTraceSoundnessClaim := by
  intro p _ hp inverse trace initial cells program inputs accepted decoded
  exact Proofs.rv_trace_execution hp inverse inputs accepted decoded

end Airbender.JumpBranchSlt
