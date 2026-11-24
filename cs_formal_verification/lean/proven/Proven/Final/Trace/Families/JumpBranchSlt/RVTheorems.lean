module
public import Human.Trace.Families.JumpBranchSlt.RVTheorems
public import Proven.JumpBranchSlt.RVTraceExecution
public import Proven.Final.Generic.Trace.Families.JumpBranchSlt.RVTheorems
public import Proven.Field.BabyBearInstance

@[expose] public section

namespace Airbender.JumpBranchSlt

/-- Accepted comparison, branch and jump rows, in native time order, are a run of `RV.step` from the public starting
    state reaching the terminal PC and register/cell values. -/
private theorem rv_trace_soundness_generic : RVTraceSoundnessClaimGeneric := by
  intro p _ hp inverse trace initial cells program inputs accepted decoded
  exact Proofs.rv_trace_execution hp inverse inputs accepted decoded

theorem rv_trace_soundness : RVTraceSoundnessClaim := by babybear_instance rv_trace_soundness_generic

end Airbender.JumpBranchSlt
