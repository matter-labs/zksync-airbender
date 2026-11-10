module
public import Human.Trace.Families.ShiftBinop.RVTheorems
public import Slop.ShiftBinop.RVTraceExecution
public import Slop.Final.Generic.Trace.Families.ShiftBinop.RVTheorems
public import Slop.Field.BabyBearInstance

@[expose] public section

namespace Airbender.ShiftBinop

/-- Publicly fetched bitwise/shift/REV8 rows, in native time order, are a run of `RV.step` from the public starting
    state reaching the terminal PC and cell values. -/
private theorem rv_trace_soundness_generic : RVTraceSoundnessClaimGeneric := by
  intro p _ hp inverse clockInverse trace initial cells program inputs accepted decoded
  exact Proofs.rv_trace_execution hp inverse clockInverse inputs accepted decoded

theorem rv_trace_soundness : RVTraceSoundnessClaim := by babybear_instance rv_trace_soundness_generic

end Airbender.ShiftBinop
