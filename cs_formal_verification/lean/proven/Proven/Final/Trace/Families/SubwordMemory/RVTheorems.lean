module
public import Human.Trace.Families.SubwordMemory.RVTheorems
public import Proven.SubwordMemory.RVTraceExecution
public import Proven.Final.Generic.Trace.Families.SubwordMemory.RVTheorems
public import Proven.Field.BabyBearInstance

@[expose] public section

namespace Airbender.SubwordMemory

/-- RAM LB/LBU/LH/LHU/SB/SH rows, in native time order, are a run of `RV.step` from the public starting state
    reaching the terminal PC and cell values. -/
private theorem rv_ram_trace_soundness_generic : RVRamTraceSoundnessClaimGeneric := by
  intro p _ hp inverse trace initial cells program inputs accepted decoded
  exact Proofs.rv_ram_trace_execution hp inverse inputs accepted decoded

theorem rv_ram_trace_soundness : RVRamTraceSoundnessClaim := by babybear_instance rv_ram_trace_soundness_generic

end Airbender.SubwordMemory
