module
public import Human.Trace.Families.SubwordMemory.RVTheorems
public import Slop.SubwordMemory.RVTraceExecution

@[expose] public section

namespace Airbender.SubwordMemory

/-- RAM LB/LBU/LH/LHU/SB/SH rows, in native time order, are a run of `RV.step` from the public starting state
    reaching the terminal PC and cell values. -/
theorem rv_ram_trace_soundness : RVRamTraceSoundnessClaim := by
  intro p _ hp inverse trace initial cells program inputs accepted decoded
  exact Proofs.rv_ram_trace_execution hp inverse inputs accepted decoded

end Airbender.SubwordMemory
