module
public import Human.Trace.UnifiedReduced.RVTheorems
public import Slop.UnifiedReduced.RV.Execution
public import Slop.Final.Generic.Trace.UnifiedReduced.RVTheorems
public import Slop.Field.BabyBearInstance

@[expose] public section

namespace Airbender.UnifiedReduced

/-- Every admitted unified row, in its history-derived order, is one `RV.step` of our RV32 spec from the public
    starting state; the final PC and every tracked cell match the trace's terminal tokens (ROM shadows read as the
    public bytes). -/
private theorem rv_execution_soundness_generic : RVExecutionSoundnessClaimGeneric := by
  intro p _ hp clockInverse byteInverse trace initial cells program inits inputs accepted decoded
  exact Proofs.RV.rv_trace_execution hp clockInverse byteInverse inputs accepted decoded

theorem rv_execution_soundness : RVExecutionSoundnessClaim := by babybear_instance rv_execution_soundness_generic

/-- Under the boot inputs every tracked RAM cell of the starting state reads 0: the seeds are the inline
    inits/teardowns sets' zero boot image, and the starting state reads as the seeds. -/
theorem boot_ram_zero : BootRamZeroClaim := by
  intro trace initial cells program inits inputs
  exact Proofs.RV.boot_ram_zero inputs

end Airbender.UnifiedReduced
