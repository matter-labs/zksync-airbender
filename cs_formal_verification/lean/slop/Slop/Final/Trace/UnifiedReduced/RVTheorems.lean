import Human.Trace.UnifiedReduced.RVTheorems
import Slop.UnifiedReduced.RV.Execution

namespace Airbender.UnifiedReduced

/-- Every admitted unified row, in its history-derived order, is one `RV.step` of our RV32 spec from the public
    starting state; the final PC and every tracked cell match the trace's terminal tokens (ROM shadows read as the
    public bytes). -/
theorem rv_execution_soundness : RVExecutionSoundnessClaim := by
  intro p _ hp clockInverse byteInverse trace initial cells program inits inputs accepted decoded
  exact Proofs.RV.rv_trace_execution hp clockInverse byteInverse inputs accepted decoded

/-- Under the boot inputs every tracked RAM cell of the starting state reads 0: the seeds are the inline
    inits/teardowns sets' zero boot image, and the starting state reads as the seeds. -/
theorem boot_ram_zero : BootRamZeroClaim := by
  intro trace initial cells program inits inputs
  exact Proofs.RV.boot_ram_zero inputs

end Airbender.UnifiedReduced
