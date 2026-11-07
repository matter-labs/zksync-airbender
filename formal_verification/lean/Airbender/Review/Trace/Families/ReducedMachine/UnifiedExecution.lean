import Airbender.Review.Trace.Execution
import Airbender.Review.Helpers.Memory.ReducedMachineUnifiedExecution

namespace Airbender.ReducedMachine.Native
open Trace NativeShadow Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem
set_option autoImplicit false

/-- Finite successful original four-byte fetched seven-profile execution and actual
    architectural terminal cells. Independent shadow tokens remain in full
    accepted native matching, not in architectural Sail byte reads. -/
def UnifiedRealizes [MemoryPlatform SailRV32.exception]
    (program : List UnifiedProgramEntry) (trace : Data mersenne31Modulus NativeReducedFamily)
    (initial : State) (cells : List Cell) : Prop :=
  ∃ after, Relation.ReflTransGen (StepWith unifiedDecoderFields unifiedClause program) initial after ∧
    run (SailRV32.Functions.get_arch_pc ()) after = .ok trace.terminal.word.toBitVec after ∧
    ∀ sink ∈ trace.terminalMemory, architecturalAddress sink.address = true →
      ∃ cell ∈ cells, cell.addressCode = sink.address ∧
        cell.read after = .ok sink.word.toBitVec after

end Airbender.ReducedMachine.Native
