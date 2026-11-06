import Airbender.Review.Helpers.Memory.SailHistory
import Airbender.Review.Helpers.Decoder.ReducedMachineBitwise

namespace Airbender.ReducedMachine.Native
open Trace Reference.RiscV.Sail Reference.Sail
set_option autoImplicit false

/-- Original GPR observations and the actual native masked write. All source
    and old-destination reads observe the same pre-state, including aliases. -/
def BitwiseRegisterTransfer (row : Row mersenne31Modulus NativeReducedFamily)
    (entry : BitwiseProgramEntry) (before after : State) : Prop :=
  (∀ i : Fin 3, run (SailRV32.Functions.rX_bits
      (.Regidx (#v[entry.data.rs1,entry.data.rs2,entry.data.rd])[i])) before =
    .ok (memoryWord (importedConstraintsMemoryPorts[i].readCode row.assignment)) before) ∧
  run (SailRV32.Functions.wX_bits (.Regidx entry.data.rd)
    (memoryWord (importedConstraintsMemoryPorts[2].writeCode row.assignment))) before = .ok () after

end Airbender.ReducedMachine.Native
