import Airbender.Proofs.ReducedMachine.NativePC
import Airbender.Proofs.Trace.Families.ReducedMachine.Decoder

namespace Airbender.ReducedMachine.NativePCProofs
open Native Trace
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Public byte/stateful decoding and actual accepted native equations alone
    derive every selected row's canonical/aligned input and bounded RV32 PC+4. -/
theorem trace_pc_successor {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ShiftMode} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat}
    (image : shiftDecoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : ShiftDecodedTrace trace setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ trace.rows) :
    ShiftPCSuccessor row.assignment := by
  have native := accepted.constraints row present
  have member := decoded row present
  rw [NativeShiftDecoderProofs.row_query] at member
  cases row with
  | mk family w => cases family; exact decoded_pc_successor image native member

end Airbender.ReducedMachine.NativePCProofs
