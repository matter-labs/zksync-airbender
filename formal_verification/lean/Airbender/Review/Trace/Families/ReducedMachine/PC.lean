import Airbender.Proofs.Trace.Families.ReducedMachine.PC

namespace Airbender.ReducedMachine.Native
open Trace
set_option autoImplicit false

/-- Original public shift decoding derives incoming PC bounds/alignment, and
    actual native constraints derive bounded PC+4 with RV32 wraparound. No row
    range, carry, successor or state answer is supplied. This is not fetched
    execution or terminal-machine soundness. The modeled setup remains explicit. -/
theorem public_shift_pc_successor {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ShiftMode} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat}
    (image : shiftDecoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : ShiftDecodedTrace trace setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ trace.rows) :
    ShiftPCSuccessor row.assignment :=
  NativePCProofs.trace_pc_successor image accepted decoded row present

end Airbender.ReducedMachine.Native
