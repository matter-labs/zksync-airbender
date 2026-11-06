import Airbender.Proofs.Trace.Families.ReducedMachine.Decoder

namespace Airbender.ReducedMachine.Native
open Trace
set_option autoImplicit false

/-- Original public bytes, stateful Sail decoding and full padded membership
    recover the actual shift mask and original source/rd/x0/immediate fields.
    Fixed ROM/compiler enforcement and initialized execution remain separate. -/
theorem public_shift_decoding {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ShiftMode} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat}
    (image : shiftDecoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : ShiftDecodedTrace trace setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ trace.rows) :
    ∃ entry ∈ setup.program, entry.SourceWith before shiftDecoderFields ∧
      row.decoderQuery = entry.query ∧ ShiftDecoded row.assignment entry :=
  NativeShiftDecoderProofs.trace_decoding image accepted decoded row present

end Airbender.ReducedMachine.Native
