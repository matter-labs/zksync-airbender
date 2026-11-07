import Airbender.Proofs.Trace.Families.ReducedMachine.JumpDecoder

namespace Airbender.ReducedMachine.Native
open Trace
set_option autoImplicit false

/-- Original public bytes, stateful Sail decoding and full padded membership
    recover the actual jump mask and original source/rd/x0/immediate fields.
    Fixed ROM/compiler enforcement and initialized execution remain separate. -/
theorem public_jump_decoding {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup JumpMode} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat}
    (image : jumpDecoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : JumpDecodedTrace trace setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ trace.rows) :
    ∃ entry ∈ setup.program, entry.SourceWith before jumpDecoderFields ∧
      row.decoderQuery = entry.query ∧ JumpDecoded row.assignment entry :=
  NativeJumpDecoderProofs.trace_decoding image accepted decoded row present

end Airbender.ReducedMachine.Native
