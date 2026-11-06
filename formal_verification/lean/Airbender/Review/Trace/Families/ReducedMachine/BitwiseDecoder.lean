import Airbender.Proofs.Trace.Families.ReducedMachine.BitwiseDecoder

namespace Airbender.ReducedMachine.Native
open Trace
set_option autoImplicit false

/-- Original public bytes, stateful Sail decoding and full padded membership
    recover the actual bitwise mask and original source/rd/x0/immediate fields.
    Fixed ROM/compiler enforcement and initialized execution remain separate. -/
theorem public_bitwise_decoding {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup BitwiseMode} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat}
    (image : bitwiseDecoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : BitwiseDecodedTrace trace setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ trace.rows) :
    ∃ entry ∈ setup.program, entry.SourceWith before bitwiseDecoderFields ∧
      row.decoderQuery = entry.query ∧ BitwiseDecoded row.assignment entry :=
  NativeBitwiseDecoderProofs.trace_decoding image accepted decoded row present

end Airbender.ReducedMachine.Native
