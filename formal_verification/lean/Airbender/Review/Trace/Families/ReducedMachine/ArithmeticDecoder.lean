import Airbender.Proofs.Trace.Families.ReducedMachine.ArithmeticDecoder

namespace Airbender.ReducedMachine.Native
open Trace
set_option autoImplicit false

/-- Original public bytes, stateful Sail decoding and full padded membership
    recover the actual arithmetic mask and original source/rd/x0/immediate fields.
    Fixed ROM/compiler enforcement and initialized execution remain separate. -/
theorem public_arithmetic_decoding {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ArithmeticMode} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat}
    (image : arithmeticDecoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : ArithmeticDecodedTrace trace setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ trace.rows) :
    ∃ entry ∈ setup.program, entry.SourceWith before arithmeticDecoderFields ∧
      row.decoderQuery = entry.query ∧ ArithmeticDecoded row.assignment entry :=
  NativeArithmeticDecoderProofs.trace_decoding image accepted decoded row present

end Airbender.ReducedMachine.Native
