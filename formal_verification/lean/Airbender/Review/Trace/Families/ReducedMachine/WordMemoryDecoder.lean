import Airbender.Proofs.Trace.Families.ReducedMachine.WordMemoryDecoder

namespace Airbender.ReducedMachine.Native
open Trace
set_option autoImplicit false

/-- Original public bytes, stateful Sail decoding and full padded membership
    recover the actual wordMemory mask and original source/rd/x0/immediate fields.
    Fixed ROM/compiler enforcement and initialized execution remain separate. -/
theorem public_word_memory_decoding {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup WordMemoryMode} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat}
    (image : wordMemoryDecoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : WordMemoryDecodedTrace trace setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ trace.rows) :
    ∃ entry ∈ setup.program, entry.SourceWith before wordMemoryDecoderFields ∧
      row.decoderQuery = entry.query ∧ WordMemoryDecoded row.assignment entry :=
  NativeWordMemoryDecoderProofs.trace_decoding image accepted decoded row present

end Airbender.ReducedMachine.Native
