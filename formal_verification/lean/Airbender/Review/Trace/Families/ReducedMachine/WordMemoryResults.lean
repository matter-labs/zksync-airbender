import Airbender.Proofs.Trace.Families.ReducedMachine.WordMemoryResults

namespace Airbender.ReducedMachine.Native
open Trace
set_option autoImplicit false

/-- Public seeds/full original decoding and native acceptance derive actual
    effective addresses, ROM/RAM/store writes, port spaces and PC+4/wrap. No read,
    source bound, value, PC, intermediate state or preservation answer is supplied.
    Original memory/ROM-shadow realization and Sail execution remain separate. -/
theorem public_word_memory_results {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup WordMemoryMode} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : wordMemoryDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary (fixedData trace) before cells) (accepted : Accepted (fixedData trace))
    (decoded : WordMemoryDecodedTrace (fixedData trace) setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ (fixedData trace).rows) :
    ∃ entry ∈ setup.program, entry.SourceWith before wordMemoryDecoderFields ∧
      row.decoderQuery = entry.query ∧ WordMemoryDecoded row.assignment entry ∧
      WordMemoryNumericalEffects row.assignment entry :=
  NativeWordMemoryRangeProofs.image_word_memory_results image inputs accepted decoded row present

end Airbender.ReducedMachine.Native
