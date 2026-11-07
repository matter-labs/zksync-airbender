import Airbender.Proofs.Trace.Families.ReducedMachine.UnifiedDecoder

namespace Airbender.ReducedMachine.Native
open Trace
set_option autoImplicit false

/-- Original public bytes, stateful Sail decoding and full padded membership
    recover original mixed-profile sources and their exact actual native query fields.
    Fixed ROM/compiler enforcement and initialized execution remain separate. -/
theorem public_unified_decoding {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup UnifiedMode} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat}
    (image : unifiedDecoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted (fixedData trace)) (decoded : UnifiedDecodedTrace (fixedData trace) setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ (fixedData trace).rows) :
    ∃ entry ∈ setup.program, entry.SourceWith before unifiedDecoderFields ∧
      row.decoderQuery = entry.query :=
  NativeUnifiedDecoderProofs.trace_decoding image accepted decoded row present

end Airbender.ReducedMachine.Native
