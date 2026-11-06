import Airbender.Proofs.Trace.Families.ReducedMachine.ComparisonDecoder

namespace Airbender.ReducedMachine.Native
open Trace
set_option autoImplicit false

/-- Original public bytes, stateful Sail decoding and full padded membership
    recover the actual comparison mask and original source/rd/x0/immediate fields.
    Fixed ROM/compiler enforcement and initialized execution remain separate. -/
theorem public_comparison_decoding {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ComparisonMode} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat}
    (image : comparisonDecoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : ComparisonDecodedTrace trace setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ trace.rows) :
    ∃ entry ∈ setup.program, entry.SourceWith before comparisonDecoderFields ∧
      row.decoderQuery = entry.query ∧ ComparisonDecoded row.assignment entry :=
  NativeComparisonDecoderProofs.trace_decoding image accepted decoded row present

end Airbender.ReducedMachine.Native
