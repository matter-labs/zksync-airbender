import Airbender.Proofs.Trace.Families.ReducedMachine.BranchDecoder

namespace Airbender.ReducedMachine.Native
open Trace
set_option autoImplicit false

/-- Original public bytes, stateful Sail decoding and full padded membership
    recover the actual branch mask and original source/rd/x0/immediate fields.
    Fixed ROM/compiler enforcement and initialized execution remain separate. -/
theorem public_branch_decoding {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup BranchMode} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat}
    (image : branchDecoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : BranchDecodedTrace trace setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ trace.rows) :
    ∃ entry ∈ setup.program, entry.SourceWith before branchDecoderFields ∧
      row.decoderQuery = entry.query ∧ BranchDecoded row.assignment entry :=
  NativeBranchDecoderProofs.trace_decoding image accepted decoded row present

end Airbender.ReducedMachine.Native
