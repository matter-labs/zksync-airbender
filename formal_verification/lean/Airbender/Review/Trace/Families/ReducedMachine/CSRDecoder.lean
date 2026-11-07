import Airbender.Proofs.Trace.Families.ReducedMachine.CSRDecoder

namespace Airbender.ReducedMachine.Native
open Trace
set_option autoImplicit false

/-- Original public bytes, stateful Sail decoding and full padded membership
    recover actual CSR mask, raw operands, rd/x0 and unsigned CSR index.
    Fixed ROM/compiler enforcement and initialized execution remain separate. -/
theorem public_csr_decoding {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup CSRMode} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat}
    (image : csrDecoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : CSRDecodedTrace trace setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ trace.rows) :
    ∃ entry ∈ setup.program, entry.SourceWith before csrDecoderFields ∧
      row.decoderQuery = entry.query ∧ CSRDecoded row.assignment entry :=
  NativeCSRDecoderProofs.trace_decoding image accepted decoded row present

/-- Public original CSR decoding supplies the local mask for the constructed
    runtime pool. This is not initialized execution, clock issuance or fulfillment. -/
theorem public_runtime_csr_effects {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup CSRMode} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat}
    (image : csrDecoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted (runtimeCSRData trace)) (decoded : CSRDecodedTrace trace setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ trace.rows) :
    ∃ entry ∈ setup.program, entry.SourceWith before csrDecoderFields ∧
      row.decoderQuery = entry.query ∧ CSRDecoded row.assignment entry ∧
      CSRRuntimeEffects row.assignment :=
  NativeCSRDecoderProofs.runtime_trace_effects image accepted decoded row present
end Airbender.ReducedMachine.Native
