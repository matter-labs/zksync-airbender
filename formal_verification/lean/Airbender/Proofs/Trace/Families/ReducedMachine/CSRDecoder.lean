import Airbender.Proofs.Trace.Families.ReducedMachine.Decoder
import Airbender.Review.Helpers.Decoder.ReducedMachineCSR
import Airbender.Proofs.ReducedMachine.NativeCSRDecoder
import Airbender.Review.Trace.Families.ReducedMachine.RuntimeCSRData
import Airbender.Review.Circuits.ReducedMachine.RuntimeCSRTheorems

namespace Airbender.ReducedMachine.NativeCSRDecoderProofs
open Native Trace
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Complete public decoder membership and original bytes derive every actual
    mask/rd/x0 field. No per-row selector, zero flag or source value is given. -/
theorem trace_decoding {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup CSRMode} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat}
    (image : csrDecoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : CSRDecodedTrace trace setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ trace.rows) :
    ∃ entry ∈ setup.program, entry.SourceWith before csrDecoderFields ∧
      row.decoderQuery = entry.query ∧ CSRDecoded row.assignment entry := by
  have holds := accepted.constraints row present
  have member := decoded row present
  rw [NativeShiftDecoderProofs.row_query] at member
  cases row with
  | mk family w =>
    cases family
    obtain ⟨entry,found,source,query⟩ := fetched_sources image holds member
    exact ⟨entry,found,source,query,decoded_fields source.fields query⟩

/-- Original public decoding discharges the local CSR mask on the explicitly
    constructed runtime pool; all other acceptance boundaries stay intact. -/
theorem runtime_trace_effects {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup CSRMode} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat}
    (image : csrDecoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted (runtimeCSRData trace)) (decoded : CSRDecodedTrace trace setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ trace.rows) :
    ∃ entry ∈ setup.program, entry.SourceWith before csrDecoderFields ∧
      row.decoderQuery = entry.query ∧ CSRDecoded row.assignment entry ∧
      CSRRuntimeEffects row.assignment := by
  have holds := accepted.constraints row present
  obtain ⟨entry,found,source,query,fields⟩ := trace_decoding image accepted decoded row present
  refine ⟨entry,found,source,query,fields,?_⟩
  cases row with
  | mk family w =>
    cases family
    exact runtime_csr_native_effects holds fields.mask
end Airbender.ReducedMachine.NativeCSRDecoderProofs
