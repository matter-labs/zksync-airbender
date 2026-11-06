import Airbender.Review.Helpers.Decoder.ReducedMachine
import Airbender.Proofs.ReducedMachine.NativeShiftDecoder

namespace Airbender.ReducedMachine.NativeShiftDecoderProofs
open Native Trace
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem row_query (row : Row mersenne31Modulus NativeReducedFamily) :
    row.decoderQuery = decoderQuery row.assignment := by
  cases row with
  | mk family w => cases family; rfl

/-- Complete public decoder membership and original bytes derive every actual
    mask/rd/x0 field. No per-row selector, zero flag or source value is given. -/
theorem trace_decoding {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ShiftMode} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat}
    (image : shiftDecoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : ShiftDecodedTrace trace setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ trace.rows) :
    ∃ entry ∈ setup.program, entry.SourceWith before shiftDecoderFields ∧
      row.decoderQuery = entry.query ∧ ShiftDecoded row.assignment entry := by
  have holds := accepted.constraints row present
  have member := decoded row present
  rw [row_query] at member
  cases row with
  | mk family w =>
    cases family
    obtain ⟨entry,found,source,query⟩ := fetched_sources image holds member
    exact ⟨entry,found,source,query,decoded_fields source.fields query⟩

end Airbender.ReducedMachine.NativeShiftDecoderProofs
