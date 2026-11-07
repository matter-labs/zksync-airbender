import Airbender.Review.Trace.Families.ReducedMachine.FixedData
import Airbender.Proofs.Trace.Families.ReducedMachine.Decoder
import Airbender.Review.Helpers.Decoder.ReducedMachineUnified
import Airbender.Proofs.ReducedMachine.NativeUnifiedDecoder

namespace Airbender.ReducedMachine.NativeUnifiedDecoderProofs
open Native Trace
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Complete public decoder membership and original bytes derive every actual
    mask/rd/x0 field. No per-row selector, zero flag or source value is given. -/
theorem trace_decoding {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup UnifiedMode} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat}
    (image : unifiedDecoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : UnifiedDecodedTrace trace setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ trace.rows) :
    ∃ entry ∈ setup.program, entry.SourceWith before unifiedDecoderFields ∧
      row.decoderQuery = entry.query := by
  have holds := accepted.constraints row present
  have member := decoded row present
  rw [NativeShiftDecoderProofs.row_query] at member
  cases row with
  | mk family w =>
    cases family
    obtain ⟨entry,found,source,query⟩ := fetched_sources image holds member
    exact ⟨entry,found,source,query⟩

end Airbender.ReducedMachine.NativeUnifiedDecoderProofs
