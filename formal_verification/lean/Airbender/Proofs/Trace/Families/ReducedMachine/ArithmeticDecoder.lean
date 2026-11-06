import Airbender.Proofs.Trace.Families.ReducedMachine.Decoder
import Airbender.Review.Helpers.Decoder.ReducedMachineArithmetic
import Airbender.Proofs.ReducedMachine.NativeArithmeticDecoder

namespace Airbender.ReducedMachine.NativeArithmeticDecoderProofs
open Native Trace
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Complete public decoder membership and original bytes derive every actual
    mask/rd/x0 field. No per-row selector, zero flag or source value is given. -/
theorem trace_decoding {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ArithmeticMode} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat}
    (image : arithmeticDecoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : ArithmeticDecodedTrace trace setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ trace.rows) :
    ∃ entry ∈ setup.program, entry.SourceWith before arithmeticDecoderFields ∧
      row.decoderQuery = entry.query ∧ ArithmeticDecoded row.assignment entry := by
  have holds := accepted.constraints row present
  have member := decoded row present
  rw [NativeShiftDecoderProofs.row_query] at member
  cases row with
  | mk family w =>
    cases family
    obtain ⟨entry,found,source,query⟩ := fetched_sources image holds member
    exact ⟨entry,found,source,query,decoded_fields source.fields query⟩

end Airbender.ReducedMachine.NativeArithmeticDecoderProofs
