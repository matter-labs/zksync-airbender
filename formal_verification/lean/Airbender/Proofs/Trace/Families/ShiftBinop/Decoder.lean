import Airbender.Proofs.Trace.Families.ShiftBinop.Values

namespace Airbender.ShiftBinop.Proofs
open Arithmetic Trace
open Airbender.Trace.Proofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Actual native constraints exclude the complete padding tail. -/
theorem decoded_entries {trace : Data mersenne31Modulus ShiftBinopFamily}
    {setup : SparseDecoderSetup Operation} (accepted : Accepted trace)
    (decoded : Decoded trace setup) :
    ∀ row ∈ trace.rows, ∃ entry ∈ setup.program, row.decoderQuery = entry.query := by
  intro row present
  have native := accepted.constraints row present
  have member := decoded row present
  rw [row_decoder_query] at member
  cases row with
  | mk family w =>
    cases family
    exact sparse_member member (padding_excluded native)

/-- Original public bytes and full native decoding recover actual source entries. -/
theorem decoded_sources {trace : Data mersenne31Modulus ShiftBinopFamily}
    {setup : SparseDecoderSetup Operation} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : Decoded trace setup) :
    ∀ row ∈ trace.rows, ∃ entry ∈ setup.program,
      entry.SourceWith before decoderFields ∧ row.decoderQuery = entry.query := by
  intro row present
  obtain ⟨entry,found,same⟩ := decoded_entries accepted decoded row present
  exact ⟨entry,found,(run_sparse_setup_sources image found).1,same⟩

end Airbender.ShiftBinop.Proofs
