import Airbender.Proofs.Trace.Families.ShiftBinop.Values
import Airbender.Proofs.ShiftBinop.Results

namespace Airbender.ShiftBinop.Proofs
open Arithmetic Trace Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Original public decoding and initialized native history derive all six
    whole numerical operations, including exact actual discarded x0 writes. -/
theorem initialized_results {trace : Data mersenne31Modulus ShiftBinopFamily}
    {setup : SparseDecoderSetup Operation} {before : Reference.RiscV.Sail.State}
    {cells : List Cell} {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup) :
    ∀ row ∈ trace.rows, ∃ entry ∈ setup.program,
      entry.SourceWith before decoderFields ∧ row.decoderQuery = entry.query ∧
      selectedWord row.assignment = Word.ofBitVec
        (entry.data.family.result (left row.assignment) (right row.assignment)) ∧
      writtenWord row.assignment = if entry.data.rd = 0 then ⟨0,0⟩ else Word.ofBitVec
        (entry.data.family.result (left row.assignment) (right row.assignment)) := by
  intro row present
  have bounded := (image_value_bounds image inputs accepted decoded).1 row present
    importedConstraintsMemoryPorts[0] (by
      cases row with
      | mk family w => cases family; change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts])
  have native := accepted.constraints row present
  have member := decoded row present
  rw [row_decoder_query] at member
  cases row with
  | mk family w =>
    cases family
    rw [Airbender.Trace.Proofs.read_word] at bounded
    change (left w).Bounded at bounded
    obtain ⟨entry,found,source,query⟩ := fetched_sources image native member
    exact ⟨entry,found,source,query,
      entry_numerical_result native source.fields query bounded⟩

end Airbender.ShiftBinop.Proofs
