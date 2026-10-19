import Airbender.Proofs.Trace.Families.MulDiv.Values
import Airbender.Review.Circuits.MulDiv.Theorems

namespace Airbender.MulDiv.Proofs
open Arithmetic Trace

/-- Native matching and actual public construction supply every local numerical
    interface. Original instruction execution and retirement remain separate. -/
theorem initialized_results {trace : Data mersenne31Modulus MulDivFamily}
    {setup : SparseDecoderSetup Operation} {before : Reference.RiscV.Sail.State}
    {cells : List Cell} {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup) :
    ∀ row ∈ trace.rows, ∃ entry ∈ setup.program,
      entry.SourceWith before decoderFields ∧ row.decoderQuery = entry.query ∧
      (selectedWord row.assignment).value = entry.data.family.result
        (left row.assignment) (right row.assignment) ∧
      (writtenWord row.assignment).value = if entry.data.rd = 0 then 0 else
        entry.data.family.result (left row.assignment) (right row.assignment) := by
  intro row present
  obtain ⟨entry,found,source,same⟩ := decoded_sources (by decide) image accepted decoded row present
  have ranges := (image_value_bounds image inputs accepted decoded).1 row present
  have native := accepted.constraints row present
  refine ⟨entry,found,source,same,?_⟩
  rw [row_decoder_query] at same
  cases row with
  | mk family w =>
    cases family
    have leftBound := ranges importedConstraintsMemoryPorts[0] (by
      change _ ∈ importedConstraintsMemoryPorts
      simp [importedConstraintsMemoryPorts])
    rw [Trace.Proofs.read_word] at leftBound
    change (left w).Bounded at leftBound
    have mask := query_mask (by decide) source.fields same
    have flag := congrArg (fun q : Vector (ZMod mersenne31Modulus) 10 => q[5]) same
    change w 8 = (if entry.data.rd = 0 then 1 else 0) at flag
    by_cases zero : entry.data.rd = 0
    · rw [if_pos zero] at flag ⊢
      exact native_unsigned_result w entry.data.family true native mask leftBound flag
    · rw [if_neg zero] at flag ⊢
      exact native_unsigned_result w entry.data.family false native mask leftBound flag

end Airbender.MulDiv.Proofs
