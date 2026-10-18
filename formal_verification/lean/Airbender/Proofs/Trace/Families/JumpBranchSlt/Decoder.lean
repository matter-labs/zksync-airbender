import Airbender.Review.Helpers.Decoder.Control
import Airbender.Proofs.JumpBranchSlt.Decoder

namespace Airbender.JumpBranchSlt.Proofs
open Trace

/-- The singleton trace registry uses exactly the existing native circuit query. -/
theorem row_decoder_query (row : Row p JumpBranchSltFamily) :
    row.decoderQuery = decoderQuery row.assignment := by
  cases row with
  | mk family w => cases family; rfl

theorem decoded_sources {p : Nat} [Fact p.Prime] (hp : 32 < p)
    {trace : Data p JumpBranchSltFamily} {setup : SparseDecoderSetup Unit}
    {before : Reference.RiscV.Sail.State} {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : Decoded trace setup) :
    ∀ row ∈ trace.rows, ∃ entry ∈ setup.program,
      entry.SourceWith before decoderFields ∧ row.decoderQuery = entry.query := by
  intro row present
  have native := accepted.constraints row present
  have member := decoded row present
  rw [row_decoder_query] at member
  cases row with
  | mk family w =>
    cases family
    obtain ⟨entry, found, source, same⟩ := fetched_sources hp image native member
    exact ⟨entry, found, source, same⟩

theorem decoded_mask_flag {trace : Data mersenne31Modulus JumpBranchSltFamily}
    {setup : SparseDecoderSetup Unit} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : Decoded trace setup)
    (row : Row mersenne31Modulus JumpBranchSltFamily) (present : row ∈ trace.rows) :
    (row.assignment 12).val ∈ [1,2,4,8,16] ∧
      (row.assignment 8 = 0 ∨ row.assignment 8 = 1) := by
  obtain ⟨entry, _, source, same⟩ := decoded_sources (by decide) image accepted decoded row present
  rw [row_decoder_query] at same
  have flag := congrArg (fun q : Vector (ZMod mersenne31Modulus) 10 => q[5]) same
  change row.assignment 8 = (if entry.data.rd = 0 then 1 else 0) at flag
  refine ⟨query_mask (by decide) source.fields same, ?_⟩
  by_cases zero : entry.data.rd = 0
  · exact Or.inr (by simpa only [zero, if_true] using flag)
  · exact Or.inl (by simpa only [zero, if_false] using flag)

end Airbender.JumpBranchSlt.Proofs
