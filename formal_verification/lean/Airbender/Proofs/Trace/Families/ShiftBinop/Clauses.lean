import Airbender.Proofs.ShiftBinop.Clauses
import Airbender.Proofs.Trace.Families.ShiftBinop.RegisterHistory
import Airbender.Review.Helpers.Memory.ShiftBinopClauses

namespace Airbender.ShiftBinop.Proofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail

/-- Actual public initialization constructs the states; native matching derives
    source ranges and the original decoder supplies the retained instruction.
    The original clause reaches the same after-state as the actual native ports. -/
theorem image_clause_history {trace : Data mersenne31Modulus ShiftBinopFamily}
    {setup : SparseDecoderSetup Operation} {initial : State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : sparseDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary trace initial cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ClauseHistory trace setup initial cells := by
  refine ⟨image_register_history image inputs accepted decoded aligned,?_⟩
  intro row present
  obtain ⟨entry,member,source,query⟩ := decoded_sources image accepted decoded row present
  have bounded := (image_value_bounds image inputs accepted decoded).1 row present
    importedConstraintsMemoryPorts[0] (by
      cases row with
      | mk family w => cases family; change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts])
  have native := accepted.constraints row present
  refine ⟨entry,member,source,query,?_⟩
  intro before after history
  cases row with
  | mk family w =>
    cases family
    rw [Airbender.Trace.Proofs.read_word] at bounded
    change (left w).Bounded at bounded
    rw [row_decoder_query] at query
    exact native_clause native source.fields query bounded
      ⟨register_reads (by decide) trace.memoryEpoch query history,
        register_write (by decide) trace.memoryEpoch query history⟩

end Airbender.ShiftBinop.Proofs
