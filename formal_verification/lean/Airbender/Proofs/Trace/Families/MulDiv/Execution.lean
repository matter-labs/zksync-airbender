import Airbender.Proofs.MulDiv.Execution
import Airbender.Proofs.Trace.Families.MulDiv.RegisterHistory
import Airbender.Proofs.Trace.Families.MulDiv.Values
import Airbender.Review.Helpers.Memory.MulDivExecution

namespace Airbender.MulDiv.Proofs
open Arithmetic Trace Verification

/-- Initialized matching supplies all operand ranges, current PC inputs and
    native histories. Original public bytes select every operation clause. -/
theorem image_instruction_history {trace : Data mersenne31Modulus MulDivFamily}
    {setup : SparseDecoderSetup Operation} {initial : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : sparseDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary trace initial cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    InstructionHistory trace setup initial cells := by
  refine ⟨image_register_history image inputs accepted decoded aligned,?_⟩
  intro row present
  obtain ⟨entry,member,source,query⟩ := decoded_sources (by decide) image accepted decoded row present
  refine ⟨entry,member,source,query,decoder_instruction source.fields,?_⟩
  have native := accepted.constraints row present
  have ranges := (image_value_bounds image inputs accepted decoded).1 row present
  have found := decoded row present
  rw [row_decoder_query] at found query
  cases row with
  | mk family w =>
    cases family
    have pcInputs := decoded_inputs (by decide) image native found
    have pc := native_pc_successor (by decide) native
      (initial := ⟨(w 0).val,(w 1).val⟩) (final := ⟨(w 13).val,(w 14).val⟩)
      ⟨(ZMod.natCast_zmod_val _).symm,(ZMod.natCast_zmod_val _).symm,rfl,rfl⟩ pcInputs.1 pcInputs.2.1
    refine ⟨pc.1,?_⟩
    intro before after history
    have bound := ranges importedConstraintsMemoryPorts[0] (by
      change _ ∈ importedConstraintsMemoryPorts
      simp [importedConstraintsMemoryPorts])
    rw [Trace.Proofs.read_word] at bound
    exact local_row_execution native source.fields query bound pcInputs.2.1 trace.memoryEpoch history

end Airbender.MulDiv.Proofs
