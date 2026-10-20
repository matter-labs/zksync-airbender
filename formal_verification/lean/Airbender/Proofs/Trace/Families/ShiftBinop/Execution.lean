import Airbender.Proofs.ShiftBinop.Execution
import Airbender.Proofs.Trace.Families.ShiftBinop.RegisterHistory
import Airbender.Review.Helpers.Memory.ShiftBinopExecution

namespace Airbender.ShiftBinop.Proofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false
open Arithmetic Trace Verification

/-- Original public decoding and initialized native matching derive all PC
    inputs, operand bounds and actual states for original preparation/retirement. -/
theorem image_instruction_history {trace : Data mersenne31Modulus ShiftBinopFamily}
    {setup : SparseDecoderSetup Operation} {initial : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : sparseDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary trace initial cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    InstructionHistory trace setup initial cells := by
  refine ⟨image_register_history image inputs accepted decoded aligned,?_⟩
  intro row present
  obtain ⟨entry,member,source,query⟩ := decoded_sources image accepted decoded row present
  refine ⟨entry,member,source,query,?_⟩
  have native := accepted.constraints row present
  have ranges := (image_value_bounds image inputs accepted decoded).1 row present
  have found := decoded row present
  rw [row_decoder_query] at found query
  cases row with
  | mk family w =>
    cases family
    have pcInputs := decoded_pc_inputs image native found
    have pc := native_pc_successor (by decide) native
      (initial := ⟨(w 0).val,(w 1).val⟩) (final := ⟨(w 13).val,(w 14).val⟩)
      ⟨(ZMod.natCast_zmod_val _).symm,(ZMod.natCast_zmod_val _).symm,rfl,rfl⟩ pcInputs.1 pcInputs.2
    refine ⟨pc.1,?_⟩
    intro before after history
    have bound := ranges importedConstraintsMemoryPorts[0] (by
      change _ ∈ importedConstraintsMemoryPorts
      simp [importedConstraintsMemoryPorts])
    rw [Trace.Proofs.read_word] at bound
    exact local_row_execution native source.fields query bound pcInputs.2 trace.memoryEpoch history

end Airbender.ShiftBinop.Proofs
