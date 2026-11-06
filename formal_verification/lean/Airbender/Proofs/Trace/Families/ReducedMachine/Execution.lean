import Airbender.Proofs.ReducedMachine.NativeShiftExecution
import Airbender.Proofs.Trace.Families.ReducedMachine.RegisterHistory
import Airbender.Proofs.Trace.Families.ReducedMachine.Values
import Airbender.Review.Helpers.Memory.ReducedMachineExecution

namespace Airbender.ReducedMachine.NativeShiftExecutionProofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false
open Native Arithmetic Trace Verification

/-- Original public decoding and initialized native matching derive all PC
    inputs, operand bounds and actual states for original preparation/retirement. -/
theorem image_instruction_history {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ShiftMode} {initial : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : shiftDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary (fixedData trace) initial cells) (accepted : Accepted (fixedData trace))
    (decoded : ShiftDecodedTrace (fixedData trace) setup) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ShiftInstructionHistory (fixedData trace) setup initial cells := by
  refine ⟨NativeShiftRegisterProofs.image_register_history image inputs accepted decoded aligned,?_⟩
  intro row present
  obtain ⟨entry,member,source,query,_⟩ := NativeShiftDecoderProofs.trace_decoding image accepted decoded row present
  refine ⟨entry,member,source,query,?_⟩
  have native := accepted.constraints row present
  have ranges := (NativeShiftRangeProofs.image_value_bounds image inputs accepted decoded).1 row present
  have found := decoded row present
  rw [NativeShiftDecoderProofs.row_query] at found query
  cases row with
  | mk family w =>
    cases family
    have pc := NativePCProofs.decoded_pc_successor image native found
    refine ⟨pc.2.2.1,?_⟩
    intro before after history
    have bound := ranges importedConstraintsMemoryPorts[0] (by
      change _ ∈ importedConstraintsMemoryPorts
      simp [importedConstraintsMemoryPorts])
    rw [Trace.Proofs.read_word] at bound
    exact local_row_execution native source.fields query bound pc.2.1 (fixedData trace).memoryEpoch history

end Airbender.ReducedMachine.NativeShiftExecutionProofs
