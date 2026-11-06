import Airbender.Proofs.ReducedMachine.NativeShiftClause
import Airbender.Proofs.Trace.Families.ReducedMachine.RegisterHistory
import Airbender.Proofs.Trace.Families.ReducedMachine.Values
import Airbender.Review.Helpers.Memory.ReducedMachineClauses

namespace Airbender.ReducedMachine.NativeShiftClauseProofs
open Native Arithmetic Trace Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Public initialization constructs the states and derives source bounds.
    Actual native routing/results and original GPR transfers execute the original
    retained clause into the same after-state, including discarded x0 forms. -/
theorem image_clause_history {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ShiftMode} {initial : State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : shiftDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary (fixedData trace) initial cells) (accepted : Accepted (fixedData trace))
    (decoded : ShiftDecodedTrace (fixedData trace) setup) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ShiftClauseHistory (fixedData trace) setup initial cells := by
  refine ⟨NativeShiftRegisterProofs.image_register_history image inputs accepted decoded aligned,?_⟩
  intro row present
  obtain ⟨entry,member,source,query,_⟩ := NativeShiftDecoderProofs.trace_decoding image accepted decoded row present
  have bounded := (NativeShiftRangeProofs.image_value_bounds image inputs accepted decoded).1 row present
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
    change (sourceWord w).Bounded at bounded
    exact native_clause native source.fields query bounded
      ⟨NativeShiftPortProofs.register_reads (fixedData trace).memoryEpoch native source.fields query history,
        NativeShiftPortProofs.register_write (fixedData trace).memoryEpoch native source.fields query history⟩

end Airbender.ReducedMachine.NativeShiftClauseProofs
