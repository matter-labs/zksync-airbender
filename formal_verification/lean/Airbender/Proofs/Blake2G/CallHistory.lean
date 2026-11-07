import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.Blake2G.ControlPool

namespace Airbender.Blake2G.Proofs
open Trace Arithmetic Reference.RiscV.Sail
set_option warningAsError true

theorem ordered_controls [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell} {reduced : Bool}
    (accepted : Delegation.MemoryAccepted data) (inputs : BoundaryCallInputs data initial cells reduced) :
    ∃ ordered : List (Delegation.Row p), ordered.Perm data.rows ∧
      ordered.Pairwise (fun a b =>
        (timeOfPair (a.writeToken importedConstraintsMemoryPorts[8]).time).value <
        (timeOfPair (b.writeToken importedConstraintsMemoryPorts[8]).time).value) ∧
      (∀ (i : Nat) (bound : i < ordered.length),
        (readToken (ordered[i]'bound).assignment importedConstraintsMemoryPorts[8]).word = controlAt reduced i ∧
        ((ordered[i]'bound).writeToken importedConstraintsMemoryPorts[8]).word = controlAt reduced (i + 1)) ∧
      ∃ sink ∈ data.terminal, sink.address = (Cell.register 12).addressCode ∧
        sink.word = controlAt reduced data.rows.length := by
  have count : 0 < data.rows.length := by
    rw [inputs.calls]
    cases reduced <;> decide
  obtain ⟨first, firstMember⟩ := List.exists_mem_of_ne_nil data.rows
    (by intro empty; simp [empty] at count)
  have portMember : importedConstraintsMemoryPorts[8] ∈ first.ports := by
    simp [Delegation.Row.ports, inputs.family first firstMember, importedConstraintsMemoryPorts]
  have tracked := Delegation.Proofs.port_initialized_cell hp accepted inputs.memory firstMember portMember
    (cell := .register 12) (by rfl)
  exact pool_ordered_controls hp accepted
    ⟨inputs.memory, inputs.tables, inputs.family, inputs.active, tracked, inputs.controlStart⟩

end Airbender.Blake2G.Proofs
