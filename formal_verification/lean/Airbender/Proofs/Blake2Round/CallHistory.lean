import Airbender.Proofs.Blake2Round.ControlPool

namespace Airbender.Blake2Round.Proofs
open Trace Arithmetic Reference.RiscV.Sail
set_option warningAsError true

def BoundaryCallInputs.toControlPoolInputs [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell} {flags : Fin 8}
    (inputs : BoundaryCallInputs data initial cells flags) (accepted : Delegation.MemoryAccepted data) :
    ControlPoolInputs data initial cells flags := by
  have count : 0 < data.rows.length ∧ data.rows.length ≤ 10 := by
    rw [inputs.calls]; split_ifs <;> decide
  obtain ⟨first, firstMember⟩ := List.exists_mem_of_ne_nil data.rows
    (by intro empty; simp [empty] at count)
  have portMember : importedConstraintsMemoryPorts[42] ∈ first.ports := by
    simp [Delegation.Row.ports, inputs.family first firstMember, importedConstraintsMemoryPorts]
  have tracked := Delegation.Proofs.port_initialized_cell hp accepted inputs.memory firstMember portMember
    (cell := .register 12) (by rfl)
  exact ⟨inputs.memory, inputs.tables, inputs.family, tracked, inputs.controlStart, count.2⟩

theorem call_order [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell} {flags : Fin 8}
    (accepted : Delegation.MemoryAccepted data) (inputs : BoundaryCallInputs data initial cells flags) :
    ∃ ordered : List (Delegation.Row p), ordered.Perm data.rows ∧
      ordered.Pairwise (fun a b =>
        (timeOfPair (a.writeToken importedConstraintsMemoryPorts[42]).time).value <
        (timeOfPair (b.writeToken importedConstraintsMemoryPorts[42]).time).value) :=
  pool_order hp accepted (inputs.toControlPoolInputs hp accepted)

theorem ordered_controls [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell} {flags : Fin 8}
    (accepted : Delegation.MemoryAccepted data) (inputs : BoundaryCallInputs data initial cells flags) :
    ∃ ordered : List (Delegation.Row p), ordered.Perm data.rows ∧
      ordered.Pairwise (fun a b =>
        (timeOfPair (a.writeToken importedConstraintsMemoryPorts[42]).time).value <
        (timeOfPair (b.writeToken importedConstraintsMemoryPorts[42]).time).value) ∧
      (∀ (i : Nat) (bound : i < ordered.length),
        (readToken (ordered[i]'bound).assignment importedConstraintsMemoryPorts[42]).word = controlAt flags i ∧
        ((ordered[i]'bound).writeToken importedConstraintsMemoryPorts[42]).word = controlAt flags (i + 1)) ∧
      ∃ sink ∈ data.terminal, sink.address = (Cell.register 12).addressCode ∧
        sink.word = controlAt flags data.rows.length :=
  pool_ordered_controls hp accepted (inputs.toControlPoolInputs hp accepted)

theorem call_rounds [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell} {flags : Fin 8}
    (accepted : Delegation.MemoryAccepted data) (inputs : BoundaryCallInputs data initial cells flags) :
    ∀ row ∈ data.rows, ∃ round : Fin 10, Memory.RoundMask row.assignment round ∧
      (row.assignment Variables.controlReadHi).val = flags.val + 8 * 2 ^ round.val :=
  pool_rounds hp accepted (inputs.toControlPoolInputs hp accepted)

theorem call_masks [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell} {flags : Fin 8}
    (accepted : Delegation.MemoryAccepted data) (inputs : BoundaryCallInputs data initial cells flags) :
    CallMasks data :=
  pool_masks hp accepted (inputs.toControlPoolInputs hp accepted)

theorem call_modes [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell} {flags : Fin 8}
    (accepted : Delegation.MemoryAccepted data) (inputs : BoundaryCallInputs data initial cells flags) :
    CallModes data flags :=
  pool_modes hp accepted (inputs.toControlPoolInputs hp accepted)

end Airbender.Blake2Round.Proofs
