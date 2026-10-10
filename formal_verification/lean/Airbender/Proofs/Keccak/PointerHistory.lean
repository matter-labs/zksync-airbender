import Airbender.Proofs.Delegation.Readonly
import Airbender.Review.Keccak.Call

namespace Airbender.Keccak.Proofs
open Trace Arithmetic Reference.RiscV.Sail Reference.Sail
set_option warningAsError true

private theorem pointer_copies {data : Delegation.MemoryData p}
    (family : ∀ row ∈ data.rows, row.family = .keccak) :
    ∀ edge ∈ data.steps, edge.1.address = (Cell.register 11).addressCode → edge.1.word = edge.2.word := by
  intro edge member address
  obtain ⟨row, rowMember, edgeMember⟩ := List.mem_flatMap.mp member
  obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp edgeMember
  cases row with
  | mk kind w =>
    have same := family ⟨kind, w⟩ rowMember
    change kind = .keccak at same
    subst kind
    simp [Delegation.Row.ports, importedConstraintsMemoryPorts] at portMember
    rcases portMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | rfl | simp [readToken, MemoryAddress.code, Cell.addressCode] at address

theorem pointer_history [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell} {pointer : BitVec 32}
    (accepted : Delegation.MemoryAccepted data) (inputs : Delegation.MemoryInputs data initial cells)
    (family : ∀ row ∈ data.rows, row.family = .keccak)
    (tracked : Cell.register 11 ∈ cells) (read : (Cell.register 11).read initial = .ok pointer initial) :
    (∀ row ∈ data.rows, statePointer row.assignment = Word.ofBitVec pointer) ∧
    ∃ sink ∈ data.terminal, sink.address = (Cell.register 11).addressCode ∧ sink.word = Word.ofBitVec pointer := by
  have stable := Delegation.Proofs.readonly_cell hp accepted inputs tracked read (pointer_copies family)
  refine ⟨?_, stable.2⟩
  intro row member
  have family := family row member
  have portMember : importedConstraintsMemoryPorts[1] ∈ row.ports := by
    simp [Delegation.Row.ports, family, importedConstraintsMemoryPorts]
  have edgeMember : (readToken row.assignment importedConstraintsMemoryPorts[1],
      row.writeToken importedConstraintsMemoryPorts[1]) ∈ data.steps :=
    List.mem_flatMap.mpr ⟨row, member, List.mem_map.mpr ⟨_, by simpa using portMember, rfl⟩⟩
  have result := stable.1 _ edgeMember (by rfl)
  simpa [statePointer, readToken, MemoryToken.word, MemoryPort.readCode,
    WordColumns.code, importedConstraintsMemoryPorts, pairCode] using result

theorem call_pointer [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : CallInputs data initial cells) :
    CallPointer data initial := by
  obtain ⟨row, member⟩ : ∃ row, row ∈ data.rows := by
    have nonempty : data.rows ≠ [] := by
      intro empty
      have count := inputs.calls
      simp [empty] at count
    exact List.exists_mem_of_ne_nil _ nonempty
  have family := inputs.family row member
  have portMember : importedConstraintsMemoryPorts[1] ∈ row.ports := by
    simp [Delegation.Row.ports, family, importedConstraintsMemoryPorts]
  have tracked := Delegation.Proofs.port_initialized_cell hp accepted inputs.memory member portMember
    (cell := .register 11) (by rfl)
  obtain ⟨_, _, pointer, read, _⟩ :=
    Trace.Proofs.image_cell_source inputs.memory.initialization (.register 11) tracked
  exact ⟨pointer, read, pointer_history hp accepted inputs.memory inputs.family tracked read⟩

end Airbender.Keccak.Proofs
