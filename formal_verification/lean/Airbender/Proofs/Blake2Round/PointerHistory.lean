import Airbender.Proofs.Blake2Round.CallHistory
import Airbender.Proofs.Delegation.Readonly

namespace Airbender.Blake2Round.Proofs
open Trace Trace.Proofs Arithmetic Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 16384

private def pointerPort (index : Fin 2) : MemoryPort :=
  if index.val = 0 then importedConstraintsMemoryPorts[0] else importedConstraintsMemoryPorts[25]

private theorem pointer_copies {data : Delegation.MemoryData p}
    (family : ∀ row ∈ data.rows, row.family = .blakeRound) (index : Fin 2) :
    ∀ edge ∈ data.steps,
      edge.1.address = (Cell.register (BitVec.ofNat 5 (10 + index.val))).addressCode →
        edge.1.word = edge.2.word := by
  intro edge edgeMember address
  obtain ⟨row, rowMember, edgeMember⟩ := List.mem_flatMap.mp edgeMember
  obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp edgeMember
  cases row with
  | mk kind w =>
    have same := family ⟨kind, w⟩ rowMember
    change kind = .blakeRound at same
    subst kind
    simp [Delegation.Row.ports, importedConstraintsMemoryPorts] at portMember
    rcases portMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    all_goals first
      | rfl
      | (fin_cases index <;> simp [readToken, MemoryAddress.code, Cell.addressCode] at address)

private theorem pointer_history [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell} {flags : Fin 8}
    (accepted : Delegation.MemoryAccepted data) (inputs : CallInputs data initial cells flags)
    (index : Fin 2) :
    ∃ pointer, (Cell.register (BitVec.ofNat 5 (10 + index.val))).read initial = .ok pointer initial ∧
      (∀ row ∈ data.rows,
        (readToken row.assignment (pointerPort index)).word =
          Word.ofBitVec pointer) ∧
      ∃ sink ∈ data.terminal, sink.address = (Cell.register (BitVec.ofNat 5 (10 + index.val))).addressCode ∧
        sink.word = Word.ofBitVec pointer := by
  have nonempty : data.rows ≠ [] := by
    intro empty
    have count := inputs.calls
    simp [empty] at count
    split_ifs at count
  obtain ⟨first, firstMember⟩ := List.exists_mem_of_ne_nil _ nonempty
  have family := inputs.family first firstMember
  have portMember : (pointerPort index) ∈ first.ports := by
    rw [Delegation.Row.ports, family]
    fin_cases index <;> simp [pointerPort, importedConstraintsMemoryPorts]
  have address : (readToken first.assignment (pointerPort index)).address =
      (Cell.register (BitVec.ofNat 5 (10 + index.val))).addressCode := by
    fin_cases index <;> rfl
  have tracked := Delegation.Proofs.port_initialized_cell hp accepted inputs.memory.toBoundaryInputs firstMember portMember address
  obtain ⟨_, _, value, read, _⟩ := image_cell_source inputs.memory.initialization _ tracked
  have constant := Delegation.Proofs.readonly_cell hp accepted inputs.memory.toBoundaryInputs tracked read
    (pointer_copies inputs.family index)
  refine ⟨value, read, ?_, constant.2⟩
  intro row member
  have family := inputs.family row member
  have portMember : (pointerPort index) ∈ row.ports := by
    rw [Delegation.Row.ports, family]
    fin_cases index <;> simp [pointerPort, importedConstraintsMemoryPorts]
  have included : (readToken row.assignment (pointerPort index),
      row.writeToken (pointerPort index)) ∈ data.steps := by
    apply List.mem_flatMap.mpr
    refine ⟨row, member, ?_⟩
    apply List.mem_map.mpr
    exact ⟨_, by simpa only [Array.mem_toList_iff] using portMember, rfl⟩
  exact constant.1 _ included (by fin_cases index <;> rfl)

theorem call_pointers [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell} {flags : Fin 8}
    (accepted : Delegation.MemoryAccepted data) (inputs : CallInputs data initial cells flags) :
    ∃ state message, (Cell.register 10).read initial = .ok state initial ∧
      (Cell.register 11).read initial = .ok message initial ∧
      (∀ row ∈ data.rows, ∀ round,
        (Native.input round row.assignment).statePointer = Word.ofBitVec state ∧
        (Native.input round row.assignment).messagePointer = Word.ofBitVec message) ∧
      (∃ sink ∈ data.terminal, sink.address = (Cell.register 10).addressCode ∧ sink.word = Word.ofBitVec state) ∧
      (∃ sink ∈ data.terminal, sink.address = (Cell.register 11).addressCode ∧ sink.word = Word.ofBitVec message) := by
  obtain ⟨state, stateRead, stateRows, stateTerminal⟩ := pointer_history hp accepted inputs 0
  obtain ⟨message, messageRead, messageRows, messageTerminal⟩ := pointer_history hp accepted inputs 1
  refine ⟨state, message, stateRead, messageRead, ?_, stateTerminal, messageTerminal⟩
  intro row member round
  constructor
  · simpa [Native.input, Delegation.Row.readWord, Delegation.Row.ports, pointerPort] using stateRows row member
  · simpa [Native.input, Delegation.Row.readWord, Delegation.Row.ports, pointerPort] using messageRows row member

end Airbender.Blake2Round.Proofs
