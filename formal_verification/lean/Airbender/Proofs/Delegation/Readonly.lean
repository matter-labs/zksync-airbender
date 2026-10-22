import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.Delegation.History

namespace Airbender.Delegation.Proofs
open Trace Arithmetic Reference.RiscV.Sail Reference.Sail
set_option warningAsError true

theorem port_initialized_cell [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    {data : MemoryData p} {initial : State} {cells : List Cell}
    (accepted : MemoryAccepted data) (inputs : BoundaryInputs data initial cells)
    {row : Row p} (member : row ∈ data.rows) {port : MemoryPort} (present : port ∈ row.ports)
    {cell : Cell} (address : (readToken row.assignment port).address = cell.addressCode) :
    cell ∈ cells := by
  have step : (readToken row.assignment port, row.writeToken port) ∈ data.steps :=
    List.mem_flatMap.mpr ⟨row, member, List.mem_map.mpr ⟨port, by simpa using present, rfl⟩⟩
  obtain ⟨actual, tracked, same⟩ := initialized_cell hp accepted inputs step
  rw [address] at same
  have equal : actual = cell := Trace.Proofs.cell_address_injective same
  exact equal ▸ tracked

theorem path_word_constant {path : List (MemoryToken p)} {source : MemoryToken p}
    (head : path.head? = some source)
    (copies : ∀ edge ∈ path.zip path.tail, edge.1.word = edge.2.word) :
    ∀ token ∈ path, token.word = source.word := by
  induction path generalizing source with
  | nil => simp at head
  | cons first rest ih =>
    have same : first = source := by simpa using head
    subst source
    intro token member
    rcases List.mem_cons.mp member with rfl | member
    · rfl
    · cases rest with
      | nil => simp at member
      | cons second tail =>
        have next := copies (first, second) (by simp)
        have result := ih (by rfl : (second :: tail).head? = some second)
          (fun edge member => copies edge (List.mem_cons_of_mem _ member)) token member
        exact result.trans next.symm

theorem readonly_cell [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    {data : MemoryData p} {initial : State} {cells : List Cell} {cell : Cell} {value : BitVec 32}
    (accepted : MemoryAccepted data) (inputs : BoundaryInputs data initial cells)
    (tracked : cell ∈ cells) (read : cell.read initial = .ok value initial)
    (copies : ∀ edge ∈ data.steps, edge.1.address = cell.addressCode → edge.1.word = edge.2.word) :
    (∀ edge ∈ data.steps, edge.1.address = cell.addressCode → edge.1.word = Word.ofBitVec value) ∧
    ∃ sink ∈ data.terminal, sink.address = cell.addressCode ∧ sink.word = Word.ofBitVec value := by
  obtain ⟨source, member, actual, actualRead, sourceCode, sourceWord⟩ :=
    boundary_cell_source inputs tracked
  have same := (EStateM.Result.ok.inj (actualRead.symm.trans read)).1
  subst actual
  obtain ⟨sink, sinkMember, address, path, head, last, _, matching⟩ :=
    (memory_effects hp accepted inputs).paths _ member
  rw [sourceCode] at matching
  have constant := path_word_constant head (fun edge edgeMember => by
    have included := matching.mem_iff.mp edgeMember
    have pair := List.mem_filter.mp included
    exact copies edge pair.1 (by simpa using pair.2))
  constructor
  · intro edge edgeMember atCell
    have included : edge ∈ path.zip path.tail := matching.mem_iff.mpr
      (List.mem_filter.mpr ⟨edgeMember, by simpa using atCell⟩)
    have first : edge.1 ∈ path := by
      exact (List.of_mem_zip included).1
    exact (constant _ first).trans sourceWord
  · refine ⟨sink, sinkMember, address.trans sourceCode, ?_⟩
    have present : sink ∈ path := List.mem_of_getLast? last
    exact (constant _ present).trans sourceWord

end Airbender.Delegation.Proofs
