import Airbender.Proofs.Blake2Round.Atomic
import Airbender.Proofs.Delegation.NativeViews

namespace Airbender.Blake2Round.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384

def wordIndex (index : Fin 40) : Fin 43 :=
  if h : index.val < 24 then ⟨1 + index.val, by omega⟩ else ⟨2 + index.val, by omega⟩

private def wordPort (index : Fin 40) : MemoryPort :=
  importedConstraintsMemoryPorts[wordIndex index]

private theorem word_port_address (index : Fin 40) :
    (wordPort index).address = .indirect importedConstraintsIndirectPorts[index] := by
  fin_cases index <;> rfl

private theorem word_address {p : Nat} {w : Nat → ZMod p} {round : Fin 10}
    (addresses : Addresses.spec ⟨(Native.input round w).statePointer, (Native.input round w).messagePointer⟩
      (Native.output w).addresses) (index : Fin 40) :
    importedConstraintsIndirectPorts[index].address w =
      (Addresses.expected ⟨(Native.input round w).statePointer, (Native.input round w).messagePointer⟩)[index] := by
  have address := congrArg (fun values : Vector (BitVec 32) 40 => values[index]) addresses
  change (importedConstraintsIndirectPorts.map (fun port => port.address w))[index] = _ at address
  simpa only [Fin.getElem_fin, Vector.getElem_map] using address

theorem native_word_observations {p : Nat} {w : Nat → ZMod p} {before after : State} {round : Fin 10}
    (addresses : Addresses.spec ⟨(Native.input round w).statePointer, (Native.input round w).messagePointer⟩
      (Native.output w).addresses)
    (reads : ∀ port ∈ (⟨.blakeRound, w⟩ : Delegation.Row p).ports, (readToken w port).word.Bounded)
    (writes : ∀ port ∈ (⟨.blakeRound, w⟩ : Delegation.Row p).ports,
      ((⟨.blakeRound, w⟩ : Delegation.Row p).writeToken port).word.Bounded)
    (observed : ∀ port ∈ (⟨.blakeRound, w⟩ : Delegation.Row p).ports,
      ∃ cell : Cell, cell.addressCode = port.address.code w ∧
        cell.read before = .ok (memoryWord (port.readCode w)) before ∧
        cell.read after = .ok (memoryWord (port.writeCode w)) after) (index : Fin 40) :
    let address := (Addresses.expected ⟨(Native.input round w).statePointer,
      (Native.input round w).messagePointer⟩)[index]
    ramWord before address = ((⟨.blakeRound, w⟩ : Delegation.Row p).readWord (wordIndex index)).value ∧
      ramWord after address = ((⟨.blakeRound, w⟩ : Delegation.Row p).writtenWord (wordIndex index)).value := by
  have member : wordPort index ∈ (⟨.blakeRound, w⟩ : Delegation.Row p).ports :=
    Array.getElem_mem (wordIndex index).isLt
  have result := indirect_word_observations (word_port_address index)
    (reads _ member) (writes _ member) (observed _ member)
  rw [word_address addresses index] at result
  exact result

theorem call_word_observations [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell} {flags : Fin 8}
    (accepted : Delegation.MemoryAccepted data) (inputs : BoundaryCallInputs data initial cells flags)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (statePointer messagePointer : BitVec 32) (ordered : List (Delegation.Row p)) (after : State),
      (Cell.register 10).read initial = .ok statePointer initial ∧
      (Cell.register 11).read initial = .ok messagePointer initial ∧ ordered.Perm data.rows ∧
      GroupedSailHistory cells (fun row => row.memorySteps.map transferEvent) ordered initial after ∧
      ∀ row ∈ ordered, ∃ round : Fin 10, ∃ events start finish,
        Row.spec (Native.input round row.assignment) (Native.output row.assignment) ∧
        events.Perm (row.memorySteps.map transferEvent) ∧ SailHistory cells events start finish ∧
        ∀ index : Fin 40,
          let address := if index.val < 24 then statePointer + BitVec.ofNat 32 (4 * index.val)
            else messagePointer + BitVec.ofNat 32 (4 * (index.val - 24))
          ramWord start address =
            ((⟨.blakeRound, row.assignment⟩ : Delegation.Row p).readWord (wordIndex index)).value ∧
          ramWord finish address =
            ((⟨.blakeRound, row.assignment⟩ : Delegation.Row p).writtenWord (wordIndex index)).value := by
  obtain ⟨ordered, after, permutation, history, effects, observed, _⟩ :=
    call_atomic_observations hp inverse accepted inputs aligned
  have clockBound : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  obtain ⟨statePointer, messagePointer, stateRead, messageRead, pointers, _, _⟩ :=
    call_pointers clockBound accepted inputs
  have operations := call_operation_inputs clockBound accepted inputs
  have bounds := operation_word_bounds_at_boundary hp inverse accepted operations
  refine ⟨statePointer, messagePointer, ordered, after, stateRead, messageRead, permutation, history, ?_⟩
  intro row member
  have included := permutation.mem_iff.mp member
  obtain ⟨round, _, effect⟩ := effects row included
  obtain ⟨events, start, finish, eventPerm, current, ports⟩ := observed row member
  refine ⟨round, events, start, finish, effect, eventPerm, current, ?_⟩
  intro index
  have native : row = ⟨.blakeRound, row.assignment⟩ := by
    have native : row = ⟨row.family, row.assignment⟩ := rfl
    simpa only [inputs.family row included] using native
  have reads : ∀ port ∈ (⟨.blakeRound, row.assignment⟩ : Delegation.Row p).ports,
      (readToken row.assignment port).word.Bounded := by
    simpa only [← native] using bounds.reads row included
  have writes : ∀ port ∈ (⟨.blakeRound, row.assignment⟩ : Delegation.Row p).ports,
      ((⟨.blakeRound, row.assignment⟩ : Delegation.Row p).writeToken port).word.Bounded := by
    simpa only [← native] using bounds.writes row included
  have actual : ∀ port ∈ (⟨.blakeRound, row.assignment⟩ : Delegation.Row p).ports,
      ∃ cell : Cell, cell.addressCode = port.address.code row.assignment ∧
        cell.read start = .ok (memoryWord (port.readCode row.assignment)) start ∧
        cell.read finish = .ok (memoryWord (port.writeCode row.assignment)) finish := by
    intro port present
    obtain ⟨cell, _, code, read, written⟩ := ports port (by simpa only [← native] using present)
    exact ⟨cell, code, read, written⟩
  have result := native_word_observations effect.2.2.2 reads writes actual index
  have pointer := pointers row included round
  simpa only [Addresses.expected, Fin.getElem_fin, Vector.getElem_ofFn,
    pointer.1, pointer.2, Word.ofBitVec_roundtrip] using result

theorem call_block_cells [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell} {flags : Fin 8}
    (accepted : Delegation.MemoryAccepted data) (inputs : BoundaryCallInputs data initial cells flags)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (statePointer messagePointer : BitVec 32),
      (Cell.register 10).read initial = .ok statePointer initial ∧
      (Cell.register 11).read initial = .ok messagePointer initial ∧
      ∀ index : Fin 40,
        Cell.ram (if index.val < 24 then statePointer + BitVec.ofNat 32 (4 * index.val)
          else messagePointer + BitVec.ofNat 32 (4 * (index.val - 24))) ∈ cells := by
  have clockBound : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  obtain ⟨statePointer, messagePointer, stateRead, messageRead, pointers, _, _⟩ :=
    call_pointers clockBound accepted inputs
  have nonempty : data.rows ≠ [] := by
    intro empty
    have count := inputs.calls
    simp only [empty, List.length_nil] at count
    split_ifs at count
  obtain ⟨row, member⟩ := List.exists_mem_of_ne_nil _ nonempty
  obtain ⟨_, _, effects⟩ := call_execution hp inverse accepted inputs aligned
  obtain ⟨round, _, effect⟩ := effects row member
  refine ⟨statePointer, messagePointer, stateRead, messageRead, ?_⟩
  intro index
  have present : wordPort index ∈ row.ports := by
    rw [Delegation.Row.ports, inputs.family row member]
    exact Array.getElem_mem (wordIndex index).isLt
  have tracked := initialized_indirect_cell_at_boundary clockBound accepted inputs.memory member present (word_port_address index)
  rw [word_address effect.2.2.2 index] at tracked
  have pointer := pointers row member round
  simpa only [Addresses.expected, Fin.getElem_fin, Vector.getElem_ofFn,
    pointer.1, pointer.2, Word.ofBitVec_roundtrip] using tracked

end Airbender.Blake2Round.Proofs
