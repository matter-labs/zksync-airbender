import Slop.Keccak.Atomic
import Slop.Keccak.MemorySoundness
import Slop.Delegation.NativeViews

namespace Airbender.Keccak.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384

private def wordPort (index : Fin 12) : MemoryPort :=
  importedConstraintsMemoryPorts[2 + index.val]'(by change 2 + index.val < 14; omega)

private theorem word_port_address (index : Fin 12) :
    (wordPort index).address = .indirect importedConstraintsIndirectPorts[index] := by
  fin_cases index <;> rfl

theorem native_word_observations {p : Nat} {w : Nat → ZMod p} {before after : State}
    (addresses : AddressChecks w)
    (reads : ∀ port ∈ (⟨.keccak, w⟩ : Delegation.Row p).ports, (readToken w port).word.Bounded)
    (writes : ∀ port ∈ (⟨.keccak, w⟩ : Delegation.Row p).ports,
      ((⟨.keccak, w⟩ : Delegation.Row p).writeToken port).word.Bounded)
    (observed : ∀ port ∈ (⟨.keccak, w⟩ : Delegation.Row p).ports,
      ∃ cell : Cell, cell.addressCode = port.address.code w ∧
        cell.read before = .ok (memoryWord (port.readCode w)) before ∧
        cell.read after = .ok (memoryWord (port.writeCode w)) after) (index : Fin 12) :
    let address := (statePointer w).toBitVec + BitVec.ofNat 32
      (8 * (w (7 + index.val / 2)).val + 4 * (index.val % 2))
    ramWord before address = (readToken w (wordPort index)).word.value ∧
      ramWord after address = ((⟨.keccak, w⟩ : Delegation.Row p).writeToken (wordPort index)).word.value := by
  have member : wordPort index ∈ (⟨.keccak, w⟩ : Delegation.Row p).ports :=
    Array.getElem_mem (by change 2 + index.val < 14; omega)
  have result := indirect_word_observations (word_port_address index)
    (reads _ member) (writes _ member) (by
      obtain ⟨cell, code, read, written⟩ := observed _ member
      exact ⟨cell, code, read, written⟩)
  rw [addresses.addresses index] at result
  exact result

theorem native_lane_observations {p : Nat} {w : Nat → ZMod p} {before after : State}
    (addresses : AddressChecks w)
    (reads : ∀ port ∈ (⟨.keccak, w⟩ : Delegation.Row p).ports, (readToken w port).word.Bounded)
    (writes : ∀ port ∈ (⟨.keccak, w⟩ : Delegation.Row p).ports,
      ((⟨.keccak, w⟩ : Delegation.Row p).writeToken port).word.Bounded)
    (observed : ∀ port ∈ (⟨.keccak, w⟩ : Delegation.Row p).ports,
      ∃ cell : Cell, cell.addressCode = port.address.code w ∧
        cell.read before = .ok (memoryWord (port.readCode w)) before ∧
        cell.read after = .ok (memoryWord (port.writeCode w)) after) (lane : Fin 6) :
    let address := (statePointer w).toBitVec + BitVec.ofNat 32 (8 * (w (7 + lane.val)).val)
    Native.readLane w lane = ramLane before address ∧
      Native.writtenLane w lane = ramLane after address := by
  have low := native_word_observations addresses reads writes observed ⟨2 * lane.val, by omega⟩
  have high := native_word_observations addresses reads writes observed ⟨2 * lane.val + 1, by omega⟩
  fin_cases lane
  all_goals simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod,
    Nat.mul_zero, Nat.add_zero, Nat.mul_one] at low high ⊢
  all_goals simp only [BitVec.ofNat_add] at high
  all_goals constructor
  all_goals first
    | simpa [ramLane, Nat.reducePow, BitVec.add_assoc, Native.readLane, Delegation.Row.readWord,
        Delegation.Row.ports, wordPort, importedConstraintsMemoryPorts] using
        (congrArg₂ (fun a b : Nat => a + 4294967296 * b) low.1 high.1).symm
    | simpa [ramLane, Nat.reducePow, BitVec.add_assoc, Native.writtenLane, Delegation.Row.writtenWord,
        Delegation.Row.ports, wordPort, importedConstraintsMemoryPorts] using
        (congrArg₂ (fun a b : Nat => a + 4294967296 * b) low.2 high.2).symm

theorem call_lane_observations [Fact p.Prime] (hp : 16777216 ≤ p)
    (inverse : 256 * (-7864320 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : BoundaryCallInputs data initial cells)
    (tables : data.setup = Delegation.modeledSetup Controller.rows)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (pointer : BitVec 32) (ordered : List (Delegation.Row p)) (after : State),
      (Cell.register 11).read initial = .ok pointer initial ∧ ordered.Perm data.rows ∧
      GroupedSailHistory cells (fun row => row.memorySteps.map transferEvent) ordered initial after ∧
      ∀ row ∈ ordered, ∃ events start finish, events.Perm (row.memorySteps.map transferEvent) ∧
        SailHistory cells events start finish ∧
        ∀ lane : Fin 6,
          let address := pointer + BitVec.ofNat 32 (8 * (row.assignment (7 + lane.val)).val)
          Native.readLane row.assignment lane = ramLane start address ∧
            Native.writtenLane row.assignment lane = ramLane finish address := by
  obtain ⟨ordered, after, permutation, history, observed⟩ :=
    call_atomic_observations hp inverse accepted inputs tables aligned
  obtain ⟨_, _, pointer, effects⟩ := call_execution hp inverse accepted inputs tables aligned
  obtain ⟨pointer, pointerRead, pointers, _⟩ := pointer
  have clockBound : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have memory : BoundaryMemoryInputs data initial cells Controller.rows :=
    ⟨inputs.memory, inputs.family, by simp [tables, Delegation.modeledSetup], inputs.active⟩
  have bounds := Memory.Proofs.value_bounds_at_boundary clockBound accepted memory
  refine ⟨pointer, ordered, after, pointerRead, permutation, history, ?_⟩
  intro row member
  have included := permutation.mem_iff.mp member
  obtain ⟨events, start, finish, eventsPerm, current, ports⟩ := observed row member
  refine ⟨events, start, finish, eventsPerm, current, ?_⟩
  intro lane
  have native : row = ⟨.keccak, row.assignment⟩ := by
    cases row with
    | mk family w =>
      have same := inputs.family ⟨family, w⟩ included
      change family = .keccak at same
      simp only [same]
  have reads : ∀ port ∈ (⟨.keccak, row.assignment⟩ : Delegation.Row p).ports,
      (readToken row.assignment port).word.Bounded := by
    simpa only [← native] using bounds.1 row included
  have writes : ∀ port ∈ (⟨.keccak, row.assignment⟩ : Delegation.Row p).ports,
      ((⟨.keccak, row.assignment⟩ : Delegation.Row p).writeToken port).word.Bounded := by
    simpa only [← native] using bounds.2.1 row included
  have actual : ∀ port ∈ (⟨.keccak, row.assignment⟩ : Delegation.Row p).ports,
      ∃ cell : Cell, cell.addressCode = port.address.code row.assignment ∧
        cell.read start = .ok (memoryWord (port.readCode row.assignment)) start ∧
        cell.read finish = .ok (memoryWord (port.writeCode row.assignment)) finish := by
    intro port member
    obtain ⟨cell, _, code, read, written⟩ := ports port (by simpa only [← native] using member)
    exact ⟨cell, code, read, written⟩
  have result := native_lane_observations (effects row included).addresses reads writes actual lane
  rw [pointers row included, Word.ofBitVec_roundtrip] at result
  exact result

end Airbender.Keccak.Proofs
