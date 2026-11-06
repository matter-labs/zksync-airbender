import Slop.Trace.RVZero
import Slop.WordMemory.RVWritable
import Slop.SubwordMemory.RVWritable

/-! The pooled writable-store law: the word and subword store lemmas assembled over every native write. -/

namespace Airbender.Trace.RVWritable
open Arithmetic Trace.Proofs

/-- Every changing native write to a RAM cell is an RV-writable store: only the word/subword store ports write RAM,
    and the circuit keeps them out of ROM; register ports never carry a RAM address. -/
theorem rv_pooled_writable {p : Nat} [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {trace : PooledTrace p} (accepted : Accepted trace)
    {cells : List Cell} (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∀ event ∈ trace.nativeEvents, event.2.2.1 ≠ event.2.2.2 → ∀ cell ∈ cells,
      cell.addressCode = event.2.1 → ∀ index, cell = .ram index → RV.writable index 4 := by
  intro event member changing cell cellMember address index cellEq
  change event ∈ trace.memorySteps.map (fun edge =>
    (trace.memoryEpoch + (timeOfPair edge.2.time).value, edge.1.address, edge.1.value, edge.2.value)) at member
  obtain ⟨edge, edgeMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨row, rowMember, rowEdge⟩ := List.mem_flatMap.mp edgeMember
  obtain ⟨port, present, rfl⟩ := List.mem_map.mp rowEdge
  have present : port ∈ row.ports := by simpa using present
  have written : port.writeValue ≠ none := by
    intro none
    apply changing
    simp [writeToken, readToken, MemoryPort.writeCode, MemoryPort.readCode, none]
  subst cellEq
  have aligned' := aligned _ cellMember
  change (Cell.ram index).addressCode = port.address.code row.assignment at address
  have bounded : index.toNat % 4 = 0 := aligned'
  have below := index.isLt
  have ramEnd : index.toNat + 4 ≤ RV.RAM_END := by
    unfold RV.RAM_END
    omega
  have constraints := accepted.constraints row rowMember
  refine ⟨?_, ramEnd⟩
  cases row with
  | mk kind w =>
    cases kind with
    | addSub =>
      have members : port ∈ AddSub.importedConstraintsMemoryPorts := present
      obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp members
      have small : i < 3 := by simpa [AddSub.importedConstraintsMemoryPorts] using hi
      interval_cases i
      all_goals simp [AddSub.importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode] at written address
    | jumpBranchSlt =>
      have members : port ∈ JumpBranchSlt.importedConstraintsMemoryPorts := present
      obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp members
      have small : i < 3 := by simpa [JumpBranchSlt.importedConstraintsMemoryPorts] using hi
      interval_cases i
      all_goals simp [JumpBranchSlt.importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode] at written address
    | mulDiv =>
      have members : port ∈ MulDiv.importedConstraintsMemoryPorts := present
      obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp members
      have small : i < 3 := by simpa [MulDiv.importedConstraintsMemoryPorts] using hi
      interval_cases i
      all_goals simp [MulDiv.importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode] at written address
    | shiftBinop =>
      have members : port ∈ ShiftBinop.importedConstraintsMemoryPorts := present
      obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp members
      have small : i < 3 := by simpa [ShiftBinop.importedConstraintsMemoryPorts] using hi
      interval_cases i
      all_goals simp [ShiftBinop.importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode] at written address
    | wordMemory =>
      have core := Verification.holds_of_sublist constraints
        (List.sublist_append_left (WordMemory.importedConstraints trace.rom.wordMemory)
          WordMemory.importedConstraintsTimestampLookups)
      have members : port ∈ WordMemory.importedConstraintsMemoryPorts := present
      obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp members
      have small : i < 3 := by simpa [WordMemory.importedConstraintsMemoryPorts] using hi
      interval_cases i
      · simp [WordMemory.importedConstraintsMemoryPorts] at written
      · simp [WordMemory.importedConstraintsMemoryPorts] at written
      · exact (word_store_ram_writable (by dsimp [timestampBase] at hp; omega) trace.rom.wordMemory w core
          index address.symm)
    | subwordMemory =>
      have core := Verification.holds_of_sublist constraints
        (List.sublist_append_left (SubwordMemory.importedConstraints trace.rom.subwordMemory)
          SubwordMemory.importedConstraintsTimestampLookups)
      have members : port ∈ SubwordMemory.importedConstraintsMemoryPorts := present
      obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp members
      have small : i < 3 := by simpa [SubwordMemory.importedConstraintsMemoryPorts] using hi
      interval_cases i
      · simp [SubwordMemory.importedConstraintsMemoryPorts] at written
      · simp [SubwordMemory.importedConstraintsMemoryPorts] at written
      · exact (subword_store_ram_writable (by dsimp [timestampBase] at hp; omega) trace.rom.subwordMemory w core
          index address.symm)

end Airbender.Trace.RVWritable
