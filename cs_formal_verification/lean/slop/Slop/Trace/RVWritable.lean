import Slop.Trace.RVZero
import Slop.WordMemory
import Slop.SubwordMemory

/-! RV-route writable-store law (piece E1, row level). A changing write (a port with `writeValue = some _`) whose
    address is a RAM cell lies in RV ROM-free RAM: only the word and subword store ports write RAM (their address tag
    is the store flag `w 10`), and `rom_selection` (the circuit rejects stores into ROM) gives `ROM_END ≤ index`.
    Register ports write register cells (tag 0), so they never meet a RAM address. -/

namespace Airbender.Trace.RVWritable
open Arithmetic Trace.Proofs

/-- A RAM cell's address code: tag 1 with the canonical limbs of `index`. -/
theorem ram_code_limbs {p : Nat} (index : BitVec 32) (tag : Nat) (lo hi : ZMod p)
    (same : Nat.pair tag (Nat.pair lo.val hi.val) = (Cell.ram index).addressCode) :
    tag = 1 ∧ lo.val = (Word.ofBitVec index).lo ∧ hi.val = (Word.ofBitVec index).hi := by
  change Nat.pair tag (Nat.pair lo.val hi.val) = Nat.pair 1 (Nat.pair (Word.ofBitVec index).lo (Word.ofBitVec index).hi) at same
  obtain ⟨tagEq, rest⟩ := Nat.pair_eq_pair.mp same
  obtain ⟨loEq, hiEq⟩ := Nat.pair_eq_pair.mp rest
  exact ⟨tagEq, loEq, hiEq⟩

/-- The RAM index's limbs are bounded, and its high limb is the Word high limb of the index. -/
theorem ram_index_rom_bound (index : BitVec 32) (high : 64 ≤ (Word.ofBitVec index).hi) :
    RV.ROM_END ≤ index.toNat := by
  unfold RV.ROM_END
  have small := index.isLt
  dsimp [Word.ofBitVec, limbBase] at high
  omega

/-- A store-port write into RAM lands at ROM_END or above (word store). -/
theorem word_store_ram_writable {p : Nat} [Fact p.Prime] (hp : 131072 < p)
    (setup : Table (ZMod p) (fields 9)) (w : Nat → ZMod p)
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (WordMemory.importedConstraints setup))
    (index : BitVec 32)
    (same : (WordMemory.importedConstraintsMemoryPorts[2]).address.code w = (Cell.ram index).addressCode) :
    RV.ROM_END ≤ index.toNat := by
  have tagged : Nat.pair (w 10).val (Nat.pair (w 25).val (w 26).val) = (Cell.ram index).addressCode := by
    simpa [WordMemory.importedConstraintsMemoryPorts, MemoryAddress.code, pairCode] using same
  obtain ⟨tagEq, loEq, hiEq⟩ := ram_code_limbs index _ (w 25) (w 26) tagged
  have store : w 10 = 1 := by
    have h10 := (ZMod.natCast_zmod_val (w 10)).symm
    rw [tagEq] at h10
    simpa using h10
  have bounded : (Word.ofBitVec index).Bounded := by
    unfold Word.Bounded Word.ofBitVec
    dsimp [limbBase]
    have small := index.isLt
    omega
  have classified := WordMemory.Proofs.rom_selection (by omega) true constraints
    (by simpa using store) (address := Word.ofBitVec index)
    (by rw [← hiEq]; exact (ZMod.natCast_zmod_val _).symm) bounded
  exact ram_index_rom_bound index (classified.2 rfl)

/-- A subword store-port write into RAM lands at ROM_END or above. -/
theorem subword_store_ram_writable {p : Nat} [Fact p.Prime] (hp : 131072 < p)
    (setup : Table (ZMod p) (fields 9)) (w : Nat → ZMod p)
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (SubwordMemory.importedConstraints setup))
    (index : BitVec 32)
    (same : (SubwordMemory.importedConstraintsMemoryPorts[2]).address.code w = (Cell.ram index).addressCode) :
    RV.ROM_END ≤ index.toNat := by
  have tagged : Nat.pair (w 10).val (Nat.pair (w 27).val (w 28).val) = (Cell.ram index).addressCode := by
    simpa [SubwordMemory.importedConstraintsMemoryPorts, MemoryAddress.code, pairCode] using same
  obtain ⟨tagEq, loEq, hiEq⟩ := ram_code_limbs index _ (w 27) (w 28) tagged
  have store : w 10 = 1 := by
    have h10 := (ZMod.natCast_zmod_val (w 10)).symm
    rw [tagEq] at h10
    simpa using h10
  have bounded : (Word.ofBitVec index).Bounded := by
    unfold Word.Bounded Word.ofBitVec
    dsimp [limbBase]
    have small := index.isLt
    omega
  have classified := SubwordMemory.Proofs.rom_selection (by omega) true constraints
    (by simpa using store) (address := Word.ofBitVec index)
    (by rw [← hiEq]; exact (ZMod.natCast_zmod_val _).symm) bounded
  exact ram_index_rom_bound index (classified.2 rfl)

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
