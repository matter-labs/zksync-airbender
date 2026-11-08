import Slop.Blake2Round.RVStateTrace
import Slop.Blake2Round.Compression
import Slop.Delegation.RVNativeViews
import Slop.Delegation.RVCallLink
import Slop.Blake2Round.StateTransport

/-! RV twins of `StateTransport.native_word_observations` and `PhysicalWords.physical_row_words` for the
    extended-BLAKE row, and the row frame: a round call's RV history touches only x10, x11, x12, the 24 state words
    at x10 and the 16 message words at x11 (RAM at any address, the shadow RAM below `ROM_END` included). -/

namespace Airbender.Blake2Round.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384

def rvPhysicalState (state : RV.State) (pointer : BitVec 32) : Compression.State :=
  (rvBlockWords state pointer 8 0, rvBlockWords state pointer 16 8)

private theorem rv_word_port_address (index : Fin 40) :
    (importedConstraintsMemoryPorts[wordIndex index]).address = .indirect importedConstraintsIndirectPorts[index] := by
  fin_cases index <;> rfl

/-- The address of indirect port `index` of a row with pointers `state`/`message`. -/
theorem round_word_address {p : Nat} {w : Nat → ZMod p} {round : Fin 10} {state message : BitVec 32}
    (addresses : Addresses.spec ⟨(Native.input round w).statePointer, (Native.input round w).messagePointer⟩
      (Native.output w).addresses)
    (pointers : (Native.input round w).statePointer = Word.ofBitVec state ∧
      (Native.input round w).messagePointer = Word.ofBitVec message) (index : Fin 40) :
    importedConstraintsIndirectPorts[index].address w =
      if index.val < 24 then state + BitVec.ofNat 32 (4 * index.val)
      else message + BitVec.ofNat 32 (4 * (index.val - 24)) := by
  have address := congrArg (fun values : Vector (BitVec 32) 40 => values[index]) addresses
  change (importedConstraintsIndirectPorts.map (fun port => port.address w))[index] = _ at address
  simpa only [Fin.getElem_fin, Vector.getElem_map, Addresses.expected, Vector.getElem_ofFn, pointers.1, pointers.2,
    Word.ofBitVec_roundtrip] using address

theorem rv_round_word_observations {p : Nat} {w : Nat → ZMod p} {before after : RV.State} {round : Fin 10}
    {state message : BitVec 32}
    (addresses : Addresses.spec ⟨(Native.input round w).statePointer, (Native.input round w).messagePointer⟩
      (Native.output w).addresses)
    (pointers : (Native.input round w).statePointer = Word.ofBitVec state ∧
      (Native.input round w).messagePointer = Word.ofBitVec message)
    (reads : ∀ port ∈ (⟨.blakeRound, w⟩ : Delegation.Row p).ports, (readToken w port).word.Bounded)
    (writes : ∀ port ∈ (⟨.blakeRound, w⟩ : Delegation.Row p).ports,
      ((⟨.blakeRound, w⟩ : Delegation.Row p).writeToken port).word.Bounded)
    (observed : ∀ port ∈ (⟨.blakeRound, w⟩ : Delegation.Row p).ports,
      ∃ cell : Cell, cell.addressCode = port.address.code w ∧
        cell.readRV before = some (memoryWord (port.readCode w)) ∧
        cell.readRV after = some (memoryWord (port.writeCode w))) (index : Fin 40) :
    let address := if index.val < 24 then state + BitVec.ofNat 32 (4 * index.val)
      else message + BitVec.ofNat 32 (4 * (index.val - 24))
    rvRamEncoding before address = (⟨.blakeRound, w⟩ : Delegation.Row p).readWord (wordIndex index) ∧
      rvRamEncoding after address = (⟨.blakeRound, w⟩ : Delegation.Row p).writtenWord (wordIndex index) := by
  have member : importedConstraintsMemoryPorts[wordIndex index] ∈ (⟨.blakeRound, w⟩ : Delegation.Row p).ports :=
    Array.getElem_mem (wordIndex index).isLt
  have result := rv_indirect_word_observations (rv_word_port_address index)
    (reads _ member) (writes _ member) (observed _ member)
  rw [round_word_address addresses pointers index] at result
  exact result

theorem rv_physical_row_words {p : Nat} {w : Nat → ZMod p} {before after : RV.State}
    {statePointer messagePointer : BitVec 32} (round : Fin 10)
    (observed : ∀ index : Fin 40,
      let address := if index.val < 24 then statePointer + BitVec.ofNat 32 (4 * index.val)
        else messagePointer + BitVec.ofNat 32 (4 * (index.val - 24))
      rvRamEncoding before address = (⟨.blakeRound, w⟩ : Delegation.Row p).readWord (wordIndex index) ∧
        rvRamEncoding after address = (⟨.blakeRound, w⟩ : Delegation.Row p).writtenWord (wordIndex index)) :
    (Native.input round w).state = (rvPhysicalState before statePointer).1 ∧
      (Native.input round w).extended = (rvPhysicalState before statePointer).2 ∧
      (Native.input round w).message = rvBlockWords before messagePointer 16 0 ∧
      (Native.output w).state = (rvPhysicalState after statePointer).1 ∧
      (Native.output w).extended = (rvPhysicalState after statePointer).2 ∧
      rvBlockWords before messagePointer 16 0 = rvBlockWords after messagePointer 16 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Vector.ext
    intro i bound
    change i < 8 at bound
    have result := (observed ⟨i, by omega⟩).1.symm
    interval_cases i
    all_goals simpa [Native.input, rvPhysicalState, rvBlockWords, wordIndex,
      Delegation.Row.readWord, Delegation.Row.ports] using result
  · apply Vector.ext
    intro i bound
    change i < 16 at bound
    have result := (observed ⟨8 + i, by omega⟩).1.symm
    interval_cases i
    all_goals simpa [Native.input, rvPhysicalState, rvBlockWords, wordIndex,
      Delegation.Row.readWord, Delegation.Row.ports] using result
  · apply Vector.ext
    intro i bound
    change i < 16 at bound
    have result := (observed ⟨24 + i, by omega⟩).1.symm
    interval_cases i
    all_goals simpa [Native.input, rvBlockWords, wordIndex,
      Delegation.Row.readWord, Delegation.Row.ports] using result
  · apply Vector.ext
    intro i bound
    change i < 8 at bound
    have result := (observed ⟨i, by omega⟩).2.symm
    interval_cases i
    all_goals simpa [Native.output, rvPhysicalState, rvBlockWords, wordIndex,
      Delegation.Row.writtenWord, Delegation.Row.ports] using result
  · apply Vector.ext
    intro i bound
    change i < 16 at bound
    have result := (observed ⟨8 + i, by omega⟩).2.symm
    interval_cases i
    all_goals simpa [Native.output, rvPhysicalState, rvBlockWords, wordIndex,
      Delegation.Row.writtenWord, Delegation.Row.ports] using result
  · apply Vector.ext
    intro i bound
    change i < 16 at bound
    have port : ∀ index : Fin 16,
        (importedConstraintsMemoryPorts[26 + index.val]'(by change 26 + index.val < 43; omega)).writeValue = none := by
      intro index
      fin_cases index <;> rfl
    have same : ((⟨.blakeRound, w⟩ : Delegation.Row p).readWord (wordIndex ⟨24 + i, by omega⟩)) =
        ((⟨.blakeRound, w⟩ : Delegation.Row p).writtenWord (wordIndex ⟨24 + i, by omega⟩)) := by
      simp only [wordIndex, show ¬ 24 + i < 24 by omega, ↓reduceDIte]
      have position : 2 + (24 + i) = 26 + i := by omega
      simp only [position, Delegation.Row.readWord, Delegation.Row.writtenWord, Delegation.Row.ports,
        Delegation.Row.writeToken, readToken, MemoryToken.word, MemoryPort.writeCode, port ⟨i, bound⟩,
        Option.getD_none, MemoryPort.readCode]
    have result := (observed ⟨24 + i, by omega⟩).1.trans
      (same.trans (observed ⟨24 + i, by omega⟩).2.symm)
    simpa [rvBlockWords, show ¬ 24 + i < 24 by omega] using result

/-- Every native round port touches x10, x11, x12, a state word at x10 or a message word at x11. -/
theorem round_port_cell {p : Nat} {w : Nat → ZMod p} {state message : BitVec 32}
    (address : ∀ index : Fin 40, importedConstraintsIndirectPorts[index].address w =
      if index.val < 24 then state + BitVec.ofNat 32 (4 * index.val)
      else message + BitVec.ofNat 32 (4 * (index.val - 24)))
    {cell : Cell} (i : Fin 43)
    (code : cell.addressCode = importedConstraintsMemoryPorts[i.val].address.code w) :
    cell = .register 10 ∨ cell = .register 11 ∨ cell = .register 12 ∨
      (∃ j : Fin 24, cell = .ram (state + BitVec.ofNat 32 (4 * j.val))) ∨
      ∃ j : Fin 16, cell = .ram (message + BitVec.ofNat 32 (4 * j.val)) := by
  by_cases zero : i.val = 0
  · have same : i = 0 := Fin.ext zero
    subst same
    exact Or.inl (cell_address_injective code)
  by_cases eleven : i.val = 25
  · have same : i = 25 := Fin.ext eleven
    subst same
    exact Or.inr (Or.inl (cell_address_injective code))
  by_cases twelve : i.val = 42
  · have same : i = 42 := Fin.ext twelve
    subst same
    exact Or.inr (Or.inr (Or.inl (cell_address_injective code)))
  let index : Fin 40 := ⟨if i.val < 25 then i.val - 1 else i.val - 2, by have := i.isLt; split <;> omega⟩
  have position : i = wordIndex index := by
    apply Fin.ext
    simp only [wordIndex, index]
    split <;> split <;> simp_all <;> omega
  have shape : importedConstraintsMemoryPorts[(wordIndex index).val].address =
      .indirect importedConstraintsIndirectPorts[index] := rv_word_port_address index
  rw [position, shape] at code
  have equal := indirect_cell code
  rw [address index] at equal
  right; right; right
  by_cases low : index.val < 24
  · rw [ite_eq_left low] at equal
    exact Or.inl ⟨⟨index.val, low⟩, equal⟩
  · rw [ite_eq_right low] at equal
    exact Or.inr ⟨⟨index.val - 24, by omega⟩, equal⟩

/-- A round call's RV history leaves every register but x10/x11/x12 and every RAM word outside both blocks
    unchanged. -/
theorem rv_round_row_frame {p : Nat} {w : Nat → ZMod p} {state message : BitVec 32}
    {before after : RV.State} {cells : List Cell} {events : List MemoryAccess}
    (address : ∀ index : Fin 40, importedConstraintsIndirectPorts[index].address w =
      if index.val < 24 then state + BitVec.ofNat 32 (4 * index.val)
      else message + BitVec.ofNat 32 (4 * (index.val - 24)))
    (observed : ∀ port ∈ (⟨.blakeRound, w⟩ : Delegation.Row p).ports,
      ∃ cell : Cell, cell.addressCode = port.address.code w)
    (history : RVHistory cells events before after)
    (permutation : events.Perm ((Delegation.Row.mk .blakeRound w).memorySteps.map transferEvent))
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    (∀ r : BitVec 5, r ≠ 10 → r ≠ 11 → r ≠ 12 → after.getReg r = before.getReg r) ∧
    (∀ a : BitVec 32, a.toNat % 4 = 0 → (∀ j : Fin 24, a ≠ state + BitVec.ofNat 32 (4 * j.val)) →
      (∀ j : Fin 16, a ≠ message + BitVec.ofNat 32 (4 * j.val)) → RV.read after.mem a 4 = RV.read before.mem a 4) := by
  have touched : ∀ event ∈ events, ∃ cell : Cell, cell.addressCode = event.2.1 ∧
      (cell = .register 10 ∨ cell = .register 11 ∨ cell = .register 12 ∨
        (∃ j : Fin 24, cell = .ram (state + BitVec.ofNat 32 (4 * j.val))) ∨
        ∃ j : Fin 16, cell = .ram (message + BitVec.ofNat 32 (4 * j.val))) := by
    intro event present
    obtain ⟨edge, included, rfl⟩ := List.mem_map.mp (permutation.mem_iff.mp present)
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp included
    have member : port ∈ importedConstraintsMemoryPorts := by
      simpa only [Delegation.Row.ports, Array.mem_toList_iff] using portMember
    obtain ⟨i, bound, equal⟩ := Array.mem_iff_getElem.mp member
    obtain ⟨cell, code⟩ := observed port (by simpa only [Delegation.Row.ports] using member)
    refine ⟨cell, code, ?_⟩
    subst equal
    exact round_port_cell address ⟨i, bound⟩ code
  constructor
  · intro r r10 r11 r12
    have untouched : ∀ event ∈ events, event.2.1 ≠ (Cell.register r).addressCode := by
      intro event present same
      obtain ⟨cell, code, kind⟩ := touched event present
      have equal : cell = .register r := cell_address_injective (code.trans same)
      subst equal
      rcases kind with h | h | h | ⟨j, h⟩ | ⟨j, h⟩
      · exact r10 (Cell.register.inj h)
      · exact r11 (Cell.register.inj h)
      · exact r12 (Cell.register.inj h)
      · cases h
      · cases h
    have frame := rv_history_cell_frame history aligned (.register r) trivial untouched (readRV_register r before)
    rw [readRV_register] at frame
    exact Option.some.inj frame
  · intro a alignedA outsideState outsideMessage
    have untouched : ∀ event ∈ events, event.2.1 ≠ (Cell.ram a).addressCode := by
      intro event present same
      obtain ⟨cell, code, kind⟩ := touched event present
      have equal : cell = .ram a := cell_address_injective (code.trans same)
      subst equal
      rcases kind with h | h | h | ⟨j, h⟩ | ⟨j, h⟩
      · cases h
      · cases h
      · cases h
      · exact outsideState j (Cell.ram.inj h)
      · exact outsideMessage j (Cell.ram.inj h)
    have readable := readable_of_aligned (address := a) alignedA
    have frame := rv_history_cell_frame history aligned (.ram a) alignedA untouched (readRV_ram before readable)
    rw [readRV_ram after readable] at frame
    exact Option.some.inj frame

end Airbender.Blake2Round.Proofs
