import Airbender.Proofs.Delegation.AtomicHistory
import Airbender.Proofs.Arithmetic.Word

namespace Airbender.Delegation.Proofs
open Trace Trace.Proofs Arithmetic Reference.RiscV.Sail
set_option warningAsError true

def ramWord (state : State) (address : BitVec 32) : Nat :=
  match (Cell.ram address).read state with
  | .ok value _ => value.toNat
  | _ => 0

def ramLane (state : State) (address : BitVec 32) : Nat :=
  ramWord state address + 2 ^ 32 * ramWord state (address + 4)

theorem ram_word_bound (state : State) (address : BitVec 32) :
    ramWord state address < wordModulus := by
  cases read : (Cell.ram address).read state with
  | ok value state => simpa only [ramWord, read, wordModulus] using value.isLt
  | error error state => simp only [ramWord, read]; decide

def ramEncoding (state : State) (address : BitVec 32) : Word :=
  Word.ofBitVec (BitVec.ofNat 32 (ramWord state address))

theorem ram_encoding_value (state : State) (address : BitVec 32) :
    (ramEncoding state address).value = ramWord state address := by
  rw [ramEncoding, Word.ofBitVec_value, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  exact ram_word_bound state address

theorem ram_encoding_native {state : State} {address : BitVec 32} {word : Word}
    (bound : word.Bounded) (value : ramWord state address = word.value) :
    ramEncoding state address = word :=
  Word.eq_of_value (Word.ofBitVec_bound _) bound ((ram_encoding_value state address).trans value)

theorem ram_word_of_read {state : State} {address : BitVec 32} {value : BitVec 32}
    (read : (Cell.ram address).read state = .ok value state) :
    ramWord state address = value.toNat := by
  simp only [ramWord, read]

theorem indirect_cell {p : Nat} {w : Nat → ZMod p} {port : Verification.IndirectPort} {cell : Cell}
    (code : cell.addressCode = (MemoryAddress.indirect port).code w) :
    cell = .ram (port.address w) := by
  cases cell with
  | register index => simp [Cell.addressCode, MemoryAddress.code, Nat.pair_eq_pair] at code
  | ram address =>
    have word := address_word code.symm
    have bits := congrArg Word.toBitVec word
    have same : port.address w = address := by
      simpa only [MemoryAddress.word, Verification.IndirectPort.rawAddress,
        Verification.IndirectPort.address, Cell.addressWord, Word.ofBitVec_roundtrip] using bits
    exact congrArg Cell.ram same.symm

theorem indirect_word_observations {p : Nat} {w : Nat → ZMod p}
    {port : MemoryPort} {indirect : Verification.IndirectPort} {before after : State}
    (shape : port.address = .indirect indirect)
    (reads : (readToken w port).word.Bounded)
    (writes : (Arithmetic.Word.mk (Nat.unpair (port.writeCode w)).1
      (Nat.unpair (port.writeCode w)).2).Bounded)
    (observed : ∃ cell : Cell, cell.addressCode = port.address.code w ∧
      cell.read before = .ok (memoryWord (port.readCode w)) before ∧
      cell.read after = .ok (memoryWord (port.writeCode w)) after) :
    ramWord before (indirect.address w) = (readToken w port).word.value ∧
      ramWord after (indirect.address w) =
        (Arithmetic.Word.mk (Nat.unpair (port.writeCode w)).1
          (Nat.unpair (port.writeCode w)).2).value := by
  obtain ⟨cell, code, read, written⟩ := observed
  rw [shape] at code
  have same := indirect_cell code
  subst cell
  have readValue := ram_word_of_read read
  have writtenValue := ram_word_of_read written
  constructor
  · exact readValue.trans (Word.toBitVec_toNat reads)
  · exact writtenValue.trans (Word.toBitVec_toNat writes)

theorem initialized_indirect_cell_at_boundary [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {initial : State} {cells : List Cell} (inputs : BoundaryInputs data initial cells)
    {row : Row p} (member : row ∈ data.rows) {port : MemoryPort} (present : port ∈ row.ports)
    {indirect : Verification.IndirectPort} (shape : port.address = .indirect indirect) :
    Cell.ram (indirect.address row.assignment) ∈ cells := by
  have edgeMember : (readToken row.assignment port, row.writeToken port) ∈ data.steps := by
    apply List.mem_flatMap.mpr
    refine ⟨row, member, ?_⟩
    apply List.mem_map.mpr
    exact ⟨port, by simpa only [Array.mem_toList_iff] using present, rfl⟩
  obtain ⟨cell, tracked, code⟩ := initialized_cell hp accepted inputs edgeMember
  change cell.addressCode = port.address.code row.assignment at code
  rw [shape] at code
  have same := indirect_cell code
  exact same ▸ tracked

theorem initialized_indirect_cell [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {initial : State} {cells : List Cell} (inputs : MemoryInputs data initial cells)
    {row : Row p} (member : row ∈ data.rows) {port : MemoryPort} (present : port ∈ row.ports)
    {indirect : Verification.IndirectPort} (shape : port.address = .indirect indirect) :
    Cell.ram (indirect.address row.assignment) ∈ cells :=
  initialized_indirect_cell_at_boundary hp accepted inputs.toBoundaryInputs member present shape

end Airbender.Delegation.Proofs
