import Slop.Blake2G.BlockFrame
import Slop.Delegation.CopyFrame

namespace Airbender.Blake2G.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000

theorem native_block_frame {p : Nat} {w : Nat → ZMod p}
    {state message : BitVec 32} {before after : State} {cells : List Cell} {events : List MemoryAccess}
    (controller : Control.Input)
    (addresses : Addresses.spec ⟨controller, Word.ofBitVec state, Word.ofBitVec message⟩
      (importedConstraintsIndirectPorts.map (fun port => port.address w)))
    (stateAligned : state.toNat % 64 = 0) (messageAligned : message.toNat % 64 = 0)
    (distinct : state ≠ message)
    (history : SailHistory cells events before after)
    (permutation : events.Perm ((Delegation.Row.mk .blakeG w).memorySteps.map transferEvent))
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (tracked : ∀ block : Bool, ∀ word : Fin 16,
      Cell.ram ((if block then state else message) + BitVec.ofNat 32 (4 * word.val)) ∈ cells)
    (readable : ∀ cell ∈ cells, ∃ value, cell.read before = .ok value before)
    (block : Bool) (word : Fin 16)
    (untouched : block = true → ∀ lane : Fin 4,
      (Control.step controller).stateOffsets[lane] ≠ word.val) :
    ramEncoding after ((if block then state else message) + BitVec.ofNat 32 (4 * word.val)) =
      ramEncoding before ((if block then state else message) + BitVec.ofNat 32 (4 * word.val)) := by
  let target := Cell.ram ((if block then state else message) + BitVec.ofNat 32 (4 * word.val))
  have member : target ∈ cells := tracked block word
  obtain ⟨value, read⟩ := readable target member
  have stateAbsent (lane : Fin 4) :
      (MemoryAddress.indirect importedConstraintsIndirectPorts[lane.val]).code w ≠ target.addressCode := by
    intro same
    have cell := indirect_cell same.symm
    have address := Cell.ram.inj cell
    have actual := congrArg (fun values : Vector (BitVec 32) 6 => values[lane.val]) addresses
    simp only [Vector.getElem_map] at actual
    have expected : (Addresses.expected ⟨controller, Word.ofBitVec state, Word.ofBitVec message⟩)[lane.val] =
      state + BitVec.ofNat 32 (4 * (Control.step controller).stateOffsets[lane]) := by
      fin_cases lane <;> simp [Addresses.expected, Word.ofBitVec_roundtrip]
    rw [expected] at actual
    change ((if block then state else message) + BitVec.ofNat 32 (4 * word.val)) =
      importedConstraintsIndirectPorts[lane.val].address w at address
    rw [actual] at address
    let selected : Fin 16 := ⟨(Control.step controller).stateOffsets[lane],
      Control.Proofs.state_offsets_bounded controller lane⟩
    cases block with
    | false =>
      exact aligned_block_words_distinct state message stateAligned messageAligned distinct selected word address.symm
    | true =>
      have equal := block_word_injective state word selected address
      exact untouched rfl lane (congrArg Fin.val equal).symm
  have copies : ∀ event ∈ events, event.2.1 = target.addressCode →
      memoryWord event.2.2.1 = memoryWord event.2.2.2 := by
    intro event present same
    obtain ⟨edge, included, rfl⟩ := List.mem_map.mp (permutation.mem_iff.mp present)
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp included
    have indexed : ∃ i : Fin 9, port = importedConstraintsMemoryPorts[i.val] := by
      have member : port ∈ importedConstraintsMemoryPorts := by
        simpa only [Delegation.Row.ports, Array.mem_toList_iff] using portMember
      obtain ⟨i, bound, equal⟩ := Array.mem_iff_getElem.mp member
      change i < 9 at bound
      exact ⟨⟨i, bound⟩, equal.symm⟩
    obtain ⟨i, rfl⟩ := indexed
    change importedConstraintsMemoryPorts[i.val].address.code w = target.addressCode at same
    fin_cases i
    · rfl
    · exact False.elim (stateAbsent 0 same)
    · exact False.elim (stateAbsent 1 same)
    · exact False.elim (stateAbsent 2 same)
    · exact False.elim (stateAbsent 3 same)
    · rfl
    · rfl
    · rfl
    · simp [importedConstraintsMemoryPorts, MemoryAddress.code, target, Cell.addressCode,
        Nat.pair_eq_pair] at same
  have written := history_cell_copy_frame history aligned target (aligned target member)
    (by simp [target]) copies read
  have words := (ram_word_of_read written).trans (ram_word_of_read read).symm
  exact congrArg (fun value : Nat => Word.ofBitVec (BitVec.ofNat 32 value)) words

end Airbender.Blake2G.Proofs
