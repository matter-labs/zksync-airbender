import Airbender.Proofs.Keccak.StateTrace
import Airbender.Proofs.Trace.MemoryFrame

namespace Airbender.Keccak.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384

theorem lane_half_address_injective (pointer : BitVec 32) (a b : Fin 31) (h k : Fin 2)
    (same : pointer + BitVec.ofNat 32 (8 * a.val + 4 * h.val) =
      pointer + BitVec.ofNat 32 (8 * b.val + 4 * k.val)) : a = b ∧ h = k := by
  have bits := (BitVec.add_right_inj pointer).mp same
  have values := congrArg BitVec.toNat bits
  have ab := a.isLt
  have bb := b.isLt
  have hb := h.isLt
  have kb := k.isLt
  simp only [BitVec.toNat_ofNat] at values
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at values
  exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩

private def halfPort (i : Fin 12) : MemoryPort :=
  importedConstraintsMemoryPorts[2 + i.val]'(by change 2 + i.val < 14; omega)

private theorem half_port_shape (i : Fin 12) :
    (halfPort i).address = .indirect importedConstraintsIndirectPorts[i] := by
  fin_cases i <;> rfl

theorem native_lane_frame [Fact p.Prime] {w : Nat → ZMod p}
    {pointer : BitVec 32} {before after : State} {cells : List Cell} {events : List MemoryAccess}
    (call : Fin 649) (effects : Native.RowEffects w) (active : w Variables.execute = 1)
    (control : (w Variables.controlReadLo).val = (scheduleControl ⟨call.val, by omega⟩).packed)
    (mapped : statePointer w = Word.ofBitVec pointer)
    (history : SailHistory cells events before after)
    (permutation : events.Perm ((Delegation.Row.mk .keccak w).memorySteps.map transferEvent))
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (tracked : ∀ physical : Fin 31, ∀ half : Fin 2,
      Cell.ram (pointer + BitVec.ofNat 32 (8 * physical.val + 4 * half.val)) ∈ cells)
    (readable : ∀ cell ∈ cells, ∃ value, cell.read before = .ok value before)
    (physical : Fin 31)
    (untouched : ∀ lane : Fin 6,
      (Controller.rows (Fin.ofNat 4096 ((scheduleControl ⟨call.val, by omega⟩).packed + 2048)))[lane] ≠ physical.val) :
    ramLane after (pointer + BitVec.ofNat 32 (8 * physical.val)) =
      ramLane before (pointer + BitVec.ofNat 32 (8 * physical.val)) := by
  have indices := scheduled_lane_indices call effects active control
  have frame (half : Fin 2) :
      ramWord after (pointer + BitVec.ofNat 32 (8 * physical.val + 4 * half.val)) =
        ramWord before (pointer + BitVec.ofNat 32 (8 * physical.val + 4 * half.val)) := by
    let other := Cell.ram (pointer + BitVec.ofNat 32 (8 * physical.val + 4 * half.val))
    have member : other ∈ cells := tracked physical half
    obtain ⟨value, read⟩ := readable other member
    have absent : ∀ event ∈ events, event.2.1 ≠ other.addressCode := by
      intro event present same
      obtain ⟨edge, edgeMember, rfl⟩ := List.mem_map.mp (permutation.mem_iff.mp present)
      obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp edgeMember
      have indexed : ∃ i : Fin 14, port = importedConstraintsMemoryPorts[i.val] := by
        have member : port ∈ importedConstraintsMemoryPorts := by
          simpa only [Delegation.Row.ports, Array.mem_toList_iff] using portMember
        obtain ⟨i, bound, equal⟩ := Array.mem_iff_getElem.mp member
        change i < 14 at bound
        exact ⟨⟨i, bound⟩, equal.symm⟩
      obtain ⟨i, rfl⟩ := indexed
      change importedConstraintsMemoryPorts[i.val].address.code w = other.addressCode at same
      clear portMember edgeMember present
      by_cases small : i.val < 2
      · fin_cases i <;>
          simp [importedConstraintsMemoryPorts, MemoryAddress.code, other, Cell.addressCode,
            Nat.pair_eq_pair] at same small
      · let position : Fin 12 := ⟨i.val - 2, by omega⟩
        have index : i.val = 2 + position.val := by dsimp [position]; omega
        have shape : importedConstraintsMemoryPorts[i.val].address =
            .indirect importedConstraintsIndirectPorts[position] := by
          simpa only [index, halfPort] using half_port_shape position
        rw [shape] at same
        have cell := indirect_cell same.symm
        have addresses := congrArg (fun cell : Cell => match cell with
          | .ram address => address
          | .register _ => 0) cell
        change pointer + BitVec.ofNat 32 (8 * physical.val + 4 * half.val) =
          (importedConstraintsIndirectPorts[position]).address w at addresses
        rw [effects.addresses.addresses position, mapped, Word.ofBitVec_roundtrip] at addresses
        let lane : Fin 6 := ⟨position.val / 2, by have := position.isLt; omega⟩
        let limb : Fin 2 := ⟨position.val % 2, Nat.mod_lt _ (by decide)⟩
        have selected := indices lane
        rw [selected] at addresses
        let key := Fin.ofNat 4096 ((scheduleControl ⟨call.val, by omega⟩).packed + 2048)
        let slot : Fin 31 := ⟨(Controller.rows key)[lane], Controller.Proofs.rows_bound key lane⟩
        have distinct := lane_half_address_injective pointer physical slot half limb addresses
        exact untouched lane (congrArg Fin.val distinct.1).symm
    have written := history_cell_frame history aligned other (aligned other member) absent read
    exact (ram_word_of_read written).trans (ram_word_of_read read).symm
  have low := frame 0
  have high := frame 1
  simp only [Fin.val_zero, Fin.val_one, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at low high
  simp only [BitVec.ofNat_add] at high
  rw [← BitVec.add_assoc] at high
  exact congrArg₂ (fun a b : Nat => a + 2 ^ 32 * b) low high

end Airbender.Keccak.Proofs
