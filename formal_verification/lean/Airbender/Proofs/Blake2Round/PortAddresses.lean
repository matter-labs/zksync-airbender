import Airbender.Review.Circuits.Blake2Round.Addresses
import Airbender.Proofs.Blake2Round.Addresses
import Airbender.Proofs.MemoryPorts

set_option warningAsError true

namespace Airbender.Blake2Round.Addresses.Proofs

theorem soundness {p : Nat} [Fact p.Prime] (hp : 8388608 ≤ p)
    (compatible : 128 * (-15728640 : ZMod p) = 1) :
    (circuitModel (p := p)).SoundnessUnder InterfaceAssumptions spec := by
  intro input output w ⟨bounds, constraints, mapping⟩
  have alignment := Blake2Round.Proofs.pointer_alignment hp compatible constraints
  have stateAligned : input.statePointer.lo % 128 = 0 := by
    rw [mapping.statePointer]; exact alignment.1
  have messageAligned : input.messagePointer.lo % 64 = 0 := by
    rw [mapping.messagePointer]; exact alignment.2
  have stateNoCarry (i : Fin 24) : input.statePointer.lo + 4 * i.val < Arithmetic.limbBase :=
    Verification.block_offset_bound (block := 128) (by norm_num [Arithmetic.limbBase])
      bounds.1.1 stateAligned (by have := i.isLt; omega)
  have messageNoCarry (i : Fin 16) : input.messagePointer.lo + 4 * i.val < Arithmetic.limbBase :=
    Verification.block_offset_bound (block := 64) (by norm_num [Arithmetic.limbBase])
      bounds.2.1 messageAligned (by have := i.isLt; omega)
  unfold spec
  rw [mapping.addresses]
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map, expected, Vector.getElem_ofFn]
  by_cases state : i < 24
  · rw [if_pos state, state_port_layout ⟨i, state⟩]
    exact Verification.IndirectPort.constant_address (by omega) rfl
      mapping.statePointer (stateNoCarry ⟨i, state⟩)
  · have size : i - 24 < 16 := by omega
    have index : 24 + (i - 24) = i := by omega
    have port := message_port_layout ⟨i - 24, size⟩
    simp only [index] at port
    rw [if_neg state, port]
    exact Verification.IndirectPort.constant_address (by omega) rfl
      mapping.messagePointer (messageNoCarry ⟨i - 24, size⟩)

end Airbender.Blake2Round.Addresses.Proofs
