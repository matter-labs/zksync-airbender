import Airbender.Review.Blake2G.Row
import Airbender.Proofs.Blake2G.Control
import Airbender.Proofs.Blake2G.Addresses
import Airbender.Proofs.Blake2G.State

namespace Airbender.Blake2G.Row.Proofs

set_option maxHeartbeats 800000

theorem soundness {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) :
    (circuitModel (p := p)).SoundnessUnder InterfaceAssumptions spec := by
  intro input output w ⟨interface, constraints, mapping⟩
  have controller := Control.Proofs.soundness (by omega) input.controller output.controller w
    ⟨constraints, mapping.controller⟩
  have stateBound (i : Fin 4) : output.controller.stateOffsets[i] < 16 := by
    rw [controller]
    exact Control.Proofs.state_offsets_bounded input.controller i
  have stateMapping : State.Mapping (stateInput input output.controller) output.state w := by
    refine ⟨mapping.words, ?_⟩
    intro i
    have binding := congrArg (fun c : Control.Output => c.stateOffsets[i]) mapping.controller.outputs
    have bound := stateBound i
    fin_cases i <;> simp [stateInput] at binding ⊢
    all_goals exact binding.symm.trans (Nat.mod_eq_of_lt bound).symm
  have active : w Variables.execute = 1 := by
    rw [mapping.controller.execute, interface.active]
    rfl
  have controlBound : (w Variables.controlReadLo).val < 256 := by
    rw [← mapping.controller.inputRegister]
    exact input.controller.register.isLt
  have state := State.Proofs.soundness (by omega) compatible (stateInput input output.controller)
    output.state w ⟨⟨active, controlBound, interface.inputs, interface.untouched⟩, constraints, stateMapping⟩
  have addressMapping : Addresses.Mapping (addressInput input) output.addresses w :=
    ⟨mapping.controller.inputRegister, mapping.controller.execute, mapping.statePointer,
      mapping.messagePointer, mapping.addresses⟩
  have addresses := Addresses.Proofs.soundness hp compatible (addressInput input) output.addresses w
    ⟨interface.pointers, constraints, addressMapping⟩
  exact ⟨controller, state, addresses⟩

/-- The schedule indices used to read the message block are canonical indices,
    not silently reduced out-of-range values. -/
theorem message_indices_exact {p : Nat} [Fact p.Prime] (hp : 512 ≤ p)
    {input : Input} {output : Output} {w : Nat → ZMod p}
    (row : (circuitModel (p := p)).relation input output w) (i : Fin 2) :
    (Fin.ofNat 16 output.controller.messageOffsets[i]).val = output.controller.messageOffsets[i] := by
  have controller := Control.Proofs.soundness hp input.controller output.controller w
    ⟨row.1, row.2.controller⟩
  rw [controller]
  exact Nat.mod_eq_of_lt (Control.Proofs.message_offsets_bounded input.controller i)

end Airbender.Blake2G.Row.Proofs
