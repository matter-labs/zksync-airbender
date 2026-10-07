import Airbender.Review.Blake2G.Addresses
import Airbender.Proofs.Blake2G.Control
import Airbender.Proofs.MemoryPorts

namespace Airbender.Blake2G.Addresses.Proofs

set_option maxHeartbeats 800000

theorem soundness {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) :
    (circuitModel (p := p)).SoundnessUnder InterfaceAssumptions spec := by
  intro input output w relation
  obtain ⟨bounds, constraints, mapping⟩ := relation
  let controlOutput : Control.Output :=
    ⟨⟨(w 5).val, (w 6).val⟩,
      Variables.stateOffsetColumns.map (fun column => (w column).val),
      Variables.messageOffsetColumns.map (fun column => (w column).val)⟩
  have controlMapping : Control.Mapping input.controller controlOutput w :=
    ⟨mapping.controlRegister, mapping.execute, rfl⟩
  have controlSound := Control.Proofs.soundness (p := p) (by omega)
    input.controller controlOutput w ⟨constraints, controlMapping⟩
  have stateIndices := congrArg Control.Output.stateOffsets controlSound
  have messageIndices := congrArg Control.Output.messageOffsets controlSound
  have stateIndex (i : Fin 4) :
      (w Variables.stateOffsetColumns[i]).val = (Control.step input.controller).stateOffsets[i] := by
    have equation := congrArg (fun (v : Vector Nat 4) => v[i]) stateIndices
    fin_cases i <;> simpa [controlOutput] using equation
  have messageIndex (i : Fin 2) :
      (w Variables.messageOffsetColumns[i]).val = (Control.step input.controller).messageOffsets[i] := by
    have equation := congrArg (fun (v : Vector Nat 2) => v[i]) messageIndices
    fin_cases i <;> simpa [controlOutput] using equation
  have stateBound (i : Fin 4) : (Control.step input.controller).stateOffsets[i] < 16 := by
    exact Control.Proofs.state_offsets_bounded input.controller i
  have messageBound (i : Fin 2) : (Control.step input.controller).messageOffsets[i] < 16 := by
    exact Control.Proofs.message_offsets_bounded input.controller i
  have alignment := Airbender.Blake2G.Proofs.pointer_alignment hp compatible constraints
  have stateAligned : input.statePointer.lo % 64 = 0 := by
    rw [mapping.statePointer]
    exact alignment.1
  have messageAligned : input.messagePointer.lo % 64 = 0 := by
    rw [mapping.messagePointer]
    exact alignment.2
  unfold spec
  rw [mapping.addresses, indirect_port_layout]
  apply Vector.ext
  intro i hi
  interval_cases i
  all_goals simp only [expected, Vector.getElem_map, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals apply Verification.IndirectPort.word_address (by omega) rfl rfl
  all_goals first
    | exact mapping.statePointer
    | exact mapping.messagePointer
    | exact stateIndex 0
    | exact stateIndex 1
    | exact stateIndex 2
    | exact stateIndex 3
    | exact messageIndex 0
    | exact messageIndex 1
    | exact bounds.1.1
    | exact bounds.2.1
    | exact stateAligned
    | exact messageAligned
    | exact stateBound 0
    | exact stateBound 1
    | exact stateBound 2
    | exact stateBound 3
    | exact messageBound 0
    | exact messageBound 1

end Airbender.Blake2G.Addresses.Proofs
