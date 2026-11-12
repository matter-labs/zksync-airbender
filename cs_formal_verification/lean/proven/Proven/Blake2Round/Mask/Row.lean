module
public import Proven.Blake2Round.Mask.Schedule
public import Proven.Blake2Round.Mask.Mixing
public import Proven.Blake2Round.Mask.Finalization
public import Proven.Blake2Round.Mask.Ports
public import Proven.Blake2Round.Preparation
public import Proven.Blake2Round.PreparationBounds
public import Proven.Blake2Round.Control
public import Proven.Blake2Round.PortAddresses

@[expose] public section
namespace Airbender.Blake2Round.Mask.Proofs
open Arithmetic
set_option maxRecDepth 16384

/-- Native word and Boolean interfaces give the complete arbitrary-mask round. -/
theorem soundness : SoundnessClaim := by
  intro input output w assumptions constraints mapping
  have stateMap : input.state = Preparation.words w Variables.stateReads := by
    rw [mapping.state]
    apply Vector.ext
    intro i hi
    simpa only [Fin.getElem_fin, Vector.getElem_ofFn] using state_reads w ⟨i, hi⟩
  have extendedMap : input.extended = Preparation.words w Variables.extendedReads := by
    rw [mapping.extended]
    apply Vector.ext
    intro i hi
    simpa only [Fin.getElem_fin, Vector.getElem_ofFn] using extended_reads w ⟨i, hi⟩
  have messageMap : input.message = Preparation.words w Variables.messageReads := by
    rw [mapping.message]
    apply Vector.ext
    intro i hi
    simpa only [Fin.getElem_fin, Vector.getElem_ofFn] using message_reads w ⟨i, hi⟩
  have stateOutMap : output.state = Preparation.words w Finalization.stateWrites := by
    rw [mapping.stateOutput]
    apply Vector.ext
    intro i hi
    simpa only [Fin.getElem_fin, Vector.getElem_ofFn] using state_writes w ⟨i, hi⟩
  have extendedOutMap : output.extended = Preparation.words w Mixing.extendedWrites := by
    rw [mapping.extendedOutput]
    apply Vector.ext
    intro i hi
    simpa only [Fin.getElem_fin, Vector.getElem_ofFn] using extended_writes w ⟨i, hi⟩
  let prepared : Preparation.Output := ⟨Preparation.words w Variables.chainingInputs,
    Preparation.words w Variables.preparedState, Preparation.messageWords w⟩
  have first : w 142 = if (preparationInput input).firstRound then 1 else 0 := by
    have bit := mapping.rounds 0
    by_cases selected : input.rounds 0 = true
    · simpa [preparationInput, selected] using bit
    · simpa [preparationInput, selected] using bit
  have prepMapping : Preparation.Mapping (preparationInput input) prepared w :=
    ⟨first, mapping.compression, mapping.inputIsRight, stateMap, extendedMap, messageMap, rfl, rfl, rfl⟩
  have preparation := Preparation.Proofs.soundness (by decide) setupTable
    (preparationInput input) prepared w ⟨constraints, prepMapping⟩
  change prepared = Preparation.step (preparationInput input) at preparation
  have preparedBounds := Preparation.Proofs.output_bounded (input := preparationInput input)
    assumptions.state assumptions.extended assumptions.message
  rw [← preparation] at preparedBounds
  let scheduled := Preparation.words w Variables.scheduledMessage
  have roundIndices : ∀ round : Fin 10, Variables.roundBits[round] = 142 + round.val := by decide
  have schedule : scheduled = scheduledMessage input.rounds prepared.message :=
    scheduled_messages constraints input.rounds (fun round => by
      rw [roundIndices]
      exact mapping.rounds round)
      preparedBounds.2.2
  let mixingInput : Mixing.Input := ⟨prepared.extended, scheduled⟩
  have mixingMapping : Mixing.WordMapping mixingInput output.extended w := ⟨rfl, rfl, extendedOutMap⟩
  have mixing := Blake2Round.Proofs.mixing_soundness_wide (by decide) (by decide)
    constraints mixingMapping preparedBounds.2.1 (by
      intro i
      change scheduled[i].lo < 655360 ∧ scheduled[i].hi < 655360
      rw [schedule]
      exact scheduled_bounds input.rounds prepared.message preparedBounds.2.2 i)
  have finalization := finalization_of_flag (isFinal input) constraints (finalization_flag constraints mapping)
  rw [← stateOutMap, ← extendedOutMap, ← stateMap] at finalization
  have controller := Control.Proofs.soundness (by decide) setupTable input.controller output.controller w
    ⟨constraints, mapping.controller.trans (control_read w), mapping.controllerOutput.trans (control_write w)⟩
  have addressMapping : Addresses.Mapping ⟨input.statePointer, input.messagePointer⟩ output.addresses w :=
    ⟨mapping.statePointer.trans (state_pointer w), mapping.messagePointer.trans (message_pointer w), mapping.addresses⟩
  have addresses := Addresses.Proofs.soundness (by decide) (by decide)
    ⟨input.statePointer, input.messagePointer⟩ output.addresses w
    ⟨assumptions.pointers, constraints, addressMapping⟩
  unfold spec
  refine ⟨controller, ?_, ?_, addresses⟩
  · simpa only [mixingInput, schedule, preparation] using mixing
  · rw [← preparation]
    exact finalization

end Airbender.Blake2Round.Mask.Proofs
