import Airbender.Review.Blake2Round.Row
import Airbender.Proofs.Blake2Round.Control
import Airbender.Proofs.Blake2Round.Preparation
import Airbender.Proofs.Blake2Round.PreparationBounds
import Airbender.Proofs.Blake2Round.Schedule
import Airbender.Proofs.Blake2Round.Soundness
import Airbender.Proofs.Blake2Round.Finalization
import Airbender.Proofs.Blake2Round.PortAddresses

namespace Airbender.Blake2Round.Row.Proofs
open Arithmetic

set_option maxHeartbeats 800000
set_option maxRecDepth 16384

theorem soundness {p : Nat} [Fact p.Prime] (hp : 8388608 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) :
    (circuitModel (p := p)).SoundnessUnder InterfaceAssumptions spec := by
  intro input output w ⟨interface, constraints, mapping⟩
  let prepared : Preparation.Output := ⟨Preparation.words w Variables.chainingInputs,
    Preparation.words w Variables.preparedState, Preparation.words w Variables.preparedMessage⟩
  have firstRound : w 142 = if (preparationInput input).firstRound then 1 else 0 := by
    have mask : w 142 = if (0 : Fin 10) = input.round then 1 else 0 := interface.roundMask 0
    by_cases zero : input.round = 0
    · simpa [preparationInput, zero] using mask
    · have nonzero : (0 : Fin 10) ≠ input.round := Ne.symm zero
      simpa [preparationInput, zero, nonzero] using mask
  have preparationMapping : Preparation.Mapping (preparationInput input) prepared w :=
    ⟨firstRound, mapping.compression, mapping.inputIsRight, mapping.state,
      mapping.extended, mapping.message, rfl, rfl, rfl⟩
  have preparation := Preparation.Proofs.soundness (by omega) setupTable
    (preparationInput input) prepared w ⟨constraints, preparationMapping⟩
  change prepared = Preparation.step (preparationInput input) at preparation
  have preparedBounds := Preparation.Proofs.output_bounded (input := preparationInput input)
    interface.state interface.extended interface.message
  rw [← preparation] at preparedBounds
  let scheduled := Preparation.words w Variables.scheduledMessage
  let scheduleInput : Schedule.Input := ⟨input.round, prepared.message⟩
  have scheduleMapping : Schedule.Mapping scheduleInput scheduled w := ⟨rfl, rfl⟩
  have schedule := Schedule.Proofs.soundness setupTable scheduleInput scheduled w
    ⟨⟨interface.roundMask⟩, constraints, scheduleMapping⟩
  change scheduled = Schedule.step scheduleInput at schedule
  have scheduledBounds : ∀ i : Fin 16, scheduled[i].Bounded := by
    intro i
    rw [schedule]
    simp only [Schedule.step, Fin.getElem_fin, Vector.getElem_map]
    exact preparedBounds.2.2 _
  let mixingInput : Mixing.Input := ⟨prepared.extended, scheduled⟩
  have mixingInterface : Mixing.InterfaceAssumptions mixingInput output.extended w := by
    constructor
    · intro i
      exact ⟨preparedBounds.2.1 ⟨i.val, by have := i.isLt; omega⟩,
        preparedBounds.2.1 ⟨8 + i.val, by have := i.isLt; omega⟩⟩
    · exact scheduledBounds
  have mixingMapping : Mixing.WordMapping mixingInput output.extended w :=
    ⟨rfl, rfl, mapping.extendedOutput⟩
  have mixing := Blake2Round.Proofs.mixing_soundness (by omega) compatible mixingInput output.extended w
    ⟨mixingInterface, constraints, mixingMapping⟩
  let finalInput : Finalization.Input := ⟨input.round, input.reducedRounds,
    input.state, prepared.chaining, output.extended⟩
  have finalMapping : Finalization.WordMapping finalInput output.state w :=
    ⟨mapping.reduced, mapping.state, rfl, mapping.extendedOutput, mapping.stateOutput⟩
  have finalization := Blake2Round.Proofs.finalization_soundness (by omega) compatible
    finalInput output.state w ⟨⟨interface.roundMask⟩, constraints, finalMapping⟩
  have controller := Control.Proofs.soundness (by omega) setupTable input.controller output.controller w
    ⟨constraints, mapping.controller⟩
  have compatible128 : 128 * (-15728640 : ZMod p) = 1 := by
    linear_combination compatible
  have addressMapping : Addresses.Mapping ⟨input.statePointer, input.messagePointer⟩ output.addresses w :=
    ⟨mapping.statePointer, mapping.messagePointer, mapping.addresses⟩
  have addresses := Addresses.Proofs.soundness hp compatible128
    ⟨input.statePointer, input.messagePointer⟩ output.addresses w
    ⟨interface.pointers, constraints, addressMapping⟩
  unfold spec
  refine ⟨controller, ?_, ?_, addresses⟩
  · simpa only [mixingInput, schedule, scheduleInput, preparation] using mixing
  · simpa only [finalInput, preparation] using finalization

end Airbender.Blake2Round.Row.Proofs
