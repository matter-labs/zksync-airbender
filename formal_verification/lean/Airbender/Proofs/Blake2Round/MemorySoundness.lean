import Airbender.Proofs.Blake2Round.Memory

namespace Airbender.Blake2Round.Memory.Proofs
open Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

theorem soundness [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1) (data : Delegation.MemoryData p)
    (before : Reference.RiscV.Sail.State) (cells : List Cell) :
    (circuitModel data).SoundnessUnder (InterfaceAssumptions data before cells) Row.spec := by
  intro input output w ⟨interface, holds, mapping⟩
  have rules := Blake2Round.Proofs.memory_rules hp inverse interface.accepted
    interface.families interface.table interface.rounds
  have bounds (i : Fin 43) :
      (readToken w importedConstraintsMemoryPorts[i]).word.Bounded := by
    apply Delegation.Proofs.read_value_bounds (by norm_num [timestampBase]; omega)
      interface.accepted interface.publicState.toBoundaryInputs rules mapping.member
    change importedConstraintsMemoryPorts[i] ∈ importedConstraintsMemoryPorts
    exact Array.getElem_mem i.isLt
  have stateBounds : ∀ i : Fin 8, input.state[i].Bounded := by
    intro i
    have bound := bounds ⟨1 + i.val, by have := i.isLt; omega⟩
    rw [mapping.words.state]
    fin_cases i
    all_goals simpa [Trace.Proofs.read_word, importedConstraintsMemoryPorts,
      Preparation.words, Variables.stateReads, WordColumns.evaluate] using bound
  have extendedBounds : ∀ i : Fin 16, input.extended[i].Bounded := by
    intro i
    have bound := bounds ⟨9 + i.val, by have := i.isLt; omega⟩
    rw [mapping.words.extended]
    fin_cases i
    all_goals simpa [Trace.Proofs.read_word, importedConstraintsMemoryPorts,
      Preparation.words, Variables.extendedReads, WordColumns.evaluate] using bound
  have messageBounds : ∀ i : Fin 16, input.message[i].Bounded := by
    intro i
    have bound := bounds ⟨26 + i.val, by have := i.isLt; omega⟩
    rw [mapping.words.message]
    fin_cases i
    all_goals simpa [Trace.Proofs.read_word, importedConstraintsMemoryPorts,
      Preparation.words, Variables.messageReads, WordColumns.evaluate] using bound
  have pointers : input.statePointer.Bounded ∧ input.messagePointer.Bounded := by
    rw [mapping.words.statePointer, mapping.words.messagePointer]
    constructor
    · simpa [Trace.Proofs.read_word, importedConstraintsMemoryPorts, WordColumns.evaluate] using bounds 0
    · simpa [Trace.Proofs.read_word, importedConstraintsMemoryPorts, WordColumns.evaluate] using bounds 25
  have core := Verification.holds_of_sublist holds (List.sublist_append_left
    (importedConstraints setupTable) importedConstraintsTimestampLookups)
  exact Row.Proofs.soundness hp inverse input output w
    ⟨⟨mapping.round, pointers, stateBounds, extendedBounds, messageBounds⟩, core, mapping.words⟩

end Airbender.Blake2Round.Memory.Proofs
