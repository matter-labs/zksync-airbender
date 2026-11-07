import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Review.Circuits.Blake2G.Memory
import Airbender.Proofs.Blake2G.Memory

namespace Airbender.Blake2G.Memory.Proofs
open Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384

theorem soundness [Fact p.Prime] (hp : FieldCapacity.NativeRomCapacity p)
    (inverse : SerializedInverse.Scale64 p) (data : Delegation.MemoryData p)
    (before : Reference.RiscV.Sail.State) (cells : List Cell) :
    (circuitModel data).SoundnessUnder (InterfaceAssumptions data before cells) Blake2G.spec := by
  intro input output w ⟨interface, holds, mapping⟩
  have rules := Blake2G.Proofs.memory_rules hp inverse interface.accepted interface.families interface.table
  have bounds (i : Fin 9) :
      (readToken w importedConstraintsMemoryPorts[i]).word.Bounded := by
    apply Delegation.Proofs.read_value_bounds (by norm_num [timestampBase]; omega)
      interface.accepted interface.publicState.toBoundaryInputs rules mapping.member
    change importedConstraintsMemoryPorts[i] ∈ importedConstraintsMemoryPorts
    exact Array.getElem_mem i.isLt
  have a := bounds 1
  have c := bounds 3
  have mx := bounds 6
  have my := bounds 7
  simp only [Trace.Proofs.read_word] at a c mx my
  obtain ⟨reads, inputX, inputY, _⟩ := mapping.words
  have localBounds : Blake2G.InterfaceAssumptions input output w := by
    constructor
    · simpa [reads, importedConstraintsMemoryPorts, WordColumns.evaluate] using a
    · simpa [reads, importedConstraintsMemoryPorts, WordColumns.evaluate] using c
    · simpa [inputX, importedConstraintsMemoryPorts, WordColumns.evaluate] using mx
    · simpa [inputY, importedConstraintsMemoryPorts, WordColumns.evaluate] using my
  have core := Verification.holds_of_sublist holds (List.sublist_append_left
    (importedConstraints (setupTable Control.controllerRows)) importedConstraintsTimestampLookups)
  exact Blake2G.Proofs.soundness (by omega) inverse Control.controllerRows input output w
    ⟨localBounds, core, mapping.words⟩

end Airbender.Blake2G.Memory.Proofs
