import Airbender.Review.Bigint.Memory
import Airbender.Proofs.Bigint.Memory
import Airbender.Proofs.Bigint.Addresses

namespace Airbender.Bigint.Memory.Proofs
open Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384

theorem addresses_soundness [Fact p.Prime] (hp : 2097152 ≤ p)
    (inverse : 32 * (-62914560 : ZMod p) = 1) (data : Delegation.MemoryData p)
    (before : Reference.RiscV.Sail.State) (cells : List Cell) :
    (circuitModel data).SoundnessUnder (InterfaceAssumptions data before cells) Addresses.spec := by
  intro input output w ⟨inputs, accepted, mapping⟩
  have rules := Bigint.Proofs.memory_rules (by omega) accepted inputs.families inputs.table
  have bounds (i : Fin 19) :
      (readToken w importedConstraintsMemoryPorts[i]).word.Bounded := by
    apply Delegation.Proofs.read_value_bounds (by norm_num [timestampBase]; omega)
      accepted inputs.publicState.toBoundaryInputs rules mapping.member
    change importedConstraintsMemoryPorts[i] ∈ importedConstraintsMemoryPorts
    exact Array.getElem_mem i.isLt
  have left := bounds 0
  have right := bounds 9
  simp only [Trace.Proofs.read_word] at left right
  have localBounds : Addresses.InterfaceAssumptions input output w := by
    constructor
    · simpa [mapping.words.left, importedConstraintsMemoryPorts, WordColumns.evaluate] using left
    · simpa [mapping.words.right, importedConstraintsMemoryPorts, WordColumns.evaluate] using right
  have holds := accepted.constraints _ mapping.member
  change FlatOperation.ConstraintsHoldFlat (Verification.environment w) (clockConstraints data.setup.bigint) at holds
  rw [inputs.table] at holds
  have core := Verification.holds_of_sublist holds (List.sublist_append_left
    (importedConstraints setupTable) importedConstraintsTimestampLookups)
  exact Addresses.Proofs.soundness hp inverse input output w ⟨localBounds, core, mapping.words⟩

theorem value_bounds [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : Inputs data before cells) :
    (∀ row ∈ data.rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) ∧
    (∀ row ∈ data.rows, ∀ port ∈ row.ports, (row.writeToken port).word.Bounded) ∧
    (∀ token ∈ data.terminal, token.word.Bounded) := by
  have size : 65536 ≤ p := by norm_num [timestampBase] at hp; omega
  have rules := Bigint.Proofs.memory_rules size accepted inputs.families inputs.table
  exact ⟨fun row member port present => Delegation.Proofs.read_value_bounds hp accepted
      inputs.publicState.toBoundaryInputs rules member present,
    fun row member port present => Delegation.Proofs.write_value_bounds hp accepted
      inputs.publicState.toBoundaryInputs rules member present,
    fun token present => Delegation.Proofs.terminal_value_bounds hp accepted inputs.publicState.toBoundaryInputs rules present⟩

end Airbender.Bigint.Memory.Proofs
