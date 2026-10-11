import Airbender.Review.Blake2G.Execution
import Airbender.Proofs.Blake2G.Soundness
import Airbender.Review.Delegation.Theorems

namespace Airbender.Blake2G.Native.Proofs
open Trace
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 250000

theorem native_mapping {p : Nat} (w : Nat → ZMod p) : WordMapping (input w) (output w) w := by
  constructor
  all_goals simp [input, output, Delegation.Row.readWord, Delegation.Row.writtenWord, Delegation.Row.ports, readToken, MemoryToken.word,
    Delegation.Row.writeToken, importedConstraintsMemoryPorts, MemoryPort.readCode,
    MemoryPort.writeCode, WordColumns.code]

theorem native_effects [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1) {w : Nat → ZMod p}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable Control.controllerRows)))
    (reads : ∀ port ∈ importedConstraintsMemoryPorts, (readToken w port).word.Bounded) :
    Blake2G.spec (input w) (output w) := by
  apply Blake2G.Proofs.soundness (by omega) inverse Control.controllerRows (input w) (output w) w
  refine ⟨?_, core, native_mapping w⟩
  constructor
  · exact reads importedConstraintsMemoryPorts[1] (by simp [importedConstraintsMemoryPorts])
  · exact reads importedConstraintsMemoryPorts[3] (by simp [importedConstraintsMemoryPorts])
  · exact reads importedConstraintsMemoryPorts[6] (by simp [importedConstraintsMemoryPorts])
  · exact reads importedConstraintsMemoryPorts[7] (by simp [importedConstraintsMemoryPorts])

theorem operation_execution [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {control : Fin 4096 → Vector Nat 6}
    (accepted : Delegation.MemoryAccepted data) (inputs : Delegation.OperationInputs data before cells control)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Delegation.MemoryExecution data before cells ∧
      ∀ row ∈ data.rows, row.family = .blakeG → Blake2G.spec (input row.assignment) (output row.assignment) := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have bounds := Delegation.Proofs.operation_word_bounds hp inverse accepted inputs
  refine ⟨Delegation.native_memory_execution size accepted inputs.publicState aligned, ?_⟩
  intro row member family
  have holds := accepted.constraints row member
  have reads := bounds.reads row member
  rcases row with ⟨kind, w⟩
  change kind = .blakeG at family
  subst kind
  simp only [Delegation.Row.constraints, inputs.tables, Delegation.modeledSetup] at holds
  have core := Verification.holds_of_sublist holds (List.sublist_append_left
    (importedConstraints (setupTable Control.controllerRows)) importedConstraintsTimestampLookups)
  exact native_effects hp inverse core reads

end Airbender.Blake2G.Native.Proofs
