import Airbender.Review.Keccak.Execution
import Airbender.Proofs.Keccak.ControllerLayout
import Airbender.Proofs.Keccak.Addresses
import Airbender.Proofs.Keccak.Theta
import Airbender.Proofs.Keccak.DecodeControl
import Airbender.Review.Delegation.Theorems

namespace Airbender.Keccak.Native.Proofs
open Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

theorem lane_ports {p : Nat} (w : Nat → ZMod p) (lane : Fin 6) :
    readLane w lane = Keccak.readLane w lane ∧ writtenLane w lane = Keccak.writeLane w lane := by
  fin_cases lane
  all_goals simp [readLane, writtenLane, Delegation.Row.readWord, Delegation.Row.writtenWord,
    Delegation.Row.ports, readToken, MemoryToken.word, Delegation.Row.writeToken,
    importedConstraintsMemoryPorts, MemoryPort.readCode, MemoryPort.writeCode, WordColumns.code,
    Word.value, limbBase, laneValue]
  all_goals constructor <;> ring

theorem operation_execution [Fact p.Prime] (hp : 16777216 ≤ p)
    (inverse : 256 * (-7864320 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (accepted : Delegation.MemoryAccepted data)
    (inputs : Delegation.OperationInputs data before cells Controller.rows)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Delegation.MemoryExecution data before cells ∧
      ∀ row ∈ data.rows, row.family = .keccak → RowEffects row.assignment := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have bounds := Delegation.Proofs.operation_word_bounds (by omega) (by
    linear_combination inverse) accepted inputs
  refine ⟨Delegation.native_memory_execution size accepted inputs.publicState aligned, ?_⟩
  intro row member family
  have holds := accepted.constraints row member
  have reads := bounds.reads row member
  have active := inputs.keccakActive row member family
  rcases row with ⟨kind, w⟩
  change kind = .keccak at family
  subst kind
  simp only [Delegation.Row.constraints, inputs.tables, Delegation.modeledSetup] at holds
  have core := Verification.holds_of_sublist holds (List.sublist_append_left
    (importedConstraints (setupTable Controller.rows)) importedConstraintsTimestampLookups)
  have pointer : (statePointer w).Bounded := by
    simpa [statePointer, Delegation.Row.ports, importedConstraintsMemoryPorts,
      readToken, MemoryToken.word, MemoryPort.readCode, WordColumns.code] using
      reads importedConstraintsMemoryPorts[1] (by simp [Delegation.Row.ports, importedConstraintsMemoryPorts])
  refine ⟨Keccak.Proofs.control_update_checks (by omega) core,
    Keccak.Proofs.controller_indices (by omega) Controller.Proofs.rows_bound core,
    Keccak.Proofs.addresses hp inverse Controller.Proofs.rows_bound pointer core, ?_⟩
  intro state control mode
  have decoded := Keccak.Proofs.decoded_control (by omega) state core active control
  have selected : w 66 = 1 := by
    have selector := decoded.1 3
    simpa [Variables.modeColumns, mode] using selector
  constructor
  · intro lane
    rw [(lane_ports w _).2, (lane_ports w _).1, (lane_ports w _).1]
    exact (Keccak.Proofs.theta_lane_xor (by omega) core active selected lane).2.2.2
  · rw [(lane_ports w _).2, (lane_ports w _).1]
    exact Keccak.Proofs.theta_scratch_preserved core selected

end Airbender.Keccak.Native.Proofs
