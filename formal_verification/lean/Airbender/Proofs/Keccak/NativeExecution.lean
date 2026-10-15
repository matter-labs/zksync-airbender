import Airbender.Proofs.Keccak.MixStage
import Airbender.Proofs.Keccak.Iota
import Airbender.Review.Circuits.Keccak.Execution
import Airbender.Proofs.Keccak.ControllerLayout
import Airbender.Proofs.Keccak.Addresses
import Airbender.Proofs.Keccak.Chi
import Airbender.Proofs.Keccak.RhoRotation
import Airbender.Proofs.Keccak.Rho
import Airbender.Proofs.Keccak.Theta
import Airbender.Proofs.Keccak.DecodeControl
import Airbender.Review.Trace.Delegation.Theorems

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

private theorem read_limbs {p : Nat} {w : Nat → ZMod p}
    (reads : ∀ port ∈ (⟨.keccak, w⟩ : Delegation.Row p).ports,
      (readToken w port).word.Bounded) (lane : Fin 6) (limb : Fin 4) :
    (readLaneLimbs w lane)[limb].val < limbBase := by
  have low := reads (importedConstraintsMemoryPorts[2 + 2 * lane.val]'(by change 2 + 2 * lane.val < 14; have := lane.isLt; omega))
    (Array.getElem_mem (by change 2 + 2 * lane.val < 14; have := lane.isLt; omega))
  have high := reads (importedConstraintsMemoryPorts[3 + 2 * lane.val]'(by change 3 + 2 * lane.val < 14; have := lane.isLt; omega))
    (Array.getElem_mem (by change 3 + 2 * lane.val < 14; have := lane.isLt; omega))
  fin_cases lane
  all_goals simp only [importedConstraintsMemoryPorts, readToken, MemoryToken.word,
    MemoryPort.readCode, WordColumns.code, Word.Bounded] at low high
  all_goals fin_cases limb
  all_goals first | simpa [readLaneLimbs] using low.1 | simpa [readLaneLimbs] using low.2 | simpa [readLaneLimbs] using high.1 | simpa [readLaneLimbs] using high.2

theorem native_effects [Fact p.Prime] (hp : 16777216 ≤ p)
    (inverse : 256 * (-7864320 : ZMod p) = 1) {w : Nat → ZMod p}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable Controller.rows)))
    (active : w Variables.execute = 1)
    (reads : ∀ port ∈ importedConstraintsMemoryPorts, (readToken w port).word.Bounded) :
    RowEffects w := by
  have pointer : (statePointer w).Bounded := by
    simpa [statePointer, importedConstraintsMemoryPorts,
      readToken, MemoryToken.word, MemoryPort.readCode, WordColumns.code] using
      reads importedConstraintsMemoryPorts[1] (by simp [importedConstraintsMemoryPorts])
  refine ⟨?_, Keccak.Proofs.control_update_checks (by omega) core,
    Keccak.Proofs.controller_indices (by omega) Controller.Proofs.rows_bound core,
    Keccak.Proofs.addresses hp inverse Controller.Proofs.rows_bound pointer core, ?_, ?_, ?_, ?_, ?_⟩
  · intro state column round control mapped
    apply Keccak.Proofs.iota_column (by omega) core
    refine ⟨active, control, ?_⟩
    intro lane
    exact (lane_ports w ⟨lane.val, by omega⟩).1.symm.trans (mapped lane)
  · intro state control mode
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
  · intro state control mode
    have decoded := Keccak.Proofs.decoded_control (by omega) state core active control
    have selected : w 67 = 1 := by
      have selector := decoded.1 4
      simpa [Variables.modeColumns, mode] using selector
    constructor
    · intro lane
      rw [(lane_ports w _).2, (lane_ports w _).1]
      apply Keccak.Proofs.Rho.rho_rotated_lane (by omega) state.iteration core active selected decoded.2.1
      intro limb
      simpa [Keccak.Proofs.Rho.rhoLimbs, limbBase] using
        read_limbs reads ⟨lane.val, by omega⟩ limb
    · rw [(lane_ports w _).2, (lane_ports w _).1]
      exact (Keccak.Proofs.lane_of_limbs (Keccak.Proofs.rho_preserved core selected).symm).symm
  · intro state control mode
    have decoded := Keccak.Proofs.decoded_control (by omega) state core active control
    have selected : w 68 = 1 := by
      have selector := decoded.1 5
      simpa [Variables.modeColumns, mode] using selector
    have facts := Keccak.Proofs.chi_first (by omega) core active selected
    apply Vector.ext
    intro index bound
    interval_cases index
    all_goals simp only [writtenLanes, Vector.getElem_ofFn, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
    all_goals simp only [lane_ports]
    all_goals first | exact facts.1 | exact facts.2.1 | exact facts.2.2.1 |
      exact facts.2.2.2.1 | exact facts.2.2.2.2 0 | exact facts.2.2.2.2 1
  · intro state control mode
    have decoded := Keccak.Proofs.decoded_control (by omega) state core active control
    have selected : w 69 = 1 := by
      have selector := decoded.1 6
      simpa [Variables.modeColumns, mode] using selector
    have facts := Keccak.Proofs.chi_second (by omega) core active selected
    apply Vector.ext
    intro index bound
    interval_cases index
    all_goals simp only [writtenLanes, Vector.getElem_ofFn, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
    all_goals simp only [lane_ports]
    all_goals first | exact facts.1 | exact facts.2.1 | exact facts.2.2.1 |
      exact facts.2.2.2 0 | exact facts.2.2.2 1 | exact facts.2.2.2 2

  · intro state second control mode
    have decoded := Keccak.Proofs.decoded_control (by omega) state core active control
    have selected : w Variables.modeColumns[Keccak.Proofs.Mix.mixMode second] = 1 := by
      have selector := decoded.1 (Keccak.Proofs.Mix.mixMode second)
      cases second <;> simpa [Keccak.Proofs.Mix.mixMode, mode] using selector
    have calculated := Keccak.Proofs.Mix.stage_writes (by omega) second core active selected
      (fun lane limb => by simpa [limbBase] using read_limbs reads lane limb)
    have ports : writtenLanes w = Vector.ofFn (Keccak.writeLane w) := by
      apply Vector.ext
      intro index bound
      simp only [writtenLanes, Vector.getElem_ofFn, lane_ports]
    rw [ports]
    simpa only [lane_ports] using calculated

theorem operation_execution_at_boundary [Fact p.Prime] (hp : 16777216 ≤ p)
    (inverse : 256 * (-7864320 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (accepted : Delegation.MemoryAccepted data)
    (inputs : Delegation.Proofs.BoundaryOperationInputs data before cells Controller.rows)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Delegation.MemoryExecution data before cells ∧
      ∀ row ∈ data.rows, row.family = .keccak → RowEffects row.assignment := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have bounds := Delegation.Proofs.operation_word_bounds_at_boundary (by omega) (by
    linear_combination inverse) accepted inputs
  refine ⟨Delegation.Proofs.native_memory_execution size accepted inputs.publicState aligned, ?_⟩
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
  exact native_effects hp inverse core active reads

theorem operation_execution [Fact p.Prime] (hp : 16777216 ≤ p)
    (inverse : 256 * (-7864320 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (accepted : Delegation.MemoryAccepted data)
    (inputs : Delegation.OperationInputs data before cells Controller.rows)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Delegation.MemoryExecution data before cells ∧
      ∀ row ∈ data.rows, row.family = .keccak → RowEffects row.assignment :=
  operation_execution_at_boundary hp inverse accepted inputs.toBoundaryInputs aligned

end Airbender.Keccak.Native.Proofs
