import Airbender.Proofs.Keccak.CallPhysical
import Airbender.Proofs.Keccak.PermutationAssembly
import Airbender.Proofs.Delegation.IntervalFold

namespace Airbender.Keccak.Proofs
open Trace Trace.Proofs Delegation.Proofs Reference.RiscV.Sail Specs.Keccak256
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

private theorem permutation_of_chain (states : Fin 650 → LaneState)
    (transitions : ∀ i : Fin 649, states ⟨i.val, by omega⟩ =
      microStep ⟨648 - i.val, by omega⟩ (states ⟨i.val + 1, by omega⟩)) :
    logicalLanes 0 (states 0) = keccakPermutation (logicalLanes 0 (states 649)) := by
  let forward : Nat → LaneState := fun n => states (Fin.ofNat 650 (649 - n))
  have advances (n : Nat) (bound : n < 649) :
      forward (n + 1) = microStep (Fin.ofNat 649 n) (forward n) := by
    have startIndex : Fin.ofNat 650 (649 - (n + 1)) = (⟨648 - n, by omega⟩ : Fin 650) := by
      apply Fin.ext
      simp only [Fin.val_ofNat]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    have endIndex : Fin.ofNat 650 (649 - n) = (⟨648 - n + 1, by omega⟩ : Fin 650) := by
      apply Fin.ext
      simp only [Fin.val_ofNat]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    have callIndex : Fin.ofNat 649 n = (⟨648 - (648 - n), by omega⟩ : Fin 649) := by
      apply Fin.ext
      simp only [Fin.val_ofNat]
      rw [Nat.mod_eq_of_lt bound]
      omega
    simpa only [forward, startIndex, endIndex, callIndex] using transitions ⟨648 - n, by omega⟩
  have interval (start count : Nat) (bound : start + count ≤ 649) :
      forward (start + count) = Fin.foldl count
        (fun state i => microStep ⟨start + i.val, by omega⟩ state) (forward start) := by
    have result := interval_fold forward (fun n state => microStep (Fin.ofNat 649 n) state)
      start count (fun i short => advances (start + i) (by omega))
    have steps : (fun state (i : Fin count) => microStep (Fin.ofNat 649 (start + i.val)) state) =
        (fun state (i : Fin count) => microStep ⟨start + i.val, by omega⟩ state) := by
      funext state i
      congr 1
      apply Fin.ext
      exact Nat.mod_eq_of_lt (by omega)
    rw [steps] at result
    exact result
  have rounds (round : Fin 24) : forward (27 * (round.val + 1)) =
      assembledRound round (forward (27 * round.val)) := by
    have a := interval (27 * round.val) 5 (by omega)
    have b := interval (27 * round.val + 5) 2 (by omega)
    have c := interval (27 * round.val + 7) 5 (by omega)
    have d := interval (27 * round.val + 12) 5 (by omega)
    have e := interval (27 * round.val + 17) 10 (by omega)
    change forward (27 * round.val + 5) = iotaPhase round (forward (27 * round.val)) at a
    change forward (27 * round.val + 7) = mixPhase round (forward (27 * round.val + 5)) at b
    change forward (27 * round.val + 12) = thetaPhase round (forward (27 * round.val + 7)) at c
    change forward (27 * round.val + 17) = rhoPhase round (forward (27 * round.val + 12)) at d
    change forward (27 * round.val + 27) = chiPhase round (forward (27 * round.val + 17)) at e
    rw [show 27 * (round.val + 1) = 27 * round.val + 27 by omega, e, d, c, b, a]
    rfl
  let trace : Fin 25 → Vector Nat 25 := fun round => logicalLanes round.val (forward (27 * round.val))
  have traceSteps (round : Fin 24) : trace ⟨round.val + 1, by omega⟩ =
      roundBody (iotaState (trace ⟨round.val, by omega⟩) (Fin.ofNat 25 round.val)) := by
    change logicalLanes (round.val + 1) (forward (27 * (round.val + 1))) = _
    rw [rounds]
    exact assembled_round_reference round (forward (27 * round.val))
  have full := deferred_trace trace traceSteps
  have finish := advances 648 (by decide)
  have lastRound : logicalLanes 24 (forward 649) =
      iota (logicalLanes 24 (forward 648)) roundConstants[23] := by
    rw [finish]
    exact final_iota_reference (forward 648)
  change logicalLanes 24 (forward 648) = deferredRounds 24 (logicalLanes 0 (forward 0)) at full
  rw [full, deferred_iota_permutation] at lastRound
  rw [final_layout] at lastRound
  exact lastRound

theorem call_permutation [Fact p.Prime] (hp : 16777216 ≤ p)
    (inverse : 256 * (-7864320 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : State} {cells : List Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : CallInputs data initial cells)
    (tables : data.setup = Delegation.modeledSetup Controller.rows)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (pointer : BitVec 32) (after : State),
      (Cell.register 11).read initial = .ok pointer initial ∧
      Delegation.TraceMapping data initial after cells ∧
      (∀ cell ∈ cells, ∃ value, cell.read after = .ok value after) ∧
      logicalLanes 0 (physicalLanes after pointer) =
        keccakPermutation (logicalLanes 0 (physicalLanes initial pointer)) := by
  obtain ⟨pointer, after, states, pointerRead, first, last, trace, readable, transitions⟩ :=
    call_physical_steps hp inverse accepted inputs tables aligned
  have result := permutation_of_chain states transitions
  rw [first, last] at result
  exact ⟨pointer, after, pointerRead, trace, readable, result⟩

end Airbender.Keccak.Proofs
