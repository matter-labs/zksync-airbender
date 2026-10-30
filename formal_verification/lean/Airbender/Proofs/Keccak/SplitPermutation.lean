import Airbender.Proofs.Keccak.SplitRoundAssembly
import Airbender.Proofs.Keccak.SplitFinalIota
import Airbender.Proofs.Delegation.IntervalFold

namespace Airbender.Keccak.Split.Call.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

/-- All 361 original split reference calls produce the original Keccak permutation.
This theorem makes no native worker or circuit soundness claim. -/
theorem permutation_of_physical_chain (states : Fin 362 → LaneState)
    (transitions : ∀ index : Fin 361,
      states ⟨index.val + 1, by omega⟩ =
        microStep index (states ⟨index.val, by omega⟩)) :
    logicalLanes 0 (states 361) = keccakPermutation (logicalLanes 0 (states 0)) := by
  let forward : Nat → LaneState := fun n => states (Fin.ofNat 362 n)
  have advances (n : Nat) (bound : n < 361) :
      forward (n + 1) = microStep (Fin.ofNat 361 n) (forward n) := by
    have first : Fin.ofNat 362 n = (⟨n, by omega⟩ : Fin 362) :=
      Fin.ext (Nat.mod_eq_of_lt (by omega))
    have next : Fin.ofNat 362 (n + 1) = (⟨n + 1, by omega⟩ : Fin 362) :=
      Fin.ext (Nat.mod_eq_of_lt (by omega))
    have call : Fin.ofNat 361 n = (⟨n, bound⟩ : Fin 361) :=
      Fin.ext (Nat.mod_eq_of_lt bound)
    simpa only [forward, first, next, call] using transitions ⟨n, bound⟩
  have interval (start count : Nat) (bound : start + count ≤ 361) :
      forward (start + count) = Fin.foldl count
        (fun state index => microStep ⟨start + index.val, by omega⟩ state) (forward start) := by
    have result := Delegation.Proofs.interval_fold forward
      (fun n state => microStep (Fin.ofNat 361 n) state)
      start count (fun index short => advances (start + index) (by omega))
    have steps : (fun state (index : Fin count) => microStep (Fin.ofNat 361 (start + index.val)) state) =
        (fun state (index : Fin count) => microStep ⟨start + index.val, by omega⟩ state) := by
      funext state index
      congr 1
      apply Fin.ext
      exact Nat.mod_eq_of_lt (by omega)
    rw [steps] at result
    exact result
  have rounds (round : Fin 24) : forward (15 * (round.val + 1)) =
      assembledRound round (forward (15 * round.val)) := by
    have a := interval (15 * round.val) 5 (by omega)
    have b := interval (15 * round.val + 5) 5 (by omega)
    have c := interval (15 * round.val + 10) 5 (by omega)
    change forward (15 * round.val + 5) = parityPhase round (forward (15 * round.val)) at a
    change forward (15 * round.val + 10) = thetaRhoPhase round (forward (15 * round.val + 5)) at b
    change forward (15 * round.val + 15) = chiPhase round (forward (15 * round.val + 10)) at c
    rw [show 15 * (round.val + 1) = 15 * round.val + 15 by omega, c, b, a]
    rfl
  let trace : Fin 25 → Vector Nat 25 := fun round => logicalLanes round.val (forward (15 * round.val))
  have traceSteps (round : Fin 24) : trace ⟨round.val + 1, by omega⟩ =
      Airbender.Keccak.Proofs.roundBody
        (iotaState (trace ⟨round.val, by omega⟩) (Fin.ofNat 25 round.val)) := by
    change logicalLanes (round.val + 1) (forward (15 * (round.val + 1))) = _
    rw [rounds]
    exact assembled_round_reference round (forward (15 * round.val))
  have full := Airbender.Keccak.Proofs.deferred_trace trace traceSteps
  have finish := advances 360 (by decide)
  have lastRound : logicalLanes 24 (forward 361) =
      iota (logicalLanes 24 (forward 360)) roundConstants[23] := by
    rw [finish]
    exact final_iota_reference (forward 360)
  change logicalLanes 24 (forward 360) =
    Airbender.Keccak.Proofs.deferredRounds 24 (logicalLanes 0 (forward 0)) at full
  rw [full, Airbender.Keccak.Proofs.deferred_iota_permutation, logical_final_layout] at lastRound
  exact lastRound

end Airbender.Keccak.Split.Call.Proofs
