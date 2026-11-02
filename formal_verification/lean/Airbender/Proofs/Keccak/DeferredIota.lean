import Clean.Specs.Keccak256
import Batteries.Data.Fin.Fold

namespace Airbender.Keccak.Proofs
open Specs.Keccak256
set_option warningAsError true

def roundBody (state : Vector Nat 25) : Vector Nat 25 := chi (rhoPi (theta state))

def deferredRounds : Nat → Vector Nat 25 → Vector Nat 25
  | 0, state => state
  | n + 1, state => if n = 0 then roundBody state else
      roundBody (iota (deferredRounds n state) roundConstants[Fin.ofNat 24 (n - 1)])

private theorem finalized_rounds (state : Vector Nat 25) {n : Nat} (bound : n < 24) :
    iota (deferredRounds (n + 1) state) roundConstants[Fin.ofNat 24 n] =
      Fin.foldl (n + 1) (fun state i => keccakRound state roundConstants[Fin.ofNat 24 i.val]) state := by
  induction n with
  | zero => simp [deferredRounds, roundBody, keccakRound, Fin.foldl_succ]
  | succ n ih =>
    rw [deferredRounds, ite_eq_right (Nat.succ_ne_zero n)]
    simp only [Nat.add_sub_cancel]
    rw [ih (by omega)]
    conv_rhs => rw [Fin.foldl_succ_last]
    rfl

private theorem fold_constants (state : Vector Nat 25) :
    Fin.foldl 24 (fun state i => keccakRound state roundConstants[Fin.ofNat 24 i.val]) state =
      roundConstants.foldl keccakRound state := by
  simp only [Vector.foldl, roundConstants, Fin.foldl_eq_foldl_finRange]
  rw [← Array.foldl_toList, ← List.foldl_map]
  simp [List.finRange, Fin.ofNat]

theorem deferred_iota_permutation (state : Vector Nat 25) :
    iota (deferredRounds 24 state) roundConstants[23] = keccakPermutation state := by
  have rounds := finalized_rounds state (n := 23) (by decide)
  change iota (deferredRounds 24 state) roundConstants[23] = _ at rounds
  rw [rounds]
  exact fold_constants state

end Airbender.Keccak.Proofs
