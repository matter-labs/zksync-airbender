import Airbender.Proofs.Keccak.DeferredIota
import Airbender.Review.Circuits.Keccak.Iota

namespace Airbender.Keccak.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option maxHeartbeats 400000

theorem deferred_trace (states : Fin 25 → Vector Nat 25)
    (transitions : ∀ round : Fin 24, states ⟨round.val + 1, by omega⟩ =
      roundBody (iotaState (states ⟨round.val, by omega⟩) (Fin.ofNat 25 round.val))) :
    states 24 = deferredRounds 24 (states 0) := by
  have prefixResult : ∀ (n : Nat) (bound : n ≤ 24), states ⟨n, by omega⟩ = deferredRounds n (states 0) := by
    intro n
    induction n with
    | zero => intro bound; rfl
    | succ n ih =>
      intro bound
      have current := transitions ⟨n, by omega⟩
      rw [ih (by omega)] at current
      rw [current, deferredRounds]
      by_cases zero : n = 0
      · subst n
        rfl
      · have positive : 0 < n := by omega
        have modRound : n % 25 = n := Nat.mod_eq_of_lt (by omega)
        have modRC : (n - 1) % 24 = n - 1 := Nat.mod_eq_of_lt (by omega)
        simp only [if_neg zero, iotaState, Fin.val_ofNat, modRound, dif_pos positive,
          Fin.getElem_fin, modRC]
  exact prefixResult 24 (by omega)

end Airbender.Keccak.Proofs
