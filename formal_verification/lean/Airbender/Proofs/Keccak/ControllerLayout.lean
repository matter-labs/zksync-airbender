import Airbender.Proofs.Keccak.ImportedController
import Airbender.Proofs.Keccak.Controller

namespace Airbender.Keccak.Controller.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

private def piDestination (lane : Fin 25) : Fin 25 :=
  ⟨5 * (lane.val % 5) + (2 * (lane.val / 5) + 3 * (lane.val % 5)) % 5, by
    have := Nat.mod_lt lane.val (by decide : 0 < 5)
    have := Nat.mod_lt (2 * (lane.val / 5) + 3 * (lane.val % 5)) (by decide : 0 < 5)
    omega⟩

private theorem destination_source (lane : Fin 25) : piDestination (piSource lane) = lane := by
  fin_cases lane <;> decide

theorem physical_bound (round : Nat) (lane : Fin 25) : physicalLane round lane < 25 := by
  induction round generalizing lane with
  | zero =>
    simp only [physicalLane]
    have := lane.isLt; have := Nat.mod_lt lane.val (by decide : 0 < 5)
    omega
  | succ round ih => exact ih _

theorem physical_injective (round : Nat) : Function.Injective (physicalLane round) := by
  induction round with
  | zero =>
    intro a b same
    simp only [physicalLane] at same
    have := a.isLt; have := b.isLt
    have := Nat.mod_lt a.val (by decide : 0 < 5)
    have := Nat.mod_lt b.val (by decide : 0 < 5)
    apply Fin.ext
    omega
  | succ round ih =>
    intro a b same
    have sources := ih same
    have restored := congrArg piDestination sources
    simpa only [destination_source] using restored

theorem physical_pi (round : Nat) (column lane : Fin 5) :
    physicalLane (round + 1) rhoDestinations[column][lane] =
      physicalLane round ⟨5 * column.val + lane.val, by omega⟩ := by
  fin_cases column <;> fin_cases lane <;> rfl

theorem rows_bound (key : Fin 4096) (lane : Fin 6) : (rows key)[lane] < 31 := by
  rw [rows_reference]
  dsimp only [referenceRows]
  by_cases valid : key.val / 8 % 8 < 5
  · rw [if_pos valid]
    by_cases iota : key.val % 8 = 0 ∧ key.val / 64 % 32 ≤ 24 ∧ 2048 ≤ key.val
    · rw [if_pos iota]; simp only [Fin.getElem_fin, Vector.getElem_ofFn]
      split_ifs with small
      · exact Nat.lt_trans (physical_bound _ _) (by decide)
      · omega
    · rw [if_neg iota]
      by_cases mix : (key.val % 8 = 1 ∨ key.val % 8 = 2) ∧ key.val / 64 % 32 < 24
      · rw [if_pos mix]; fin_cases lane <;> norm_num
      · rw [if_neg mix]
        by_cases theta : key.val % 8 = 3 ∧ key.val / 64 % 32 < 24
        · rw [if_pos theta]; simp only [Fin.getElem_fin, Vector.getElem_ofFn]
          split_ifs with small
          · exact Nat.lt_trans (physical_bound _ _) (by decide)
          · have := Nat.mod_lt (key.val / 8 % 8 + 4) (by decide : 0 < 5); omega
        · rw [if_neg theta]
          by_cases rho : key.val % 8 = 4 ∧ key.val / 64 % 32 < 24
          · rw [if_pos rho]; simp only [Fin.getElem_fin, Vector.getElem_ofFn]
            split_ifs
            · exact Nat.lt_trans (physical_bound _ _) (by decide)
            · decide
          · rw [if_neg rho]
            by_cases chi1 : key.val % 8 = 5 ∧ key.val / 64 % 32 < 24
            · rw [if_pos chi1]; simp only [Fin.getElem_fin, Vector.getElem_ofFn]
              split_ifs
              · exact Nat.lt_trans (physical_bound _ _) (by decide)
              · have := lane.isLt; omega
            · rw [if_neg chi1]
              by_cases chi2 : key.val % 8 = 6 ∧ key.val / 64 % 32 < 24
              · rw [if_pos chi2]; simp only [Fin.getElem_fin, Vector.getElem_ofFn]
                split_ifs
                all_goals first
                  | exact Nat.lt_trans (physical_bound _ _) (by decide)
                  | (have := lane.isLt; omega)
              · rw [if_neg chi2]
                split_ifs
                · simp only [Fin.getElem_fin, Vector.getElem_replicate]; norm_num
                · fin_cases lane <;> norm_num
  · rw [if_neg valid]; fin_cases lane <;> norm_num

end Airbender.Keccak.Controller.Proofs
