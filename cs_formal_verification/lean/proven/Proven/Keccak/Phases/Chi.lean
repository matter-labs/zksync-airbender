module
public import Proven.Keccak.PhaseSteps

@[expose] public section

/-! The ten chi calls of any round, proven once: they form five row pairs; the first call of a row
computes lanes x = 1, 2 and saves (not b1) and b2 and b1 in scratch, the second computes lanes
x = 0, 3, 4 from them. -/

namespace Airbender.Keccak.Proofs
open Specs.Keccak256
set_option warningAsError true

/-- Both chi calls of row `row`. -/
def chiPair (round : Fin 24) (row : Fin 5) (state : LaneState) : LaneState :=
  microStep ⟨27 * round.val + 18 + 2 * row.val, by omega⟩
    (microStep ⟨27 * round.val + 17 + 2 * row.val, by omega⟩ state)

theorem chi_phase_pairs (round : Fin 24) (state : LaneState) :
    chiPhase round state = Fin.foldl 5 (fun t row => chiPair round row t) state := by
  simp only [chiPhase, chiPair, Fin.foldl_succ_last, Fin.foldl_zero]
  rfl

/-- A row pair gives lane (x, row) its chi value along the row. -/
theorem chi_pair_lane (round : Fin 24) (row x : Fin 5) (t : LaneState) :
    chiPair round row t (chiCell round.val row x) = t (chiCell round.val row x) ^^^
      (not64 (t (chiCell round.val row (x + 1))) &&& t (chiCell round.val row (x + 2))) := by
  have first : (⟨27 * round.val + 17 + 2 * row.val, by omega⟩ : Fin 649).val =
      27 * round.val + 17 + 2 * row.val := rfl
  have second : (⟨27 * round.val + 18 + 2 * row.val, by omega⟩ : Fin 649).val =
      27 * round.val + 18 + 2 * row.val := rfl
  obtain ⟨f1, f2, f3, f4, f25, f26⟩ := chi_first_values first t
  obtain ⟨g0, g3, g4⟩ := chi_second_values second
    (microStep ⟨27 * round.val + 17 + 2 * row.val, by omega⟩ t)
  have keptFirst (x : Fin 5) (zero : x = 0) :
      microStep ⟨27 * round.val + 17 + 2 * row.val, by omega⟩ t (chiCell round.val row x) =
        t (chiCell round.val row x) :=
    chi_first_kept first t _ (fun x' other => chi_cell_ne (Or.inr (by rw [zero]; exact other)))
      ⟨by have := chi_cell_bound round.val row x; omega, by have := chi_cell_bound round.val row x; omega⟩
  have keptSecond (x : Fin 5) (middle : x = 1 ∨ x = 2) (s : LaneState) :
      microStep ⟨27 * round.val + 18 + 2 * row.val, by omega⟩ s (chiCell round.val row x) =
        s (chiCell round.val row x) :=
    chi_second_kept second s _ fun x' outer => chi_cell_ne (Or.inr (by
      rcases outer with rfl | rfl | rfl <;> rcases middle with rfl | rfl <;> decide))
  have c0 : chiPair round row t (chiCell round.val row 0) = t (chiCell round.val row 0) ^^^
      (not64 (t (chiCell round.val row 1)) &&& t (chiCell round.val row 2)) := by
    simp only [chiPair]
    rw [g0, keptFirst 0 rfl, f25]
  have c1 : chiPair round row t (chiCell round.val row 1) = t (chiCell round.val row 1) ^^^
      (not64 (t (chiCell round.val row 2)) &&& t (chiCell round.val row 3)) := by
    simp only [chiPair]
    rw [keptSecond 1 (Or.inl rfl), f1]
  have c2 : chiPair round row t (chiCell round.val row 2) = t (chiCell round.val row 2) ^^^
      (not64 (t (chiCell round.val row 3)) &&& t (chiCell round.val row 4)) := by
    simp only [chiPair]
    rw [keptSecond 2 (Or.inr rfl), f2]
  have c3 : chiPair round row t (chiCell round.val row 3) = t (chiCell round.val row 3) ^^^
      (not64 (t (chiCell round.val row 4)) &&& t (chiCell round.val row 0)) := by
    simp only [chiPair]
    rw [g3, f3, f4, keptFirst 0 rfl]
  have c4 : chiPair round row t (chiCell round.val row 4) = t (chiCell round.val row 4) ^^^
      (not64 (t (chiCell round.val row 0)) &&& t (chiCell round.val row 1)) := by
    simp only [chiPair]
    rw [g4, f4, keptFirst 0 rfl, f26]
  fin_cases x
  exacts [c0, c1, c2, c3, c4]

/-- The slots one row pair reads: the lanes of its row. -/
def chiReads (round : Nat) (row : Fin 5) (q : Fin 31) : Prop :=
  ∃ x : Fin 5, chiCell round row x = q

theorem chi_kept (round : Fin 24) (row call : Fin 5) (other : call ≠ row) (t : LaneState) (q : Fin 31)
    (read : chiReads round.val row q) : chiPair round call t q = t q := by
  obtain ⟨x, rfl⟩ := read
  have first : (⟨27 * round.val + 17 + 2 * call.val, by omega⟩ : Fin 649).val =
      27 * round.val + 17 + 2 * call.val := rfl
  have second : (⟨27 * round.val + 18 + 2 * call.val, by omega⟩ : Fin 649).val =
      27 * round.val + 18 + 2 * call.val := rfl
  have bound := chi_cell_bound round.val row x
  simp only [chiPair]
  rw [chi_second_kept second _ _ fun x' _ => chi_cell_ne (Or.inl other),
    chi_first_kept first _ _ (fun x' _ => chi_cell_ne (Or.inl other)) ⟨by omega, by omega⟩]

/-- The chi calls of any round give each lane its chi value along its row. -/
theorem chi_phase_slot (round : Fin 24) (state : LaneState) (row x : Fin 5) :
    chiPhase round state (chiCell round.val row x) = state (chiCell round.val row x) ^^^
      (not64 (state (chiCell round.val row (x + 1))) &&& state (chiCell round.val row (x + 2))) := by
  rw [chi_phase_pairs]
  refine (fold_owned (fun row t => chiPair round row t) state (chiCell round.val row x) row
    (chiReads round.val row)
    (fun call other t => chi_kept round row call other t _ ⟨x, rfl⟩)
    (fun call other t q read => chi_kept round row call other t q read)
    (fun t t' agree => ?_)).trans (chi_pair_lane round row x state)
  rw [chi_pair_lane, chi_pair_lane, agree _ ⟨x, rfl⟩, agree _ ⟨x + 1, rfl⟩, agree _ ⟨x + 2, rfl⟩]

theorem chi_phase_lanes (round : Fin 24) (state : LaneState) :
    logicalLanes (round.val + 1) (chiPhase round state) = chi (logicalLanes (round.val + 1) state) := by
  apply Vector.ext
  intro lane bound
  rw [chi_entry _ ⟨lane, bound⟩]
  simp only [logical_lanes_entry]
  have row : lane % 5 < 5 := Nat.mod_lt _ (by decide)
  have column : lane / 5 < 5 := by omega
  have here : physicalCell (round.val + 1) ⟨lane, bound⟩ = chiCell round.val ⟨lane % 5, row⟩ ⟨lane / 5, column⟩ := by
    simp only [chiCell]
    congr 2
    omega
  have one : physicalCell (round.val + 1) ⟨(lane + 5) % 25, Nat.mod_lt _ (by decide)⟩ =
      chiCell round.val ⟨lane % 5, row⟩ (⟨lane / 5, column⟩ + 1) := by
    simp only [chiCell]
    congr 2
    simp [Fin.val_add]
    omega
  have two : physicalCell (round.val + 1) ⟨(lane + 10) % 25, Nat.mod_lt _ (by decide)⟩ =
      chiCell round.val ⟨lane % 5, row⟩ (⟨lane / 5, column⟩ + 2) := by
    simp only [chiCell]
    congr 2
    simp [Fin.val_add]
    omega
  rw [here, one, two]
  exact chi_phase_slot round state _ _

end Airbender.Keccak.Proofs
