module
public import CleanCore.Specs.Keccak256
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! Facts shared by the special5 and the split Keccak references, proven once: a phase of five calls
gives a slot the value its owning call computes when no other call writes it or what the owner reads,
and the entries of Clean's Theta-C, Theta-xor and Chi for every lane. -/

namespace Airbender.Keccak
open Specs.Keccak256
set_option warningAsError true

/-- Five calls in which only `owner` writes `physical` and no other call writes what `owner`
    reads: the phase gives `physical` the value `owner` computes on the initial state. -/
theorem fold_owned {α β : Type} (step : Fin 5 → (α → β) → α → β) (state : α → β) (physical : α)
    (owner : Fin 5) (reads : α → Prop)
    (kept : ∀ call, call ≠ owner → ∀ t, step call t physical = t physical)
    (frame : ∀ call, call ≠ owner → ∀ t q, reads q → step call t q = t q)
    (owned : ∀ t t', (∀ q, reads q → t q = t' q) → step owner t physical = step owner t' physical) :
    Fin.foldl 5 (fun t call => step call t) state physical = step owner state physical := by
  have five : Fin.foldl 5 (fun t call => step call t) state =
      step 4 (step 3 (step 2 (step 1 (step 0 state)))) := by
    simp only [Fin.foldl_succ_last, Fin.foldl_zero]
    rfl
  rw [five]
  fin_cases owner
  · rw [kept 4 (by decide), kept 3 (by decide), kept 2 (by decide), kept 1 (by decide)]
    rfl
  · rw [kept 4 (by decide), kept 3 (by decide), kept 2 (by decide)]
    exact owned _ _ fun q read => frame 0 (by decide) _ q read
  · rw [kept 4 (by decide), kept 3 (by decide)]
    exact owned _ _ fun q read => by
      rw [frame 1 (by decide) _ q read, frame 0 (by decide) _ q read]
  · rw [kept 4 (by decide)]
    exact owned _ _ fun q read => by
      rw [frame 2 (by decide) _ q read, frame 1 (by decide) _ q read, frame 0 (by decide) _ q read]
  · exact owned _ _ fun q read => by
      rw [frame 3 (by decide) _ q read, frame 2 (by decide) _ q read, frame 1 (by decide) _ q read,
        frame 0 (by decide) _ q read]

/-- Clean's column parity C[x] is the XOR of lanes 5x .. 5x + 4. -/
theorem theta_c_entry (v : Vector Nat 25) (column : Nat) (small : column < 5) :
    (thetaC v)[column] = v[5 * column]'(by omega) ^^^ v[5 * column + 1]'(by omega) ^^^
      v[5 * column + 2]'(by omega) ^^^ v[5 * column + 3]'(by omega) ^^^ v[5 * column + 4]'(by omega) := by
  interval_cases column <;> rfl

theorem theta_xor_entry (v : Vector Nat 25) (d : Vector Nat 5) (lane : Fin 25) :
    (thetaXor v d)[lane.val] = v[lane.val] ^^^ d[lane.val / 5]'(by omega) := by
  fin_cases lane <;> rfl

/-- Clean's `chi` on lane (x, y) reads lanes (x + 1, y) and (x + 2, y). -/
theorem chi_entry (b : Vector Nat 25) (lane : Fin 25) :
    (chi b)[lane.val] = b[lane.val] ^^^
      (not64 (b[(lane.val + 5) % 25]'(by omega)) &&& b[(lane.val + 10) % 25]'(by omega)) := by
  fin_cases lane <;> rfl

end Airbender.Keccak
