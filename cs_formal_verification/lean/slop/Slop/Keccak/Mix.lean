module
public import Slop.Keccak.Lanes
public import Slop.Keccak.MixRotation
public import Slop.Keccak.OpIndex
public import Mathlib.Tactic.IntervalCases
public import Slop.CleanCore.Circuit.Operations
public import Slop.Defs.Circuits.Keccak.Artifact
public import Slop.Defs.Circuits.Keccak.Mix

@[expose] public section

namespace Airbender.Keccak.Proofs
open Arithmetic Mix
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000

def preservedLanes (second : Bool) : Vector (Fin 6) 3 :=
  if second then #v[0, 2, 5] else #v[1, 3, 4]

theorem mix_preserved {p : Nat} [Fact p.Prime]
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p} (second : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w Variables.modeColumns[mixMode second] = 1) (i : Fin 3) :
    writeLaneLimbs w (preservedLanes second)[i] = readLaneLimbs w (preservedLanes second)[i] := by
  apply Vector.ext
  intro limb bound
  change limb < 4 at bound
  have equation := Verification.assertion_of_holds h
    ⟨(if second then 112 else 100) + 4 * i.val + limb, by rw [constraint_count]; cases second <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega⟩
  cases second <;> fin_cases i <;> interval_cases limb
  all_goals simp [Variables.modeColumns, mixMode] at selected
  all_goals simp only [Bool.false_eq_true, ite_false, ite_true] at equation
  all_goals op_index at equation
  all_goals simp [Expression.eval, Verification.environment, selected, preservedLanes,
    readLaneLimbs, writeLaneLimbs] at equation ⊢
  all_goals linear_combination -equation

theorem mix_written_bounds {p : Nat} [Fact p.Prime] (hp : 1048576 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p} (second : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control)))
    (active : w 0 = 1) (selected : w Variables.modeColumns[mixMode second] = 1)
    (reads : ∀ lane : Fin 6, ∀ limb : Fin 4,
      (w (15 + 8 * lane.val + (#v[0, 1, 4, 5] : Vector Nat 4)[limb])).val < 65536)
    (lane : Fin 6) (limb : Fin 4) :
    (w (17 + 8 * lane.val + (#v[0, 1, 4, 5] : Vector Nat 4)[limb])).val < 65536 := by
  have preserved (i : Fin 3) :
      (w (17 + 8 * (preservedLanes second)[i].val + (#v[0, 1, 4, 5] : Vector Nat 4)[limb])).val < 65536 := by
    have equal := congrArg (fun v : Vector (ZMod p) 4 => v[limb])
      (mix_preserved second h selected i)
    have bound := reads (preservedLanes second)[i] limb
    cases second <;> fin_cases i <;> fin_cases limb
    all_goals simp [preservedLanes, readLaneLimbs, writeLaneLimbs] at equal bound ⊢
    all_goals rw [equal]; exact bound
  have result (op : Fin 5) (ordinary : isRotation second op = false) :=
    (mix_xor_limb hp second h active selected op ordinary limb).2.2.1
  have scratch : second = false → (w (57 + (#v[0, 1, 4, 5] : Vector Nat 4)[limb])).val < 65536 := by
    intro first
    subst second
    have input (i : Fin 4) : (w (aColumns false)[(0 : Fin 5)][i]).val < 65536 := by
      have bound := reads 0 i
      fin_cases i <;> simpa [aColumns, nativeLimbs] using bound
    have rotation := mix_rotated_limb hp false h active selected 0 (by decide) input limb
    have current := input limb
    have prior := input (previous limb)
    have bound : (2 * (w (aColumns false)[(0 : Fin 5)][limb]).val) % 65536 +
        (w (aColumns false)[(0 : Fin 5)][previous limb]).val / 32768 < 65536 := by omega
    have written : (w (cColumns false)[(0 : Fin 5)][limb]).val < 65536 := by
      rw [rotation]; exact bound
    fin_cases limb <;> simpa [cColumns, nativeLimbs] using written
  cases second <;> fin_cases lane <;> fin_cases limb
  all_goals first
    | simpa [preservedLanes] using preserved 0
    | simpa [preservedLanes] using preserved 1
    | simpa [preservedLanes] using preserved 2
    | simpa [cColumns, nativeLimbs] using result 1 (by decide)
    | simpa [cColumns, nativeLimbs] using result 2 (by decide)
    | simpa [cColumns, nativeLimbs] using result 3 (by decide)
    | simpa [cColumns, nativeLimbs] using result 4 (by decide)
    | simpa using scratch rfl

end Airbender.Keccak.Proofs
