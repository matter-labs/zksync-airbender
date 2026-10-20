import Slop.Keccak.Mix

namespace Airbender.Keccak.Proofs.Mix
open Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

theorem stage_writes [Fact p.Prime] (hp : 1048576 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p} (second : Bool)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control)))
    (active : w 0 = 1) (selected : w Variables.modeColumns[mixMode second] = 1)
    (reads : ∀ lane : Fin 6, ∀ limb : Fin 4, (readLaneLimbs w lane)[limb].val < 65536) :
    Vector.ofFn (Keccak.writeLane w) = if second then
      #v[readLane w 0, readLane w 1 ^^^ rotLeft64 (readLane w 3) 1,
        readLane w 2, readLane w 3 ^^^ readLane w 5,
        readLane w 4 ^^^ rotLeft64 (readLane w 1) 1, readLane w 5]
    else #v[readLane w 0 ^^^ rotLeft64 (readLane w 2) 1, readLane w 1,
      readLane w 2 ^^^ rotLeft64 (readLane w 4) 1, readLane w 3,
      readLane w 4, rotLeft64 (readLane w 0) 1] := by
  have bound (operation : Fin 5) (limb : Fin 4) : (w (aColumns second)[operation][limb]).val < 65536 := by
    have b0 := reads 0 limb; have b1 := reads 1 limb; have b2 := reads 2 limb
    have b3 := reads 3 limb; have b4 := reads 4 limb
    cases second <;> fin_cases operation <;> fin_cases limb
    all_goals first
      | simpa [aColumns, nativeLimbs, readLaneLimbs] using b0
      | simpa [aColumns, nativeLimbs, readLaneLimbs] using b1
      | simpa [aColumns, nativeLimbs, readLaneLimbs] using b2
      | simpa [aColumns, nativeLimbs, readLaneLimbs] using b3
      | simpa [aColumns, nativeLimbs, readLaneLimbs] using b4
  have preserved (i : Fin 3) := Keccak.Proofs.mix_preserved second holds selected i
  cases second
  · have f0 := mix_rotation_operation hp false holds active selected 0 (by decide) (bound 0)
    have f1 := mix_rotation_operation hp false holds active selected 1 (by decide) (bound 1)
    have f2 := mix_xor_operation hp false holds active selected 2 (by decide)
    have f3 := mix_rotation_operation hp false holds active selected 3 (by decide) (bound 3)
    have f4 := mix_xor_operation hp false holds active selected 4 (by decide)
    change writeLane w 5 = rotLeft64 (readLane w 0) 1 at f0
    change packed w (temporary 90) = rotLeft64 (readLane w 2) 1 at f1
    change writeLane w 0 = readLane w 0 ^^^ packed w (temporary 90) at f2
    change packed w (temporary 94) = rotLeft64 (readLane w 4) 1 at f3
    change writeLane w 2 = readLane w 2 ^^^ packed w (temporary 94) at f4
    rw [f1] at f2
    rw [f3] at f4
    have p0 := preserved 0; have p1 := preserved 1; have p2 := preserved 2
    change writeLaneLimbs w 1 = readLaneLimbs w 1 at p0
    change writeLaneLimbs w 3 = readLaneLimbs w 3 at p1
    change writeLaneLimbs w 4 = readLaneLimbs w 4 at p2
    have c0 := (lane_of_limbs p0.symm).symm
    have c1 := (lane_of_limbs p1.symm).symm
    have c2 := (lane_of_limbs p2.symm).symm
    apply Vector.ext
    intro i hi
    interval_cases i
    all_goals simp only [Bool.false_eq_true, ite_false, Vector.getElem_ofFn,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
    all_goals first | exact f2 | exact c0 | exact f4 | exact c1 | exact c2 | exact f0
  · have s0 := mix_rotation_operation hp true holds active selected 0 (by decide) (bound 0)
    have s1 := mix_xor_operation hp true holds active selected 1 (by decide)
    have s2 := mix_rotation_operation hp true holds active selected 2 (by decide) (bound 2)
    have s3 := mix_xor_operation hp true holds active selected 3 (by decide)
    have s4 := mix_xor_operation hp true holds active selected 4 (by decide)
    change packed w (temporary 90) = rotLeft64 (readLane w 1) 1 at s0
    change writeLane w 4 = readLane w 4 ^^^ packed w (temporary 90) at s1
    change packed w (temporary 94) = rotLeft64 (readLane w 3) 1 at s2
    change writeLane w 1 = readLane w 1 ^^^ packed w (temporary 94) at s3
    change writeLane w 3 = readLane w 3 ^^^ readLane w 5 at s4
    rw [s0] at s1
    rw [s2] at s3
    have p0 := preserved 0; have p1 := preserved 1; have p2 := preserved 2
    change writeLaneLimbs w 0 = readLaneLimbs w 0 at p0
    change writeLaneLimbs w 2 = readLaneLimbs w 2 at p1
    change writeLaneLimbs w 5 = readLaneLimbs w 5 at p2
    have c0 := (lane_of_limbs p0.symm).symm
    have c1 := (lane_of_limbs p1.symm).symm
    have c2 := (lane_of_limbs p2.symm).symm
    apply Vector.ext
    intro i hi
    interval_cases i
    all_goals simp only [ite_true, Vector.getElem_ofFn, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
    all_goals first | exact c0 | exact s3 | exact c1 | exact s4 | exact s1 | exact c2

end Airbender.Keccak.Proofs.Mix
