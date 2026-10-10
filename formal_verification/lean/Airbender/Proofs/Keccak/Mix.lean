import Airbender.Proofs.Keccak.Lanes
import Airbender.Proofs.Keccak.MixRotation
import Mathlib.Tactic.IntervalCases

namespace Airbender.Keccak.Proofs
open Arithmetic Mix
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private def preservedLanes (second : Bool) : Vector (Fin 6) 3 :=
  if second then #v[0, 2, 5] else #v[1, 3, 4]

private theorem mix_preserved {p : Nat} [Fact p.Prime]
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p} (second : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w Variables.modeColumns[mixMode second] = 1) (i : Fin 3) :
    writeLaneLimbs w (preservedLanes second)[i] = readLaneLimbs w (preservedLanes second)[i] := by
  apply Vector.ext
  intro limb bound
  change limb < 4 at bound
  have equation := Verification.assertion_of_holds h
    ⟨(if second then 112 else 100) + 4 * i.val + limb, by rw [constraint_count]; cases second <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega⟩
  cases second <;> fin_cases i <;> interval_cases limb
  all_goals simp [Variables.modeColumns, mixMode] at selected
  all_goals simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, selected, preservedLanes, readLaneLimbs, writeLaneLimbs] at equation ⊢
  all_goals linear_combination -equation

private theorem preserved_lane_value {p : Nat} {w : Nat → ZMod p} {i : Fin 6}
    (same : writeLaneLimbs w i = readLaneLimbs w i) : writeLane w i = readLane w i :=
  (lane_of_limbs same.symm).symm

private theorem read_limbs_native {p : Nat} (w : Nat → ZMod p) (lane : Fin 6) (limb : Fin 4) :
    (readLaneLimbs w lane)[limb] = w (nativeLimbs (15 + 8 * lane.val))[limb] := by
  fin_cases limb <;> simp [readLaneLimbs, nativeLimbs] <;> congr 1 <;> omega

private theorem write_limbs_native {p : Nat} (w : Nat → ZMod p) (lane : Fin 6) (limb : Fin 4) :
    (writeLaneLimbs w lane)[limb] = w (nativeLimbs (17 + 8 * lane.val))[limb] := by
  fin_cases limb <;> simp [writeLaneLimbs, nativeLimbs] <;> congr 1 <;> omega

private theorem mix_bounds {p : Nat} [Fact p.Prime] (hp : 1048576 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {first second : Nat → ZMod p}
    (hfirst : FlatOperation.ConstraintsHoldFlat (Verification.environment first)
      (importedConstraints (setupTable control)))
    (hsecond : FlatOperation.ConstraintsHoldFlat (Verification.environment second)
      (importedConstraints (setupTable control)))
    (activeFirst : first 0 = 1) (activeSecond : second 0 = 1)
    (selectedFirst : first 64 = 1) (selectedSecond : second 65 = 1)
    (transport : ∀ i : Fin 6, readLaneLimbs second i = writeLaneLimbs first i) :
    (∀ lane : Fin 5, ∀ limb : Fin 4,
      (readLaneLimbs first ⟨lane.val, by omega⟩)[limb].val < 65536) ∧
    (∀ lane : Fin 5, ∀ limb : Fin 4,
      (readLaneLimbs second ⟨lane.val, by omega⟩)[limb].val < 65536) := by
  have f0 (i : Fin 4) := (mix_xor_limb hp false hfirst activeFirst selectedFirst 2 (by decide) i).1
  have f2 (i : Fin 4) := (mix_xor_limb hp false hfirst activeFirst selectedFirst 4 (by decide) i).1
  have s4 (i : Fin 4) := (mix_xor_limb hp true hsecond activeSecond selectedSecond 1 (by decide) i).1
  have s1 (i : Fin 4) := (mix_xor_limb hp true hsecond activeSecond selectedSecond 3 (by decide) i).1
  have s3 (i : Fin 4) := (mix_xor_limb hp true hsecond activeSecond selectedSecond 4 (by decide) i).1
  have preserved (i : Fin 3) := mix_preserved false hfirst selectedFirst i
  have copied (i : Fin 3) : readLaneLimbs second (preservedLanes false)[i] =
      readLaneLimbs first (preservedLanes false)[i] :=
    (transport _).trans (preserved i)
  have firstBounds : ∀ lane : Fin 5, ∀ limb : Fin 4,
      (readLaneLimbs first ⟨lane.val, by omega⟩)[limb].val < 65536 := by
    intro lane limb
    fin_cases lane
    · have bound := f0 limb
      fin_cases limb <;> simpa [aColumns, nativeLimbs, readLaneLimbs] using bound
    · have bound := s1 limb
      have bound : (readLaneLimbs second 1)[limb].val < 65536 := by
        rw [read_limbs_native]; exact bound
      have same : readLaneLimbs second 1 = readLaneLimbs first 1 := copied 0
      rw [same] at bound
      exact bound
    · have bound := f2 limb
      fin_cases limb <;> simpa [aColumns, nativeLimbs, readLaneLimbs] using bound
    · have bound := s3 limb
      have bound : (readLaneLimbs second 3)[limb].val < 65536 := by
        rw [read_limbs_native]; exact bound
      have same : readLaneLimbs second 3 = readLaneLimbs first 3 := copied 1
      rw [same] at bound
      exact bound
    · have bound := s4 limb
      have bound : (readLaneLimbs second 4)[limb].val < 65536 := by
        rw [read_limbs_native]; exact bound
      have same : readLaneLimbs second 4 = readLaneLimbs first 4 := copied 2
      rw [same] at bound
      exact bound
  refine ⟨firstBounds, ?_⟩
  intro lane limb
  fin_cases lane
  · have bound := (mix_xor_limb hp false hfirst activeFirst selectedFirst 2 (by decide) limb).2.2.1
    have bound : (writeLaneLimbs first 0)[limb].val < 65536 := by
      rw [write_limbs_native]; exact bound
    rw [← transport 0] at bound
    exact bound
  · have bound := s1 limb
    fin_cases limb <;> simpa [aColumns, nativeLimbs, readLaneLimbs] using bound
  · have bound := (mix_xor_limb hp false hfirst activeFirst selectedFirst 4 (by decide) limb).2.2.1
    have bound : (writeLaneLimbs first 2)[limb].val < 65536 := by
      rw [write_limbs_native]; exact bound
    rw [← transport 2] at bound
    exact bound
  · have bound := s3 limb
    fin_cases limb <;> simpa [aColumns, nativeLimbs, readLaneLimbs] using bound
  · have bound := s4 limb
    fin_cases limb <;> simpa [aColumns, nativeLimbs, readLaneLimbs] using bound

theorem mixed_columns {p : Nat} [Fact p.Prime] (hp : 1048576 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {first second : Nat → ZMod p}
    {c : Vector Nat 5} {round : Fin 32}
    (hfirst : FlatOperation.ConstraintsHoldFlat (Verification.environment first)
      (importedConstraints (setupTable control)))
    (hsecond : FlatOperation.ConstraintsHoldFlat (Verification.environment second)
      (importedConstraints (setupTable control)))
    (mapping : MixMapping c round first second) : MixResult c first second := by
  have firstDecoded := decoded_control (by omega) (ControlState.mk 1 0 round)
    hfirst mapping.firstActive mapping.firstControl
  have next := next_control (by omega) (ControlState.mk 1 0 round)
    hfirst mapping.firstActive mapping.firstControl
  have secondInput : (second 3).val = (ControlState.mk 2 0 round).packed := by
    rw [mapping.controlTransport, next]
    simp [ControlState.nextPacked, ControlState.packed]
  have secondDecoded := decoded_control (by omega) (ControlState.mk 2 0 round)
    hsecond mapping.secondActive secondInput
  have selectedFirst : first 64 = 1 := by simpa [Variables.modeColumns] using firstDecoded.1 (1 : Fin 7)
  have selectedSecond : second 65 = 1 := by simpa [Variables.modeColumns] using secondDecoded.1 (2 : Fin 7)
  have bounds := mix_bounds hp hfirst hsecond mapping.firstActive mapping.secondActive
    selectedFirst selectedSecond mapping.transport
  have fbound (operation : Fin 5) (i : Fin 4) :
      (first (aColumns false)[operation][i]).val < 65536 := by
    have b0 := bounds.1 0 i
    have b2 := bounds.1 2 i
    have b4 := bounds.1 4 i
    rw [read_limbs_native] at b0 b2 b4
    fin_cases operation
    all_goals first | exact b0 | exact b2 | exact b4
  have sbound (operation : Fin 5) (i : Fin 4) :
      (second (aColumns true)[operation][i]).val < 65536 := by
    have b1 := bounds.2 1 i
    have b3 := bounds.2 3 i
    have b4 := bounds.2 4 i
    rw [read_limbs_native] at b1 b3 b4
    fin_cases operation
    all_goals first | exact b1 | exact b3 | exact b4
  have f0 := mix_rotation_operation hp false hfirst mapping.firstActive selectedFirst 0 (by decide) (fbound 0)
  have f1 := mix_rotation_operation hp false hfirst mapping.firstActive selectedFirst 1 (by decide) (fbound 1)
  have f2 := mix_xor_operation hp false hfirst mapping.firstActive selectedFirst 2 (by decide)
  have f3 := mix_rotation_operation hp false hfirst mapping.firstActive selectedFirst 3 (by decide) (fbound 3)
  have f4 := mix_xor_operation hp false hfirst mapping.firstActive selectedFirst 4 (by decide)
  have s0 := mix_rotation_operation hp true hsecond mapping.secondActive selectedSecond 0 (by decide) (sbound 0)
  have s1 := mix_xor_operation hp true hsecond mapping.secondActive selectedSecond 1 (by decide)
  have s2 := mix_rotation_operation hp true hsecond mapping.secondActive selectedSecond 2 (by decide) (sbound 2)
  have s3 := mix_xor_operation hp true hsecond mapping.secondActive selectedSecond 3 (by decide)
  have s4 := mix_xor_operation hp true hsecond mapping.secondActive selectedSecond 4 (by decide)
  change writeLane first 5 = rotLeft64 (readLane first 0) 1 at f0
  change packed first (temporary 90) = rotLeft64 (readLane first 2) 1 at f1
  change writeLane first 0 = readLane first 0 ^^^ packed first (temporary 90) at f2
  change packed first (temporary 94) = rotLeft64 (readLane first 4) 1 at f3
  change writeLane first 2 = readLane first 2 ^^^ packed first (temporary 94) at f4
  change packed second (temporary 90) = rotLeft64 (readLane second 1) 1 at s0
  change writeLane second 4 = readLane second 4 ^^^ packed second (temporary 90) at s1
  change packed second (temporary 94) = rotLeft64 (readLane second 3) 1 at s2
  change writeLane second 1 = readLane second 1 ^^^ packed second (temporary 94) at s3
  change writeLane second 3 = readLane second 3 ^^^ readLane second 5 at s4
  have preservedFirst (i : Fin 3) := mix_preserved false hfirst selectedFirst i
  have preservedSecond (i : Fin 3) := mix_preserved true hsecond selectedSecond i
  have transferred (i : Fin 6) := lane_of_limbs (mapping.transport i)
  have copied (i : Fin 3) : readLane second (preservedLanes false)[i] =
      readLane first (preservedLanes false)[i] :=
    (transferred _).trans (preserved_lane_value (preservedFirst i))
  have p0 := mapping.parities (0 : Fin 5); have p1 := mapping.parities (1 : Fin 5)
  have p2 := mapping.parities (2 : Fin 5); have p3 := mapping.parities (3 : Fin 5)
  have p4 := mapping.parities (4 : Fin 5)
  change readLane first 0 = c[0] at p0
  change readLane first 1 = c[1] at p1
  change readLane first 2 = c[2] at p2
  change readLane first 3 = c[3] at p3
  change readLane first 4 = c[4] at p4
  have t1 := copied (0 : Fin 3); have t3 := copied (1 : Fin 3); have t4 := copied (2 : Fin 3)
  change readLane second 1 = readLane first 1 at t1
  change readLane second 3 = readLane first 3 at t3
  change readLane second 4 = readLane first 4 at t4
  rw [f1, p0, p2] at f2
  rw [f3, p2, p4] at f4
  rw [s0, t1, t4, p1, p4] at s1
  rw [s2, t1, t3, p1, p3] at s3
  rw [t3, transferred 5, f0, p0, p3] at s4
  refine ⟨?_, preservedFirst, preservedSecond⟩
  apply Vector.ext
  intro i hi
  change i < 5 at hi
  interval_cases i
  · exact s1
  · exact f2
  · exact s3
  · exact f4
  · exact s4

end Airbender.Keccak.Proofs
