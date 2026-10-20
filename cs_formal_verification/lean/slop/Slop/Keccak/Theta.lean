import Human.Circuits.Keccak.Theta
import Slop.Keccak.Lookups
import Slop.Keccak.OpIndex
import Slop.Arithmetic.ByteAssembly

namespace Airbender.Keccak.Proofs
open Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 800000

private theorem theta_rotations {p : Nat} [Fact p.Prime] (hp : 7 < p)
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (active : w 0 = 1) (theta : w 66 = 1) : ∀ i : Fin 5, w (80 + i.val) = 0 := by
  have modes := selected_modes hp h active (3 : Fin 7) theta
  have rho : w 67 = 0 := by simpa [Variables.modeColumns] using modes (4 : Fin 7)
  intro i
  have flag := Verification.assertion_of_holds h ⟨9 + i.val, by rw [constraint_count]; omega⟩
  fin_cases i
  all_goals op_index at flag
  all_goals simpa [Expression.eval, Verification.environment, rho] using flag.symm

private def limbOffsets : Vector Nat 4 := #v[0, 1, 4, 5]

private theorem theta_limb_routes {p : Nat} [Fact p.Prime] (hp : 7 < p)
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (active : w 0 = 1) (theta : w 66 = 1) (operation : Fin 5) (limb : Fin 4) :
    w (102 + 24 * operation.val + 2 * limb.val) +
      256 * w (103 + 24 * operation.val + 2 * limb.val) =
      w (15 + 8 * operation.val + limbOffsets[limb]) ∧
    w (110 + 24 * operation.val + 2 * limb.val) +
      256 * w (111 + 24 * operation.val + 2 * limb.val) = w (55 + limbOffsets[limb]) ∧
    w (118 + 24 * operation.val + 2 * limb.val) +
      256 * w (119 + 24 * operation.val + 2 * limb.val) =
      w (17 + 8 * operation.val + limbOffsets[limb]) := by
  have modes := selected_modes hp h active (3 : Fin 7) theta
  have m0 : w 63 = 0 := by simpa [Variables.modeColumns] using modes (0 : Fin 7)
  have m1 : w 64 = 0 := by simpa [Variables.modeColumns] using modes (1 : Fin 7)
  have m2 : w 65 = 0 := by simpa [Variables.modeColumns] using modes (2 : Fin 7)
  have m4 : w 67 = 0 := by simpa [Variables.modeColumns] using modes (4 : Fin 7)
  have m5 : w 68 = 0 := by simpa [Variables.modeColumns] using modes (5 : Fin 7)
  have m6 : w 69 = 0 := by simpa [Variables.modeColumns] using modes (6 : Fin 7)
  have rotations := theta_rotations hp h active theta
  have r0 := rotations (0 : Fin 5); have r1 := rotations (1 : Fin 5)
  have r2 := rotations (2 : Fin 5); have r3 := rotations (3 : Fin 5)
  have r4 := rotations (4 : Fin 5)
  change w 80 = 0 at r0
  change w 81 = 0 at r1
  change w 82 = 0 at r2
  change w 83 = 0 at r3
  change w 84 = 0 at r4
  have a := Verification.assertion_of_holds h
    ⟨20 + 13 * operation.val + 3 * limb.val, by rw [constraint_count]; omega⟩
  have b := Verification.assertion_of_holds h
    ⟨21 + 13 * operation.val + 3 * limb.val, by rw [constraint_count]; omega⟩
  have c := Verification.assertion_of_holds h
    ⟨22 + 13 * operation.val + 3 * limb.val, by rw [constraint_count]; omega⟩
  fin_cases operation <;> fin_cases limb
  all_goals op_index at a b c
  all_goals simp [Expression.eval, Verification.environment,
      m0, m1, m2, theta, m4, m5, m6, r0, r1, r2, r3, r4, limbOffsets] at a b c ⊢
  all_goals exact ⟨by linear_combination a, by linear_combination b, by linear_combination c⟩

private theorem theta_bytes {p : Nat} [Fact p.Prime] (hp : 256 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control)))
    (active : w 0 = 1) (theta : w 66 = 1) (operation : Fin 5) (byte : Fin 8) :
    (w (102 + 24 * operation.val + byte.val)).val < 256 ∧
    (w (110 + 24 * operation.val + byte.val)).val < 256 ∧
    (w (118 + 24 * operation.val + byte.val)).val < 256 ∧
    (w (118 + 24 * operation.val + byte.val)).val =
      (w (102 + 24 * operation.val + byte.val)).val ^^^
        (w (110 + 24 * operation.val + byte.val)).val := by
  have query := theta_byte_relations hp h active theta
    ⟨8 * operation.val + byte.val, by omega⟩
  fin_cases operation <;> fin_cases byte <;>
    simpa [byteQuery, importedConstraints, FlatOperation.lookups, Expression.eval,
      Verification.environment] using query


/-- Every observed input/output limb is forced by its two native byte queries. -/
theorem theta_limb_xors {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control)))
    (active : w 0 = 1) (theta : w 66 = 1) (operation : Fin 5) (limb : Fin 4) :
    (w (15 + 8 * operation.val + limbOffsets[limb])).val < 65536 ∧
    (w (55 + limbOffsets[limb])).val < 65536 ∧
    (w (17 + 8 * operation.val + limbOffsets[limb])).val < 65536 ∧
    (w (17 + 8 * operation.val + limbOffsets[limb])).val =
      (w (15 + 8 * operation.val + limbOffsets[limb])).val ^^^
        (w (55 + limbOffsets[limb])).val := by
  have low := theta_bytes (by omega) h active theta operation ⟨2 * limb.val, by omega⟩
  have high := theta_bytes (by omega) h active theta operation ⟨2 * limb.val + 1, by omega⟩
  have routes := theta_limb_routes (by omega) h active theta operation limb
  have ia : 103 + 24 * operation.val + 2 * limb.val =
      102 + 24 * operation.val + (2 * limb.val + 1) := by omega
  have ib : 111 + 24 * operation.val + 2 * limb.val =
      110 + 24 * operation.val + (2 * limb.val + 1) := by omega
  have ic : 119 + 24 * operation.val + 2 * limb.val =
      118 + 24 * operation.val + (2 * limb.val + 1) := by omega
  rw [ia, ib, ic] at routes
  have a := value_of_bounded_pair (radix := 256) (capacity := 256) hp low.1 high.1 routes.1
  have b := value_of_bounded_pair (radix := 256) (capacity := 256) hp low.2.1 high.2.1 routes.2.1
  have c := value_of_bounded_pair (radix := 256) (capacity := 256) hp low.2.2.1 high.2.2.1 routes.2.2
  have aBound : (w (15 + 8 * operation.val + limbOffsets[limb])).val < 65536 := by
    rw [a]; have := low.1; have := high.1; omega
  have bBound : (w (55 + limbOffsets[limb])).val < 65536 := by
    rw [b]; have := low.2.1; have := high.2.1; omega
  have cBound : (w (17 + 8 * operation.val + limbOffsets[limb])).val < 65536 := by
    rw [c]; have := low.2.2.1; have := high.2.2.1; omega
  refine ⟨aBound, bBound, cBound, ?_⟩
  have xor := xor_of_chunks (width := 8) low.1 low.2.1
    (a₁ := (w (102 + 24 * operation.val + (2 * limb.val + 1))).val)
    (b₁ := (w (110 + 24 * operation.val + (2 * limb.val + 1))).val)
  norm_num only [Nat.reducePow] at xor
  rw [c, low.2.2.2, high.2.2.2]
  rw [a, b]
  exact xor.symm

/-- Assemble the five written state lanes, deriving all six read-lane bounds
    and all five result bounds from the actual byte queries. -/
theorem theta_lane_xor {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control)))
    (active : w 0 = 1) (theta : w 66 = 1) (operation : Fin 5) :
    readLane w ⟨operation.val, by omega⟩ < 2 ^ 64 ∧ readLane w 5 < 2 ^ 64 ∧
    writeLane w ⟨operation.val, by omega⟩ < 2 ^ 64 ∧
    writeLane w ⟨operation.val, by omega⟩ =
      readLane w ⟨operation.val, by omega⟩ ^^^ readLane w 5 := by
  have l0 := theta_limb_xors hp h active theta operation (0 : Fin 4)
  have l1 := theta_limb_xors hp h active theta operation (1 : Fin 4)
  have l2 := theta_limb_xors hp h active theta operation (2 : Fin 4)
  have l3 := theta_limb_xors hp h active theta operation (3 : Fin 4)
  simp [limbOffsets] at l0 l1 l2 l3
  change laneValue w (15 + 8 * operation.val) < 2 ^ 64 ∧ laneValue w 55 < 2 ^ 64 ∧
    laneValue w (17 + 8 * operation.val) < 2 ^ 64 ∧
    laneValue w (17 + 8 * operation.val) =
      laneValue w (15 + 8 * operation.val) ^^^ laneValue w 55
  unfold laneValue
  simp only [Nat.reduceAdd, Nat.reducePow]
  refine ⟨by omega, by omega, by omega, ?_⟩
  have xor := xor_of_four_chunks (width := 16) l0.1 l1.1 l2.1 l0.2.1 l1.2.1 l2.2.1
    (a₃ := (w (15 + 8 * operation.val + 5)).val) (b₃ := (w 60).val)
  norm_num only [Nat.reducePow] at xor
  rw [l0.2.2.2, l1.2.2.2, l2.2.2.2, l3.2.2.2]
  exact xor.symm

theorem theta_written_bounds {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control))) (active : w 0 = 1) (selected : w 66 = 1)
    (reads : ∀ lane : Fin 6, ∀ limb : Fin 4,
      (w (15 + 8 * lane.val + (#v[0, 1, 4, 5] : Vector Nat 4)[limb])).val < 65536)
    (lane : Fin 6) (limb : Fin 4) :
    (w (17 + 8 * lane.val + (#v[0, 1, 4, 5] : Vector Nat 4)[limb])).val < 65536 := by
  by_cases scratch : lane.val = 5
  · have same : lane = 5 := Fin.ext scratch
    subst lane
    have equation := Verification.assertion_of_holds h
      ⟨124 + limb.val, by rw [constraint_count]; omega⟩
    have copy : w (57 + limbOffsets[limb]) = w (55 + limbOffsets[limb]) := by
      fin_cases limb
      all_goals op_index at equation
      all_goals simp [Expression.eval, Verification.environment, selected, limbOffsets] at equation ⊢
      all_goals linear_combination -equation
    change (w (57 + limbOffsets[limb])).val < 65536
    rw [copy]
    exact reads 5 limb
  · have small : lane.val < 5 := by omega
    exact (theta_limb_xors hp h active selected ⟨lane.val, small⟩ limb).2.2.1

theorem theta_scratch_preserved {p : Nat} [Fact p.Prime]
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (theta : w 66 = 1) : writeLane w 5 = readLane w 5 := by
  have limbs (i : Fin 4) : w (55 + limbOffsets[i]) = w (57 + limbOffsets[i]) := by
    have equation := Verification.assertion_of_holds h ⟨124 + i.val, by rw [constraint_count]; omega⟩
    fin_cases i
    all_goals op_index at equation
    all_goals simp [Expression.eval, Verification.environment, theta, limbOffsets] at equation ⊢
    all_goals linear_combination equation
  have l0 := limbs (0 : Fin 4); have l1 := limbs (1 : Fin 4)
  have l2 := limbs (2 : Fin 4); have l3 := limbs (3 : Fin 4)
  simp [limbOffsets] at l0 l1 l2 l3
  change laneValue w 57 = laneValue w 55
  simp only [laneValue, ← l0, ← l1, ← l2, ← l3]

/-- The original Clean reference exposes the same five-lane column projection. -/
theorem theta_reference_column (state : Vector Nat 25) (d : Vector Nat 5)
    (column i : Fin 5) :
    (Specs.Keccak256.thetaXor state d)[5 * column.val + i.val] =
      state[5 * column.val + i.val] ^^^ d[column] := by
  fin_cases column <;> fin_cases i <;> rfl

theorem theta_column {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p}
    {state : Vector Nat 25} {d : Vector Nat 5} {column : Fin 5}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control)))
    (interface : ThetaInterface state d column w) :
    ThetaResult state d column w := by
  constructor
  · intro i
    rw [theta_reference_column]
    rw [← interface.stateReads i, ← interface.dRead]
    exact (theta_lane_xor hp h interface.active interface.thetaSelected i).2.2.2
  · exact theta_scratch_preserved h interface.thetaSelected

end Airbender.Keccak.Proofs
