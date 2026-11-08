module
public import Human.Circuits.Keccak.Theta
public import Slop.Keccak.ByteFacts
public import Slop.Keccak.XorRoutes
public import Slop.Arithmetic.ByteAssembly

@[expose] public section

namespace Airbender.Keccak.Proofs
open Arithmetic
set_option warningAsError true

def limbOffsets : Vector Nat 4 := #v[0, 1, 4, 5]

/-- Theta's routes: lane `operation` of the read and written columns, and the scratch lane. -/
private theorem theta_route_columns : ∀ (operation : Fin 5) (limb : Fin 4),
    routeA[(3 : Fin 7)][operation][limb] = 15 + 8 * operation.val + limbOffsets[limb] ∧
    routeB[(3 : Fin 7)][operation][limb] = 55 + limbOffsets[limb] ∧
    routeC[(3 : Fin 7)][operation][limb] = 17 + 8 * operation.val + limbOffsets[limb] := by
  decide

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
  have routes := xor_routes hp h active 3 (Or.inr (Or.inl rfl)) theta operation limb
  obtain ⟨ea, eb, ec⟩ := theta_route_columns operation limb
  rwa [ea, eb, ec] at routes

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
  have ho : (8 * operation.val + byte.val) / 8 = operation.val := by omega
  have hb : (8 * operation.val + byte.val) % 8 = byte.val := by omega
  obtain ⟨c0, c1, c2⟩ := byte_columns (setupTable control) w ⟨8 * operation.val + byte.val, by omega⟩
  simp only [ho, hb] at c0 c1 c2
  simpa only [c0, c1, c2] using query

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

/-- The scratch lane's copy constraints. -/
private theorem theta_copies {p : Nat} [Fact p.Prime]
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (theta : w 66 = 1) (limb : Fin 4) : w (55 + limbOffsets[limb]) = w (57 + limbOffsets[limb]) := by
  refine copy_of_holds h ⟨124 + limb.val, by rw [constraint_count]; omega⟩ ?_ theta
  fin_cases limb
  all_goals op_index
  all_goals rfl

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
    change (w (57 + limbOffsets[limb])).val < 65536
    rw [← theta_copies h selected limb]
    exact reads 5 limb
  · have small : lane.val < 5 := by omega
    exact (theta_limb_xors hp h active selected ⟨lane.val, small⟩ limb).2.2.1

theorem theta_scratch_preserved {p : Nat} [Fact p.Prime]
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (theta : w 66 = 1) : writeLane w 5 = readLane w 5 :=
  lane_copy_of_limbs (theta_copies h theta)

end Airbender.Keccak.Proofs
