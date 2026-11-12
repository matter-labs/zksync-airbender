module
public import Slop.Keccak.XorRoutes
public import Slop.Keccak.ByteFacts
public import Slop.Arithmetic.BitwiseAssembly
public import Slop.CleanCore.Circuit.Operations
public import Slop.Defs.Circuits.Keccak.Artifact
public import Slop.Defs.Circuits.Keccak.Theta
public import Slop.Defs.Circuits.Keccak.Tables.Setup

@[expose] public section

namespace Airbender.Keccak.Proofs
open Arithmetic
set_option warningAsError true
def chiMode (second : Bool) : Fin 7 := if second then 6 else 5
private def aColumns (second : Bool) : Vector (Vector Nat 4) 5 :=
  if second then #v[routeNative 31, routeNative 23, routeNative 15, routeNative 31, routeNative 15]
  else #v[routeNative 15, routeNative 23, routeNative 15, routeNative 31, routeNative 23]
private def bColumns (second : Bool) : Vector (Vector Nat 4) 5 :=
  if second then #v[routeNative 15, routeScratch 90, routeNative 47, routeScratch 94, routeNative 39]
  else #v[routeNative 23, routeNative 31, routeScratch 90, routeNative 39, routeScratch 94]
private def cColumns (second : Bool) : Vector (Vector Nat 4) 5 :=
  if second then #v[routeScratch 90, routeNative 25, routeScratch 94, routeNative 33, routeNative 17]
  else #v[routeNative 49, routeScratch 90, routeNative 17, routeScratch 94, routeNative 25]
private def isAndn (second : Bool) (operation : Fin 5) : Bool :=
  if second then operation.val = 0 || operation.val = 2
  else operation.val = 0 || operation.val = 1 || operation.val = 3
private def packed {p : Nat} (w : Nat → ZMod p) (columns : Vector Nat 4) : Nat :=
  (w columns[0]).val + 65536 * ((w columns[1]).val +
    65536 * ((w columns[2]).val + 65536 * (w columns[3]).val))

private theorem chi_routes {p : Nat} [Fact p.Prime] (hp : 7 < p)
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p} (second : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (active : w 0 = 1) (selected : w Variables.modeColumns[chiMode second] = 1)
    (operation : Fin 5) (limb : Fin 4) :
    w (102 + 24 * operation.val + 2 * limb.val) +
      256 * w (103 + 24 * operation.val + 2 * limb.val) = w (aColumns second)[operation][limb] ∧
    w (110 + 24 * operation.val + 2 * limb.val) +
      256 * w (111 + 24 * operation.val + 2 * limb.val) = w (bColumns second)[operation][limb] ∧
    w (118 + 24 * operation.val + 2 * limb.val) +
      256 * w (119 + 24 * operation.val + 2 * limb.val) = w (cColumns second)[operation][limb] := by
  have routes := xor_routes hp h active (chiMode second) (by cases second <;> decide) selected
    operation limb
  have ca : routeA[chiMode second] = aColumns second := by cases second <;> rfl
  have cb : routeB[chiMode second] = bColumns second := by cases second <;> rfl
  have cc : routeC[chiMode second] = cColumns second := by cases second <;> rfl
  rwa [ca, cb, cc] at routes

/-- The routing tag of each chi operation is ANDN (39) or XOR (4), by the selected mode. -/
private theorem chi_tag (second : Bool) (operation : Fin 5) :
    operationTags[chiMode second][operation.val] = if isAndn second operation then 39 else 4 := by
  cases second <;> fin_cases operation <;> decide

private theorem chi_bytes {p : Nat} [Fact p.Prime] (hp : 1048576 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p} (second : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control)))
    (active : w 0 = 1) (selected : w Variables.modeColumns[chiMode second] = 1)
    (operation : Fin 5) (byte : Fin 8) :
    (w (102 + 24 * operation.val + byte.val)).val < 256 ∧
    (w (110 + 24 * operation.val + byte.val)).val < 256 ∧
    (w (118 + 24 * operation.val + byte.val)).val < 256 ∧
    (w (118 + 24 * operation.val + byte.val)).val =
      (if isAndn second operation then
        ((w (102 + 24 * operation.val + byte.val)).val ^^^ 255) &&&
          (w (110 + 24 * operation.val + byte.val)).val
      else (w (102 + 24 * operation.val + byte.val)).val ^^^
        (w (110 + 24 * operation.val + byte.val)).val) := by
  have facts := selected_byte_facts hp h active (chiMode second) selected operation byte
  rw [chi_tag] at facts
  cases hA : isAndn second operation
  · simp only [hA, Bool.false_eq_true, ↓reduceIte] at facts ⊢
    exact xor_byte_facts facts
  · simp only [hA, ↓reduceIte] at facts ⊢
    exact andn_byte_facts facts

private theorem chi_limb {p : Nat} [Fact p.Prime] (hp : 1048576 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p} (second : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control)))
    (active : w 0 = 1) (selected : w Variables.modeColumns[chiMode second] = 1)
    (operation : Fin 5) (limb : Fin 4) :
    (w (aColumns second)[operation][limb]).val < 65536 ∧
    (w (bColumns second)[operation][limb]).val < 65536 ∧
    (w (cColumns second)[operation][limb]).val < 65536 ∧
    (w (cColumns second)[operation][limb]).val =
      if isAndn second operation then
        ((w (aColumns second)[operation][limb]).val ^^^ 65535) &&&
          (w (bColumns second)[operation][limb]).val
      else (w (aColumns second)[operation][limb]).val ^^^
        (w (bColumns second)[operation][limb]).val := by
  have low := chi_bytes hp second h active selected operation ⟨2 * limb.val, by omega⟩
  have high := chi_bytes hp second h active selected operation ⟨2 * limb.val + 1, by omega⟩
  have routes := chi_routes (by omega) second h active selected operation limb
  have ia : 103 + 24 * operation.val + 2 * limb.val =
      102 + 24 * operation.val + (2 * limb.val + 1) := by omega
  have ib : 111 + 24 * operation.val + 2 * limb.val =
      110 + 24 * operation.val + (2 * limb.val + 1) := by omega
  have ic : 119 + 24 * operation.val + 2 * limb.val =
      118 + 24 * operation.val + (2 * limb.val + 1) := by omega
  rw [ia, ib, ic] at routes
  have a := value_of_bounded_pair (radix := 256) (capacity := 256) (by omega) low.1 high.1 routes.1
  have b := value_of_bounded_pair (radix := 256) (capacity := 256) (by omega) low.2.1 high.2.1 routes.2.1
  have c := value_of_bounded_pair (radix := 256) (capacity := 256) (by omega) low.2.2.1 high.2.2.1 routes.2.2
  refine ⟨by rw [a]; omega, by rw [b]; omega, by rw [c]; omega, ?_⟩
  rw [a, b, c, low.2.2.2, high.2.2.2]
  split
  · have value := andn_of_chunks (width := 8) low.1 low.2.1
      (a₁ := (w (102 + 24 * operation.val + (2 * limb.val + 1))).val)
      (b₁ := (w (110 + 24 * operation.val + (2 * limb.val + 1))).val)
    norm_num only [Nat.reducePow, Nat.reduceSub] at value
    exact value.symm
  · have value := xor_of_chunks (width := 8) low.1 low.2.1
      (a₁ := (w (102 + 24 * operation.val + (2 * limb.val + 1))).val)
      (b₁ := (w (110 + 24 * operation.val + (2 * limb.val + 1))).val)
    norm_num only [Nat.reducePow] at value
    exact value.symm

private theorem chi_operation {p : Nat} [Fact p.Prime] (hp : 1048576 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p} (second : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control)))
    (active : w 0 = 1) (selected : w Variables.modeColumns[chiMode second] = 1)
    (operation : Fin 5) :
    packed w (cColumns second)[operation] =
      if isAndn second operation then
        (not64 (packed w (aColumns second)[operation])) &&& packed w (bColumns second)[operation]
      else packed w (aColumns second)[operation] ^^^ packed w (bColumns second)[operation] := by
  have l0 := chi_limb hp second h active selected operation (0 : Fin 4)
  have l1 := chi_limb hp second h active selected operation (1 : Fin 4)
  have l2 := chi_limb hp second h active selected operation (2 : Fin 4)
  have l3 := chi_limb hp second h active selected operation (3 : Fin 4)
  simp [packed] at l0 l1 l2 l3 ⊢
  by_cases flag : isAndn second operation = true
  · simp only [flag, ite_true] at l0 l1 l2 l3 ⊢
    rw [l0.2.2.2, l1.2.2.2, l2.2.2.2, l3.2.2.2]
    have value := andn_of_four_limbs l0.1 l1.1 l2.1 l0.2.1 l1.2.1 l2.2.1
      (a₃ := (w (aColumns second)[operation][3]).val)
      (b₃ := (w (bColumns second)[operation][3]).val)
    exact value.symm
  · simp only [flag] at l0 l1 l2 l3 ⊢
    rw [l0.2.2.2, l1.2.2.2, l2.2.2.2, l3.2.2.2]
    have value := xor_of_four_chunks (width := 16) l0.1 l1.1 l2.1 l0.2.1 l1.2.1 l2.2.1
      (a₃ := (w (aColumns second)[operation][3]).val)
      (b₃ := (w (bColumns second)[operation][3]).val)
    norm_num only [Nat.reducePow] at value
    exact value.symm

/-- Lanes copied by each chi step: lane `chiSources[i]` is written to lane `chiTargets[i]`. -/
private def chiTargets (second : Bool) : Vector (Fin 6) 3 := if second then #v[3, 4, 5] else #v[5, 2, 3]
private def chiSources (second : Bool) : Vector (Fin 6) 3 := if second then #v[3, 4, 5] else #v[0, 2, 3]

private theorem chi_copies {p : Nat} [Fact p.Prime]
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p} (second : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w Variables.modeColumns[chiMode second] = 1) (i : Fin 3) (limb : Fin 4) :
    w (15 + 8 * (chiSources second)[i].val + (#v[0, 1, 4, 5] : Vector Nat 4)[limb]) =
      w (17 + 8 * (chiTargets second)[i].val + (#v[0, 1, 4, 5] : Vector Nat 4)[limb]) := by
  cases second
  · refine copy_of_holds h ⟨132 + 4 * i.val + limb.val, by rw [constraint_count]; omega⟩ ?_ selected
    fin_cases i <;> fin_cases limb
    all_goals op_index
    all_goals rfl
  · refine copy_of_holds h ⟨144 + 4 * i.val + limb.val, by rw [constraint_count]; omega⟩ ?_ selected
    fin_cases i <;> fin_cases limb
    all_goals op_index
    all_goals rfl

private theorem chi_copy_lane {p : Nat} [Fact p.Prime]
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p} (second : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w Variables.modeColumns[chiMode second] = 1) (i : Fin 3) :
    writeLane w (chiTargets second)[i] = readLane w (chiSources second)[i] :=
  lane_copy_of_limbs (chi_copies second h selected i)

private theorem first_preserved {p : Nat} [Fact p.Prime]
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w 68 = 1) (lane : Fin 2) :
    writeLane w ⟨lane.val + 2, by omega⟩ = readLane w ⟨lane.val + 2, by omega⟩ := by
  fin_cases lane
  · exact chi_copy_lane false h selected 1
  · exact chi_copy_lane false h selected 2

private theorem second_preserved {p : Nat} [Fact p.Prime]
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w 69 = 1) (lane : Fin 3) :
    writeLane w ⟨lane.val + 3, by omega⟩ = readLane w ⟨lane.val + 3, by omega⟩ := by
  fin_cases lane
  · exact chi_copy_lane true h selected 0
  · exact chi_copy_lane true h selected 1
  · exact chi_copy_lane true h selected 2

private theorem first_scratch_copy {p : Nat} [Fact p.Prime]
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w 68 = 1) : writeLane w 5 = readLane w 0 :=
  chi_copy_lane false h selected 0

/-- Every written lane is an operation's output or a copy target. -/
private theorem chi_written_cover : ∀ second : Bool, ∀ lane : Fin 6, ∀ limb : Fin 4,
    (∃ operation : Fin 5, (cColumns second)[operation][limb] =
      17 + 8 * lane.val + (#v[0, 1, 4, 5] : Vector Nat 4)[limb]) ∨
    ∃ i : Fin 3, (chiTargets second)[i] = lane := by
  decide

theorem chi_written_bounds {p : Nat} [Fact p.Prime] (hp : 1048576 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p} (second : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control)))
    (active : w 0 = 1) (selected : w Variables.modeColumns[chiMode second] = 1)
    (reads : ∀ lane : Fin 6, ∀ limb : Fin 4,
      (w (15 + 8 * lane.val + (#v[0, 1, 4, 5] : Vector Nat 4)[limb])).val < 65536)
    (lane : Fin 6) (limb : Fin 4) :
    (w (17 + 8 * lane.val + (#v[0, 1, 4, 5] : Vector Nat 4)[limb])).val < 65536 := by
  rcases chi_written_cover second lane limb with ⟨operation, same⟩ | ⟨i, same⟩
  · rw [← same]
    exact (chi_limb hp second h active selected operation limb).2.2.1
  · subst same
    rw [← chi_copies second h selected i limb]
    exact reads _ limb

theorem chi_first {p : Nat} [Fact p.Prime] (hp : 1048576 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control))) (active : w 0 = 1) (selected : w 68 = 1) :
    writeLane w 0 = readLane w 0 ^^^ ((not64 (readLane w 1)) &&& readLane w 2) ∧
    writeLane w 1 = readLane w 1 ^^^ ((not64 (readLane w 2)) &&& readLane w 3) ∧
    writeLane w 4 = (not64 (readLane w 0)) &&& readLane w 1 ∧
    writeLane w 5 = readLane w 0 ∧
    (∀ i : Fin 2, writeLane w ⟨i.val + 2, by omega⟩ = readLane w ⟨i.val + 2, by omega⟩) := by
  have operations (i : Fin 5) := chi_operation hp false h active selected i
  have o0 := operations (0 : Fin 5); have o1 := operations (1 : Fin 5)
  have o2 := operations (2 : Fin 5); have o3 := operations (3 : Fin 5)
  have o4 := operations (4 : Fin 5)
  simp [aColumns, bColumns, cColumns, routeNative, routeScratch, isAndn] at o0 o1 o2 o3 o4
  rw [o1] at o2
  rw [o3] at o4
  exact ⟨o2, o4, o0, first_scratch_copy h selected, first_preserved h selected⟩

theorem chi_second {p : Nat} [Fact p.Prime] (hp : 1048576 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control))) (active : w 0 = 1) (selected : w 69 = 1) :
    writeLane w 0 = readLane w 0 ^^^ readLane w 3 ∧
    writeLane w 1 = readLane w 1 ^^^ ((not64 (readLane w 2)) &&& readLane w 0) ∧
    writeLane w 2 = readLane w 2 ^^^ ((not64 (readLane w 0)) &&& readLane w 4) ∧
    (∀ i : Fin 3, writeLane w ⟨i.val + 3, by omega⟩ = readLane w ⟨i.val + 3, by omega⟩) := by
  have operations (i : Fin 5) := chi_operation hp true h active selected i
  have o0 := operations (0 : Fin 5); have o1 := operations (1 : Fin 5)
  have o2 := operations (2 : Fin 5); have o3 := operations (3 : Fin 5)
  have o4 := operations (4 : Fin 5)
  simp [aColumns, bColumns, cColumns, routeNative, routeScratch, isAndn] at o0 o1 o2 o3 o4
  rw [o0] at o1
  rw [o2] at o3
  exact ⟨o4, o1, o3, second_preserved h selected⟩

end Airbender.Keccak.Proofs
