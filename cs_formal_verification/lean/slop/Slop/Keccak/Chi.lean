import Human.Circuits.Keccak.Chi
import Slop.Keccak.FixedLookups
import Slop.Arithmetic.BitwiseAssembly

namespace Airbender.Keccak.Proofs
open Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private def nativeLimbs (start : Nat) : Vector Nat 4 := #v[start, start + 1, start + 4, start + 5]
private def temporary (start : Nat) : Vector Nat 4 := #v[start, start + 1, start + 2, start + 3]
private def chiMode (second : Bool) : Fin 7 := if second then 6 else 5
private def aColumns (second : Bool) : Vector (Vector Nat 4) 5 :=
  if second then #v[nativeLimbs 31, nativeLimbs 23, nativeLimbs 15, nativeLimbs 31, nativeLimbs 15]
  else #v[nativeLimbs 15, nativeLimbs 23, nativeLimbs 15, nativeLimbs 31, nativeLimbs 23]
private def bColumns (second : Bool) : Vector (Vector Nat 4) 5 :=
  if second then #v[nativeLimbs 15, temporary 90, nativeLimbs 47, temporary 94, nativeLimbs 39]
  else #v[nativeLimbs 23, nativeLimbs 31, temporary 90, nativeLimbs 39, temporary 94]
private def cColumns (second : Bool) : Vector (Vector Nat 4) 5 :=
  if second then #v[temporary 90, nativeLimbs 25, temporary 94, nativeLimbs 33, nativeLimbs 17]
  else #v[nativeLimbs 49, temporary 90, nativeLimbs 17, temporary 94, nativeLimbs 25]
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
  have modes := selected_modes hp h active (chiMode second) selected
  have m0 := modes (0 : Fin 7); have m1 := modes (1 : Fin 7)
  have m2 := modes (2 : Fin 7); have m3 := modes (3 : Fin 7)
  have m4 := modes (4 : Fin 7); have m5 := modes (5 : Fin 7); have m6 := modes (6 : Fin 7)
  have rho : w 67 = 0 := by
    cases second <;> simpa [Variables.modeColumns, chiMode] using m4
  have rotations (i : Fin 5) : w (80 + i.val) = 0 := by
    have equation := Verification.assertion_of_holds h ⟨9 + i.val, by rw [constraint_count]; omega⟩
    fin_cases i <;>
      simpa [importedConstraints, FlatOperation.constraints, Expression.eval,
        Verification.environment, rho] using equation.symm
  have r0 := rotations (0 : Fin 5); have r1 := rotations (1 : Fin 5)
  have r2 := rotations (2 : Fin 5); have r3 := rotations (3 : Fin 5); have r4 := rotations (4 : Fin 5)
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
  cases second <;> fin_cases operation <;> fin_cases limb <;>
    simp [Variables.modeColumns, chiMode] at m0 m1 m2 m3 m4 m5 m6
  all_goals simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, m0, m1, m2, m3, m4, m5, m6,
    r0, r1, r2, r3, r4, aColumns, bColumns, cColumns, nativeLimbs, temporary] at a b c ⊢
  all_goals exact ⟨by linear_combination a, by linear_combination b, by linear_combination c⟩

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
  have query := byte_lookup_checks hp h ⟨8 * operation.val + byte.val, by omega⟩
  have tags := selected_tags (by omega) h active (chiMode second) selected
    ⟨8 * operation.val + byte.val, by omega⟩
  cases second <;> fin_cases operation <;> fin_cases byte <;>
    simp [chiMode, operationTags, byteTag, byteQuery, importedConstraints,
      FlatOperation.lookups, Expression.eval, Verification.environment,
      ByteOperationFacts, isAndn] at tags query ⊢
  all_goals
    split at query
    · rename_i zero
      have value := congrArg ZMod.val zero
      simp only [ZMod.val_zero] at value
      omega
    · simpa [tags] using query

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

private theorem lane_copy {p : Nat} {w : Nat → ZMod p} {start : Nat}
    (limbs : ∀ i : Fin 4, w (start + (#v[0, 1, 4, 5] : Vector Nat 4)[i]) =
      w (start + 2 + (#v[0, 1, 4, 5] : Vector Nat 4)[i])) :
    laneValue w (start + 2) = laneValue w start := by
  have l0 := limbs (0 : Fin 4); have l1 := limbs (1 : Fin 4)
  have l2 := limbs (2 : Fin 4); have l3 := limbs (3 : Fin 4)
  simp at l0 l1 l2 l3
  simp only [laneValue, ← l0, ← l1, ← l2, ← l3]

private theorem first_preserved {p : Nat} [Fact p.Prime]
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w 68 = 1) (lane : Fin 2) :
    writeLane w ⟨lane.val + 2, by omega⟩ = readLane w ⟨lane.val + 2, by omega⟩ := by
  change laneValue w (17 + 8 * (lane.val + 2)) = laneValue w (15 + 8 * (lane.val + 2))
  rw [show 17 + 8 * (lane.val + 2) = 31 + 8 * lane.val + 2 by omega,
    show 15 + 8 * (lane.val + 2) = 31 + 8 * lane.val by omega]
  apply lane_copy
  intro limb
  have equation := Verification.assertion_of_holds h
    ⟨136 + 4 * lane.val + limb.val, by rw [constraint_count]; omega⟩
  fin_cases lane <;> fin_cases limb <;>
    simp [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, selected] at equation ⊢
  all_goals linear_combination equation

private theorem second_preserved {p : Nat} [Fact p.Prime]
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w 69 = 1) (lane : Fin 3) :
    writeLane w ⟨lane.val + 3, by omega⟩ = readLane w ⟨lane.val + 3, by omega⟩ := by
  change laneValue w (17 + 8 * (lane.val + 3)) = laneValue w (15 + 8 * (lane.val + 3))
  rw [show 17 + 8 * (lane.val + 3) = 39 + 8 * lane.val + 2 by omega,
    show 15 + 8 * (lane.val + 3) = 39 + 8 * lane.val by omega]
  apply lane_copy
  intro limb
  have equation := Verification.assertion_of_holds h
    ⟨144 + 4 * lane.val + limb.val, by rw [constraint_count]; omega⟩
  fin_cases lane <;> fin_cases limb <;>
    simp [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, selected] at equation ⊢
  all_goals linear_combination equation

private theorem first_scratch_copy {p : Nat} [Fact p.Prime]
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w 68 = 1) : writeLane w 5 = readLane w 0 := by
  have limbs (i : Fin 4) : w (15 + (#v[0, 1, 4, 5] : Vector Nat 4)[i]) =
      w (57 + (#v[0, 1, 4, 5] : Vector Nat 4)[i]) := by
    have equation := Verification.assertion_of_holds h ⟨132 + i.val, by rw [constraint_count]; omega⟩
    fin_cases i <;> simp [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, selected] at equation ⊢
    all_goals linear_combination equation
  have l0 := limbs (0 : Fin 4); have l1 := limbs (1 : Fin 4)
  have l2 := limbs (2 : Fin 4); have l3 := limbs (3 : Fin 4)
  simp at l0 l1 l2 l3
  change laneValue w 57 = laneValue w 15
  simp only [laneValue, Nat.reduceAdd, ← l0, ← l1, ← l2, ← l3]

theorem chi_written_bounds {p : Nat} [Fact p.Prime] (hp : 1048576 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p} (second : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control)))
    (active : w 0 = 1) (selected : w Variables.modeColumns[chiMode second] = 1)
    (reads : ∀ lane : Fin 6, ∀ limb : Fin 4,
      (w (15 + 8 * lane.val + (#v[0, 1, 4, 5] : Vector Nat 4)[limb])).val < 65536)
    (lane : Fin 6) (limb : Fin 4) :
    (w (17 + 8 * lane.val + (#v[0, 1, 4, 5] : Vector Nat 4)[limb])).val < 65536 := by
  let targets : Vector (Fin 6) 3 := if second then #v[3, 4, 5] else #v[5, 2, 3]
  let sources : Vector (Fin 6) 3 := if second then #v[3, 4, 5] else #v[0, 2, 3]
  have copied (i : Fin 3) :
      (w (17 + 8 * targets[i].val + (#v[0, 1, 4, 5] : Vector Nat 4)[limb])).val < 65536 := by
    have same : w (17 + 8 * targets[i].val + (#v[0, 1, 4, 5] : Vector Nat 4)[limb]) =
        w (15 + 8 * sources[i].val + (#v[0, 1, 4, 5] : Vector Nat 4)[limb]) := by
      have equation := Verification.assertion_of_holds h
        ⟨(if second then 144 else 132) + 4 * i.val + limb.val,
          by rw [constraint_count]; cases second <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega⟩
      cases second <;> fin_cases i <;> fin_cases limb
      all_goals simp [Variables.modeColumns, chiMode] at selected
      all_goals simp [importedConstraints, FlatOperation.constraints, Expression.eval,
        Verification.environment, selected, targets, sources] at equation ⊢
      all_goals linear_combination -equation
    rw [same]
    exact reads sources[i] limb
  have results (op : Fin 5) := (chi_limb hp second h active selected op limb).2.2.1
  have r0 := results 0; have r1 := results 1; have r2 := results 2
  have r3 := results 3; have r4 := results 4
  have c0 := copied 0; have c1 := copied 1; have c2 := copied 2
  cases second <;> fin_cases lane <;> fin_cases limb
  all_goals first
    | simpa [cColumns, nativeLimbs, temporary] using r0
    | simpa [cColumns, nativeLimbs, temporary] using r1
    | simpa [cColumns, nativeLimbs, temporary] using r2
    | simpa [cColumns, nativeLimbs, temporary] using r3
    | simpa [cColumns, nativeLimbs, temporary] using r4
    | simpa [targets] using c0
    | simpa [targets] using c1
    | simpa [targets] using c2

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
  simp [aColumns, bColumns, cColumns, nativeLimbs, temporary, isAndn] at o0 o1 o2 o3 o4
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
  simp [aColumns, bColumns, cColumns, nativeLimbs, temporary, isAndn] at o0 o1 o2 o3 o4
  rw [o0] at o1
  rw [o2] at o3
  exact ⟨o4, o1, o3, second_preserved h selected⟩

private theorem chi_reference_row (state : Vector Nat 25) (row column : Fin 5) :
    (Specs.Keccak256.chi state)[5 * column.val + row.val] =
      state[5 * column.val + row.val] ^^^
        ((not64 state[5 * ((column.val + 1) % 5) + row.val]) &&&
          state[5 * ((column.val + 2) % 5) + row.val]) := by
  fin_cases row <;> fin_cases column <;> rfl

theorem chi_row {p : Nat} [Fact p.Prime] (hp : 1048576 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {first second : Nat → ZMod p}
    {state : Vector Nat 25} {row : Fin 5}
    (firstHolds : FlatOperation.ConstraintsHoldFlat (Verification.environment first)
      (importedConstraints (setupTable control)))
    (secondHolds : FlatOperation.ConstraintsHoldFlat (Verification.environment second)
      (importedConstraints (setupTable control)))
    (mapping : ChiMapping state row first second) : ChiResult state row first second := by
  have f := chi_first hp firstHolds mapping.firstActive mapping.firstSelected
  have s := chi_second hp secondHolds mapping.secondActive mapping.secondSelected
  have f0 := mapping.firstState (0 : Fin 4); have f1 := mapping.firstState (1 : Fin 4)
  have f2 := mapping.firstState (2 : Fin 4); have f3 := mapping.firstState (3 : Fin 4)
  change readLane first 0 = state[5 + row.val] at f0
  change readLane first 1 = state[10 + row.val] at f1
  change readLane first 2 = state[15 + row.val] at f2
  change readLane first 3 = state[20 + row.val] at f3
  have r0 := mapping.secondState
  have r1 : readLane second 1 = state[15 + row.val] :=
    (mapping.preservedState (0 : Fin 2)).trans ((f.2.2.2.2 (0 : Fin 2)).trans f2)
  have r2 : readLane second 2 = state[20 + row.val] :=
    (mapping.preservedState (1 : Fin 2)).trans ((f.2.2.2.2 (1 : Fin 2)).trans f3)
  have r3 : readLane second 3 = (not64 state[5 + row.val]) &&& state[10 + row.val] := by
    rw [mapping.scratch.1, f.2.2.1, f0, f1]
  have r4 : readLane second 4 = state[5 + row.val] := by
    rw [mapping.scratch.2, f.2.2.2.1, f0]
  have c0 := s.1; have c1 := f.1; have c2 := f.2.1
  have c3 := s.2.1; have c4 := s.2.2.1
  simp only [r0, r1, r2, r3, r4, f0, f1, f2, f3] at c0 c1 c2 c3 c4
  refine ⟨?_, f.2.2.2.2, s.2.2.2⟩
  intro i
  rw [chi_reference_row]
  fin_cases i
  · simpa [chiWrites] using c0
  · simpa [chiWrites] using c1
  · simpa [chiWrites] using c2
  · simpa [chiWrites] using c3
  · simpa [chiWrites] using c4

end Airbender.Keccak.Proofs
