import Airbender.Review.Keccak.Iota
import Airbender.Proofs.Keccak.DecodeControl
import Airbender.Proofs.Keccak.FixedLookups
import Airbender.Proofs.Arithmetic.ByteAssembly

namespace Airbender.Keccak.Proofs
open Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private def nativeLimbs (start : Nat) : Vector Nat 4 := #v[start, start + 1, start + 4, start + 5]
private def temporary (start : Nat) : Vector Nat 4 := #v[start, start + 1, start + 2, start + 3]
private def aColumns : Vector (Vector Nat 4) 5 :=
  #v[nativeLimbs 15, nativeLimbs 17, temporary 90, temporary 94, temporary 98]
private def bColumns : Vector (Vector Nat 4) 5 :=
  #v[temporary 86, nativeLimbs 23, nativeLimbs 31, nativeLimbs 39, nativeLimbs 47]
private def cColumns : Vector (Vector Nat 4) 5 :=
  #v[nativeLimbs 17, temporary 90, temporary 94, temporary 98, nativeLimbs 57]
private def packed {p : Nat} (w : Nat → ZMod p) (columns : Vector Nat 4) : Nat :=
  (w columns[0]).val + 65536 * ((w columns[1]).val +
    65536 * ((w columns[2]).val + 65536 * (w columns[3]).val))

private theorem iota_routes {p : Nat} [Fact p.Prime] (hp : 7 < p)
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (active : w 0 = 1) (selected : w 63 = 1) (operation : Fin 5) (limb : Fin 4) :
    w (102 + 24 * operation.val + 2 * limb.val) +
      256 * w (103 + 24 * operation.val + 2 * limb.val) = w aColumns[operation][limb] ∧
    w (110 + 24 * operation.val + 2 * limb.val) +
      256 * w (111 + 24 * operation.val + 2 * limb.val) = w bColumns[operation][limb] ∧
    w (118 + 24 * operation.val + 2 * limb.val) +
      256 * w (119 + 24 * operation.val + 2 * limb.val) = w cColumns[operation][limb] := by
  have modes := selected_modes hp h active (0 : Fin 7) selected
  have m1 := modes (1 : Fin 7); have m2 := modes (2 : Fin 7); have m3 := modes (3 : Fin 7)
  have m4 := modes (4 : Fin 7); have m5 := modes (5 : Fin 7); have m6 := modes (6 : Fin 7)
  simp [Variables.modeColumns] at m1 m2 m3 m4 m5 m6
  have rotations (i : Fin 5) : w (80 + i.val) = 0 := by
    have equation := Verification.assertion_of_holds h ⟨9 + i.val, by rw [constraint_count]; omega⟩
    fin_cases i <;> simpa [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, m4] using equation.symm
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
  fin_cases operation <;> fin_cases limb <;>
    simp [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, selected, m1, m2, m3, m4, m5, m6,
      r0, r1, r2, r3, r4, aColumns, bColumns, cColumns, nativeLimbs, temporary] at a b c ⊢
  all_goals exact ⟨by linear_combination a, by linear_combination b, by linear_combination c⟩

private theorem iota_bytes {p : Nat} [Fact p.Prime] (hp : 1048576 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control)))
    (active : w 0 = 1) (selected : w 63 = 1) (operation : Fin 5) (byte : Fin 8) :
    (w (102 + 24 * operation.val + byte.val)).val < 256 ∧
    (w (110 + 24 * operation.val + byte.val)).val < 256 ∧
    (w (118 + 24 * operation.val + byte.val)).val < 256 ∧
    (w (118 + 24 * operation.val + byte.val)).val =
      (w (102 + 24 * operation.val + byte.val)).val ^^^
        (if operation.val = 0 then iotaByte (w (110 + 24 * operation.val + byte.val)).val
         else (w (110 + 24 * operation.val + byte.val)).val) := by
  have query := byte_lookup_checks hp h ⟨8 * operation.val + byte.val, by omega⟩
  have tags := selected_tags (by omega) h active (0 : Fin 7) selected
    ⟨8 * operation.val + byte.val, by omega⟩
  fin_cases operation <;> fin_cases byte <;>
    simp [operationTags, byteTag, byteQuery, importedConstraints,
      FlatOperation.lookups, Expression.eval, Verification.environment,
      ByteOperationFacts] at tags query ⊢
  all_goals
    split at query
    · rename_i zero
      have value := congrArg ZMod.val zero
      simp only [ZMod.val_zero] at value
      omega
    · simpa [tags] using query

private theorem effective_round {p : Nat} [Fact p.Prime] (hp : 2048 ≤ p)
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p}
    (column : Fin 5) (round : Fin 25)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (active : w 0 = 1)
    (input : (w 3).val = (ControlState.mk 0 column ⟨round.val, by omega⟩).packed) :
    w 63 = 1 ∧ w 85 = ((if column.val = 0 then round.val else 0 : Nat) : ZMod p) := by
  have decoded := decoded_control hp (ControlState.mk 0 column ⟨round.val, by omega⟩) h active input
  have mode := decoded.1 (0 : Fin 7)
  have iter := decoded.2.1 (0 : Fin 5)
  have equation := Verification.assertion_of_holds h ⟨14, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment] at equation
  simp [Variables.modeColumns] at mode
  have flag : w 70 = if column.val = 0 then 1 else 0 := by
    by_cases zero : column.val = 0
    · have same : column = 0 := Fin.ext zero
      subst column
      simpa [Variables.iterationColumns] using iter
    · have different : (0 : Fin 5) ≠ column := by
        intro same
        have value := congrArg Fin.val same
        simp only [Fin.val_zero] at value
        omega
      simpa [Variables.iterationColumns, different, zero] using iter
  refine ⟨mode, ?_⟩
  rw [decoded.2.2, flag] at equation
  split_ifs with zero
  · simp only [zero, ite_true, mul_one] at equation
    linear_combination -equation
  · simp only [zero, ite_false, mul_zero] at equation
    simpa using equation.symm

private theorem constant_limb (round : Fin 32) (limb : Fin 4) :
    iotaByte (round.val + 32 * (2 * limb.val)) +
      256 * iotaByte (round.val + 32 * (2 * limb.val + 1)) =
      adjustedConstant round.val / 65536 ^ limb.val % 65536 := by
  fin_cases round <;> fin_cases limb <;> decide +kernel

private theorem constant_assembly (round : Fin 32) :
    adjustedConstant round.val =
      (adjustedConstant round.val % 65536) +
      65536 * ((adjustedConstant round.val / 65536 % 65536) +
      65536 * ((adjustedConstant round.val / 65536 ^ 2 % 65536) +
      65536 * (adjustedConstant round.val / 65536 ^ 3 % 65536))) := by
  fin_cases round <;> decide +kernel

private theorem control_pair {p : Nat} [Fact p.Prime] (hp : 1048576 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p} (round : Fin 32)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control)))
    (active : w 0 = 1) (selected : w 63 = 1) (rc : w 85 = (round.val : ZMod p))
    (limb : Fin 4) :
    (w (110 + 2 * limb.val)).val = round.val + 32 * (2 * limb.val) ∧
    (w (111 + 2 * limb.val)).val = round.val + 32 * (2 * limb.val + 1) := by
  have low := iota_bytes (by omega : 1048576 ≤ p) h active selected (0 : Fin 5)
    ⟨2 * limb.val, by omega⟩
  have high := iota_bytes (by omega : 1048576 ≤ p) h active selected (0 : Fin 5)
    ⟨2 * limb.val + 1, by omega⟩
  have routes := (iota_routes (by omega) h active selected (0 : Fin 5) limb).2.1
  simp only [Fin.val_zero, Nat.mul_zero, Nat.add_zero] at low high routes
  have definition := Verification.assertion_of_holds h ⟨15 + limb.val, by rw [constraint_count]; omega⟩
  have pair : w (110 + 2 * limb.val) + 256 * w (111 + 2 * limb.val) =
      ((round.val + 32 * (2 * limb.val) +
        256 * (round.val + 32 * (2 * limb.val + 1)) : Nat) : ZMod p) := by
    fin_cases limb <;> simp [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, bColumns, temporary, rc] at definition routes ⊢
    all_goals linear_combination routes - definition
  have bound : round.val + 32 * (2 * limb.val) +
      256 * (round.val + 32 * (2 * limb.val + 1)) < p := by
    have := round.isLt; have := limb.isLt
    omega
  have ib : 110 + (2 * limb.val + 1) = 111 + 2 * limb.val := by omega
  rw [ib] at high
  have canonical := value_of_bounded_pair (radix := 256) (capacity := 256)
    (by omega) low.2.1 high.2.1 pair
  rw [ZMod.val_natCast_of_lt bound] at canonical
  have smallLow : round.val + 32 * (2 * limb.val) < 256 := by
    have := round.isLt; have := limb.isLt; omega
  have splitLow : (w (110 + 2 * limb.val)).val = round.val + 32 * (2 * limb.val) := by omega
  have splitHigh : (w (111 + 2 * limb.val)).val = round.val + 32 * (2 * limb.val + 1) := by omega
  exact ⟨splitLow, splitHigh⟩

private theorem control_bytes {p : Nat} [Fact p.Prime] (hp : 1048576 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p} (round : Fin 32)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control)))
    (active : w 0 = 1) (selected : w 63 = 1) (rc : w 85 = (round.val : ZMod p))
    (byte : Fin 8) : (w (110 + byte.val)).val = round.val + 32 * byte.val := by
  have pair := control_pair hp round h active selected rc ⟨byte.val / 2, by omega⟩
  fin_cases byte <;> simp at pair ⊢
  all_goals first | exact pair.1 | exact pair.2

private def rhsLimb {p : Nat} (w : Nat → ZMod p) (round : Fin 32)
    (operation : Fin 5) (limb : Fin 4) : Nat :=
  if operation.val = 0 then adjustedConstant round.val / 65536 ^ limb.val % 65536
  else (w bColumns[operation][limb]).val

private theorem iota_limb {p : Nat} [Fact p.Prime] (hp : 1048576 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p} (round : Fin 32)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control)))
    (active : w 0 = 1) (selected : w 63 = 1) (rc : w 85 = (round.val : ZMod p))
    (operation : Fin 5) (limb : Fin 4) :
    (w aColumns[operation][limb]).val < 65536 ∧ rhsLimb w round operation limb < 65536 ∧
    (w cColumns[operation][limb]).val < 65536 ∧
    (w cColumns[operation][limb]).val = (w aColumns[operation][limb]).val ^^^
      rhsLimb w round operation limb := by
  have low := iota_bytes hp h active selected operation ⟨2 * limb.val, by omega⟩
  have high := iota_bytes hp h active selected operation ⟨2 * limb.val + 1, by omega⟩
  have routes := iota_routes (by omega) h active selected operation limb
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
  let lo := if operation.val = 0 then iotaByte (w (110 + 24 * operation.val + 2 * limb.val)).val
    else (w (110 + 24 * operation.val + 2 * limb.val)).val
  let hi := if operation.val = 0 then iotaByte (w (110 + 24 * operation.val + (2 * limb.val + 1))).val
    else (w (110 + 24 * operation.val + (2 * limb.val + 1))).val
  have loBound : lo < 256 := by
    dsimp [lo]; split_ifs
    · exact Nat.mod_lt _ (by decide)
    · exact low.2.1
  have hiBound : hi < 256 := by
    dsimp [hi]; split_ifs
    · exact Nat.mod_lt _ (by decide)
    · exact high.2.1
  have rhs : rhsLimb w round operation limb = lo + 256 * hi := by
    by_cases zero : operation.val = 0
    · have op : operation = 0 := Fin.ext zero
      subst operation
      have bl := control_bytes hp round h active selected rc ⟨2 * limb.val, by omega⟩
      have bh := control_bytes hp round h active selected rc ⟨2 * limb.val + 1, by omega⟩
      dsimp [lo, hi, rhsLimb]
      rw [bl, bh]
      exact (constant_limb round limb).symm
    · simpa [rhsLimb, lo, hi, zero] using b
  refine ⟨by rw [a]; omega, by rw [rhs]; omega, by rw [c]; omega, ?_⟩
  rw [a, rhs, c, low.2.2.2, high.2.2.2]
  have xor := xor_of_chunks (width := 8) low.1 loBound
    (a₁ := (w (102 + 24 * operation.val + (2 * limb.val + 1))).val) (b₁ := hi)
  norm_num only [Nat.reducePow] at xor
  exact xor.symm

private theorem iota_operation {p : Nat} [Fact p.Prime] (hp : 1048576 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p} (round : Fin 32)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control)))
    (active : w 0 = 1) (selected : w 63 = 1) (rc : w 85 = (round.val : ZMod p))
    (operation : Fin 5) : packed w cColumns[operation] = packed w aColumns[operation] ^^^
      (if operation.val = 0 then adjustedConstant round.val else packed w bColumns[operation]) := by
  have l0 := iota_limb hp round h active selected rc operation (0 : Fin 4)
  have l1 := iota_limb hp round h active selected rc operation (1 : Fin 4)
  have l2 := iota_limb hp round h active selected rc operation (2 : Fin 4)
  have l3 := iota_limb hp round h active selected rc operation (3 : Fin 4)
  simp [packed] at l0 l1 l2 l3 ⊢
  have xor := xor_of_four_chunks (width := 16) l0.1 l1.1 l2.1 l0.2.1 l1.2.1 l2.2.1
    (a₃ := (w aColumns[operation][3]).val) (b₃ := rhsLimb w round operation 3)
  norm_num only [Nat.reducePow] at xor
  rw [l0.2.2.2, l1.2.2.2, l2.2.2.2, l3.2.2.2]
  refine xor.symm.trans ?_
  by_cases zero : operation.val = 0
  · have same : operation = 0 := Fin.ext zero
    subst operation
    simpa [rhsLimb] using congrArg (fun n => packed w aColumns[(0 : Fin 5)] ^^^ n)
      (constant_assembly round).symm
  · have different : operation ≠ 0 := by
      intro same
      subst operation
      simp at zero
    simp [rhsLimb, zero, different]

private theorem iota_preserved {p : Nat} [Fact p.Prime]
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w 63 = 1) (lane : Fin 4) :
    writeLane w ⟨lane.val + 1, by omega⟩ = readLane w ⟨lane.val + 1, by omega⟩ := by
  have limbs (limb : Fin 4) :
      w (25 + 8 * lane.val + (#v[0, 1, 4, 5] : Vector Nat 4)[limb]) =
        w (23 + 8 * lane.val + (#v[0, 1, 4, 5] : Vector Nat 4)[limb]) := by
    have equation := Verification.assertion_of_holds h
      ⟨84 + 4 * lane.val + limb.val, by rw [constraint_count]; omega⟩
    fin_cases lane <;> fin_cases limb <;>
      simp [importedConstraints, FlatOperation.constraints, Expression.eval,
        Verification.environment, selected] at equation ⊢
    all_goals linear_combination -equation
  have l0 := limbs (0 : Fin 4); have l1 := limbs (1 : Fin 4)
  have l2 := limbs (2 : Fin 4); have l3 := limbs (3 : Fin 4)
  simp at l0 l1 l2 l3
  fin_cases lane <;> simp [writeLane, readLane, laneValue] at l0 l1 l2 l3 ⊢
  all_goals rw [l0, l1, l2, l3]

private theorem reference_column (state : Vector Nat 25) (column i : Fin 5) (round : Fin 25) :
    (iotaState state round)[5 * column.val + i.val] =
      if column.val = 0 ∧ i.val = 0 then state[0] ^^^ adjustedConstant round.val
      else state[5 * column.val + i.val] := by
  fin_cases column <;> fin_cases i <;>
    simp [iotaState, Specs.Keccak256.iota, adjustedConstant ]
  all_goals split_ifs <;> simp_all
  all_goals have := round.isLt; omega

private theorem reference_parity (state : Vector Nat 25) (column : Fin 5) :
    (Specs.Keccak256.thetaC state)[column] =
      state[5 * column.val] ^^^ state[5 * column.val + 1] ^^^
      state[5 * column.val + 2] ^^^ state[5 * column.val + 3] ^^^ state[5 * column.val + 4] := by
  fin_cases column <;> rfl

theorem iota_column {p : Nat} [Fact p.Prime] (hp : 1048576 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p}
    {state : Vector Nat 25} {column : Fin 5} {round : Fin 25}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control)))
    (mapping : IotaMapping state column round w) : IotaResult state column round w := by
  have flags := effective_round (by omega) column round h mapping.active mapping.control
  let rc : Fin 32 := ⟨if column.val = 0 then round.val else 0, by split_ifs <;> have := round.isLt <;> omega⟩
  have op0 := iota_operation hp rc h mapping.active flags.1 flags.2 (0 : Fin 5)
  have op1 := iota_operation hp rc h mapping.active flags.1 flags.2 (1 : Fin 5)
  have op2 := iota_operation hp rc h mapping.active flags.1 flags.2 (2 : Fin 5)
  have op3 := iota_operation hp rc h mapping.active flags.1 flags.2 (3 : Fin 5)
  have op4 := iota_operation hp rc h mapping.active flags.1 flags.2 (4 : Fin 5)
  simp [packed, aColumns, bColumns, cColumns, nativeLimbs, temporary] at op0 op1 op2 op3 op4
  have changed : ∀ i : Fin 5, writeLane w ⟨i.val, by omega⟩ =
      (iotaState state round)[5 * column.val + i.val] := by
    intro i
    rw [reference_column]
    fin_cases i
    · change laneValue w 17 = _
      have read := mapping.stateReads (0 : Fin 5)
      change laneValue w 15 = state[5 * column.val] at read
      change laneValue w 17 = laneValue w 15 ^^^ adjustedConstant rc.val at op0
      rw [op0, read]
      by_cases zero : column.val = 0
      · simp [rc, zero]
      · simp [rc, zero, adjustedConstant]
    · simpa using (iota_preserved h flags.1 (0 : Fin 4)).trans (mapping.stateReads (1 : Fin 5))
    · simpa using (iota_preserved h flags.1 (1 : Fin 4)).trans (mapping.stateReads (2 : Fin 5))
    · simpa using (iota_preserved h flags.1 (2 : Fin 4)).trans (mapping.stateReads (3 : Fin 5))
    · simpa using (iota_preserved h flags.1 (3 : Fin 4)).trans (mapping.stateReads (4 : Fin 5))
  refine ⟨changed, ?_⟩
  rw [reference_parity]
  have c0 := changed (0 : Fin 5); have c1 := changed (1 : Fin 5)
  have c2 := changed (2 : Fin 5); have c3 := changed (3 : Fin 5); have c4 := changed (4 : Fin 5)
  change writeLane w 0 = (iotaState state round)[5 * column.val] at c0
  change writeLane w 1 = (iotaState state round)[5 * column.val + 1] at c1
  change writeLane w 2 = (iotaState state round)[5 * column.val + 2] at c2
  change writeLane w 3 = (iotaState state round)[5 * column.val + 3] at c3
  change writeLane w 4 = (iotaState state round)[5 * column.val + 4] at c4
  rw [← c0, ← c1, ← c2, ← c3, ← c4]
  have p1 : writeLane w 1 = readLane w 1 := iota_preserved h flags.1 (0 : Fin 4)
  have p2 : writeLane w 2 = readLane w 2 := iota_preserved h flags.1 (1 : Fin 4)
  have p3 : writeLane w 3 = readLane w 3 := iota_preserved h flags.1 (2 : Fin 4)
  have p4 : writeLane w 4 = readLane w 4 := iota_preserved h flags.1 (3 : Fin 4)
  rw [p1, p2, p3, p4]
  change laneValue w 57 = _
  change laneValue w 57 = packed w (temporary 98) ^^^ laneValue w 47 at op4
  rw [op4]
  change packed w (temporary 98) = packed w (temporary 94) ^^^ laneValue w 39 at op3
  rw [op3]
  change packed w (temporary 94) = packed w (temporary 90) ^^^ laneValue w 31 at op2
  rw [op2]
  change packed w (temporary 90) = laneValue w 17 ^^^ laneValue w 23 at op1
  rw [op1]
  rfl

end Airbender.Keccak.Proofs
