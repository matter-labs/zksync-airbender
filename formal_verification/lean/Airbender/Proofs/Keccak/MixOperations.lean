import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Circuits.Keccak.Mix
import Airbender.Proofs.Keccak.DecodeControl
import Airbender.Proofs.Keccak.FixedLookups
import Airbender.Proofs.Arithmetic.ByteAssembly

namespace Airbender.Keccak.Proofs.Mix
open Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

def nativeLimbs (start : Nat) : Vector Nat 4 := #v[start, start + 1, start + 4, start + 5]
def temporary (start : Nat) : Vector Nat 4 := #v[start, start + 1, start + 2, start + 3]
def mixMode (second : Bool) : Fin 7 := if second then 2 else 1
def aColumns (second : Bool) : Vector (Vector Nat 4) 5 :=
  if second then #v[nativeLimbs 23, nativeLimbs 47, nativeLimbs 39, nativeLimbs 23, nativeLimbs 39]
  else #v[nativeLimbs 15, nativeLimbs 31, nativeLimbs 15, nativeLimbs 47, nativeLimbs 31]
def bColumns (second : Bool) : Vector (Vector Nat 4) 5 :=
  if second then #v[temporary 90, temporary 90, temporary 94, temporary 94, nativeLimbs 55]
  else #v[nativeLimbs 57, temporary 90, temporary 90, temporary 94, temporary 94]
def cColumns (second : Bool) : Vector (Vector Nat 4) 5 :=
  if second then #v[temporary 90, nativeLimbs 49, temporary 94, nativeLimbs 25, nativeLimbs 41]
  else #v[nativeLimbs 57, temporary 90, nativeLimbs 17, temporary 94, nativeLimbs 33]
def isRotation (second : Bool) (operation : Fin 5) : Bool :=
  if second then operation.val = 0 || operation.val = 2
  else operation.val = 0 || operation.val = 1 || operation.val = 3
def previous (i : Fin 4) : Fin 4 := ⟨(i.val + 3) % 4, by omega⟩
def packed {p : Nat} (w : Nat → ZMod p) (columns : Vector Nat 4) : Nat :=
  (w columns[0]).val + 65536 * ((w columns[1]).val +
    65536 * ((w columns[2]).val + 65536 * (w columns[3]).val))

theorem mix_routes {p : Nat} [Fact p.Prime] (hp : FieldCapacity.NoWrap p 7)
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p} (second : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (active : w 0 = 1) (selected : w Variables.modeColumns[mixMode second] = 1)
    (operation : Fin 5) (limb : Fin 4) :
    if isRotation second operation then
      w (102 + 24 * operation.val + limb.val) = w (aColumns second)[operation][limb] + 65536 ∧
      w (118 + 24 * operation.val + limb.val) +
        w (110 + 24 * operation.val + (previous limb).val) = w (cColumns second)[operation][limb]
    else
      w (102 + 24 * operation.val + 2 * limb.val) +
        256 * w (103 + 24 * operation.val + 2 * limb.val) = w (aColumns second)[operation][limb] ∧
      w (110 + 24 * operation.val + 2 * limb.val) +
        256 * w (111 + 24 * operation.val + 2 * limb.val) = w (bColumns second)[operation][limb] ∧
      w (118 + 24 * operation.val + 2 * limb.val) +
        256 * w (119 + 24 * operation.val + 2 * limb.val) = w (cColumns second)[operation][limb] := by
  have modes := selected_modes hp h active (mixMode second) selected
  have m0 := modes (0 : Fin 7); have m1 := modes (1 : Fin 7)
  have m2 := modes (2 : Fin 7); have m3 := modes (3 : Fin 7)
  have m4 := modes (4 : Fin 7); have m5 := modes (5 : Fin 7); have m6 := modes (6 : Fin 7)
  have rho : w 67 = 0 := by
    cases second <;> simpa [Variables.modeColumns, mixMode] using m4
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
    simp [Variables.modeColumns, mixMode] at m0 m1 m2 m3 m4 m5 m6
  all_goals simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, m0, m1, m2, m3, m4, m5, m6,
    r0, r1, r2, r3, r4, aColumns, bColumns, cColumns, nativeLimbs, temporary, isRotation, previous] at a b c ⊢
  all_goals first
    | exact ⟨by linear_combination a, by linear_combination c⟩
    | exact ⟨by linear_combination a, by linear_combination b, by linear_combination c⟩


theorem mix_xor_bytes {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 1048576)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p} (second : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control)))
    (active : w 0 = 1) (selected : w Variables.modeColumns[mixMode second] = 1)
    (operation : Fin 5) (xor : isRotation second operation = false) (byte : Fin 8) :
    (w (102 + 24 * operation.val + byte.val)).val < 256 ∧
    (w (110 + 24 * operation.val + byte.val)).val < 256 ∧
    (w (118 + 24 * operation.val + byte.val)).val < 256 ∧
    (w (118 + 24 * operation.val + byte.val)).val =
      (w (102 + 24 * operation.val + byte.val)).val ^^^
        (w (110 + 24 * operation.val + byte.val)).val := by
  have query := byte_lookup_checks hp h ⟨8 * operation.val + byte.val, by omega⟩
  have tags := selected_tags (by omega) h active (mixMode second) selected
    ⟨8 * operation.val + byte.val, by omega⟩
  cases second <;> fin_cases operation <;> simp [isRotation] at xor
  all_goals fin_cases byte <;>
    simp [mixMode, operationTags, byteTag, byteQuery, importedConstraints,
      FlatOperation.lookups, Expression.eval, Verification.environment,
      ByteOperationFacts] at tags query ⊢
  all_goals
    split at query
    · rename_i zero
      have value := congrArg ZMod.val zero
      simp only [ZMod.val_zero] at value
      omega
    · simpa [tags] using query

theorem mix_xor_limb {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 1048576)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p} (second : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control)))
    (active : w 0 = 1) (selected : w Variables.modeColumns[mixMode second] = 1)
    (operation : Fin 5) (xor : isRotation second operation = false) (limb : Fin 4) :
    (w (aColumns second)[operation][limb]).val < 65536 ∧
    (w (bColumns second)[operation][limb]).val < 65536 ∧
    (w (cColumns second)[operation][limb]).val < 65536 ∧
    (w (cColumns second)[operation][limb]).val =
      (w (aColumns second)[operation][limb]).val ^^^
        (w (bColumns second)[operation][limb]).val := by
  have low := mix_xor_bytes hp second h active selected operation xor ⟨2 * limb.val, by omega⟩
  have high := mix_xor_bytes hp second h active selected operation xor ⟨2 * limb.val + 1, by omega⟩
  have routes := mix_routes (by omega) second h active selected operation limb
  simp only [xor, Bool.false_eq_true, if_false] at routes
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
  have value := xor_of_chunks (width := 8) low.1 low.2.1
    (a₁ := (w (102 + 24 * operation.val + (2 * limb.val + 1))).val)
    (b₁ := (w (110 + 24 * operation.val + (2 * limb.val + 1))).val)
  norm_num only [Nat.reducePow] at value
  exact value.symm

theorem mix_xor_operation {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 1048576)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p} (second : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control)))
    (active : w 0 = 1) (selected : w Variables.modeColumns[mixMode second] = 1)
    (operation : Fin 5) (xor : isRotation second operation = false) :
    packed w (cColumns second)[operation] =
      packed w (aColumns second)[operation] ^^^ packed w (bColumns second)[operation] := by
  have l0 := mix_xor_limb hp second h active selected operation xor (0 : Fin 4)
  have l1 := mix_xor_limb hp second h active selected operation xor (1 : Fin 4)
  have l2 := mix_xor_limb hp second h active selected operation xor (2 : Fin 4)
  have l3 := mix_xor_limb hp second h active selected operation xor (3 : Fin 4)
  simp [packed] at l0 l1 l2 l3 ⊢
  rw [l0.2.2.2, l1.2.2.2, l2.2.2.2, l3.2.2.2]
  have value := xor_of_four_chunks (width := 16) l0.1 l1.1 l2.1 l0.2.1 l1.2.1 l2.2.1
    (a₃ := (w (aColumns second)[operation][3]).val)
    (b₃ := (w (bColumns second)[operation][3]).val)
  norm_num only [Nat.reducePow] at value
  exact value.symm

end Airbender.Keccak.Proofs.Mix
