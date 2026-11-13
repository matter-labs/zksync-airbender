module
public import Proven.Keccak.Tags
public import Proven.Eval
public import Human.Circuits.Keccak.Theta
public import Proven.CleanCore.Circuit.Operations
public import Proven.Defs.Circuits.Keccak.Artifact

@[expose] public section

/-! The operand routes of the byte operations, proven once for every operation and limb (lean-strategies
§2.1). Constraints `20 + 13 * operation + 3 * limb + k` (`k` = 0, 1, 2) route the operation's input pair, second
input pair and output pair; outside the rotating modes (1, 2, 4) each is a sum over modes 0, 3, 5, 6 of the
mode flag times one source column (`routeA`, `routeB`, `routeC`). The copy constraints (`copyExpr`) state
`(w read - w write) * w mode = 0`. -/

namespace Airbender.Keccak.Proofs
open Arithmetic
set_option warningAsError true

def routeNative (start : Nat) : Vector Nat 4 := #v[start, start + 1, start + 4, start + 5]
def routeScratch (start : Nat) : Vector Nat 4 := #v[start, start + 1, start + 2, start + 3]

/-- Theta's routes (mode 3): lane `operation` of the read column, and the scratch lane. Also the filler
    for the rotating modes 1, 2, 4, whose routes these tables do not describe. -/
def thetaRouteA : Vector (Vector Nat 4) 5 :=
  #v[routeNative 15, routeNative 23, routeNative 31, routeNative 39, routeNative 47]
def thetaRouteB : Vector (Vector Nat 4) 5 :=
  #v[routeNative 55, routeNative 55, routeNative 55, routeNative 55, routeNative 55]
def thetaRouteC : Vector (Vector Nat 4) 5 :=
  #v[routeNative 17, routeNative 25, routeNative 33, routeNative 41, routeNative 49]

/-- First input of each operation, by mode (Iota 0, Theta 3, Chi 5 and 6). -/
def routeA : Vector (Vector (Vector Nat 4) 5) 7 := #v[
  #v[routeNative 15, routeNative 17, routeScratch 90, routeScratch 94, routeScratch 98],
  thetaRouteA, thetaRouteA, thetaRouteA, thetaRouteA,
  #v[routeNative 15, routeNative 23, routeNative 15, routeNative 31, routeNative 23],
  #v[routeNative 31, routeNative 23, routeNative 15, routeNative 31, routeNative 15]]

/-- Second input of each operation, by mode. -/
def routeB : Vector (Vector (Vector Nat 4) 5) 7 := #v[
  #v[routeScratch 86, routeNative 23, routeNative 31, routeNative 39, routeNative 47],
  thetaRouteB, thetaRouteB, thetaRouteB, thetaRouteB,
  #v[routeNative 23, routeNative 31, routeScratch 90, routeNative 39, routeScratch 94],
  #v[routeNative 15, routeScratch 90, routeNative 47, routeScratch 94, routeNative 39]]

/-- Output of each operation, by mode. -/
def routeC : Vector (Vector (Vector Nat 4) 5) 7 := #v[
  #v[routeNative 17, routeScratch 90, routeScratch 94, routeScratch 98, routeNative 57],
  thetaRouteC, thetaRouteC, thetaRouteC, thetaRouteC,
  #v[routeNative 49, routeScratch 90, routeNative 17, routeScratch 94, routeNative 25],
  #v[routeScratch 90, routeNative 25, routeScratch 94, routeNative 33, routeNative 17]]

/-- One entry of a route table. -/
def routeAt (table : Vector (Vector (Vector Nat 4) 5) 7) (mode : Fin 7) (operation : Fin 5) (limb : Fin 4) :
    Nat :=
  table[mode][operation][limb]

/-- Without the Rho mode, the five rotation flags are zero. -/
theorem rotation_flags_zero {p : Nat} [Fact p.Prime]
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (rho : w 67 = 0) (i : Fin 5) : w (80 + i.val) = 0 := by
  have equation := Verification.assertion_of_holds h ⟨9 + i.val, by rw [constraint_count]; omega⟩
  fin_cases i
  all_goals op_index at equation
  all_goals eval_entry [rho, Nat.cast_ofNat, zero_mul, Int.cast_negSucc, Nat.cast_zero, neg_zero,
    Nat.reduceAdd, one_mul, neg_mul, neg_eq_zero] at equation ⊢
  all_goals exact equation

/-- The routes of operation `operation`, limb `limb`, as sums over the non-rotating modes. -/
theorem xor_route_sums {p : Nat} [Fact p.Prime]
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (z64 : w 64 = 0) (z65 : w 65 = 0) (z67 : w 67 = 0) (operation : Fin 5) (limb : Fin 4) :
    w (102 + 24 * operation.val + 2 * limb.val) + 256 * w (103 + 24 * operation.val + 2 * limb.val) =
      w (routeAt routeA 0 operation limb) * w 63 + w (routeAt routeA 3 operation limb) * w 66 +
      w (routeAt routeA 5 operation limb) * w 68 + w (routeAt routeA 6 operation limb) * w 69 ∧
    w (110 + 24 * operation.val + 2 * limb.val) + 256 * w (111 + 24 * operation.val + 2 * limb.val) =
      w (routeAt routeB 0 operation limb) * w 63 + w (routeAt routeB 3 operation limb) * w 66 +
      w (routeAt routeB 5 operation limb) * w 68 + w (routeAt routeB 6 operation limb) * w 69 ∧
    w (118 + 24 * operation.val + 2 * limb.val) + 256 * w (119 + 24 * operation.val + 2 * limb.val) =
      w (routeAt routeC 0 operation limb) * w 63 + w (routeAt routeC 3 operation limb) * w 66 +
      w (routeAt routeC 5 operation limb) * w 68 + w (routeAt routeC 6 operation limb) * w 69 := by
  have r0 : w 80 = 0 := rotation_flags_zero h z67 0
  have r1 : w 81 = 0 := rotation_flags_zero h z67 1
  have r2 : w 82 = 0 := rotation_flags_zero h z67 2
  have r3 : w 83 = 0 := rotation_flags_zero h z67 3
  have r4 : w 84 = 0 := rotation_flags_zero h z67 4
  have a := Verification.assertion_of_holds h
    ⟨20 + 13 * operation.val + 3 * limb.val, by rw [constraint_count]; omega⟩
  have b := Verification.assertion_of_holds h
    ⟨21 + 13 * operation.val + 3 * limb.val, by rw [constraint_count]; omega⟩
  have c := Verification.assertion_of_holds h
    ⟨22 + 13 * operation.val + 3 * limb.val, by rw [constraint_count]; omega⟩
  fin_cases operation <;> fin_cases limb
  all_goals op_index at a b c
  all_goals simp only [Expression.eval, Verification.environment, Int.ofNat_eq_natCast, Nat.cast_ofNat,
    Nat.cast_one, Nat.cast_zero, Int.cast_negSucc, Int.cast_one, Int.cast_ofNat, Int.cast_zero,
    z64, z65, z67, r0, r1, r2, r3, r4] at a b c
  -- `ring1!` compares atoms up to unfolding, so `w (routeAt routeA 0 ⟨1, _⟩ ⟨2, _⟩)` is `w 18`.
  all_goals exact ⟨by linear_combination (norm := ring1!) a, by linear_combination (norm := ring1!) b,
    by linear_combination (norm := ring1!) c⟩

/-- With a non-rotating mode selected, each route is that mode's source column. -/
theorem xor_routes {p : Nat} [Fact p.Prime] (hp : 7 < p)
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (active : w 0 = 1) (mode : Fin 7) (still : mode = 0 ∨ mode = 3 ∨ mode = 5 ∨ mode = 6)
    (selected : w Variables.modeColumns[mode] = 1) (operation : Fin 5) (limb : Fin 4) :
    w (102 + 24 * operation.val + 2 * limb.val) + 256 * w (103 + 24 * operation.val + 2 * limb.val) =
      w routeA[mode][operation][limb] ∧
    w (110 + 24 * operation.val + 2 * limb.val) + 256 * w (111 + 24 * operation.val + 2 * limb.val) =
      w routeB[mode][operation][limb] ∧
    w (118 + 24 * operation.val + 2 * limb.val) + 256 * w (119 + 24 * operation.val + 2 * limb.val) =
      w routeC[mode][operation][limb] := by
  have modes := selected_modes hp h active mode selected
  have z64 : w 64 = 0 := by rcases still with rfl | rfl | rfl | rfl <;> exact modes 1
  have z65 : w 65 = 0 := by rcases still with rfl | rfl | rfl | rfl <;> exact modes 2
  have z67 : w 67 = 0 := by rcases still with rfl | rfl | rfl | rfl <;> exact modes 4
  have sums := xor_route_sums h z64 z65 z67 operation limb
  rcases still with rfl | rfl | rfl | rfl
  · rw [show w 63 = 1 from modes 0, show w 66 = 0 from modes 3, show w 68 = 0 from modes 5,
      show w 69 = 0 from modes 6] at sums
    simpa only [routeAt, mul_zero, mul_one, zero_add, add_zero] using sums
  · rw [show w 63 = 0 from modes 0, show w 66 = 1 from modes 3, show w 68 = 0 from modes 5,
      show w 69 = 0 from modes 6] at sums
    simpa only [routeAt, mul_zero, mul_one, zero_add, add_zero] using sums
  · rw [show w 63 = 0 from modes 0, show w 66 = 0 from modes 3, show w 68 = 1 from modes 5,
      show w 69 = 0 from modes 6] at sums
    simpa only [routeAt, mul_zero, mul_one, zero_add, add_zero] using sums
  · rw [show w 63 = 0 from modes 0, show w 66 = 0 from modes 3, show w 68 = 0 from modes 5,
      show w 69 = 1 from modes 6] at sums
    simpa only [routeAt, mul_zero, mul_one, zero_add, add_zero] using sums

/-- A copy constraint: `(w read - w write) * w mode = 0`. -/
def copyExpr {p : Nat} (read write mode : Nat) : Expression (ZMod p) :=
  ((Expression.const ((Int.ofNat 1 : Int) : ZMod p)).mul
    (((Expression.const ((Int.ofNat 0 : Int) : ZMod p)).add (Expression.var { index := read })).add
      (((Expression.const ((Int.ofNat 1 : Int) : ZMod p)).mul
        (Expression.const ((Int.negSucc 0 : Int) : ZMod p))).mul (Expression.var { index := write })))).mul
    (Expression.var { index := mode })

/-- A copy constraint with its mode selected equates the two columns. -/
theorem copy_of_holds {p : Nat} [Fact p.Prime]
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    {read write mode : Nat} (k : Fin (FlatOperation.constraints (importedConstraints setup)).length)
    (shape : (FlatOperation.constraints (importedConstraints setup)).get k = copyExpr read write mode)
    (selected : w mode = 1) : w read = w write := by
  have equation := Verification.assertion_of_holds h k
  rw [shape] at equation
  simp only [copyExpr, Expression.eval, Verification.environment, selected, Int.ofNat_eq_natCast,
    Nat.cast_one, Int.cast_one, Int.cast_zero, Int.cast_negSucc, Nat.cast_zero, zero_add,
    one_mul, mul_one, neg_mul] at equation
  linear_combination equation

/-- A lane whose four limbs equal another lane's limbs has its value. -/
theorem lane_copy_of_limbs {p : Nat} {w : Nat → ZMod p} {read write : Nat}
    (limbs : ∀ limb : Fin 4, w (read + (#v[0, 1, 4, 5] : Vector Nat 4)[limb]) =
      w (write + (#v[0, 1, 4, 5] : Vector Nat 4)[limb])) :
    laneValue w write = laneValue w read := by
  have l0 : w read = w write := limbs 0
  have l1 : w (read + 1) = w (write + 1) := limbs 1
  have l2 : w (read + 4) = w (write + 4) := limbs 2
  have l3 : w (read + 5) = w (write + 5) := limbs 3
  simp only [laneValue, l0, l1, l2, l3]

end Airbender.Keccak.Proofs
