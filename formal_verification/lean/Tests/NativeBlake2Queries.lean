import Airbender.Review.Circuits.Blake2Worker.QueriesTheorems

namespace Airbender.Tests.NativeBlake2Queries
open Verification Blake2Worker Blake2Worker.Native Blake2Worker.QueryArtifact
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem same_native_source : querySourceBytes = constraintsSourceBytes := QueryProofs.same_source

theorem complete_geometry :
    (queryScalars : Vector (Expression (ZMod mersenne31Modulus)) 2).toArray.size = 2 ∧
    (queryClocks0 : Vector (Expression (ZMod mersenne31Modulus)) 30).toArray.size = 30 ∧
    (queryClocks1 : Vector (Expression (ZMod mersenne31Modulus)) 56).toArray.size = 56 ∧
    (queryFixed0 : Vector (Vector (Expression (ZMod mersenne31Modulus)) 4) 8).toArray.size = 8 ∧
    (queryFixed1 : Vector (Vector (Expression (ZMod mersenne31Modulus)) 4) 64).toArray.size = 64 ∧
    (queryFixed2 : Vector (Vector (Expression (ZMod mersenne31Modulus)) 4) 64).toArray.size = 64 ∧
    (queryFixed3 : Vector (Vector (Expression (ZMod mersenne31Modulus)) 4) 64).toArray.size = 64 ∧
    (queryFixed4 : Vector (Vector (Expression (ZMod mersenne31Modulus)) 4) 8).toArray.size = 8 := by decide +kernel

/-- Static compiled-query counts, not worker issuance/accounting counts. -/
theorem tag_counts :
    ((List.finRange 208).filter (fun i => decide (fixedKind i = .byte))).length = 80 ∧
    ((List.finRange 208).filter (fun i => decide (fixedKind i = .three))).length = 16 ∧
    ((List.finRange 208).filter (fun i => decide (fixedKind i = .four))).length = 16 ∧
    ((List.finRange 208).filter (fun i => decide (fixedKind i = .seven))).length = 40 ∧
    ((List.finRange 208).filter (fun i => decide (fixedKind i = .nine))).length = 56 := by decide +kernel

theorem first_query (w : Nat → ZMod mersenne31Modulus) :
    fixedQuery w ⟨0,by decide⟩ = #v[w 274,w 272,w 275,4] := by
  simp [fixedQuery,fixedExpressions,queryFixed0,Vector.get,Expression.eval,environment]

theorem first_scaled_pointer (w : Nat → ZMod mersenne31Modulus) :
    (queryScalars[0]).eval (environment w) = 16777216 * w 2 := by
  simp [queryScalars,Expression.eval,environment]

theorem second_scaled_pointer (w : Nat → ZMod mersenne31Modulus) :
    (queryScalars[1]).eval (environment w) = 33554432 * w 100 := by
  simp [queryScalars,Expression.eval,environment]

theorem first_clock_difference (w : Nat → ZMod mersenne31Modulus) :
    (clockExpression ⟨0,by decide⟩).eval (environment w) = -w 740 + 524288*w 742 + w 743 := by
  simp [clockExpression,queryClocks0,Vector.get,Expression.eval,environment]

theorem first_clock_high_difference (w : Nat → ZMod mersenne31Modulus) :
    (clockExpression ⟨1,by decide⟩).eval (environment w) = 524288*w 0 - w 741 - w 742 + w 744 := by
  simp [clockExpression,queryClocks0,Vector.get,Expression.eval,environment]
  ring

theorem wrong_actual_xor {w : Nat → ZMod mersenne31Modulus} (slot : Fin 208)
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Fixed.table))
    (wrong : (fixedQuery w slot)[2].val ≠ (fixedQuery w slot)[0].val ^^^ (fixedQuery w slot)[1].val) : False := by
  exact wrong ((lookup_effects holds).results slot)

theorem oversized_first_query {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Fixed.table))
    (oversized : 256 ≤ (w 274).val) : False := by
  have bound := (lookup_effects holds).leftBounds ⟨0,by decide⟩
  rw [first_query] at bound
  change (w 274).val < 256 at bound
  omega

theorem rejects_unit_state_pointer {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Fixed.table))
    (pointer : w 2 = 1) : False := by
  have bound : ((queryScalars[0]).eval (environment w)).val < 65536 :=
    (lookup_effects holds).scalars ⟨0,by decide⟩
  rw [first_scaled_pointer,pointer,mul_one] at bound
  have canonical : (16777216 : ZMod mersenne31Modulus).val = 16777216 := by decide +kernel
  rw [canonical] at bound
  omega

/-- Positive actual scalar slices, not complete accepted worker witnesses. -/
theorem aligned_pointer_slices :
    ((16777216 : ZMod mersenne31Modulus)*128).val = 1 ∧
    ((33554432 : ZMod mersenne31Modulus)*64).val = 1 := by decide +kernel

private def coincidentTimes (column : Nat) : ZMod mersenne31Modulus :=
  if column = 740 ∨ column = 743 then 600000 else 0

/-- Actual difference expressions can be small with raw timestamps above19bits.
    This query-only slice does not satisfy or claim complete worker acceptance. -/
theorem difference_is_not_raw_time :
    (clockExpression ⟨0,by decide⟩).eval (environment coincidentTimes) = 0 ∧
    (clockExpression ⟨1,by decide⟩).eval (environment coincidentTimes) = 0 ∧
    (coincidentTimes 743).val = 600000 := by
  rw [first_clock_difference,first_clock_high_difference]
  simp only [coincidentTimes]
  decide +kernel

end Airbender.Tests.NativeBlake2Queries
