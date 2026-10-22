import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.Blake2Round.NativeFinalQueryBase

namespace Airbender.Blake2Round.Proofs
open Arithmetic Blake2G.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

/-- The native b/d queries expose the width change as an expression. No
    separately allocated split witness or extra constraint is required. -/
theorem native_bd_queries_0 {p : Nat} [Fact p.Prime]
    (compatible : SerializedInverse.Scale64 p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    chunkXor 9 (bdLowB w (0 : Fin 8)) (bdTemp w (0 : Fin 8) 0) (bdTemp w (0 : Fin 8) 1) ∧
    chunkXor 7 (bdHighB w (0 : Fin 8))
      ((-3932160 : ZMod p) * (bdInitial w (0 : Fin 8) - bdTemp w (0 : Fin 8) 0)) (bdTemp w (0 : Fin 8) 2) ∧
    chunkXor 8 (bdLowD w (0 : Fin 8)) (bdTemp w (0 : Fin 8) 1 - 256 * bdTemp w (0 : Fin 8) 3) (bdTemp w (0 : Fin 8) 4) ∧
    chunkXor 8 (bdHighD w (0 : Fin 8)) (2 * bdTemp w (0 : Fin 8) 2 + bdTemp w (0 : Fin 8) 3) (bdTemp w (0 : Fin 8) 5) := by
  have field := serialized_field compatible
  subst p
  unfold babyBearModulus at *
  have tag (stage : Fin 4) : finalColumn w (bdIndex (0 : Fin 8)) stage 5 =
      (if stage.val = 0 then 20 else if stage.val = 1 then 19 else 4 : ZMod 2013265921) := by
    fin_cases stage <;> simp [finalColumn,
      NativeFinalLayout.queryColumn, NativeFinalLayout.query, NativeFinalLayout.queryIndex,
      bdIndex, importedConstraints, FlatOperation.lookups, Expression.eval, Verification.environment]
  have q0 := final_query (by decide) (bdIndex (0 : Fin 8)) 0 2 h (tag 0)
  have q1 := final_query (by decide) (bdIndex (0 : Fin 8)) 1 1 h (tag 1)
  have q2 := final_query (by decide) (bdIndex (0 : Fin 8)) 2 0 h (tag 2)
  have q3 := final_query (by decide) (bdIndex (0 : Fin 8)) 3 0 h (tag 3)
  have initialHigh : finalColumn w (bdIndex (0 : Fin 8)) 1 1 =
      (-3932160 : ZMod 2013265921) * (bdInitial w (0 : Fin 8) - bdTemp w (0 : Fin 8) 0) := by
    all_goals simp [finalColumn, NativeFinalLayout.queryColumn, NativeFinalLayout.query,
      NativeFinalLayout.queryIndex, importedConstraints, FlatOperation.lookups,
      Expression.eval, Verification.environment, bdInitial, NativeFinalLayout.initial,
      bdTemp, bdIndex, NativeFinalLayout.temporary]
    all_goals ring
  rw [initialHigh] at q1
  all_goals simp [finalColumn, NativeFinalLayout.queryColumn, NativeFinalLayout.query,
    NativeFinalLayout.queryIndex, importedConstraints, FlatOperation.lookups,
    Expression.eval, Verification.environment, bdTemp, bdIndex, NativeFinalLayout.temporary,
    bdLowB, NativeFinalLayout.lowB, bdHighB, bdB, NativeFinalLayout.firstInput,
    bdLowD, NativeFinalLayout.lowD, bdHighD, bdD, NativeFinalLayout.secondInput,
    diagonalFrame, NativeLayout.diagonal, NativeLayout.Layout.read, NativeLayout.Location.read]
    at q0 q1 q2 q3 ⊢
  all_goals
    refine ⟨q0, ?_, ?_, ?_⟩
    · convert q1 using 1
      all_goals ring
    · convert q2 using 1
      all_goals ring
    · convert q3 using 1
      all_goals ring


/-- The native b/d queries expose the width change as an expression. No
    separately allocated split witness or extra constraint is required. -/
theorem native_bd_queries_1 {p : Nat} [Fact p.Prime]
    (compatible : SerializedInverse.Scale64 p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    chunkXor 9 (bdLowB w (1 : Fin 8)) (bdTemp w (1 : Fin 8) 0) (bdTemp w (1 : Fin 8) 1) ∧
    chunkXor 7 (bdHighB w (1 : Fin 8))
      ((-3932160 : ZMod p) * (bdInitial w (1 : Fin 8) - bdTemp w (1 : Fin 8) 0)) (bdTemp w (1 : Fin 8) 2) ∧
    chunkXor 8 (bdLowD w (1 : Fin 8)) (bdTemp w (1 : Fin 8) 1 - 256 * bdTemp w (1 : Fin 8) 3) (bdTemp w (1 : Fin 8) 4) ∧
    chunkXor 8 (bdHighD w (1 : Fin 8)) (2 * bdTemp w (1 : Fin 8) 2 + bdTemp w (1 : Fin 8) 3) (bdTemp w (1 : Fin 8) 5) := by
  have field := serialized_field compatible
  subst p
  unfold babyBearModulus at *
  have tag (stage : Fin 4) : finalColumn w (bdIndex (1 : Fin 8)) stage 5 =
      (if stage.val = 0 then 20 else if stage.val = 1 then 19 else 4 : ZMod 2013265921) := by
    fin_cases stage <;> simp [finalColumn,
      NativeFinalLayout.queryColumn, NativeFinalLayout.query, NativeFinalLayout.queryIndex,
      bdIndex, importedConstraints, FlatOperation.lookups, Expression.eval, Verification.environment]
  have q0 := final_query (by decide) (bdIndex (1 : Fin 8)) 0 2 h (tag 0)
  have q1 := final_query (by decide) (bdIndex (1 : Fin 8)) 1 1 h (tag 1)
  have q2 := final_query (by decide) (bdIndex (1 : Fin 8)) 2 0 h (tag 2)
  have q3 := final_query (by decide) (bdIndex (1 : Fin 8)) 3 0 h (tag 3)
  have initialHigh : finalColumn w (bdIndex (1 : Fin 8)) 1 1 =
      (-3932160 : ZMod 2013265921) * (bdInitial w (1 : Fin 8) - bdTemp w (1 : Fin 8) 0) := by
    all_goals simp [finalColumn, NativeFinalLayout.queryColumn, NativeFinalLayout.query,
      NativeFinalLayout.queryIndex, importedConstraints, FlatOperation.lookups,
      Expression.eval, Verification.environment, bdInitial, NativeFinalLayout.initial,
      bdTemp, bdIndex, NativeFinalLayout.temporary]
    all_goals ring
  rw [initialHigh] at q1
  all_goals simp [finalColumn, NativeFinalLayout.queryColumn, NativeFinalLayout.query,
    NativeFinalLayout.queryIndex, importedConstraints, FlatOperation.lookups,
    Expression.eval, Verification.environment, bdTemp, bdIndex, NativeFinalLayout.temporary,
    bdLowB, NativeFinalLayout.lowB, bdHighB, bdB, NativeFinalLayout.firstInput,
    bdLowD, NativeFinalLayout.lowD, bdHighD, bdD, NativeFinalLayout.secondInput,
    diagonalFrame, NativeLayout.diagonal, NativeLayout.Layout.read, NativeLayout.Location.read]
    at q0 q1 q2 q3 ⊢
  all_goals
    refine ⟨q0, ?_, ?_, ?_⟩
    · convert q1 using 1
      all_goals ring
    · convert q2 using 1
      all_goals ring
    · convert q3 using 1
      all_goals ring


/-- The native b/d queries expose the width change as an expression. No
    separately allocated split witness or extra constraint is required. -/
theorem native_bd_queries_2 {p : Nat} [Fact p.Prime]
    (compatible : SerializedInverse.Scale64 p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    chunkXor 9 (bdLowB w (2 : Fin 8)) (bdTemp w (2 : Fin 8) 0) (bdTemp w (2 : Fin 8) 1) ∧
    chunkXor 7 (bdHighB w (2 : Fin 8))
      ((-3932160 : ZMod p) * (bdInitial w (2 : Fin 8) - bdTemp w (2 : Fin 8) 0)) (bdTemp w (2 : Fin 8) 2) ∧
    chunkXor 8 (bdLowD w (2 : Fin 8)) (bdTemp w (2 : Fin 8) 1 - 256 * bdTemp w (2 : Fin 8) 3) (bdTemp w (2 : Fin 8) 4) ∧
    chunkXor 8 (bdHighD w (2 : Fin 8)) (2 * bdTemp w (2 : Fin 8) 2 + bdTemp w (2 : Fin 8) 3) (bdTemp w (2 : Fin 8) 5) := by
  have field := serialized_field compatible
  subst p
  unfold babyBearModulus at *
  have tag (stage : Fin 4) : finalColumn w (bdIndex (2 : Fin 8)) stage 5 =
      (if stage.val = 0 then 20 else if stage.val = 1 then 19 else 4 : ZMod 2013265921) := by
    fin_cases stage <;> simp [finalColumn,
      NativeFinalLayout.queryColumn, NativeFinalLayout.query, NativeFinalLayout.queryIndex,
      bdIndex, importedConstraints, FlatOperation.lookups, Expression.eval, Verification.environment]
  have q0 := final_query (by decide) (bdIndex (2 : Fin 8)) 0 2 h (tag 0)
  have q1 := final_query (by decide) (bdIndex (2 : Fin 8)) 1 1 h (tag 1)
  have q2 := final_query (by decide) (bdIndex (2 : Fin 8)) 2 0 h (tag 2)
  have q3 := final_query (by decide) (bdIndex (2 : Fin 8)) 3 0 h (tag 3)
  have initialHigh : finalColumn w (bdIndex (2 : Fin 8)) 1 1 =
      (-3932160 : ZMod 2013265921) * (bdInitial w (2 : Fin 8) - bdTemp w (2 : Fin 8) 0) := by
    all_goals simp [finalColumn, NativeFinalLayout.queryColumn, NativeFinalLayout.query,
      NativeFinalLayout.queryIndex, importedConstraints, FlatOperation.lookups,
      Expression.eval, Verification.environment, bdInitial, NativeFinalLayout.initial,
      bdTemp, bdIndex, NativeFinalLayout.temporary]
    all_goals ring
  rw [initialHigh] at q1
  all_goals simp [finalColumn, NativeFinalLayout.queryColumn, NativeFinalLayout.query,
    NativeFinalLayout.queryIndex, importedConstraints, FlatOperation.lookups,
    Expression.eval, Verification.environment, bdTemp, bdIndex, NativeFinalLayout.temporary,
    bdLowB, NativeFinalLayout.lowB, bdHighB, bdB, NativeFinalLayout.firstInput,
    bdLowD, NativeFinalLayout.lowD, bdHighD, bdD, NativeFinalLayout.secondInput,
    diagonalFrame, NativeLayout.diagonal, NativeLayout.Layout.read, NativeLayout.Location.read]
    at q0 q1 q2 q3 ⊢
  all_goals
    refine ⟨q0, ?_, ?_, ?_⟩
    · convert q1 using 1
      all_goals ring
    · convert q2 using 1
      all_goals ring
    · convert q3 using 1
      all_goals ring


/-- The native b/d queries expose the width change as an expression. No
    separately allocated split witness or extra constraint is required. -/
theorem native_bd_queries_3 {p : Nat} [Fact p.Prime]
    (compatible : SerializedInverse.Scale64 p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    chunkXor 9 (bdLowB w (3 : Fin 8)) (bdTemp w (3 : Fin 8) 0) (bdTemp w (3 : Fin 8) 1) ∧
    chunkXor 7 (bdHighB w (3 : Fin 8))
      ((-3932160 : ZMod p) * (bdInitial w (3 : Fin 8) - bdTemp w (3 : Fin 8) 0)) (bdTemp w (3 : Fin 8) 2) ∧
    chunkXor 8 (bdLowD w (3 : Fin 8)) (bdTemp w (3 : Fin 8) 1 - 256 * bdTemp w (3 : Fin 8) 3) (bdTemp w (3 : Fin 8) 4) ∧
    chunkXor 8 (bdHighD w (3 : Fin 8)) (2 * bdTemp w (3 : Fin 8) 2 + bdTemp w (3 : Fin 8) 3) (bdTemp w (3 : Fin 8) 5) := by
  have field := serialized_field compatible
  subst p
  unfold babyBearModulus at *
  have tag (stage : Fin 4) : finalColumn w (bdIndex (3 : Fin 8)) stage 5 =
      (if stage.val = 0 then 20 else if stage.val = 1 then 19 else 4 : ZMod 2013265921) := by
    fin_cases stage <;> simp [finalColumn,
      NativeFinalLayout.queryColumn, NativeFinalLayout.query, NativeFinalLayout.queryIndex,
      bdIndex, importedConstraints, FlatOperation.lookups, Expression.eval, Verification.environment]
  have q0 := final_query (by decide) (bdIndex (3 : Fin 8)) 0 2 h (tag 0)
  have q1 := final_query (by decide) (bdIndex (3 : Fin 8)) 1 1 h (tag 1)
  have q2 := final_query (by decide) (bdIndex (3 : Fin 8)) 2 0 h (tag 2)
  have q3 := final_query (by decide) (bdIndex (3 : Fin 8)) 3 0 h (tag 3)
  have initialHigh : finalColumn w (bdIndex (3 : Fin 8)) 1 1 =
      (-3932160 : ZMod 2013265921) * (bdInitial w (3 : Fin 8) - bdTemp w (3 : Fin 8) 0) := by
    all_goals simp [finalColumn, NativeFinalLayout.queryColumn, NativeFinalLayout.query,
      NativeFinalLayout.queryIndex, importedConstraints, FlatOperation.lookups,
      Expression.eval, Verification.environment, bdInitial, NativeFinalLayout.initial,
      bdTemp, bdIndex, NativeFinalLayout.temporary]
    all_goals ring
  rw [initialHigh] at q1
  all_goals simp [finalColumn, NativeFinalLayout.queryColumn, NativeFinalLayout.query,
    NativeFinalLayout.queryIndex, importedConstraints, FlatOperation.lookups,
    Expression.eval, Verification.environment, bdTemp, bdIndex, NativeFinalLayout.temporary,
    bdLowB, NativeFinalLayout.lowB, bdHighB, bdB, NativeFinalLayout.firstInput,
    bdLowD, NativeFinalLayout.lowD, bdHighD, bdD, NativeFinalLayout.secondInput,
    diagonalFrame, NativeLayout.diagonal, NativeLayout.Layout.read, NativeLayout.Location.read]
    at q0 q1 q2 q3 ⊢
  all_goals
    refine ⟨q0, ?_, ?_, ?_⟩
    · convert q1 using 1
      all_goals ring
    · convert q2 using 1
      all_goals ring
    · convert q3 using 1
      all_goals ring


end Airbender.Blake2Round.Proofs
