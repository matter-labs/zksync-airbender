import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.Blake2Round.NativeFinalQueryBase

namespace Airbender.Blake2Round.Proofs
open Arithmetic Blake2G.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

/-- Native query projections for the first half of finalization. -/
theorem native_ac_queries_0 {p : Nat} [Fact p.Prime]
    (compatible : SerializedInverse.Scale64 p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    chunkXor 7 (acTemp w (0 : Fin 8) 0) (acLowC w (0 : Fin 8)) (acTemp w (0 : Fin 8) 1) ∧
    chunkXor 9 ((-15728640 : ZMod p) * (acInitial w (0 : Fin 8) - acTemp w (0 : Fin 8) 0))
      ((-15728640 : ZMod p) * (acC w (0 : Fin 8) - acLowC w (0 : Fin 8))) (acTemp w (0 : Fin 8) 2) ∧
    chunkXor 7 (acTemp w (0 : Fin 8) 1) (acLowA w (0 : Fin 8)) (acTemp w (0 : Fin 8) 4) ∧
    chunkXor 9 (acTemp w (0 : Fin 8) 2)
      ((-15728640 : ZMod p) * (acA w (0 : Fin 8) - acLowA w (0 : Fin 8))) (acTemp w (0 : Fin 8) 5) := by
  have field := serialized_field compatible
  subst p
  unfold babyBearModulus at *
  have tag (stage : Fin 4) : finalColumn w ((0 : Fin 8).castLE (by decide)) stage 5 =
      (if stage.val % 2 = 0 then 19 else 20 : ZMod 2013265921) := by
    fin_cases stage <;> simp [finalColumn,
      NativeFinalLayout.queryColumn, NativeFinalLayout.query, NativeFinalLayout.queryIndex,
      importedConstraints, FlatOperation.lookups, Expression.eval, Verification.environment]
  have q0 := final_query (by decide) ((0 : Fin 8).castLE (by decide)) 0 1 h (tag 0)
  have q1 := final_query (by decide) ((0 : Fin 8).castLE (by decide)) 1 2 h (tag 1)
  have q2 := final_query (by decide) ((0 : Fin 8).castLE (by decide)) 2 1 h (tag 2)
  have q3 := final_query (by decide) ((0 : Fin 8).castLE (by decide)) 3 2 h (tag 3)
  have initialHigh : finalColumn w ((0 : Fin 8).castLE (by decide)) 1 0 =
      (-15728640 : ZMod 2013265921) * (acInitial w (0 : Fin 8) - acTemp w (0 : Fin 8) 0) := by
    all_goals simp [finalColumn, NativeFinalLayout.queryColumn, NativeFinalLayout.query,
      NativeFinalLayout.queryIndex, importedConstraints, FlatOperation.lookups,
      Expression.eval, Verification.environment, acInitial, NativeFinalLayout.initial,
      acTemp, NativeFinalLayout.temporary]
    all_goals ring
  have cHigh : finalColumn w ((0 : Fin 8).castLE (by decide)) 1 1 =
      (-15728640 : ZMod 2013265921) * (acC w (0 : Fin 8) - acLowC w (0 : Fin 8)) := by
    all_goals simp [finalColumn, NativeFinalLayout.queryColumn, NativeFinalLayout.query,
      NativeFinalLayout.queryIndex, importedConstraints, FlatOperation.lookups,
      Expression.eval, Verification.environment, acC, NativeFinalLayout.secondInput,
      acLowC, NativeFinalLayout.lowC, diagonalFrame, NativeLayout.diagonal,
      NativeLayout.Layout.read, NativeLayout.Location.read]
    all_goals ring
  have aHigh : finalColumn w ((0 : Fin 8).castLE (by decide)) 3 1 =
      (-15728640 : ZMod 2013265921) * (acA w (0 : Fin 8) - acLowA w (0 : Fin 8)) := by
    all_goals simp [finalColumn, NativeFinalLayout.queryColumn, NativeFinalLayout.query,
      NativeFinalLayout.queryIndex, importedConstraints, FlatOperation.lookups,
      Expression.eval, Verification.environment, acA, NativeFinalLayout.firstInput,
      acLowA, NativeFinalLayout.lowA, diagonalFrame, NativeLayout.diagonal,
      NativeLayout.Layout.read, NativeLayout.Location.read, NativeFinalLayout.temporary]

    all_goals ring_nf
    all_goals reduce_mod_char
    all_goals ring_nf
    all_goals reduce_mod_char
  rw [initialHigh, cHigh] at q1
  rw [aHigh] at q3
  all_goals simp [finalColumn, NativeFinalLayout.queryColumn, NativeFinalLayout.query,
    NativeFinalLayout.queryIndex, importedConstraints, FlatOperation.lookups,
    Expression.eval, Verification.environment, acTemp, NativeFinalLayout.temporary,
    acLowC, NativeFinalLayout.lowC, acLowA, NativeFinalLayout.lowA, diagonalFrame,
    NativeLayout.diagonal, NativeLayout.Layout.read, NativeLayout.Location.read] at q0 q1 q2 q3 ⊢
  all_goals
    refine ⟨q0, ?_, ?_, ?_⟩
    · exact q1
    · convert q2 using 1
      all_goals ring
    · exact q3


/-- Native query projections for the first half of finalization. -/
theorem native_ac_queries_1 {p : Nat} [Fact p.Prime]
    (compatible : SerializedInverse.Scale64 p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    chunkXor 7 (acTemp w (1 : Fin 8) 0) (acLowC w (1 : Fin 8)) (acTemp w (1 : Fin 8) 1) ∧
    chunkXor 9 ((-15728640 : ZMod p) * (acInitial w (1 : Fin 8) - acTemp w (1 : Fin 8) 0))
      ((-15728640 : ZMod p) * (acC w (1 : Fin 8) - acLowC w (1 : Fin 8))) (acTemp w (1 : Fin 8) 2) ∧
    chunkXor 7 (acTemp w (1 : Fin 8) 1) (acLowA w (1 : Fin 8)) (acTemp w (1 : Fin 8) 4) ∧
    chunkXor 9 (acTemp w (1 : Fin 8) 2)
      ((-15728640 : ZMod p) * (acA w (1 : Fin 8) - acLowA w (1 : Fin 8))) (acTemp w (1 : Fin 8) 5) := by
  have field := serialized_field compatible
  subst p
  unfold babyBearModulus at *
  have tag (stage : Fin 4) : finalColumn w ((1 : Fin 8).castLE (by decide)) stage 5 =
      (if stage.val % 2 = 0 then 19 else 20 : ZMod 2013265921) := by
    fin_cases stage <;> simp [finalColumn,
      NativeFinalLayout.queryColumn, NativeFinalLayout.query, NativeFinalLayout.queryIndex,
      importedConstraints, FlatOperation.lookups, Expression.eval, Verification.environment]
  have q0 := final_query (by decide) ((1 : Fin 8).castLE (by decide)) 0 1 h (tag 0)
  have q1 := final_query (by decide) ((1 : Fin 8).castLE (by decide)) 1 2 h (tag 1)
  have q2 := final_query (by decide) ((1 : Fin 8).castLE (by decide)) 2 1 h (tag 2)
  have q3 := final_query (by decide) ((1 : Fin 8).castLE (by decide)) 3 2 h (tag 3)
  have initialHigh : finalColumn w ((1 : Fin 8).castLE (by decide)) 1 0 =
      (-15728640 : ZMod 2013265921) * (acInitial w (1 : Fin 8) - acTemp w (1 : Fin 8) 0) := by
    all_goals simp [finalColumn, NativeFinalLayout.queryColumn, NativeFinalLayout.query,
      NativeFinalLayout.queryIndex, importedConstraints, FlatOperation.lookups,
      Expression.eval, Verification.environment, acInitial, NativeFinalLayout.initial,
      acTemp, NativeFinalLayout.temporary]
    all_goals ring
  have cHigh : finalColumn w ((1 : Fin 8).castLE (by decide)) 1 1 =
      (-15728640 : ZMod 2013265921) * (acC w (1 : Fin 8) - acLowC w (1 : Fin 8)) := by
    all_goals simp [finalColumn, NativeFinalLayout.queryColumn, NativeFinalLayout.query,
      NativeFinalLayout.queryIndex, importedConstraints, FlatOperation.lookups,
      Expression.eval, Verification.environment, acC, NativeFinalLayout.secondInput,
      acLowC, NativeFinalLayout.lowC, diagonalFrame, NativeLayout.diagonal,
      NativeLayout.Layout.read, NativeLayout.Location.read]
    all_goals ring
  have aHigh : finalColumn w ((1 : Fin 8).castLE (by decide)) 3 1 =
      (-15728640 : ZMod 2013265921) * (acA w (1 : Fin 8) - acLowA w (1 : Fin 8)) := by
    all_goals simp [finalColumn, NativeFinalLayout.queryColumn, NativeFinalLayout.query,
      NativeFinalLayout.queryIndex, importedConstraints, FlatOperation.lookups,
      Expression.eval, Verification.environment, acA, NativeFinalLayout.firstInput,
      acLowA, NativeFinalLayout.lowA, diagonalFrame, NativeLayout.diagonal,
      NativeLayout.Layout.read, NativeLayout.Location.read, NativeFinalLayout.temporary]

    all_goals ring_nf
    all_goals reduce_mod_char
    all_goals ring_nf
    all_goals reduce_mod_char
  rw [initialHigh, cHigh] at q1
  rw [aHigh] at q3
  all_goals simp [finalColumn, NativeFinalLayout.queryColumn, NativeFinalLayout.query,
    NativeFinalLayout.queryIndex, importedConstraints, FlatOperation.lookups,
    Expression.eval, Verification.environment, acTemp, NativeFinalLayout.temporary,
    acLowC, NativeFinalLayout.lowC, acLowA, NativeFinalLayout.lowA, diagonalFrame,
    NativeLayout.diagonal, NativeLayout.Layout.read, NativeLayout.Location.read] at q0 q1 q2 q3 ⊢
  all_goals
    refine ⟨q0, ?_, ?_, ?_⟩
    · exact q1
    · convert q2 using 1
      all_goals ring
    · exact q3


/-- Native query projections for the first half of finalization. -/
theorem native_ac_queries_2 {p : Nat} [Fact p.Prime]
    (compatible : SerializedInverse.Scale64 p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    chunkXor 7 (acTemp w (2 : Fin 8) 0) (acLowC w (2 : Fin 8)) (acTemp w (2 : Fin 8) 1) ∧
    chunkXor 9 ((-15728640 : ZMod p) * (acInitial w (2 : Fin 8) - acTemp w (2 : Fin 8) 0))
      ((-15728640 : ZMod p) * (acC w (2 : Fin 8) - acLowC w (2 : Fin 8))) (acTemp w (2 : Fin 8) 2) ∧
    chunkXor 7 (acTemp w (2 : Fin 8) 1) (acLowA w (2 : Fin 8)) (acTemp w (2 : Fin 8) 4) ∧
    chunkXor 9 (acTemp w (2 : Fin 8) 2)
      ((-15728640 : ZMod p) * (acA w (2 : Fin 8) - acLowA w (2 : Fin 8))) (acTemp w (2 : Fin 8) 5) := by
  have field := serialized_field compatible
  subst p
  unfold babyBearModulus at *
  have tag (stage : Fin 4) : finalColumn w ((2 : Fin 8).castLE (by decide)) stage 5 =
      (if stage.val % 2 = 0 then 19 else 20 : ZMod 2013265921) := by
    fin_cases stage <;> simp [finalColumn,
      NativeFinalLayout.queryColumn, NativeFinalLayout.query, NativeFinalLayout.queryIndex,
      importedConstraints, FlatOperation.lookups, Expression.eval, Verification.environment]
  have q0 := final_query (by decide) ((2 : Fin 8).castLE (by decide)) 0 1 h (tag 0)
  have q1 := final_query (by decide) ((2 : Fin 8).castLE (by decide)) 1 2 h (tag 1)
  have q2 := final_query (by decide) ((2 : Fin 8).castLE (by decide)) 2 1 h (tag 2)
  have q3 := final_query (by decide) ((2 : Fin 8).castLE (by decide)) 3 2 h (tag 3)
  have initialHigh : finalColumn w ((2 : Fin 8).castLE (by decide)) 1 0 =
      (-15728640 : ZMod 2013265921) * (acInitial w (2 : Fin 8) - acTemp w (2 : Fin 8) 0) := by
    all_goals simp [finalColumn, NativeFinalLayout.queryColumn, NativeFinalLayout.query,
      NativeFinalLayout.queryIndex, importedConstraints, FlatOperation.lookups,
      Expression.eval, Verification.environment, acInitial, NativeFinalLayout.initial,
      acTemp, NativeFinalLayout.temporary]
    all_goals ring
  have cHigh : finalColumn w ((2 : Fin 8).castLE (by decide)) 1 1 =
      (-15728640 : ZMod 2013265921) * (acC w (2 : Fin 8) - acLowC w (2 : Fin 8)) := by
    all_goals simp [finalColumn, NativeFinalLayout.queryColumn, NativeFinalLayout.query,
      NativeFinalLayout.queryIndex, importedConstraints, FlatOperation.lookups,
      Expression.eval, Verification.environment, acC, NativeFinalLayout.secondInput,
      acLowC, NativeFinalLayout.lowC, diagonalFrame, NativeLayout.diagonal,
      NativeLayout.Layout.read, NativeLayout.Location.read]
    all_goals ring
  have aHigh : finalColumn w ((2 : Fin 8).castLE (by decide)) 3 1 =
      (-15728640 : ZMod 2013265921) * (acA w (2 : Fin 8) - acLowA w (2 : Fin 8)) := by
    all_goals simp [finalColumn, NativeFinalLayout.queryColumn, NativeFinalLayout.query,
      NativeFinalLayout.queryIndex, importedConstraints, FlatOperation.lookups,
      Expression.eval, Verification.environment, acA, NativeFinalLayout.firstInput,
      acLowA, NativeFinalLayout.lowA, diagonalFrame, NativeLayout.diagonal,
      NativeLayout.Layout.read, NativeLayout.Location.read, NativeFinalLayout.temporary]

    all_goals ring_nf
    all_goals reduce_mod_char
    all_goals ring_nf
    all_goals reduce_mod_char
  rw [initialHigh, cHigh] at q1
  rw [aHigh] at q3
  all_goals simp [finalColumn, NativeFinalLayout.queryColumn, NativeFinalLayout.query,
    NativeFinalLayout.queryIndex, importedConstraints, FlatOperation.lookups,
    Expression.eval, Verification.environment, acTemp, NativeFinalLayout.temporary,
    acLowC, NativeFinalLayout.lowC, acLowA, NativeFinalLayout.lowA, diagonalFrame,
    NativeLayout.diagonal, NativeLayout.Layout.read, NativeLayout.Location.read] at q0 q1 q2 q3 ⊢
  all_goals
    refine ⟨q0, ?_, ?_, ?_⟩
    · exact q1
    · convert q2 using 1
      all_goals ring
    · exact q3


/-- Native query projections for the first half of finalization. -/
theorem native_ac_queries_3 {p : Nat} [Fact p.Prime]
    (compatible : SerializedInverse.Scale64 p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    chunkXor 7 (acTemp w (3 : Fin 8) 0) (acLowC w (3 : Fin 8)) (acTemp w (3 : Fin 8) 1) ∧
    chunkXor 9 ((-15728640 : ZMod p) * (acInitial w (3 : Fin 8) - acTemp w (3 : Fin 8) 0))
      ((-15728640 : ZMod p) * (acC w (3 : Fin 8) - acLowC w (3 : Fin 8))) (acTemp w (3 : Fin 8) 2) ∧
    chunkXor 7 (acTemp w (3 : Fin 8) 1) (acLowA w (3 : Fin 8)) (acTemp w (3 : Fin 8) 4) ∧
    chunkXor 9 (acTemp w (3 : Fin 8) 2)
      ((-15728640 : ZMod p) * (acA w (3 : Fin 8) - acLowA w (3 : Fin 8))) (acTemp w (3 : Fin 8) 5) := by
  have field := serialized_field compatible
  subst p
  unfold babyBearModulus at *
  have tag (stage : Fin 4) : finalColumn w ((3 : Fin 8).castLE (by decide)) stage 5 =
      (if stage.val % 2 = 0 then 19 else 20 : ZMod 2013265921) := by
    fin_cases stage <;> simp [finalColumn,
      NativeFinalLayout.queryColumn, NativeFinalLayout.query, NativeFinalLayout.queryIndex,
      importedConstraints, FlatOperation.lookups, Expression.eval, Verification.environment]
  have q0 := final_query (by decide) ((3 : Fin 8).castLE (by decide)) 0 1 h (tag 0)
  have q1 := final_query (by decide) ((3 : Fin 8).castLE (by decide)) 1 2 h (tag 1)
  have q2 := final_query (by decide) ((3 : Fin 8).castLE (by decide)) 2 1 h (tag 2)
  have q3 := final_query (by decide) ((3 : Fin 8).castLE (by decide)) 3 2 h (tag 3)
  have initialHigh : finalColumn w ((3 : Fin 8).castLE (by decide)) 1 0 =
      (-15728640 : ZMod 2013265921) * (acInitial w (3 : Fin 8) - acTemp w (3 : Fin 8) 0) := by
    all_goals simp [finalColumn, NativeFinalLayout.queryColumn, NativeFinalLayout.query,
      NativeFinalLayout.queryIndex, importedConstraints, FlatOperation.lookups,
      Expression.eval, Verification.environment, acInitial, NativeFinalLayout.initial,
      acTemp, NativeFinalLayout.temporary]
    all_goals ring
  have cHigh : finalColumn w ((3 : Fin 8).castLE (by decide)) 1 1 =
      (-15728640 : ZMod 2013265921) * (acC w (3 : Fin 8) - acLowC w (3 : Fin 8)) := by
    all_goals simp [finalColumn, NativeFinalLayout.queryColumn, NativeFinalLayout.query,
      NativeFinalLayout.queryIndex, importedConstraints, FlatOperation.lookups,
      Expression.eval, Verification.environment, acC, NativeFinalLayout.secondInput,
      acLowC, NativeFinalLayout.lowC, diagonalFrame, NativeLayout.diagonal,
      NativeLayout.Layout.read, NativeLayout.Location.read]
    all_goals ring
  have aHigh : finalColumn w ((3 : Fin 8).castLE (by decide)) 3 1 =
      (-15728640 : ZMod 2013265921) * (acA w (3 : Fin 8) - acLowA w (3 : Fin 8)) := by
    all_goals simp [finalColumn, NativeFinalLayout.queryColumn, NativeFinalLayout.query,
      NativeFinalLayout.queryIndex, importedConstraints, FlatOperation.lookups,
      Expression.eval, Verification.environment, acA, NativeFinalLayout.firstInput,
      acLowA, NativeFinalLayout.lowA, diagonalFrame, NativeLayout.diagonal,
      NativeLayout.Layout.read, NativeLayout.Location.read, NativeFinalLayout.temporary]

    all_goals ring_nf
    all_goals reduce_mod_char
    all_goals ring_nf
    all_goals reduce_mod_char
  rw [initialHigh, cHigh] at q1
  rw [aHigh] at q3
  all_goals simp [finalColumn, NativeFinalLayout.queryColumn, NativeFinalLayout.query,
    NativeFinalLayout.queryIndex, importedConstraints, FlatOperation.lookups,
    Expression.eval, Verification.environment, acTemp, NativeFinalLayout.temporary,
    acLowC, NativeFinalLayout.lowC, acLowA, NativeFinalLayout.lowA, diagonalFrame,
    NativeLayout.diagonal, NativeLayout.Layout.read, NativeLayout.Location.read] at q0 q1 q2 q3 ⊢
  all_goals
    refine ⟨q0, ?_, ?_, ?_⟩
    · exact q1
    · convert q2 using 1
      all_goals ring
    · exact q3


end Airbender.Blake2Round.Proofs
