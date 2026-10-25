import GKRProtocol.RetableConstraints
import GKRProtocol.CleanClosedNative.WordMemoryUncached
import GKRProtocol.CleanClosedNative.SubwordMemoryUncached
import Airbender.Proofs.WordMemory
import Airbender.Proofs.SubwordMemory

namespace Airbender.Compiler.PublicConstraints
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

noncomputable abbrev wordQueries := CleanGenericArgumentsNative.WordMemoryUncached.native.genericExpressions
noncomputable abbrev subwordQueries := CleanGenericArgumentsNative.SubwordMemoryUncached.native.genericExpressions

theorem word_not_decoder (setup : Table Source.BaseField (fields 9)) (w : Nat → Source.BaseField)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (WordMemory.clockConstraints setup)) :
    ∀ query ∈ wordQueries, (query.map (fun expression => expression.eval (Verification.environment w)))[8] ≠ 46 := by
  have core := Verification.holds_of_sublist holds
    (List.sublist_append_left (WordMemory.importedConstraints setup) WordMemory.importedConstraintsTimestampLookups)
  have r := Verification.assertion_of_holds core ⟨9, by rw [WordMemory.constraint_count]; decide⟩
  have active := Verification.assertion_of_holds core ⟨16, by rw [WordMemory.constraint_count]; decide⟩
  have tag := Verification.assertion_of_holds core ⟨17, by rw [WordMemory.constraint_count]; decide⟩
  simp [WordMemory.importedConstraints, FlatOperation.constraints, _root_.Expression.eval, Verification.environment] at r active tag
  have copyR : w 37 = w 35 := by linear_combination r
  have copyA : w 44 = w 4 := by linear_combination active
  have notTag : w 45 ≠ 46 := by
    intro wrong
    rw [copyR, copyA, wrong] at tag
    have fa : w 4 = 0 ∨ w 4 = 1 := by simpa using WordMemory.Proofs.local_flags core 0
    have fb : w 35 = 0 ∨ w 35 = 1 := by simpa using WordMemory.Proofs.local_flags core 2
    rcases fa with a | a
    all_goals rcases fb with b | b
    all_goals norm_num [a, b] at tag
    all_goals have bad := congrArg ZMod.val tag
    all_goals norm_num [ZMod.val_ofNat, Source.BaseField, babyBearModulus] at bad
  intro query member
  simp only [wordQueries, CleanGenericArgumentsNative.WordMemoryUncached.native.genericExpressions,
    List.mem_singleton] at member
  subst query
  simpa [CleanGenericArgumentsNative.WordMemoryUncached.native.genericExpressions0,
    CleanGenericArgumentsNative.WordMemoryUncached.native.part0.genericExpression0_8,
    _root_.Expression.eval, Verification.environment] using notTag

theorem subword_not_decoder (setup : Table Source.BaseField (fields 9)) (w : Nat → Source.BaseField)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (SubwordMemory.clockConstraints setup)) :
    ∀ query ∈ subwordQueries, (query.map (fun expression => expression.eval (Verification.environment w)))[8] ≠ 46 := by
  have core := Verification.holds_of_sublist holds
    (List.sublist_append_left (SubwordMemory.importedConstraints setup) SubwordMemory.importedConstraintsTimestampLookups)
  have tag := Verification.assertion_of_holds core ⟨27, by rw [SubwordMemory.constraint_count]; decide⟩
  have enabled := Verification.assertion_of_holds core ⟨28, by rw [SubwordMemory.constraint_count]; decide⟩
  have outTag := Verification.assertion_of_holds core ⟨29, by rw [SubwordMemory.constraint_count]; decide⟩
  simp [SubwordMemory.importedConstraints, FlatOperation.constraints, _root_.Expression.eval, Verification.environment] at tag enabled outTag
  have enabledEq : w 60 = w 4 := by linear_combination enabled
  rw [enabledEq] at outTag
  have tagEq : w 61 = w 4 * (w 41 * (1 - w 11) * 44 + w 41 * w 11 * 45 +
      (1 - w 10 - w 41) * (1 - w 11) * 42 + (1 - w 10 - w 41) * w 11 * 43 +
      w 10 * w 11 * 29) := by linear_combination w 4 * tag + outTag
  have notTag : w 61 ≠ 46 := by
    intro wrong
    rw [wrong] at tagEq
    have fx : w 4 = 0 ∨ w 4 = 1 := by simpa using SubwordMemory.Proofs.local_flags core 0
    have fy : w 10 = 0 ∨ w 10 = 1 := by simpa using SubwordMemory.Proofs.local_flags core 1
    have fz : w 11 = 0 ∨ w 11 = 1 := by simpa using SubwordMemory.Proofs.local_flags core 2
    have ft : w 41 = 0 ∨ w 41 = 1 := by simpa using SubwordMemory.Proofs.local_flags core 8
    rcases fx with x | x
    all_goals rcases fy with y | y
    all_goals rcases fz with z | z
    all_goals rcases ft with t | t
    all_goals norm_num [x, y, z, t] at tagEq
    all_goals have bad := congrArg ZMod.val tagEq
    all_goals norm_num [ZMod.val_ofNat, Source.BaseField, babyBearModulus] at bad
  intro query member
  simp [subwordQueries, CleanGenericArgumentsNative.SubwordMemoryUncached.native.genericExpressions] at member
  rcases member with rfl | rfl
  · norm_num [CleanGenericArgumentsNative.SubwordMemoryUncached.native.genericExpressions0,
      CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.genericExpression0_8, _root_.Expression.eval, Source.BaseField, babyBearModulus]
    decide +kernel
  · simpa [CleanGenericArgumentsNative.SubwordMemoryUncached.native.genericExpressions1,
      CleanGenericArgumentsNative.SubwordMemoryUncached.native.part0.genericExpression1_8,
      _root_.Expression.eval, Verification.environment] using notTag

theorem word_transport (before after : Table Source.BaseField (fields 9)) (w : Nat → Source.BaseField)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (WordMemory.clockConstraints before))
    (refines : ∀ query : Vector Source.BaseField 9, before.Contains #[] query → query[8] ≠ 46 → after.Contains #[] query) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment w) (WordMemory.clockConstraints after) := by
  apply retable_constraints before after wordQueries
    (CleanArgumentsNative.WordMemoryUncached.native.rangeExpressions.map Verification.range16)
    (CleanArgumentsNative.WordMemoryUncached.native.timestampExpressions.map Trace.timestampLookup)
    (WordMemory.clockConstraints before) (WordMemory.clockConstraints after) (by rfl) (by rfl) (by rfl)
    (Verification.environment w) holds
  intro query member present
  simp only [ProverData.getTable, Verification.environment, Array.map_empty] at present ⊢
  exact refines _ present (word_not_decoder before w holds query member)

theorem subword_transport (before after : Table Source.BaseField (fields 9)) (w : Nat → Source.BaseField)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (SubwordMemory.clockConstraints before))
    (refines : ∀ query : Vector Source.BaseField 9, before.Contains #[] query → query[8] ≠ 46 → after.Contains #[] query) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment w) (SubwordMemory.clockConstraints after) := by
  apply retable_constraints before after subwordQueries
    (CleanArgumentsNative.SubwordMemoryUncached.native.rangeExpressions.map Verification.range16)
    (CleanArgumentsNative.SubwordMemoryUncached.native.timestampExpressions.map Trace.timestampLookup)
    (SubwordMemory.clockConstraints before) (SubwordMemory.clockConstraints after) (by rfl) (by rfl) (by rfl)
    (Verification.environment w) holds
  intro query member present
  simp only [ProverData.getTable, Verification.environment, Array.map_empty] at present ⊢
  exact refines _ present (subword_not_decoder before w holds query member)

end Airbender.Compiler.PublicConstraints
