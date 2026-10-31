import Airbender.Proofs.GKRProtocol.ProgramUnifiedArithmeticTags
import Airbender.Proofs.GKRProtocol.RetableConstraints
import Airbender.Proofs.GKRProtocol.CleanClosedNative.UnifiedUncached
import Airbender.Proofs.GKRProtocol.ROMNative.UnifiedFullPublic
import Airbender.Proofs.UnifiedReduced

namespace Airbender.Compiler.UnifiedPublicConstraints
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

noncomputable abbrev rowQueries := CleanGenericArgumentsNative.UnifiedUncached.native.genericExpressions

theorem not_decoder (setup : Table Source.BaseField (fields 10)) (w : Nat → Source.BaseField)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (UnifiedReduced.clockConstraints setup))
    (active : w 4 = 1) (operation : w 10 ≠ 46) :
    ∀ query ∈ rowQueries, (query.map (fun expression => expression.eval (Verification.environment w)))[9] ≠ 46 := by
  have core := Verification.holds_of_sublist holds
    (List.sublist_append_left (UnifiedReduced.importedConstraints setup) UnifiedReduced.importedConstraintsTimestampLookups)
  have total := UnifiedReduced.Proofs.dispatch_count (by decide +kernel) core active
  simp [UnifiedReduced.Variables.dispatchColumns, Fin.sum_univ_succ] at total
  have gate := Verification.assertion_of_holds core ⟨39, by rw [UnifiedReduced.constraint_count]; decide⟩
  simp [UnifiedReduced.importedConstraints, FlatOperation.constraints, _root_.Expression.eval,
    Verification.environment] at gate
  have romEq : w 81 = w 28 * w 54 := by linear_combination gate
  have romLe : (w 81).val ≤ (w 28).val := by
    have load : w 28 = 0 ∨ w 28 = 1 := by simpa using UnifiedReduced.Proofs.local_flags core 18
    have rom : w 54 = 0 ∨ w 54 = 1 := by simpa using UnifiedReduced.Proofs.local_flags core 22
    rw [romEq]
    rcases load with load | load <;> rcases rom with rom | rom
    all_goals norm_num [load, rom]
  let control := (w 21).val + (w 22).val + (w 23).val + (w 24).val
  have oneHotBound : control + (w 26).val + (w 27).val + (w 81).val ≤ 1 := by dsimp [control]; omega
  have tags := one_hot_tags (w 10) operation control (w 26).val (w 27).val (w 81).val oneHotBound
  have equation (index : Fin 5) := Verification.assertion_of_holds core
    ⟨(#v[45, 49, 58, 67, 76][index]), by rw [UnifiedReduced.constraint_count]; fin_cases index <;> norm_num⟩
  have e0 := equation 0; have e1 := equation 1; have e2 := equation 2
  have e3 := equation 3; have e4 := equation 4
  simp [UnifiedReduced.importedConstraints, FlatOperation.constraints, _root_.Expression.eval,
    Verification.environment, active] at e0 e1 e2 e3 e4
  have ccast : (control : Source.BaseField) = w 21 + w 22 + w 23 + w 24 := by
    simp [control, Nat.cast_add]
  have t0 : w 82 = (control : Source.BaseField) + 8 * (w 26).val + 3 * (w 27).val + 34 * (w 81).val := by
    simp only [ccast, ZMod.natCast_zmod_val]
    linear_combination e0
  have t1 : w 86 = 5 * (control : Source.BaseField) + 9 * (w 26).val + (w 27).val * w 10 := by
    simp only [ccast, ZMod.natCast_zmod_val]
    linear_combination e1
  have t2 : w 95 = 5 * (control : Source.BaseField) + 9 * (w 26).val + (w 27).val * w 10 := by
    simp only [ccast, ZMod.natCast_zmod_val]
    linear_combination e2
  have t3 : w 104 = 51 * (control : Source.BaseField) + 9 * (w 26).val + (w 27).val * w 10 := by
    simp only [ccast, ZMod.natCast_zmod_val]
    linear_combination e3
  have t4 : w 113 = 2 * (control : Source.BaseField) + 9 * (w 26).val + (w 27).val * w 10 := by
    simp only [ccast, ZMod.natCast_zmod_val]
    linear_combination e4
  have n0 : w 82 ≠ 46 := by rw [t0]; exact tags.1
  have n1 : w 86 ≠ 46 := by rw [t1]; exact tags.2.1
  have n2 : w 95 ≠ 46 := by rw [t2]; exact tags.2.1
  have n3 : w 104 ≠ 46 := by rw [t3]; exact tags.2.2.1
  have n4 : w 113 ≠ 46 := by rw [t4]; exact tags.2.2.2
  intro query member
  simp [rowQueries, CleanGenericArgumentsNative.UnifiedUncached.native.genericExpressions] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals first
    | simpa [CleanGenericArgumentsNative.UnifiedUncached.native.genericExpressions0,
        CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression0_9, _root_.Expression.eval, Verification.environment] using n0
    | simpa [CleanGenericArgumentsNative.UnifiedUncached.native.genericExpressions1,
        CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression1_9, _root_.Expression.eval, Verification.environment] using n1
    | simpa [CleanGenericArgumentsNative.UnifiedUncached.native.genericExpressions2,
        CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression2_9, _root_.Expression.eval, Verification.environment] using n2
    | simpa [CleanGenericArgumentsNative.UnifiedUncached.native.genericExpressions3,
        CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression3_9, _root_.Expression.eval, Verification.environment] using n3
    | simpa [CleanGenericArgumentsNative.UnifiedUncached.native.genericExpressions4,
        CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression4_9, _root_.Expression.eval, Verification.environment] using n4

theorem transport (before after : Table Source.BaseField (fields 10)) (w : Nat → Source.BaseField)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (UnifiedReduced.clockConstraints before))
    (active : w 4 = 1) (operation : w 10 ≠ 46)
    (refines : ∀ query : Vector Source.BaseField 10, before.Contains #[] query → query[9] ≠ 46 → after.Contains #[] query) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment w) (UnifiedReduced.clockConstraints after) := by
  apply retable_constraints before after rowQueries
    (CleanArgumentsNative.UnifiedUncached.native.rangeExpressions.map Verification.range16)
    (CleanArgumentsNative.UnifiedUncached.native.timestampExpressions.map Trace.timestampLookup)
    (UnifiedReduced.clockConstraints before) (UnifiedReduced.clockConstraints after) (by rfl) (by rfl) (by rfl)
    (Verification.environment w) holds
  intro query member present
  simp only [ProverData.getTable, Verification.environment, Array.map_empty] at present ⊢
  exact refines _ present (not_decoder before w holds active operation query member)

end Airbender.Compiler.UnifiedPublicConstraints
