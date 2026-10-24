import GKRProtocol.HelperNative.AddSubCached
import GKRProtocol.HelperSemantics

namespace Tests.GKRHelperSources
open Airbender Airbender.Compiler
open Airbender.Compiler.HelperNative.AddSubCached
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

private def replaceBorrow : Source.HelperField → Source.HelperField
  | .memory field => .memory field
  | .borrow index => .borrow (index + 1)
  | .add left right => .add (replaceBorrow left) (replaceBorrow right)
  | .scale coefficient field => .scale coefficient (replaceBorrow field)
  | .neg field => .neg (replaceBorrow field)

theorem rejects_changed_borrow_dependency :
    ({native.candidate9 with «source» := replaceBorrow native.candidate9.source} :
      HelperAgreement native.copyRelations native.recipe9).check native.placement
      MemoryNative.AddSubCached.native.bank = false := by decide +kernel

theorem rejects_changed_consumed_coefficient :
    (HelperAgreement.mk native.candidate9.source native.candidate9.witness :
      HelperAgreement native.copyRelations (.add native.recipe9 (.constant 268435454))).check
      native.placement MemoryNative.AddSubCached.native.bank = false := by decide +kernel

theorem rejects_omitted_clock_field :
    ({native.candidate6 with «source» := .memory (.constant 0)} :
      HelperAgreement native.copyRelations native.recipe6).check native.placement
      MemoryNative.AddSubCached.native.bank = false := by decide +kernel

theorem rejects_dangling_borrow_reference :
    Source.HelperField.referencesValid 42 3 0 3 false (.borrow 3) = false := by decide +kernel

theorem rejects_nonboolean_borrow : (2 : Source.BaseField) * (2 - 1) ≠ 0 := by decide +kernel

theorem excludes_alignment_without_field_capacity : ¬2 ^ (12 + 19) < babyBearModulus := by decide +kernel

theorem constructs_borrow_in_same_high_limb :
    let borrow : Source.BaseField := comparisonBorrow 9 10
    borrow * (borrow - 1) = 0 ∧ ((9 : Source.BaseField) - 10 + 524288 * borrow).val < 524288 ∧
      ((3 : Source.BaseField) + 524288 - borrow - 3).val < 524288 := by
  exact comparison_complete (by decide) (by decide) (by decide) (by decide) (by decide)

theorem constructs_borrow_across_high_limb :
    let borrow : Source.BaseField := comparisonBorrow 524287 0
    borrow * (borrow - 1) = 0 ∧ ((524287 : Source.BaseField) - 0 + 524288 * borrow).val < 524288 ∧
      ((2 : Source.BaseField) + 524288 - borrow - 3).val < 524288 := by
  exact comparison_complete (by decide) (by decide) (by decide) (by decide) (by decide)

theorem constructs_aligned_pointer_query : (((128 : Source.BaseField)⁻¹ * 65408).val) < 524288 := by
  exact alignment_complete (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem rejects_unaligned_pointer_query : ¬(((128 : Source.BaseField)⁻¹ * 65409).val) < 524288 := by
  intro ranged
  have aligned := alignment_sound (scale := 128) (by decide) (by decide) ranged
  rw [show (65409 : Source.BaseField).val = 65409 by decide +kernel] at aligned
  exact (by decide : ¬128 ∣ 65409) aligned

theorem rejects_changed_executor_clock_step :
    let carry : Source.BaseField := (524288 : Source.BaseField)⁻¹ * ((0 : Source.BaseField) + 4 - 5)
    carry * (carry - 1) ≠ 0 := by decide +kernel

theorem borrow_domain_preserves_original_columns (values : Source.HelperValues)
    (borrow : Nat → Source.BaseField) (index : Nat) :
    ({values with borrow := borrow} : Source.HelperValues).memory.original index =
      values.memory.original index := rfl

end Tests.GKRHelperSources
