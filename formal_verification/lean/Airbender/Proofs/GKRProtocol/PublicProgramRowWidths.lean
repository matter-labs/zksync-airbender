import Airbender.Review.Compiler.NativePublicSetup
import Airbender.Proofs.GKRProtocol.ProgramMasks

namespace Airbender.Compiler.NativeProgramSetup
open Airbender.Trace Airbender.Trace.NativeDecoder
set_option warningAsError true
set_option Elab.async false

private theorem selected_fields_length {α : Type} (selection : List Bool) (values : List α)
    (lengths : selection.length = values.length) :
    ((selection.zip values).filterMap fun (selected, value) =>
      if selected then some value else none).length = (selection.filter id).length := by
  induction selection generalizing values with
  | nil => simp
  | cons selected rest previous =>
    cases values with
    | nil => simp at lengths
    | cons value remaining =>
      have tails : rest.length = remaining.length := Nat.succ.inj lengths
      cases selected <;> simpa using previous remaining tails

theorem mask_row_width (mask : ProgramRows.Mask) (row : Vector Source.BaseField 9) :
    (ProgramRows.maskRow mask row).length = 2 + (mask.columns.toList.drop 2 |>.filter id).length := by
  have lengths : (mask.columns.toList.drop 2).length = (row.toList.drop 2).length := by
    simp [mask.width]
  have selected := selected_fields_length (mask.columns.toList.drop 2) (row.toList.drop 2) lengths
  simp only [ProgramRows.maskRow, List.length_cons]
  rw [selected]
  omega

private theorem mask_ext {left right : ProgramRows.Mask} (same : left.columns = right.columns) :
    left = right := by
  cases left
  cases right
  cases same
  rfl

theorem unrolled_mask_eq
    {config : ProgramRows.Config} {initial : Reference.RiscV.Sail.State} {text : List (BitVec 32)}
    {capacity : Nat} {masks : PooledFamily → ProgramRows.Mask}
    {columns : PooledFamily → List (List Source.BaseField)}
    (setup : UnrolledProgramSetup config initial text capacity masks columns) (family : PooledFamily) :
    masks family = ProgramRows.Proofs.maskOfFamily family :=
  mask_ext ((setup.maskMatches family).trans (ProgramRows.Proofs.mask_of_family_matches family).symm)

theorem unified_mask_eq
    {initial : Reference.RiscV.Sail.State} {text : List (BitVec 32)} {capacity : Nat}
    {mask : ProgramRows.Mask} {columns : List (List Source.BaseField)}
    (setup : UnifiedProgramSetup initial text capacity mask columns) : mask = ProgramRows.Proofs.unifiedMask :=
  mask_ext (setup.maskMatches.trans ProgramRows.Proofs.unified_mask_matches.symm)

/-- Each public family mask has the payload width of its native layout. -/
theorem unrolled_native_mask_width (configuration : Configuration) (family : PooledFamily)
    (layout : Airbender.Reference.Compiler.ProgramSetup.Layout)
    (familyCase : pooledFamily configuration = some family)
    (layoutCase : layouts configuration = some layout) (row : Vector Source.BaseField 9) :
    (ProgramRows.maskRow (ProgramRows.Proofs.maskOfFamily family) row).length =
      if layout.tagged then layout.width - 1 else layout.width := by
  rw [mask_row_width]
  cases configuration <;> simp only [pooledFamily, Option.some.injEq, reduceCtorEq] at familyCase
  all_goals subst family
  all_goals simp only [layouts, Option.some.injEq] at layoutCase
  all_goals subst layout
  all_goals decide +kernel

theorem unified_native_mask_width (configuration : Configuration)
    (layout : Airbender.Reference.Compiler.ProgramSetup.Layout)
    (unified : configuration = .unifiedUncached ∨ configuration = .unifiedCached)
    (layoutCase : layouts configuration = some layout) (row : Vector Source.BaseField 9) :
    (ProgramRows.maskRow ProgramRows.Proofs.unifiedMask row).length = layout.width - 1 := by
  rw [mask_row_width]
  rcases unified with rfl | rfl
  all_goals simp only [layouts, Option.some.injEq] at layoutCase
  all_goals subst layout
  all_goals decide +kernel

theorem unrolled_column_width
    {config : ProgramRows.Config} {initial : Reference.RiscV.Sail.State} {text : List (BitVec 32)}
    {capacity : Nat} {masks : PooledFamily → ProgramRows.Mask}
    {columns : PooledFamily → List (List Source.BaseField)}
    (setup : UnrolledProgramSetup config initial text capacity masks columns)
    (configuration : Configuration) (family : PooledFamily)
    (layout : Airbender.Reference.Compiler.ProgramSetup.Layout)
    (familyCase : pooledFamily configuration = some family)
    (layoutCase : layouts configuration = some layout) (row : List Source.BaseField)
    (member : row ∈ columns family) :
    row.length = if layout.tagged then layout.width - 1 else layout.width := by
  rw [setup.decoderRows family, ProgramRows.nativeDecoderRows] at member
  obtain ⟨raw, _, rfl⟩ := List.mem_map.mp member
  rw [unrolled_mask_eq setup family]
  exact unrolled_native_mask_width configuration family layout familyCase layoutCase raw

theorem unified_column_width
    {initial : Reference.RiscV.Sail.State} {text : List (BitVec 32)} {capacity : Nat}
    {mask : ProgramRows.Mask} {columns : List (List Source.BaseField)}
    (setup : UnifiedProgramSetup initial text capacity mask columns)
    (configuration : Configuration) (layout : Airbender.Reference.Compiler.ProgramSetup.Layout)
    (unified : configuration = .unifiedUncached ∨ configuration = .unifiedCached)
    (layoutCase : layouts configuration = some layout) (row : List Source.BaseField)
    (member : row ∈ columns) : row.length = layout.width - 1 := by
  rw [setup.decoderRows, UnifiedProgramRows.nativeDecoderRows] at member
  obtain ⟨raw, _, rfl⟩ := List.mem_map.mp member
  rw [unified_mask_eq setup]
  exact unified_native_mask_width configuration layout unified layoutCase raw

end Airbender.Compiler.NativeProgramSetup
