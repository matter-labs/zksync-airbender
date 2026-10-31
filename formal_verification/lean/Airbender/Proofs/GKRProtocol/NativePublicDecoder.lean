import Airbender.Proofs.GKRProtocol.NativeProgramQueries
import Airbender.Proofs.GKRProtocol.PublicProgramRowWidths
import Airbender.Proofs.GKRProtocol.PublicProgramSetup

namespace Airbender.Compiler.NativeProgramSetup
open Airbender.Trace Airbender.Trace.NativeDecoder
open Airbender.Reference.Compiler
set_option warningAsError true
set_option Elab.async false

private theorem layout_width (configuration : Configuration) (layout : ProgramSetup.Layout)
    (selected : layouts configuration = some layout) : 1 < layout.width := by
  cases configuration <;> simp only [layouts, Option.some.injEq, reduceCtorEq] at selected
  all_goals subst layout
  all_goals decide +kernel

theorem active_decoder_payload (mask : ProgramRows.Mask) (query : Vector Source.BaseField 9)
    (bounded : query[0].val < 65536) : (ProgramRows.maskRow mask query).head? ≠ some (-1) := by
  intro sentinel
  have equal : query[0] = -1 := by simpa only [ProgramRows.maskRow, List.head?_cons, Option.some.injEq] using sentinel
  rw [equal] at bounded
  exact (by decide +kernel : ¬((-1 : Source.BaseField).val < 65536)) bounded

/-- Native decoder matching yields membership in the public program columns.
The caller must prove the native operand transport for the actual query. -/
theorem unrolled_decoder_lookup
    {config : ProgramRows.Config} {initial : Reference.RiscV.Sail.State} {text : List (BitVec 32)}
    {capacity : Nat} {masks : PooledFamily → ProgramRows.Mask}
    {columns : PooledFamily → List (List Source.BaseField)}
    (setup : UnrolledProgramSetup config initial text capacity masks columns)
    (configuration : Configuration) (family : PooledFamily) (layout : ProgramSetup.Layout)
    (familyCase : pooledFamily configuration = some family)
    (selected : layouts configuration = some layout) (index : Nat)
    (query : Vector Source.BaseField 9) (bounded : query[0].val < 65536)
    (same : (if layout.tagged then
        ProgramSetup.packTagged layout.width 46 (ProgramRows.maskRow (masks family) query)
      else ProgramRows.maskRow (masks family) query) =
        unrolledLookupRows initial columns configuration 0 index) :
    ProgramRows.maskRow (masks family) query ∈ columns family := by
  have columnsAt : unrolledDecoderColumns columns configuration = columns family := by
    simp [unrolledDecoderColumns, familyCase]
  have positive := layout_width configuration layout selected
  have active := active_decoder_payload (masks family) query bounded
  cases tagged : layout.tagged with
  | false =>
    have member := untagged_decoder_member (unrolledDecoderColumns columns) (ROM.words initial)
      configuration layout selected tagged (by omega) index (ProgramRows.maskRow (masks family) query)
      (by simpa only [tagged, Bool.false_eq_true, if_false, unrolledLookupRows] using same) active
    simpa only [columnsAt] using member
  | true =>
    have widths : ∀ row ∈ unrolledDecoderColumns columns configuration, row.length = layout.width - 1 := by
      intro row member
      rw [columnsAt] at member
      simpa only [tagged, if_true] using
        unrolled_column_width setup configuration family layout familyCase selected row member
    have payloadWidth : (ProgramRows.maskRow (masks family) query).length = layout.width - 1 := by
      rw [unrolled_mask_eq setup family]
      simpa only [tagged, if_true] using
        unrolled_native_mask_width configuration family layout familyCase selected query
    have member := tagged_decoder_member (unrolledDecoderColumns columns) (ROM.words initial)
      configuration layout selected tagged (by omega) widths index
      (ProgramRows.maskRow (masks family) query) payloadWidth
      (by simpa only [tagged, if_true, unrolledLookupRows] using same) active
    simpa only [columnsAt] using member

theorem unified_decoder_lookup
    {initial : Reference.RiscV.Sail.State} {text : List (BitVec 32)} {capacity : Nat}
    {mask : ProgramRows.Mask} {columns : List (List Source.BaseField)}
    (setup : UnifiedProgramSetup initial text capacity mask columns)
    (configuration : Configuration) (layout : ProgramSetup.Layout)
    (unified : configuration = .unifiedUncached ∨ configuration = .unifiedCached)
    (selected : layouts configuration = some layout) (index : Nat)
    (query : Vector Source.BaseField 9) (bounded : query[0].val < 65536)
    (same : ProgramSetup.packTagged layout.width 46 (ProgramRows.maskRow mask query) =
      unifiedLookupRows initial columns configuration 0 index) :
    ProgramRows.maskRow mask query ∈ columns := by
  have columnsAt : unifiedDecoderColumns columns configuration = columns := by
    rcases unified with rfl | rfl <;> rfl
  have tagged : layout.tagged = true := by
    rcases unified with rfl | rfl
    all_goals simp only [layouts, Option.some.injEq] at selected
    all_goals subst layout
    all_goals rfl
  have widths : ∀ row ∈ unifiedDecoderColumns columns configuration, row.length = layout.width - 1 := by
    intro row member
    rw [columnsAt] at member
    exact unified_column_width setup configuration layout unified selected row member
  have payloadWidth : (ProgramRows.maskRow mask query).length = layout.width - 1 := by
    rw [unified_mask_eq setup]
    exact unified_native_mask_width configuration layout unified selected query
  have positive := layout_width configuration layout selected
  have member := tagged_decoder_member (unifiedDecoderColumns columns) (ROM.words initial)
    configuration layout selected tagged (by omega) widths index
    (ProgramRows.maskRow mask query) payloadWidth same (active_decoder_payload mask query bounded)
  simpa only [columnsAt] using member

end Airbender.Compiler.NativeProgramSetup
