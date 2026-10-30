import Airbender.Proofs.FullUnsigned.ChiSourceCycle0
import Airbender.Proofs.FullUnsigned.SourceBlockCycles
import Airbender.Proofs.FullUnsigned.ChiSourceController
import Airbender.Proofs.Keccak.SplitChiOutputs

namespace Airbender.Setup.SourceCaptureChiProofs
open Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
-- Each finite row check covers at most one 4,096-row source cycle.
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private noncomputable def sourceBinding : SourceBank.ColumnBinding :=
  (SourceCaptureChi.columnBindings[5]'(by change 5 < 11; decide +kernel)).1

private noncomputable def frontBlocks : List Block := ChiSourceCycle0.front.map sourceBinding.blocks
private noncomputable def cycleBlocks : List Block := ChiSourceCycle0.cycle.map sourceBinding.blocks
private noncomputable def tailBlocks : List Block := (ChiSourceCycle0.tail.take 213).map sourceBinding.blocks
private noncomputable def restBlocks : List Block := (ChiSourceCycle0.tail.drop 213).map sourceBinding.blocks

private theorem source_column_binding :
    (SourceCaptureChi.columns[5]?).getD ({ blocks := #[] } : Column) = sourceBinding.column := by
  setup_source_rfl

private theorem binding_entries : sourceBinding.entries = SourceCaptureChi.entries_2715 := by
  simp only [sourceBinding, SourceCaptureChi.columnBindings, List.getElem_cons_zero, List.getElem_cons_succ]
  source_record_entries

private theorem source_blocks :
    (sourceBinding.column.blocks.toList) =
      frontBlocks ++ (List.replicate 255 cycleBlocks).flatten ++ (tailBlocks ++ restBlocks) := by
  simp only [SourceBank.ColumnBinding.column, List.toList_toArray]
  rw [binding_entries, ChiSourceCycle0.source_indices]
  simp only [List.map_append, List.map_flatten, List.map_replicate]
  unfold frontBlocks cycleBlocks tailBlocks restBlocks
  rw [← List.map_append, List.take_append_drop]

private def output0Expected (index : Nat) : Nat :=
  (index % 16) ^^^ ((15 ^^^ (index / 16 % 16)) &&& (index / 256 % 16))

private theorem front_length : (frontBlocks.map Block.length).sum = 256 := by
  setup_source_rfl

private theorem cycle_length : (cycleBlocks.map Block.length).sum = 4096 := by
  setup_source_rfl

private theorem tail_length : (tailBlocks.map Block.length).sum = 3840 := by
  setup_source_rfl

private theorem front_checked : checkBlockRows output0Expected 0 frontBlocks = true := by
  decide +kernel

private theorem cycle_checked : checkBlockRows output0Expected 256 cycleBlocks = true := by
  decide +kernel

private theorem tail_checked : checkBlockRows output0Expected 256 tailBlocks = true := by
  decide +kernel

private theorem output0_periodic (a b : Nat) (same : a % 4096 = b % 4096) :
    output0Expected a = output0Expected b := by
  have low : a % 16 = b % 16 := by omega
  have middle : a / 16 % 16 = b / 16 % 16 := by omega
  have high : a / 256 % 16 = b / 256 % 16 := by omega
  simp only [output0Expected, low, middle, high]

/-- Every physical source row for chi output zero has its exact nibble value. -/
theorem source_output0_get (index : Fin 1048576) :
    ((SourceCaptureChi.columns[5]?).getD ({ blocks := #[] } : Column)).get? index.val =
      some ((index.val % 16) ^^^ ((15 ^^^ (index.val / 16 % 16)) &&& (index.val / 256 % 16))) := by
  rw [source_column_binding]
  change getFromBlocks sourceBinding.column.blocks.toList index.val = _
  rw [source_blocks]
  exact checked_cycle_rows output0Expected frontBlocks cycleBlocks tailBlocks restBlocks 255 4096 index.val
    cycle_length front_checked (by rw [front_length]; exact cycle_checked)
    (by rw [front_length]; exact tail_checked) output0_periodic
    (by rw [front_length, tail_length]; exact index.isLt)

/-- Source output zero matches its original canonical generic-table field. -/
theorem source_output0_matches (index : Fin 1048576) :
    ((SourceCaptureChi.columns[5]?).getD ({ blocks := #[] } : Column)).get? index.val =
      Airbender.Keccak.Split.Native.Fixed.chi5Generic.columns[5].get? index.val := by
  have present := Airbender.Keccak.Split.Native.Fixed.Proofs.chi5_output_get
    (⟨0, by decide +kernel⟩ : Fin 5) index
  have value := Airbender.Keccak.Split.Native.Fixed.Proofs.chi5_output_value
    (⟨0, by decide +kernel⟩ : Fin 5) index
  change Airbender.Keccak.Split.Native.Fixed.chi5Generic.columns[5].get? index.val = some _ at present
  conv_rhs at value => norm_num
  change (Airbender.Keccak.Split.Native.Fixed.chi5Generic.columns[5].get? index.val).getD 0 =
    (index.val % 16) ^^^ ((15 ^^^ (index.val / 16 % 16)) &&& (index.val / 256 % 16)) at value
  rw [present, Option.getD_some] at value
  exact (source_output0_get index).trans ((present.trans (congrArg some value)).symm)

end Airbender.Setup.SourceCaptureChiProofs
