import Airbender.Proofs.FullUnsigned.ThetaLowTwoSuffix
import Airbender.Proofs.FullUnsigned.SourceUniformCycles
import Airbender.Proofs.FullUnsigned.SourceColumnCoverage
import Airbender.Proofs.FullUnsigned.ThetaSourceLowZero
import Airbender.Proofs.Keccak.SplitThetaFragmentValues

namespace Airbender.Setup.SourceCaptureThetaProofs
open Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
-- 64 stored templates cover this complete 65,536-row shift case.
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private noncomputable def sourceColumn : Column := (SourceCaptureTheta.columns[3]?).getD ⟨#[]⟩
private noncomputable def binding : SourceBank.ColumnBinding :=
  (SourceCaptureTheta.columnBindings[3]'(by change 3 < 9; decide +kernel)).1
private noncomputable def tailBlocks : List Block := ThetaLowTwoSuffix.entries.map binding.blocks
private noncomputable def cycleBlocks : List Block := (ThetaLowTwoSuffix.entries.take 64).map binding.blocks
private noncomputable def blockAt (index : Fin 64) : Block := (cycleBlocks[index.val]?).getD (.affine 0 0 0)
private def periodicValues : Block → Array Nat
  | .periodic _ _ values => values
  | _ => #[]

private theorem source_column_binding : sourceColumn = binding.column := by
  simp only [binding, SourceCaptureTheta.columnBindings, List.getElem_cons_zero, List.getElem_cons_succ]
  rfl

private theorem binding_entries : binding.entries = SourceCaptureTheta.entries_9296 := by
  simp only [binding, SourceCaptureTheta.columnBindings, List.getElem_cons_zero, List.getElem_cons_succ]
  low_source_kernel_rfl

private theorem binding_tail (b : SourceBank.ColumnBinding) (first : Nat) :
    b.column.blocks.toList.drop first = (b.entries.drop first).map b.blocks := by
  simp only [SourceBank.ColumnBinding.column, List.toList_toArray, ← List.map_drop]

private theorem source_suffix : sourceColumn.blocks.toList.drop ThetaLowTwoSuffix.skip = tailBlocks := by
  refine (congrArg (fun column : Column => column.blocks.toList.drop ThetaLowTwoSuffix.skip) source_column_binding).trans ?_
  refine (binding_tail binding ThetaLowTwoSuffix.skip).trans ?_
  apply congrArg (List.map binding.blocks)
  exact (congrArg (List.drop ThetaLowTwoSuffix.skip) binding_entries).trans ThetaLowTwoSuffix.matches

private theorem tail_length : (tailBlocks.map Block.length).sum = 3997696 := by low_source_kernel_rfl
private theorem cycle_count : cycleBlocks.length = 64 := by low_source_kernel_rfl
private theorem cycle_lengths : ∀ block ∈ cycleBlocks, block.length = 256 := by decide +kernel
private theorem cycle_length : (cycleBlocks.map Block.length).sum = 16384 := by low_source_kernel_rfl
private theorem window_shape : tailBlocks.take 256 = (List.replicate 4 cycleBlocks).flatten := by low_source_kernel_rfl
private theorem window_length : ((tailBlocks.take 256).map Block.length).sum = 65536 := by
  rw [window_shape, repeated_blocks_length, cycle_length]

private theorem source_covered {artifact : Artifact} (parsed : parse SourceCaptureTheta.source = .ok artifact) :
    (sourceColumn.blocks.toList.map Block.length).sum = 4194304 := by
  have bound : 3 < SourceCaptureTheta.columns.size := by change 3 < 9; decide +kernel
  have member : sourceColumn ∈ SourceCaptureTheta.columns := by
    unfold sourceColumn
    rw [Array.getElem?_eq_getElem bound, Option.getD_some]
    simp
  exact source_column_lengths SourceCaptureThetaProofs.parsed trace_len_decoded columns_decoded parsed _ member

private theorem source_window {artifact : Artifact} (parsed : parse SourceCaptureTheta.source = .ok artifact)
    (index : Fin 65536) : sourceColumn.get? (196608 + index.val) = getFromBlocks (tailBlocks.take 256) index.val := by
  have selected := column_suffix_get sourceColumn ThetaLowTwoSuffix.skip 4194304 (196608 + index.val)
    (source_covered parsed) (by rw [source_suffix, tail_length]; omega)
  rw [source_suffix, tail_length] at selected
  have offset : 196608 + index.val - (4194304 - 3997696) = index.val := by omega
  rw [offset] at selected
  exact selected.trans (getFromBlocks_take _ _ _ (by rw [window_length]; exact index.isLt))

private theorem shapes (index : Fin 64) : blockAt index = .periodic 4 0 (periodicValues (blockAt index)) := by
  fin_cases index <;> low_source_kernel_rfl

private theorem pattern_sizes : ∀ index : Fin 64, (periodicValues (blockAt index)).size = 64 := by decide +kernel
private theorem pattern_cells_part_0 : ∀ high : Fin 8, ∀ low : Fin 64,
    (blockAt ⟨high.val + 8 * 0, by omega⟩).get? low.val =
      some (((high.val + 8 * 0) ^^^ low.val) * 4) := by decide +kernel

private theorem pattern_cells_part_1 : ∀ high : Fin 8, ∀ low : Fin 64,
    (blockAt ⟨high.val + 8 * 1, by omega⟩).get? low.val =
      some (((high.val + 8 * 1) ^^^ low.val) * 4) := by decide +kernel

private theorem pattern_cells_part_2 : ∀ high : Fin 8, ∀ low : Fin 64,
    (blockAt ⟨high.val + 8 * 2, by omega⟩).get? low.val =
      some (((high.val + 8 * 2) ^^^ low.val) * 4) := by decide +kernel

private theorem pattern_cells_part_3 : ∀ high : Fin 8, ∀ low : Fin 64,
    (blockAt ⟨high.val + 8 * 3, by omega⟩).get? low.val =
      some (((high.val + 8 * 3) ^^^ low.val) * 4) := by decide +kernel

private theorem pattern_cells_part_4 : ∀ high : Fin 8, ∀ low : Fin 64,
    (blockAt ⟨high.val + 8 * 4, by omega⟩).get? low.val =
      some (((high.val + 8 * 4) ^^^ low.val) * 4) := by decide +kernel

private theorem pattern_cells_part_5 : ∀ high : Fin 8, ∀ low : Fin 64,
    (blockAt ⟨high.val + 8 * 5, by omega⟩).get? low.val =
      some (((high.val + 8 * 5) ^^^ low.val) * 4) := by decide +kernel

private theorem pattern_cells_part_6 : ∀ high : Fin 8, ∀ low : Fin 64,
    (blockAt ⟨high.val + 8 * 6, by omega⟩).get? low.val =
      some (((high.val + 8 * 6) ^^^ low.val) * 4) := by decide +kernel

private theorem pattern_cells_part_7 : ∀ high : Fin 8, ∀ low : Fin 64,
    (blockAt ⟨high.val + 8 * 7, by omega⟩).get? low.val =
      some (((high.val + 8 * 7) ^^^ low.val) * 4) := by decide +kernel

private theorem pattern_cells : ∀ high low : Fin 64,
    (blockAt high).get? low.val = some ((high.val ^^^ low.val) * 4) := by
  intro high low
  by_cases bucket0 : high.val / 8 = 0
  · have same : high.val % 8 + 8 * 0 = high.val := by omega
    simpa only [same] using pattern_cells_part_0 ⟨high.val % 8, Nat.mod_lt _ (by decide +kernel)⟩ low
  by_cases bucket1 : high.val / 8 = 1
  · have same : high.val % 8 + 8 * 1 = high.val := by omega
    simpa only [same] using pattern_cells_part_1 ⟨high.val % 8, Nat.mod_lt _ (by decide +kernel)⟩ low
  by_cases bucket2 : high.val / 8 = 2
  · have same : high.val % 8 + 8 * 2 = high.val := by omega
    simpa only [same] using pattern_cells_part_2 ⟨high.val % 8, Nat.mod_lt _ (by decide +kernel)⟩ low
  by_cases bucket3 : high.val / 8 = 3
  · have same : high.val % 8 + 8 * 3 = high.val := by omega
    simpa only [same] using pattern_cells_part_3 ⟨high.val % 8, Nat.mod_lt _ (by decide +kernel)⟩ low
  by_cases bucket4 : high.val / 8 = 4
  · have same : high.val % 8 + 8 * 4 = high.val := by omega
    simpa only [same] using pattern_cells_part_4 ⟨high.val % 8, Nat.mod_lt _ (by decide +kernel)⟩ low
  by_cases bucket5 : high.val / 8 = 5
  · have same : high.val % 8 + 8 * 5 = high.val := by omega
    simpa only [same] using pattern_cells_part_5 ⟨high.val % 8, Nat.mod_lt _ (by decide +kernel)⟩ low
  by_cases bucket6 : high.val / 8 = 6
  · have same : high.val % 8 + 8 * 6 = high.val := by omega
    simpa only [same] using pattern_cells_part_6 ⟨high.val % 8, Nat.mod_lt _ (by decide +kernel)⟩ low
  have same : high.val % 8 + 8 * 7 = high.val := by have bound := high.isLt; omega
  simpa only [same] using pattern_cells_part_7 ⟨high.val % 8, Nat.mod_lt _ (by decide +kernel)⟩ low

private theorem block_get (high : Fin 64) (offset : Fin 256) :
    (blockAt high).get? offset.val = some ((high.val ^^^ (offset.val % 64)) * 4) := by
  have size := pattern_sizes high
  have first := periodic_zero_get_mod (periodicValues (blockAt high)) 4 offset.val
    (by rw [size]; decide +kernel) (by decide +kernel) (by rw [size]; exact offset.isLt)
  rw [size] at first
  have a := congrArg (fun block : Block => block.get? offset.val) (shapes high)
  have b := congrArg (fun block : Block => block.get? (offset.val % 64)) (shapes high)
  exact (a.trans first).trans (b.symm.trans (pattern_cells high ⟨offset.val % 64, Nat.mod_lt _ (by decide +kernel)⟩))

/-- This source fragment uses all three original parse and coverage facts.
Eight checked periodic templates supply every row for shift two. -/
theorem source_split_low_two_get {artifact : Artifact}
    (parsed : parse SourceCaptureTheta.source = .ok artifact) (index : Fin 65536) :
    ((SourceCaptureTheta.columns[3]?).getD ({ blocks := #[] } : Column)).get? (196608 + index.val) =
      some (((index.val / 256 % 64) ^^^ (index.val % 64)) * 4) := by
  change sourceColumn.get? (196608 + index.val) = _
  rw [source_window parsed, window_shape, getFromBlocks_repeated _ _ _ (by
    rw [cycle_length]; exact index.isLt), uniform256_get _ cycle_lengths]
  have high : index.val % 16384 / 256 < cycleBlocks.length := by rw [cycle_count]; omega
  have selected : cycleBlocks[index.val % 16384 / 256]? = some (blockAt ⟨index.val % 16384 / 256, by omega⟩) := by
    simp only [blockAt, List.getElem?_eq_getElem high, Option.getD_some]
  rw [cycle_length, selected, Option.bind_some]
  have value := block_get ⟨index.val % 16384 / 256, by omega⟩ ⟨index.val % 16384 % 256, by omega⟩
  have quotient : index.val % 16384 / 256 = index.val / 256 % 64 := by omega
  have residue : index.val % 16384 % 256 % 64 = index.val % 64 := by omega
  simpa only [quotient, residue] using value

/-- The retained fragment equals the complete native low-fragment value. -/
theorem source_split_low_two_match {artifact : Artifact}
    (parsed : parse SourceCaptureTheta.source = .ok artifact) (index : Fin 65536) :
    (((SourceCaptureTheta.columns[3]?).getD ({ blocks := #[] } : Column)).get? (196608 + index.val)).getD 0 =
      (Airbender.Keccak.Split.Native.Fixed.thetaRhoXorSplit.columns[3]).value (131072 + index.val) := by
  rw [source_split_low_two_get parsed, Option.getD_some]
  have native := Airbender.Keccak.Split.Native.Fixed.Proofs.theta_fragment_low_value
    ⟨131072 + index.val, by change 131072 + index.val < 524288; have bound := index.isLt; omega⟩
  have shift : (131072 + index.val) / 65536 = 2 := by omega
  have high : (131072 + index.val) / 256 % 256 = index.val / 256 % 256 := by omega
  have low : (131072 + index.val) % 256 = index.val % 256 := by omega
  rw [shift, high, low] at native
  change _ = ((index.val / 256 % 256) ^^^ (index.val % 256)) * 4 % 256 at native
  rw [native]
  have reduced := Nat.mul_mod_mul_right 4 ((index.val / 256 % 256) ^^^ (index.val % 256)) 64
  have mask := Nat.xor_mod_two_pow (a := index.val / 256 % 256) (b := index.val % 256) (n := 6)
  change _ % 64 = _ at mask
  have hmod : index.val / 256 % 256 % 64 = index.val / 256 % 64 := by omega
  have lmod : index.val % 256 % 64 = index.val % 64 := by omega
  simpa only [mask, hmod, lmod] using reduced.symm

end Airbender.Setup.SourceCaptureThetaProofs
