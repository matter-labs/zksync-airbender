import Airbender.Proofs.FullUnsigned.ThetaLowSixSuffix
import Airbender.Proofs.FullUnsigned.SourceUniformCycles
import Airbender.Proofs.FullUnsigned.SourceColumnCoverage
import Airbender.Proofs.FullUnsigned.ThetaSourceLowZero
import Airbender.Proofs.Keccak.SplitThetaFragmentValues

namespace Airbender.Setup.SourceCaptureThetaProofs
open Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
-- One short periodic template covers this complete shift case.
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private noncomputable def sourceColumn : Column := (SourceCaptureTheta.columns[3]?).getD ⟨#[]⟩
private noncomputable def binding : SourceBank.ColumnBinding :=
  (SourceCaptureTheta.columnBindings[3]'(by change 3 < 9; decide +kernel)).1
private noncomputable def tailBlocks : List Block := ThetaLowSixSuffix.entries.map binding.blocks
private def patternArray : Array Nat :=
  (List.ofFn fun index : Fin 1024 => ((index.val / 256 % 4) ^^^ (index.val % 4)) * 64).toArray

private theorem source_column_binding : sourceColumn = binding.column := by
  simp only [binding, SourceCaptureTheta.columnBindings, List.getElem_cons_zero, List.getElem_cons_succ]
  rfl

private theorem binding_entries : binding.entries = SourceCaptureTheta.entries_9296 := by
  simp only [binding, SourceCaptureTheta.columnBindings, List.getElem_cons_zero, List.getElem_cons_succ]
  low_source_kernel_rfl

private theorem binding_tail (b : SourceBank.ColumnBinding) (first : Nat) :
    b.column.blocks.toList.drop first = (b.entries.drop first).map b.blocks := by
  simp only [SourceBank.ColumnBinding.column, List.toList_toArray, ← List.map_drop]

private theorem source_suffix : sourceColumn.blocks.toList.drop ThetaLowSixSuffix.skip = tailBlocks := by
  refine (congrArg (fun column : Column => column.blocks.toList.drop ThetaLowSixSuffix.skip) source_column_binding).trans ?_
  refine (binding_tail binding ThetaLowSixSuffix.skip).trans ?_
  apply congrArg (List.map binding.blocks)
  exact (congrArg (List.drop ThetaLowSixSuffix.skip) binding_entries).trans ThetaLowSixSuffix.matches

private theorem tail_length : (tailBlocks.map Block.length).sum = 3735552 := by low_source_kernel_rfl
private theorem pattern_size : patternArray.size = 1024 := by
  simp only [patternArray, List.size_toArray, List.length_ofFn]

private theorem pattern_get (index : Fin 1024) :
    patternArray[index.val]'(by rw [pattern_size]; exact index.isLt) =
      ((index.val / 256 % 4) ^^^ (index.val % 4)) * 64 := by
  simp only [patternArray, List.getElem_toArray, List.getElem_ofFn]

private theorem window_shape : tailBlocks.take 1 = [.periodic 64 0 patternArray] := by low_source_kernel_rfl
private theorem window_length : ((tailBlocks.take 1).map Block.length).sum = 65536 := by
  rw [window_shape]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Block.length, pattern_size, Nat.add_zero]

private theorem source_covered {artifact : Artifact} (parsed : parse SourceCaptureTheta.source = .ok artifact) :
    (sourceColumn.blocks.toList.map Block.length).sum = 4194304 := by
  have bound : 3 < SourceCaptureTheta.columns.size := by change 3 < 9; decide +kernel
  have member : sourceColumn ∈ SourceCaptureTheta.columns := by
    unfold sourceColumn
    rw [Array.getElem?_eq_getElem bound, Option.getD_some]
    simp
  exact source_column_lengths SourceCaptureThetaProofs.parsed trace_len_decoded columns_decoded parsed _ member

private theorem source_window {artifact : Artifact} (parsed : parse SourceCaptureTheta.source = .ok artifact)
    (index : Fin 65536) : sourceColumn.get? (458752 + index.val) = getFromBlocks (tailBlocks.take 1) index.val := by
  have selected := column_suffix_get sourceColumn ThetaLowSixSuffix.skip 4194304 (458752 + index.val)
    (source_covered parsed) (by rw [source_suffix, tail_length]; omega)
  rw [source_suffix, tail_length] at selected
  have offset : 458752 + index.val - (4194304 - 3735552) = index.val := by omega
  rw [offset] at selected
  exact selected.trans (getFromBlocks_take _ _ _ (by rw [window_length]; exact index.isLt))

/-- The stored periodic template proves every source low fragment for shift six. -/
theorem source_split_low_six_get {artifact : Artifact}
    (parsed : parse SourceCaptureTheta.source = .ok artifact) (index : Fin 65536) :
    ((SourceCaptureTheta.columns[3]?).getD ({ blocks := #[] } : Column)).get? (458752 + index.val) =
      some (((index.val / 256 % 4) ^^^ (index.val % 4)) * 64) := by
  change sourceColumn.get? (458752 + index.val) = _
  rw [source_window parsed, window_shape, getFromBlocks]
  have bound : index.val < (Block.periodic 64 0 patternArray).length := by
    rw [Block.length, pattern_size]
    exact index.isLt
  rw [if_pos bound]
  have sampled := periodic_get patternArray 64 0 index.val (by rw [pattern_size]; decide +kernel)
    (by rw [pattern_size]; exact index.isLt)
  simp only [Int.natCast_zero, Nat.zero_mul, Nat.add_zero, pattern_size] at sampled
  rw [pattern_get ⟨index.val % 1024, Nat.mod_lt _ (by decide +kernel)⟩] at sampled
  have high : index.val % 1024 / 256 % 4 = index.val / 256 % 4 := by omega
  have low : index.val % 1024 % 4 = index.val % 4 := by omega
  simpa only [high, low] using sampled

/-- The retained fragment equals the complete native low-fragment value. -/
theorem source_split_low_six_match {artifact : Artifact}
    (parsed : parse SourceCaptureTheta.source = .ok artifact) (index : Fin 65536) :
    (((SourceCaptureTheta.columns[3]?).getD ({ blocks := #[] } : Column)).get? (458752 + index.val)).getD 0 =
      (Airbender.Keccak.Split.Native.Fixed.thetaRhoXorSplit.columns[3]).value (393216 + index.val) := by
  rw [source_split_low_six_get parsed, Option.getD_some]
  have native := Airbender.Keccak.Split.Native.Fixed.Proofs.theta_fragment_low_value
    ⟨393216 + index.val, by change 393216 + index.val < 524288; have bound := index.isLt; omega⟩
  have shift : (393216 + index.val) / 65536 = 6 := by omega
  have high : (393216 + index.val) / 256 % 256 = index.val / 256 % 256 := by omega
  have low : (393216 + index.val) % 256 = index.val % 256 := by omega
  rw [shift, high, low] at native
  change _ = ((index.val / 256 % 256) ^^^ (index.val % 256)) * 64 % 256 at native
  rw [native]
  have reduced := Nat.mul_mod_mul_right 64 ((index.val / 256 % 256) ^^^ (index.val % 256)) 4
  have mask := Nat.xor_mod_two_pow (a := index.val / 256 % 256) (b := index.val % 256) (n := 2)
  change _ % 4 = _ at mask
  have hmod : index.val / 256 % 256 % 4 = index.val / 256 % 4 := by omega
  have lmod : index.val % 256 % 4 = index.val % 4 := by omega
  simpa only [mask, hmod, lmod] using reduced.symm


end Airbender.Setup.SourceCaptureThetaProofs
