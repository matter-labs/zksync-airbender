import Airbender.Proofs.FullUnsigned.SourceColumnRanges
import Airbender.Proofs.FullUnsigned.Source.Chi
import Airbender.Proofs.Keccak.SplitChiInputs
import Airbender.Proofs.Tables.PeriodicColumns

namespace Airbender.Setup.SourceCaptureChiProofs
open Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
-- The retained input prefixes contain at most 256 blocks.
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private def prefixCount (column : Fin 5) : Nat :=
  if column.val < 2 then 1 else if column.val = 4 then 16 else 256

private noncomputable def inputBlocks (column : Fin 5) : List Block :=
  (((SourceCaptureChi.columns[column.val]?).getD ⟨#[]⟩).blocks.toList).take (prefixCount column)

private theorem prefix_length (column : Fin 5) :
    ((inputBlocks column).map Block.length).sum = 1048576 := by
  fin_cases column <;> setup_source_rfl

private theorem source_prefix (column : Fin 5) (index : Fin 1048576) :
    ((SourceCaptureChi.columns[column.val]?).getD ⟨#[]⟩).get? index.val =
      getFromBlocks (inputBlocks column) index.val := by
  apply getFromBlocks_take
  change index.val < ((inputBlocks column).map Block.length).sum
  rw [prefix_length]
  exact index.isLt

private theorem prefix0 : inputBlocks 0 = [.periodic 65536 0 (Array.range 16)] := by
  setup_source_rfl

private theorem prefix1 : inputBlocks 1 =
    [.periodic 4096 0 (Array.ofFn fun index : Fin 256 => index.val / 16)] := by
  setup_source_rfl

private theorem prefix2 : inputBlocks 2 =
    List.replicate 256 (.periodic 16 1 (Array.replicate 256 0)) := by
  setup_source_rfl

private theorem prefix3 : inputBlocks 3 =
    (List.range 256).map (fun index => .affine 4096 (index % 16) 0) := by
  setup_source_rfl

private theorem prefix4 : inputBlocks 4 =
    (List.range 16).map (fun index => .affine 65536 index 0) := by
  setup_source_rfl

/-- The five parsed source input columns contain the exact native digits. -/
theorem source_input_get (column : Fin 5) (index : Fin 1048576) :
    ((SourceCaptureChi.columns[column.val]?).getD ⟨#[]⟩).get? index.val =
      some (index.val / 16 ^ column.val % 16) := by
  rw [source_prefix]
  fin_cases column
  · change getFromBlocks (inputBlocks 0) index.val = some (index.val / 16 ^ 0 % 16)
    rw [prefix0, getFromBlocks, if_pos (show index.val < Block.length (.periodic 65536 0 (Array.range 16)) by
      simpa only [Block.length, Array.size_range] using index.isLt)]
    simpa using periodic_get (Array.range 16) 65536 0 index.val (by simp)
      (by simpa only [Array.size_range] using index.isLt)
  · change getFromBlocks (inputBlocks 1) index.val = some (index.val / 16 ^ 1 % 16)
    rw [prefix1, getFromBlocks, if_pos (show index.val < Block.length
        (.periodic 4096 0 (Array.ofFn fun index : Fin 256 => index.val / 16)) by
      simpa only [Block.length, Array.size_ofFn] using index.isLt)]
    have sampled := periodic_get (Array.ofFn fun index : Fin 256 => index.val / 16)
      4096 0 index.val (by simp) (by simpa only [Array.size_ofFn] using index.isLt)
    have position : index.val % 256 / 16 = index.val / 16 % 16 := by omega
    simpa [position] using sampled
  · change getFromBlocks (inputBlocks 2) index.val = some (index.val / 16 ^ 2 % 16)
    rw [prefix2]
    rw [uniform4096_get _ (by simp [Block.length])]
    have blockBound : index.val / 4096 < 256 := by omega
    simp only [List.getElem?_replicate, blockBound, ↓reduceIte, Option.bind_some]
    have sampled := periodic_get (Array.replicate 256 0) 16 1 (index.val % 4096)
      (by simp) (by have := Nat.mod_lt index.val (by decide : 0 < 4096); simpa using this)
    have position : index.val % 4096 / 256 = index.val / 256 % 16 := by omega
    simpa [position] using sampled
  · change getFromBlocks (inputBlocks 3) index.val = some (index.val / 16 ^ 3 % 16)
    rw [prefix3]
    rw [uniform4096_get _ (by simp [List.mem_map, Block.length])]
    have blockBound : index.val / 4096 < 256 := by omega
    simp only [List.getElem?_map, List.getElem?_range, blockBound,
      Option.map_some, Option.bind_some]
    rw [constant_affine_get _ _ _ (Nat.mod_lt _ (by decide : 0 < 4096))]
    norm_num only [Nat.reducePow]
  · change getFromBlocks (inputBlocks 4) index.val = some (index.val / 16 ^ 4 % 16)
    rw [prefix4]
    rw [uniform65536_get _ (by simp [List.mem_map, Block.length])]
    have blockBound : index.val / 65536 < 16 := by omega
    simp only [List.getElem?_map, List.getElem?_range, blockBound,
      Option.map_some, Option.bind_some]
    rw [constant_affine_get _ _ _ (Nat.mod_lt _ (by decide : 0 < 65536))]
    norm_num only [Nat.reducePow]
    rw [Nat.mod_eq_of_lt blockBound]

/-- Each source input field matches the unchanged canonical table column. -/
theorem source_inputs_match (column : Fin 5) (index : Fin 1048576) :
    ((SourceCaptureChi.columns[column.val]?).getD ⟨#[]⟩).get? index.val =
      Airbender.Keccak.Split.Native.Fixed.chi5Generic.columns[column.val].get? index.val := by
  rw [source_input_get, Airbender.Keccak.Split.Native.Fixed.Proofs.chi5_input_get]

/-- The retained tag column equals the original canonical tag column. -/
theorem source_tag_column : SourceCaptureChi.columns[10]? =
    some (Airbender.Keccak.Split.Native.Fixed.chi5Generic.columns[10]) := by
  have source : SourceCaptureChi.columns[10]? =
      some (⟨#[.affine 1048576 65 0, .affine 121 66 0, .affine 3145607 0 0]⟩ : Column) := by
    setup_source_rfl
  have native : Airbender.Keccak.Split.Native.Fixed.chi5Generic.columns[10] =
      ⟨#[.affine 1048576 65 0, .affine 121 66 0, .affine 3145607 0 0]⟩ := by rfl
  rw [native]
  exact source

theorem source_tag_matches (index : Nat) :
    ((SourceCaptureChi.columns[10]?).getD ({ blocks := #[] } : Column)).get? index =
      Airbender.Keccak.Split.Native.Fixed.chi5Generic.columns[10].get? index := by
  rw [source_tag_column]
  rfl

end Airbender.Setup.SourceCaptureChiProofs
