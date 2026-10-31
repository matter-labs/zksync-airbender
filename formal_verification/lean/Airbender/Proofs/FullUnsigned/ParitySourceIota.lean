import Airbender.Proofs.FullUnsigned.ParitySourcePrefixRead
import Airbender.Data.Setup.Keccak.ColumnParityGeneric
import Airbender.Proofs.FullUnsigned.CapturedSetup

namespace Airbender.Setup.SourceCaptureParityProofs
open Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private def initialCount (column : Fin 8) : Nat := if column.val = 2 then 106 else 1
private noncomputable def initialBlocks (column : Fin 8) : List Block := (prefixBlocks column).take (initialCount column)
private theorem initial_covers : ∀ column : Fin 8, 65536 ≤ ((initialBlocks column).map Block.length).sum := by decide +kernel
private theorem source_initial_get (column : Fin 8) (index : Fin 65536) :
    ((SourceCaptureParity.columns[column.val]?).getD ({ blocks := #[] } : Column)).get? index.val =
      getFromBlocks (initialBlocks column) index.val := by
  rw [source_prefix_get column ⟨index.val, by omega⟩]
  change getFromBlocks (prefixBlocks column) index.val = _
  exact getFromBlocks_take _ _ _ (by
    change index.val < ((initialBlocks column).map Block.length).sum
    exact lt_of_lt_of_le index.isLt (initial_covers column))

private def nonzeroColumn (column : Fin 4) : Fin 8 := if column.val = 3 then ⟨7, by decide +kernel⟩ else ⟨column.val, by omega⟩
private theorem same_blocks (column : Fin 4) : initialBlocks (nonzeroColumn column) =
    Airbender.Keccak.Split.Native.Fixed.columnParityIota.columns[(nonzeroColumn column).val].blocks.toList := by
  fin_cases column <;> setup_source_rfl
private theorem zero_blocks : ∀ column : Fin 4,
    initialBlocks ⟨3 + column.val, by omega⟩ = [.affine 65537 0 0] := by decide +kernel
private theorem native_zero_blocks : ∀ column : Fin 4,
    Airbender.Keccak.Split.Native.Fixed.columnParityIota.columns[3 + column.val].blocks.toList = [.affine 65536 0 0] := by decide +kernel

/-- Every original byte-iota source field equals its unchanged native field. -/
theorem source_iota_columns (column : Fin 8) (index : Fin 65536) :
    ((SourceCaptureParity.columns[column.val]?).getD ({ blocks := #[] } : Column)).get? index.val =
      Airbender.Keccak.Split.Native.Fixed.columnParityIota.columns[column.val].get? index.val := by
  rw [source_initial_get]
  fin_cases column
  · have same := same_blocks (⟨0, by decide +kernel⟩ : Fin 4)
    change initialBlocks ⟨0, by decide +kernel⟩ = Airbender.Keccak.Split.Native.Fixed.columnParityIota.columns[0].blocks.toList at same
    change _ = getFromBlocks _ index.val
    rw [same]
  · have same := same_blocks (⟨1, by decide +kernel⟩ : Fin 4)
    change initialBlocks ⟨1, by decide +kernel⟩ = Airbender.Keccak.Split.Native.Fixed.columnParityIota.columns[1].blocks.toList at same
    change _ = getFromBlocks _ index.val
    rw [same]
  · have same := same_blocks (⟨2, by decide +kernel⟩ : Fin 4)
    change initialBlocks ⟨2, by decide +kernel⟩ = Airbender.Keccak.Split.Native.Fixed.columnParityIota.columns[2].blocks.toList at same
    change _ = getFromBlocks _ index.val
    rw [same]
  · have same := zero_blocks (⟨0, by decide +kernel⟩ : Fin 4)
    have native := native_zero_blocks (⟨0, by decide +kernel⟩ : Fin 4)
    change initialBlocks ⟨3, by decide +kernel⟩ = [.affine 65537 0 0] at same
    change Airbender.Keccak.Split.Native.Fixed.columnParityIota.columns[3].blocks.toList = [.affine 65536 0 0] at native
    change _ = getFromBlocks _ index.val
    rw [same, native]
    simp only [getFromBlocks, Block.length, if_pos (by omega : index.val < 65537), if_pos index.isLt]
    exact (constant_affine_get _ _ _ (by omega)).trans (constant_affine_get _ _ _ index.isLt).symm
  · have same := zero_blocks (⟨1, by decide +kernel⟩ : Fin 4)
    have native := native_zero_blocks (⟨1, by decide +kernel⟩ : Fin 4)
    change initialBlocks ⟨4, by decide +kernel⟩ = [.affine 65537 0 0] at same
    change Airbender.Keccak.Split.Native.Fixed.columnParityIota.columns[4].blocks.toList = [.affine 65536 0 0] at native
    change _ = getFromBlocks _ index.val
    rw [same, native]
    simp only [getFromBlocks, Block.length, if_pos (by omega : index.val < 65537), if_pos index.isLt]
    exact (constant_affine_get _ _ _ (by omega)).trans (constant_affine_get _ _ _ index.isLt).symm
  · have same := zero_blocks (⟨2, by decide +kernel⟩ : Fin 4)
    have native := native_zero_blocks (⟨2, by decide +kernel⟩ : Fin 4)
    change initialBlocks ⟨5, by decide +kernel⟩ = [.affine 65537 0 0] at same
    change Airbender.Keccak.Split.Native.Fixed.columnParityIota.columns[5].blocks.toList = [.affine 65536 0 0] at native
    change _ = getFromBlocks _ index.val
    rw [same, native]
    simp only [getFromBlocks, Block.length, if_pos (by omega : index.val < 65537), if_pos index.isLt]
    exact (constant_affine_get _ _ _ (by omega)).trans (constant_affine_get _ _ _ index.isLt).symm
  · have same := zero_blocks (⟨3, by decide +kernel⟩ : Fin 4)
    have native := native_zero_blocks (⟨3, by decide +kernel⟩ : Fin 4)
    change initialBlocks ⟨6, by decide +kernel⟩ = [.affine 65537 0 0] at same
    change Airbender.Keccak.Split.Native.Fixed.columnParityIota.columns[6].blocks.toList = [.affine 65536 0 0] at native
    change _ = getFromBlocks _ index.val
    rw [same, native]
    simp only [getFromBlocks, Block.length, if_pos (by omega : index.val < 65537), if_pos index.isLt]
    exact (constant_affine_get _ _ _ (by omega)).trans (constant_affine_get _ _ _ index.isLt).symm
  · have same := same_blocks (⟨3, by decide +kernel⟩ : Fin 4)
    change initialBlocks ⟨7, by decide +kernel⟩ = Airbender.Keccak.Split.Native.Fixed.columnParityIota.columns[7].blocks.toList at same
    change _ = getFromBlocks _ index.val
    rw [same]

/-- Complete byte-iota source rows equal their original native rows. -/
theorem source_iota_rows (index : Fin 65536) :
    (Vector.ofFn fun column : Fin 8 => signedValue
      ((((SourceCaptureParity.columns[column.val]?).getD ({ blocks := #[] } : Column)).get? index.val).getD 0)) =
      Airbender.Keccak.Split.Native.Fixed.columnParityIota.row ⟨index.val, by change index.val < 65536; exact index.isLt⟩ := by
  apply Vector.ext
  intro column bound
  simp only [Vector.getElem_ofFn, TableData.row, Vector.getElem_map]
  have offset : Airbender.Keccak.Split.Native.Fixed.columnParityIota.offset = 0 := by rfl
  simp only [offset, Nat.zero_add]
  change signedValue _ = signedValue ((Airbender.Keccak.Split.Native.Fixed.columnParityIota.columns[column].get? index.val).getD 0)
  exact congrArg (fun value : Option Nat => signedValue (value.getD 0)) (source_iota_columns ⟨column, bound⟩ index)

end Airbender.Setup.SourceCaptureParityProofs

namespace Airbender.Compiler.MachineTargets.Proofs
open Airbender.Setup
set_option warningAsError true
set_option Elab.async false

/-- Parsing supplies canonical membership for every byte-iota source row. -/
theorem parity_source_iota_member [Fact babyBearModulus.Prime] {artifact : Artifact}
    (parsed : parse SourceCaptureParity.source = .ok artifact) (_shape : artifact.columns.size = 8)
    (index : Fin artifact.trace_len) (upper : index.val < 65536) (row : Vector F 8)
    (values : ∀ column : Fin 8,
      row[column] = (signedValue
        ((((artifact.columns[column.val]?).getD ⟨#[]⟩).get? index.val).getD 0) : F)) :
    Keccak.Split.Native.Fixed.columnParityGenericTable.toRaw.Contains #[] row := by
  have decoded := fields_of_parse SourceCaptureParityProofs.parsed parsed
  have sameColumns : artifact.columns = SourceCaptureParity.columns :=
    Except.ok.inj (decoded.2.symm.trans SourceCaptureParityProofs.columns_decoded)
  have sameRow : row = (Vector.ofFn (fun column : Fin 8 =>
      signedValue ((((SourceCaptureParity.columns[column.val]?).getD ⟨#[]⟩).get? index.val).getD 0))).map
      (fun value : Int => (value : F)) := by
    apply Vector.ext
    intro column bound
    simpa only [Vector.getElem_map, Vector.getElem_ofFn, Fin.getElem_fin, sameColumns] using values ⟨column, bound⟩
  change ∃ nativeIndex : Fin Keccak.Split.Native.Fixed.columnParityGenericLength,
    row = (Keccak.Split.Native.Fixed.columnParityGenericRow nativeIndex).map (fun value : Int => (value : F))
  refine ⟨⟨index.val, by change index.val < 4194304; omega⟩, ?_⟩
  rw [sameRow]
  have canonical := SourceCaptureParityProofs.source_iota_rows ⟨index.val, upper⟩
  have physical : Keccak.Split.Native.Fixed.columnParityGenericRow ⟨index.val, by
      change index.val < 4194304; omega⟩ = Keccak.Split.Native.Fixed.columnParityIota.row ⟨index.val, upper⟩ := by
    simp only [Keccak.Split.Native.Fixed.columnParityGenericRow, dif_pos upper]
  rw [physical]
  exact congrArg (fun actual : Vector Int 8 => actual.map (fun value : Int => (value : F))) canonical

end Airbender.Compiler.MachineTargets.Proofs
