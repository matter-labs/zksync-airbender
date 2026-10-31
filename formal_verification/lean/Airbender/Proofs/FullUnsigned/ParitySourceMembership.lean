import Airbender.Proofs.FullUnsigned.ParitySourceXorInputs
import Airbender.Proofs.FullUnsigned.ParitySourceXorOutput
import Airbender.Proofs.FullUnsigned.ParitySourceIota
import Airbender.Proofs.FullUnsigned.ParitySourceControlSlots
import Airbender.Proofs.FullUnsigned.PaddingMembership

namespace Airbender.Setup.SourceCaptureParityProofs
set_option warningAsError true
set_option Elab.async false

/-- Every XOR-five source field equals its complete original native field. -/
theorem source_xor_columns_match (column : Fin 8) (index : Fin 1048576) :
    (((SourceCaptureParity.columns[column.val]?).getD ({ blocks := #[] } : Column)).get? (65780 + index.val)).getD 0 =
      (Airbender.Keccak.Split.Native.Fixed.columnParityXor5.columns[column.val]).value index.val := by
  fin_cases column
  · exact source_xor_keys_match (⟨0, by decide +kernel⟩ : Fin 5) index
  · exact source_xor_keys_match (⟨1, by decide +kernel⟩ : Fin 5) index
  · exact source_xor_keys_match (⟨2, by decide +kernel⟩ : Fin 5) index
  · exact source_xor_keys_match (⟨3, by decide +kernel⟩ : Fin 5) index
  · exact source_xor_keys_match (⟨4, by decide +kernel⟩ : Fin 5) index
  · exact source_xor_output_match index
  · exact source_xor_fixed_match (⟨0, by decide +kernel⟩ : Fin 2) index
  · exact source_xor_fixed_match (⟨1, by decide +kernel⟩ : Fin 2) index

/-- Every XOR-five source row equals its complete original native row. -/
theorem source_xor_rows (index : Fin 1048576) :
    (Vector.ofFn fun column : Fin 8 => signedValue
      ((((SourceCaptureParity.columns[column.val]?).getD ({ blocks := #[] } : Column)).get? (65780 + index.val)).getD 0)) =
      (Airbender.Keccak.Split.Native.Fixed.columnParityXor5.row ⟨index.val, by
        change index.val < 1048576; exact index.isLt⟩).map signedValue := by
  apply Vector.ext
  intro column bound
  simp only [Vector.getElem_ofFn, Vector.getElem_map, LiteralTree.Region.row]
  change signedValue _ = signedValue ((Airbender.Keccak.Split.Native.Fixed.columnParityXor5.columns[column]).value index.val)
  exact congrArg signedValue (source_xor_columns_match ⟨column, bound⟩ index)

end Airbender.Setup.SourceCaptureParityProofs

namespace Airbender.Compiler.MachineTargets.Proofs
open Airbender.Setup
set_option warningAsError true
set_option Elab.async false

/-- Parsing supplies original canonical membership for every XOR-five source row. -/
theorem parity_source_xor_member [Fact babyBearModulus.Prime] {artifact : Artifact}
    (parsed : parse SourceCaptureParity.source = .ok artifact) (_shape : artifact.columns.size = 8)
    (index : Fin artifact.trace_len) (lower : 65780 ≤ index.val) (upper : index.val < 1114356)
    (row : Vector F 8)
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
  let localIndex : Fin 1048576 := ⟨index.val - 65780, by omega⟩
  have position : 65780 + localIndex.val = index.val := by dsimp [localIndex]; omega
  have canonical := SourceCaptureParityProofs.source_xor_rows localIndex
  have physical : Keccak.Split.Native.Fixed.columnParityGenericRow ⟨index.val, by
      change index.val < 4194304; omega⟩ =
      (Keccak.Split.Native.Fixed.columnParityXor5.row ⟨index.val - 65780, by
        change index.val - 65780 < 1048576; omega⟩).map signedValue := by
    simp only [Keccak.Split.Native.Fixed.columnParityGenericRow,
      dif_neg (by omega : ¬ index.val < 65536), dif_neg (by omega : ¬ index.val < 65658),
      dif_neg (by omega : ¬ index.val < 65780), dif_pos upper]
  rw [physical]
  have reference := congrArg (fun actual : Vector Int 8 => actual.map (fun value : Int => (value : F))) canonical
  simpa only [position] using reference

/-- All real parity source rows have complete original canonical membership. -/
theorem split_parity_real_rows : SplitParityRealRows := by
  intro prime artifact parsed shape row index bound values
  by_cases iota : index.val < 65536
  · exact parity_source_iota_member parsed shape index iota row values
  · by_cases control : index.val < 65780
    · exact parity_source_control_slot_member parsed shape index (Nat.le_of_not_gt iota) control row values
    · exact parity_source_xor_member parsed shape index (Nat.le_of_not_gt control) bound row values

/-- All represented-source parity rows, including padding, have canonical membership. -/
theorem parity_source_rows [Fact babyBearModulus.Prime] :
    FixedSetupRows SourceCaptureParity.source Keccak.Split.Native.Fixed.columnParityGenericTable :=
  parity_source_rows_of_real_range split_parity_real_rows

end Airbender.Compiler.MachineTargets.Proofs
