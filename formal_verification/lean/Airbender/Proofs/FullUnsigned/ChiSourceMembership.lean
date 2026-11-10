import Airbender.Proofs.FullUnsigned.ChiSourceInputs
import Airbender.Proofs.FullUnsigned.ChiSourceOuterOutputs
import Airbender.Proofs.FullUnsigned.ChiSourceMiddleOutput
import Airbender.Proofs.FullUnsigned.ChiSourceLowOutput
import Airbender.Proofs.FullUnsigned.ChiSourceOutputOne
import Airbender.Proofs.FullUnsigned.ChiSourceController
import Airbender.Proofs.FullUnsigned.PaddingMembership

namespace Airbender.Setup.SourceCaptureChiProofs
open Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false

/-- Every arithmetic source field equals the original canonical field. -/
theorem source_arithmetic_columns (column : Fin 11) (index : Fin 1048576) :
    ((SourceCaptureChi.columns[column.val]?).getD ({ blocks := #[] } : Column)).get? index.val =
      Airbender.Keccak.Split.Native.Fixed.chi5Generic.columns[column.val].get? index.val := by
  fin_cases column
  · exact source_inputs_match (⟨0, by decide +kernel⟩ : Fin 5) index
  · exact source_inputs_match (⟨1, by decide +kernel⟩ : Fin 5) index
  · exact source_inputs_match (⟨2, by decide +kernel⟩ : Fin 5) index
  · exact source_inputs_match (⟨3, by decide +kernel⟩ : Fin 5) index
  · exact source_inputs_match (⟨4, by decide +kernel⟩ : Fin 5) index
  · exact source_output0_matches index
  · exact source_output1_matches index
  · exact source_output2_matches index
  · exact source_output3_matches index
  · exact source_output4_matches index
  · exact source_tag_matches index.val

/-- All arithmetic source rows equal their original generic-table rows. -/
theorem source_arithmetic_rows (index : Fin 1048576) :
    (Vector.ofFn fun column : Fin 11 => signedValue
      ((((SourceCaptureChi.columns[column.val]?).getD ({ blocks := #[] } : Column)).get? index.val).getD 0)) =
      Airbender.Keccak.Split.Native.Fixed.chi5Generic.row ⟨index.val, by
        change index.val < 1048697
        have bound := index.isLt
        omega⟩ := by
  apply Vector.ext
  intro column bound
  simp only [Vector.getElem_ofFn, TableData.row, Vector.getElem_map]
  change signedValue ((((SourceCaptureChi.columns[column]?).getD ({ blocks := #[] } : Column)).get? index.val).getD 0) =
    signedValue ((Airbender.Keccak.Split.Native.Fixed.chi5Generic.columns[column].get? (0 + index.val)).getD 0)
  rw [Nat.zero_add]
  exact congrArg (fun value : Option Nat => signedValue (value.getD 0))
    (source_arithmetic_columns ⟨column, bound⟩ index)

end Airbender.Setup.SourceCaptureChiProofs

namespace Airbender.Compiler.MachineTargets.Proofs
open Airbender.Setup
set_option warningAsError true
set_option Elab.async false

/-- Parsing supplies canonical membership for every arithmetic source row.
The parse, column shape and complete row values stay explicit. -/
theorem chi_source_arithmetic_member [Fact babyBearModulus.Prime] {artifact : Artifact}
    (parsed : parse SourceCaptureChi.source = .ok artifact) (_shape : artifact.columns.size = 11)
    (index : Fin artifact.trace_len) (upper : index.val < 1048576) (row : Vector F 11)
    (values : ∀ column : Fin 11,
      row[column] = (signedValue
        ((((artifact.columns[column.val]?).getD ⟨#[]⟩).get? index.val).getD 0) : F)) :
    (Keccak.Split.Native.Fixed.chi5Generic.table "Airbender.SplitChi5Generic").toRaw.Contains #[] row := by
  have decoded := fields_of_parse SourceCaptureChiProofs.parsed parsed
  have sameColumns : artifact.columns = SourceCaptureChi.columns :=
    Except.ok.inj (decoded.2.symm.trans SourceCaptureChiProofs.columns_decoded)
  have sameRow : row = (Vector.ofFn (fun column : Fin 11 =>
      signedValue ((((SourceCaptureChi.columns[column.val]?).getD ⟨#[]⟩).get? index.val).getD 0))).map
      (fun value : Int => (value : F)) := by
    apply Vector.ext
    intro column bound
    simpa only [Vector.getElem_map, Vector.getElem_ofFn, Fin.getElem_fin, sameColumns]
      using values ⟨column, bound⟩
  change ∃ nativeIndex : Fin Keccak.Split.Native.Fixed.chi5Generic.length,
    row = (Keccak.Split.Native.Fixed.chi5Generic.row nativeIndex).map (fun value : Int => (value : F))
  refine ⟨⟨index.val, by change index.val < 1048697; omega⟩, ?_⟩
  rw [sameRow]
  exact congrArg (fun actual : Vector Int 11 => actual.map (fun value : Int => (value : F)))
    (SourceCaptureChiProofs.source_arithmetic_rows ⟨index.val, upper⟩)

/-- The complete real chi5 source-row obligation is closed. -/
theorem split_chi_real_rows : SplitChiRealRows := by
  intro prime artifact parsed shape row index bound values
  by_cases arithmetic : index.val < 1048576
  · exact chi_source_arithmetic_member parsed shape index arithmetic row values
  · exact chi_source_controller_member parsed shape index (Nat.le_of_not_gt arithmetic) bound row values

/-- Native tags restrict source lookups to the proved arithmetic and controller rows. -/
theorem chi_source_rows [Fact babyBearModulus.Prime] :
    GuardedSetupRows SourceCaptureChi.source
      (Keccak.Split.Native.Fixed.chi5Generic.table "Airbender.SplitChi5Generic")
      (fun row => row[10] = 65 ∨ row[10] = 66) :=
  chi_source_rows_of_real_range split_chi_real_rows

end Airbender.Compiler.MachineTargets.Proofs
