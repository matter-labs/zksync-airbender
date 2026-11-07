import Airbender.Proofs.FullUnsigned.ThetaSourceXorInputs
import Airbender.Proofs.FullUnsigned.ThetaSourceXorOutput
import Airbender.Data.Setup.Keccak.ThetaRhoPhysical
import Airbender.Proofs.FullUnsigned.CapturedSetup

namespace Airbender.Setup.SourceCaptureThetaProofs
set_option warningAsError true
set_option Elab.async false

/-- Every byte-XOR source field equals its original native literal-tree field. -/
theorem source_xor_columns_match (column : Fin 9) (index : Fin 65536) :
    (((SourceCaptureTheta.columns[column.val]?).getD ({ blocks := #[] } : Column)).get? index.val).getD 0 =
      (Airbender.Keccak.Split.Native.Fixed.thetaRhoXor.columns[column.val]).value index.val := by
  fin_cases column
  · exact source_xor_keys_match (⟨0, by decide +kernel⟩ : Fin 2) index
  · exact source_xor_keys_match (⟨1, by decide +kernel⟩ : Fin 2) index
  · exact source_xor_output_match index
  · have source := source_xor_padding_get (⟨0, by decide +kernel⟩ : Fin 5) index
    have native := Airbender.Keccak.Split.Native.Fixed.Proofs.xor_byte_padding_value
      (⟨0, by decide +kernel⟩ : Fin 5) index.val
    change ((SourceCaptureTheta.columns[3]?).getD ({ blocks := #[] } : Column)).get? index.val = some 0 at source
    change (Airbender.Keccak.Split.Native.Fixed.thetaRhoXor.columns[3]).value index.val = 0 at native
    exact (congrArg (fun value : Option Nat => value.getD 0) source).trans native.symm
  · have source := source_xor_padding_get (⟨1, by decide +kernel⟩ : Fin 5) index
    have native := Airbender.Keccak.Split.Native.Fixed.Proofs.xor_byte_padding_value
      (⟨1, by decide +kernel⟩ : Fin 5) index.val
    change ((SourceCaptureTheta.columns[4]?).getD ({ blocks := #[] } : Column)).get? index.val = some 0 at source
    change (Airbender.Keccak.Split.Native.Fixed.thetaRhoXor.columns[4]).value index.val = 0 at native
    exact (congrArg (fun value : Option Nat => value.getD 0) source).trans native.symm
  · have source := source_xor_padding_get (⟨2, by decide +kernel⟩ : Fin 5) index
    have native := Airbender.Keccak.Split.Native.Fixed.Proofs.xor_byte_padding_value
      (⟨2, by decide +kernel⟩ : Fin 5) index.val
    change ((SourceCaptureTheta.columns[5]?).getD ({ blocks := #[] } : Column)).get? index.val = some 0 at source
    change (Airbender.Keccak.Split.Native.Fixed.thetaRhoXor.columns[5]).value index.val = 0 at native
    exact (congrArg (fun value : Option Nat => value.getD 0) source).trans native.symm
  · have source := source_xor_padding_get (⟨3, by decide +kernel⟩ : Fin 5) index
    have native := Airbender.Keccak.Split.Native.Fixed.Proofs.xor_byte_padding_value
      (⟨3, by decide +kernel⟩ : Fin 5) index.val
    change ((SourceCaptureTheta.columns[6]?).getD ({ blocks := #[] } : Column)).get? index.val = some 0 at source
    change (Airbender.Keccak.Split.Native.Fixed.thetaRhoXor.columns[6]).value index.val = 0 at native
    exact (congrArg (fun value : Option Nat => value.getD 0) source).trans native.symm
  · have source := source_xor_padding_get (⟨4, by decide +kernel⟩ : Fin 5) index
    have native := Airbender.Keccak.Split.Native.Fixed.Proofs.xor_byte_padding_value
      (⟨4, by decide +kernel⟩ : Fin 5) index.val
    change ((SourceCaptureTheta.columns[7]?).getD ({ blocks := #[] } : Column)).get? index.val = some 0 at source
    change (Airbender.Keccak.Split.Native.Fixed.thetaRhoXor.columns[7]).value index.val = 0 at native
    exact (congrArg (fun value : Option Nat => value.getD 0) source).trans native.symm
  · exact (congrArg (fun value : Option Nat => value.getD 0) (source_xor_tag_get index)).trans
      (Airbender.Keccak.Split.Native.Fixed.Proofs.xor_byte_tag_value index.val).symm

/-- All byte-XOR source rows equal their original native literal-tree rows. -/
theorem source_xor_rows (index : Fin 65536) :
    (Vector.ofFn fun column : Fin 9 => signedValue
      ((((SourceCaptureTheta.columns[column.val]?).getD ({ blocks := #[] } : Column)).get? index.val).getD 0)) =
      (Airbender.Keccak.Split.Native.Fixed.thetaRhoXor.row ⟨index.val, by
        change index.val < 65536; exact index.isLt⟩).map signedValue := by
  apply Vector.ext
  intro column bound
  simp only [Vector.getElem_ofFn, Vector.getElem_map, LiteralTree.Region.row]
  change signedValue _ = signedValue ((Airbender.Keccak.Split.Native.Fixed.thetaRhoXor.columns[column]).value index.val)
  exact congrArg signedValue (source_xor_columns_match ⟨column, bound⟩ index)

end Airbender.Setup.SourceCaptureThetaProofs

namespace Airbender.Compiler.MachineTargets.Proofs
open Airbender.Setup
set_option warningAsError true
set_option Elab.async false

/-- The complete byte-XOR source region has canonical physical-table membership. -/
theorem theta_source_xor_member [Fact babyBearModulus.Prime] {artifact : Artifact}
    (parsed : parse SourceCaptureTheta.source = .ok artifact) (_shape : artifact.columns.size = 9)
    (index : Fin artifact.trace_len) (upper : index.val < 65536) (row : Vector F 9)
    (values : ∀ column : Fin 9,
      row[column] = (signedValue
        ((((artifact.columns[column.val]?).getD ⟨#[]⟩).get? index.val).getD 0) : F)) :
    Keccak.Split.Native.Fixed.thetaRhoPhysicalGenericTable.toRaw.Contains #[] row := by
  have decoded := fields_of_parse SourceCaptureThetaProofs.parsed parsed
  have sameColumns : artifact.columns = SourceCaptureTheta.columns :=
    Except.ok.inj (decoded.2.symm.trans SourceCaptureThetaProofs.columns_decoded)
  have sameRow : row = (Vector.ofFn (fun column : Fin 9 =>
      signedValue ((((SourceCaptureTheta.columns[column.val]?).getD ⟨#[]⟩).get? index.val).getD 0))).map
      (fun value : Int => (value : F)) := by
    apply Vector.ext
    intro column bound
    simpa only [Vector.getElem_map, Vector.getElem_ofFn, Fin.getElem_fin, sameColumns] using values ⟨column, bound⟩
  change ∃ nativeIndex : Fin Keccak.Split.Native.Fixed.thetaRhoPhysicalGenericLength,
    row = (Keccak.Split.Native.Fixed.thetaRhoPhysicalGenericRow nativeIndex).map (fun value : Int => (value : F))
  refine ⟨⟨index.val, by change index.val < 4194304; omega⟩, ?_⟩
  rw [sameRow]
  have canonical := SourceCaptureThetaProofs.source_xor_rows ⟨index.val, upper⟩
  have physical : Keccak.Split.Native.Fixed.thetaRhoPhysicalGenericRow ⟨index.val, by
      change index.val < 4194304; omega⟩ =
      (Keccak.Split.Native.Fixed.thetaRhoXor.row ⟨index.val, upper⟩).map signedValue := by
    simp only [Keccak.Split.Native.Fixed.thetaRhoPhysicalGenericRow, dif_pos upper]
  rw [physical]
  exact congrArg (fun actual : Vector Int 9 => actual.map (fun value : Int => (value : F))) canonical

end Airbender.Compiler.MachineTargets.Proofs
