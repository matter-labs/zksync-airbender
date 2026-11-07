import Airbender.Proofs.FullUnsigned.CapturedPadding
import Airbender.Review.Compiler.SplitRealRows

namespace Airbender.Compiler.MachineTargets.Proofs
open Airbender.Setup
set_option warningAsError true
set_option Elab.async false
variable [Fact babyBearModulus.Prime]

/-- Exact source cells determine the whole padding row. -/
theorem setup_row_zero_of_padding {artifact : Artifact} {width index : Nat}
    (shape : artifact.columns.size = width)
    (padding : ∀ column : Fin artifact.columns.size,
      artifact.columns[column].get? index = some 0)
    (row : Vector F width)
    (values : ∀ column : Fin width,
      row[column] = (signedValue
        ((((artifact.columns[column.val]?).getD ⟨#[]⟩).get? index).getD 0) : F)) :
    row = Vector.replicate width 0 := by
  apply Vector.ext
  intro column bound
  have columnBound : column < artifact.columns.size := by omega
  have value := values ⟨column, bound⟩
  have cell := padding ⟨column, columnBound⟩
  change artifact.columns[column].get? index = some 0 at cell
  simp only [Fin.getElem_fin, Array.getElem?_eq_getElem columnBound,
    Option.getD_some, cell, signedValue_cast] at value
  simpa only [Vector.getElem_replicate, Nat.cast_zero] using value

/-- The original parity reference includes its physical zero padding. -/
theorem parity_padding_row :
    Keccak.Split.Native.Fixed.columnParityGenericTable.toRaw.Contains #[] (Vector.replicate 8 (0 : F)) := by
  change ∃ index : Fin Keccak.Split.Native.Fixed.columnParityGenericLength,
    Vector.replicate 8 (0 : F) =
      (Keccak.Split.Native.Fixed.columnParityGenericRow index).map (fun value : Int => (value : F))
  refine ⟨⟨1114356, by decide +kernel⟩, ?_⟩
  simp [Keccak.Split.Native.Fixed.columnParityGenericRow]

/-- The original theta/rho reference includes its physical zero padding. -/
theorem theta_padding_row :
    Keccak.Split.Native.Fixed.thetaRhoPhysicalGenericTable.toRaw.Contains #[]
      (Vector.replicate 9 (0 : F)) := by
  change ∃ index : Fin Keccak.Split.Native.Fixed.thetaRhoPhysicalGenericLength,
    Vector.replicate 9 (0 : F) =
      (Keccak.Split.Native.Fixed.thetaRhoPhysicalGenericRow index).map (fun value : Int => (value : F))
  refine ⟨⟨590066, by decide +kernel⟩, ?_⟩
  simp [Keccak.Split.Native.Fixed.thetaRhoPhysicalGenericRow]

/-- Parsing and retained terminal blocks close parity padding membership. -/
theorem parity_source_padding_member {artifact : Artifact}
    (parsed : parse SourceCaptureParity.source = .ok artifact) (shape : artifact.columns.size = 8)
    (index : Fin artifact.trace_len) (lower : 1114356 ≤ index.val)
    (row : Vector F 8)
    (values : ∀ column : Fin 8,
      row[column] = (signedValue
        ((((artifact.columns[column.val]?).getD ⟨#[]⟩).get? index.val).getD 0) : F)) :
    Keccak.Split.Native.Fixed.columnParityGenericTable.toRaw.Contains #[] row := by
  rw [setup_row_zero_of_padding shape (SourceCaptureParityProofs.source_padding parsed index lower) row values]
  exact parity_padding_row

/-- Parsing and retained terminal blocks close theta/rho padding membership. -/
theorem theta_source_padding_member {artifact : Artifact}
    (parsed : parse SourceCaptureTheta.source = .ok artifact) (shape : artifact.columns.size = 9)
    (index : Fin artifact.trace_len) (lower : 590066 ≤ index.val)
    (row : Vector F 9)
    (values : ∀ column : Fin 9,
      row[column] = (signedValue
        ((((artifact.columns[column.val]?).getD ⟨#[]⟩).get? index.val).getD 0) : F)) :
    Keccak.Split.Native.Fixed.thetaRhoPhysicalGenericTable.toRaw.Contains #[] row := by
  rw [setup_row_zero_of_padding shape (SourceCaptureThetaProofs.source_padding parsed index lower) row values]
  exact theta_padding_row

/-- The parity padding case is closed. Only real source membership remains. -/
theorem parity_source_rows_of_real_range (realRows : SplitParityRealRows) :
    FixedSetupRows SourceCaptureParity.source Keccak.Split.Native.Fixed.columnParityGenericTable := by
  intro artifact parsed shape row member
  obtain ⟨index, values⟩ := member
  by_cases real : index.val < 1114356
  · exact realRows artifact parsed shape row index real values
  · exact parity_source_padding_member parsed shape index (Nat.le_of_not_gt real) row values

/-- The theta/rho padding case is closed. Only real source membership remains. -/
theorem theta_source_rows_of_real_range (realRows : SplitThetaRealRows) :
    FixedSetupRows SourceCaptureTheta.source Keccak.Split.Native.Fixed.thetaRhoPhysicalGenericTable := by
  intro artifact parsed shape row member
  obtain ⟨index, values⟩ := member
  by_cases real : index.val < 590066
  · exact realRows artifact parsed shape row index real values
  · exact theta_source_padding_member parsed shape index (Nat.le_of_not_gt real) row values

/-- Native query tags exclude chi5 padding. Only real source membership remains. -/
theorem chi_source_rows_of_real_range (realRows : SplitChiRealRows) :
    GuardedSetupRows SourceCaptureChi.source
      (Keccak.Split.Native.Fixed.chi5Generic.table "Airbender.SplitChi5Generic")
      (fun row => row[10] = 65 ∨ row[10] = 66) := by
  intro artifact parsed shape row member tag
  obtain ⟨index, values⟩ := member
  by_cases real : index.val < 1048697
  · exact realRows artifact parsed shape row index real values
  · have zero := setup_row_zero_of_padding shape
      (SourceCaptureChiProofs.source_padding parsed index (Nat.le_of_not_gt real)) row values
    rw [zero] at tag
    simp only [Vector.getElem_replicate] at tag
    rcases tag with tag | tag
    · have value := congrArg ZMod.val tag
      change 0 = 65 at value
      omega
    · have value := congrArg ZMod.val tag
      change 0 = 66 at value
      omega

end Airbender.Compiler.MachineTargets.Proofs
