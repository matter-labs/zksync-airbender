import Airbender.Review.Compiler.SplitPhysicalRows
import Airbender.Proofs.Keccak.SplitChiTagDomain
import Airbender.Proofs.FullUnsigned.CapturedSetup

namespace Airbender.Compiler.MachineTargets.Proofs
open Airbender.Setup
set_option warningAsError true
set_option Elab.async false
variable [Fact babyBearModulus.Prime]

omit [Fact babyBearModulus.Prime] in
private theorem source_tag_column : SourceCaptureChi.columns[10]? =
    some ⟨#[.affine 1048576 65 0, .affine 121 66 0, .affine 3145607 0 0]⟩ := by
  setup_source_rfl

/-- A native chi5 tag excludes every padding index in the captured source. -/
theorem chi_source_query_index (index : Fin SourceCaptureChi.traceLength)
    (tag :
      (signedValue ((((SourceCaptureChi.columns[10]?).getD ({ blocks := #[] } : Column)).get? index.val).getD 0) : F) = 65 ∨
      (signedValue ((((SourceCaptureChi.columns[10]?).getD ({ blocks := #[] } : Column)).get? index.val).getD 0) : F) = 66) :
    index.val < 1048697 := by
  by_contra outside
  have lower : 1048697 ≤ index.val := by omega
  have upper : index.val < 4194304 := index.isLt
  have zero :
      ((((SourceCaptureChi.columns[10]?).getD ({ blocks := #[] } : Column)).get? index.val).getD 0) = 0 := by
    rw [source_tag_column]
    simp only [Option.getD_some, Column.get?, getFromBlocks, Block.length, Block.get?]
    split_ifs <;> simp_all only [zero_mul, add_zero, Int.toNat_natCast, Option.getD_some, Option.getD_none] <;> omega
  rw [zero] at tag
  simp only [signedValue_cast] at tag
  rcases tag with tag | tag
  · have value := congrArg ZMod.val tag
    change 0 = 65 at value
    omega
  · have value := congrArg ZMod.val tag
    change 0 = 66 at value
    omega

/-- Only real chi5 rows remain once native tags exclude source padding. -/
theorem chi_queried_rows_of_real
    (realRows : PhysicalRows SourceCaptureChi.columns 1048697
      (Keccak.Split.Native.Fixed.chi5Generic.table "Airbender.SplitChi5Generic"))
    (index : Fin SourceCaptureChi.traceLength)
    (tag :
      (signedValue ((((SourceCaptureChi.columns[10]?).getD ({ blocks := #[] } : Column)).get? index.val).getD 0) : F) = 65 ∨
      (signedValue ((((SourceCaptureChi.columns[10]?).getD ({ blocks := #[] } : Column)).get? index.val).getD 0) : F) = 66) :
    (Keccak.Split.Native.Fixed.chi5Generic.table "Airbender.SplitChi5Generic").toRaw.Contains #[]
      (Vector.ofFn fun column : Fin 11 =>
        (signedValue ((((SourceCaptureChi.columns[column.val]?).getD ⟨#[]⟩).get? index.val).getD 0) : F)) :=
  realRows ⟨index.val, chi_source_query_index index tag⟩

/-- The original parsed-source premise supplies all fields of the guarded
certificate. No source validation or padding assumption is added. -/
theorem chi_source_rows_of_real
    (realRows : PhysicalRows SourceCaptureChi.columns 1048697
      (Keccak.Split.Native.Fixed.chi5Generic.table "Airbender.SplitChi5Generic")) :
    GuardedSetupRows SourceCaptureChi.source
      (Keccak.Split.Native.Fixed.chi5Generic.table "Airbender.SplitChi5Generic")
      (fun row => row[10] = 65 ∨ row[10] = 66) := by
  intro artifact parsed _ row member tag
  have decoded := fields_of_parse SourceCaptureChiProofs.parsed parsed
  have sameLength : artifact.trace_len = SourceCaptureChi.traceLength :=
    Except.ok.inj (decoded.1.symm.trans SourceCaptureChiProofs.trace_len_decoded)
  have sameColumns : artifact.columns = SourceCaptureChi.columns :=
    Except.ok.inj (decoded.2.symm.trans SourceCaptureChiProofs.columns_decoded)
  obtain ⟨index, values⟩ := member
  let physical : Fin SourceCaptureChi.traceLength := ⟨index.val, sameLength ▸ index.isLt⟩
  have sameRow : row = Vector.ofFn (fun column : Fin 11 =>
      (signedValue ((((SourceCaptureChi.columns[column.val]?).getD ⟨#[]⟩).get? physical.val).getD 0) : F)) := by
    apply Vector.ext
    intro column bound
    simpa only [Vector.getElem_ofFn, sameColumns, Fin.getElem_fin, physical]
      using values ⟨column, bound⟩
  rw [sameRow] at tag ⊢
  exact chi_queried_rows_of_real realRows physical (by
    simpa only [Vector.getElem_ofFn, Fin.getElem_fin] using tag)

end Airbender.Compiler.MachineTargets.Proofs
