import Airbender.Proofs.FullUnsigned.CapturedSetup
import Airbender.Proofs.FullUnsigned.SetupSourceTails

set_option warningAsError true
set_option Elab.async false
-- Literal metadata lists can hold 1,024 indices. These finite bounds match
-- the retained source certificate modules. Long lists use a proved decoder rule.
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

certify_source_tails Airbender.Setup.SourceCaptureParityProofs using Airbender.Setup.SourceCaptureParity
  trace_rows 4194304 padding_start 1114356
certify_source_tails Airbender.Setup.SourceCaptureThetaProofs using Airbender.Setup.SourceCaptureTheta
  trace_rows 4194304 padding_start 590066
certify_source_tails Airbender.Setup.SourceCaptureChiProofs using Airbender.Setup.SourceCaptureChi
  trace_rows 4194304 padding_start 1048697

namespace Airbender.Setup
open SourceBankCertificate

/-- Parsing and exact terminal-block facts prove every padding cell is zero. -/
theorem parsed_columns_padding {source : String} {artifact : Artifact} {cutoff : Nat}
    (parsed : parse source = .ok artifact)
    (tails : ∀ column ∈ artifact.columns, PaddingTail artifact.trace_len cutoff column)
    (index : Fin artifact.trace_len) (lower : cutoff ≤ index.val) :
    ∀ column : Fin artifact.columns.size, (artifact.columns[column].get? index.val) = some 0 := by
  intro column
  have member : artifact.columns[column] ∈ artifact.columns := by simp
  obtain ⟨tail, last, bound⟩ := tails _ member
  exact parsed_column_zero_tail parsed member tail index.val last (by omega) index.isLt

/-- The source parser and exact field certificates supply the padding premises. -/
theorem source_columns_padding {source : String} {json : Lean.Json} {artifact : Artifact}
    {length cutoff : Nat} {columns : Array Column}
    (sourceDecoded : Import.SetupJson.parse source = .ok json)
    (lengthDecoded : json.getObjValAs? Nat "trace_len" = .ok length)
    (columnsDecoded : json.getObjValAs? (Array Column) "columns" = .ok columns)
    (tails : ∀ column ∈ columns, PaddingTail length cutoff column)
    (parsed : parse source = .ok artifact)
    (index : Fin artifact.trace_len) (lower : cutoff ≤ index.val) :
    ∀ column : Fin artifact.columns.size, artifact.columns[column].get? index.val = some 0 := by
  have decoded := fields_of_parse sourceDecoded parsed
  have sameLength : artifact.trace_len = length := Except.ok.inj (decoded.1.symm.trans lengthDecoded)
  have sameColumns : artifact.columns = columns := Except.ok.inj (decoded.2.symm.trans columnsDecoded)
  apply parsed_columns_padding parsed ?_ index lower
  simpa only [sameLength, sameColumns] using tails

namespace SourceCaptureParityProofs

theorem source_padding {artifact : Artifact} (parsed : parse SourceCaptureParity.source = .ok artifact)
    (index : Fin artifact.trace_len) (lower : 1114356 ≤ index.val) :
    ∀ column : Fin artifact.columns.size, artifact.columns[column].get? index.val = some 0 :=
  source_columns_padding SourceCaptureParityProofs.parsed trace_len_decoded columns_decoded
    SourceCaptureParityProofs.padding_columns parsed index lower

end SourceCaptureParityProofs
namespace SourceCaptureThetaProofs

theorem source_padding {artifact : Artifact} (parsed : parse SourceCaptureTheta.source = .ok artifact)
    (index : Fin artifact.trace_len) (lower : 590066 ≤ index.val) :
    ∀ column : Fin artifact.columns.size, artifact.columns[column].get? index.val = some 0 :=
  source_columns_padding SourceCaptureThetaProofs.parsed trace_len_decoded columns_decoded
    SourceCaptureThetaProofs.padding_columns parsed index lower

end SourceCaptureThetaProofs
namespace SourceCaptureChiProofs

theorem source_padding {artifact : Artifact} (parsed : parse SourceCaptureChi.source = .ok artifact)
    (index : Fin artifact.trace_len) (lower : 1048697 ≤ index.val) :
    ∀ column : Fin artifact.columns.size, artifact.columns[column].get? index.val = some 0 :=
  source_columns_padding SourceCaptureChiProofs.parsed trace_len_decoded columns_decoded
    SourceCaptureChiProofs.padding_columns parsed index lower

end SourceCaptureChiProofs
end Airbender.Setup
