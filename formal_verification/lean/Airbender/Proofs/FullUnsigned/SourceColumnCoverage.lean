import Airbender.Proofs.FullUnsigned.SetupFields
import Airbender.Proofs.FullUnsigned.SetupPadding

namespace Airbender.Setup
set_option warningAsError true
set_option Elab.async false

/-- The original successful parse supplies complete coverage for every
exactly decoded source column. No validation premise is added. -/
theorem source_column_lengths {source : String} {json : Lean.Json} {artifact : Artifact}
    {length : Nat} {columns : Array Column}
    (sourceDecoded : Import.SetupJson.parse source = .ok json)
    (lengthDecoded : json.getObjValAs? Nat "trace_len" = .ok length)
    (columnsDecoded : json.getObjValAs? (Array Column) "columns" = .ok columns)
    (parsed : parse source = .ok artifact) :
    ∀ column ∈ columns, (column.blocks.toList.map Block.length).sum = length := by
  have decoded := fields_of_parse sourceDecoded parsed
  have sameLength : artifact.trace_len = length := Except.ok.inj (decoded.1.symm.trans lengthDecoded)
  have sameColumns : artifact.columns = columns := Except.ok.inj (decoded.2.symm.trans columnsDecoded)
  intro column member
  have actualMember : column ∈ artifact.columns := by rw [sameColumns]; exact member
  exact (parsed_column_length parsed actualMember).trans sameLength

end Airbender.Setup
