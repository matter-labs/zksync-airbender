import Airbender.Review.Compiler.SetupSource

namespace Airbender.Setup
open Lean
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
set_option Elab.async false

/-- A successful artifact decoder preserves the complete column field. -/
theorem columns_of_fromJson {json : Json} {artifact : Artifact}
    (decoded : (fromJson? json : Except String Artifact) = .ok artifact) :
    json.getObjValAs? (Array Column) "columns" = .ok artifact.columns := by
  change instFromJsonArtifact.fromJson json = .ok artifact at decoded
  simp only [instFromJsonArtifact.fromJson, Except.mapError, bind, Except.bind] at decoded
  repeat' split at decoded
  all_goals first
    | contradiction
    | cases decoded
      cases columns : json.getObjValAs? (Array Column) "columns" <;> simp_all

/-- A successful artifact decoder preserves the physical domain length. -/
theorem trace_len_of_fromJson {json : Json} {artifact : Artifact}
    (decoded : (fromJson? json : Except String Artifact) = .ok artifact) :
    json.getObjValAs? Nat "trace_len" = .ok artifact.trace_len := by
  change instFromJsonArtifact.fromJson json = .ok artifact at decoded
  simp only [instFromJsonArtifact.fromJson, Except.mapError, bind, Except.bind] at decoded
  repeat' split at decoded
  all_goals first
    | contradiction
    | cases decoded
      cases traceLength : json.getObjValAs? Nat "trace_len" <;> simp_all

/-- Validation cannot change the artifact that the JSON decoder returned. -/
theorem fromJson_of_parse {source : String} {json : Json} {artifact : Artifact}
    (sourceDecoded : Import.SetupJson.parse source = .ok json)
    (parsed : parse source = .ok artifact) :
    (fromJson? json : Except String Artifact) = .ok artifact := by
  unfold parse at parsed
  rw [sourceDecoded] at parsed
  cases decoded : (fromJson? json : Except String Artifact) with
  | error error =>
    simp only [decoded, bind, Except.bind] at parsed
    split at parsed <;> contradiction
  | ok candidate =>
    simp only [decoded, bind, Except.bind, pure, Except.pure] at parsed
    repeat' split at parsed
    all_goals first | contradiction | cases parsed; rfl

/-- A source certificate can use decoded fields without evaluating unrelated
circuit fields or repeating artifact validation. -/
theorem fields_of_parse {source : String} {json : Json} {artifact : Artifact}
    (sourceDecoded : Import.SetupJson.parse source = .ok json)
    (parsed : parse source = .ok artifact) :
    json.getObjValAs? Nat "trace_len" = .ok artifact.trace_len ∧
      json.getObjValAs? (Array Column) "columns" = .ok artifact.columns := by
  have decoded := fromJson_of_parse sourceDecoded parsed
  exact ⟨trace_len_of_fromJson decoded, columns_of_fromJson decoded⟩

end Airbender.Setup

namespace Airbender.Compiler.MachineTargets.Proofs
open Lean
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
set_option Elab.async false

/-- Exact source and field certificates reduce the original setup-row premise
to membership for every physical row. Padding stays in the physical domain. -/
theorem fixed_setup_rows_of_decoded_columns
    {source : String} {json : Json} {columns : Array Setup.Column} {length : Nat}
    {table : Table F (fields width)}
    (sourceDecoded : Import.SetupJson.parse source = .ok json)
    (lengthDecoded : json.getObjValAs? Nat "trace_len" = .ok length)
    (columnsDecoded : json.getObjValAs? (Array Setup.Column) "columns" = .ok columns)
    (physicalRows : ∀ index : Fin length, table.toRaw.Contains #[]
      (Vector.ofFn fun column : Fin width =>
        (Setup.signedValue
          ((((columns[column.val]?).getD ⟨#[]⟩).get? index.val).getD 0) : F))) :
    FixedSetupRows source table := by
  intro artifact parsed _ row member
  have decoded := Setup.fields_of_parse sourceDecoded parsed
  have sameLength : artifact.trace_len = length :=
    Except.ok.inj (decoded.1.symm.trans lengthDecoded)
  have sameColumns : artifact.columns = columns :=
    Except.ok.inj (decoded.2.symm.trans columnsDecoded)
  obtain ⟨index, values⟩ := member
  let physical : Fin length := ⟨index.val, sameLength ▸ index.isLt⟩
  have sameRow : row = Vector.ofFn (fun column : Fin width =>
      (Setup.signedValue
        ((((columns[column.val]?).getD ⟨#[]⟩).get? physical.val).getD 0) : F)) := by
    apply Vector.ext
    intro column bound
    simpa only [Vector.getElem_ofFn, sameColumns, Fin.getElem_fin, physical]
      using values ⟨column, bound⟩
  rw [sameRow]
  exact physicalRows physical

end Airbender.Compiler.MachineTargets.Proofs
