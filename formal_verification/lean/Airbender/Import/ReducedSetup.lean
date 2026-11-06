import Airbender.Import.Setup

namespace Airbender.Setup.Reduced
open Lean

private def exactKeys (json : Json) (keys : Array String) : Except String Unit := do
  let entries := (← json.getObj?).toArray
  unless entries.size == keys.size && entries.all (fun (key, _) => keys.contains key) do
    throw "unexpected or missing reduced setup JSON fields"

def validateSignHigh (artifact : ControlArtifact) : Except String Unit := do
  unless artifact.version == 1 && artifact.field_modulus == mersenne31Modulus &&
      artifact.profile == "reduced_machine_sign_high" do
    throw "unsupported native reduced sign/high-byte profile"
  unless artifact.generic_rows == 65536 && artifact.tables.size == 1 do
    throw "unexpected native reduced sign/high-byte extent"
  let some region := artifact.tables[0]? | throw "missing native reduced sign/high-byte region"
  unless region.id == 16 && region.offset == 196609 do
    throw "unexpected native reduced sign/high-byte placement"
  unless region.data.length == 65536 && region.data.columns.size == 4 do
    throw "unexpected native reduced sign/high-byte matrix geometry"
  for column in region.data.columns do column.validate 65536 mersenne31Modulus

/-- Literal native rows only: validation does not certify their sign/high-byte semantics. -/
def parseSignHigh (source : String) : Except String ControlArtifact := do
  let json ← Json.parse source
  exactKeys json #["version", "field_modulus", "profile", "generic_rows", "tables"]
  for region in (← (← json.getObjVal? "tables").getArr?) do
    exactKeys region #["id", "offset", "data"]
    let matrix ← region.getObjVal? "data"
    exactKeys matrix #["length", "columns"]
    for column in (← (← matrix.getObjVal? "columns").getArr?) do
      exactKeys column #["blocks"]
  let artifact : ControlArtifact ← fromJson? json
  validateSignHigh artifact
  return artifact

end Airbender.Setup.Reduced
