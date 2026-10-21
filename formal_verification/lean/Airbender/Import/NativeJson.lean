import Airbender.Import.Schema

namespace Airbender
open Lean
set_option warningAsError true

/-- Match Rust's `GKRCircuitArtifact` serialization: only the absent
    `generic_lookup_padding` field is omitted (`serde(skip_serializing_if)`).
    Present zero and nonzero values, and every other nullable field, are retained. -/
def GKRCircuitArtifact.toNativeJson (circuit : GKRCircuitArtifact) : Json :=
  match toJson circuit with
  | .obj fields =>
    if circuit.generic_lookup_padding.isNone then
      Json.mkObj (fields.toList.filter fun field => field.1 != "generic_lookup_padding")
    else .obj fields
  | other => other

end Airbender
