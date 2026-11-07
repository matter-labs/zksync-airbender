import Airbender.Import.Schema

namespace Airbender
open Lean
set_option warningAsError true

/-- Rust omits the timestamp-group vector when empty. The imported schema also
    accepts an absent vector as `none`; both empty representations serialize alike. -/
def GKRAuxLayoutData.toNativeJson (layout : GKRAuxLayoutData) : Json :=
  match toJson layout with
  | .obj fields =>
    if (layout.relative_timestamp_groups.getD #[]).isEmpty then
      Json.mkObj (fields.toList.filter fun field => field.1 != "relative_timestamp_groups")
    else .obj fields
  | other => other

/-- Match Rust's circuit serialization, including nested auxiliary layout data.
    Only absent padding and empty timestamp groups are omitted. Present padding
    values, nonempty groups and every other nullable field are retained. -/
def GKRCircuitArtifact.toNativeJson (circuit : GKRCircuitArtifact) : Json :=
  match toJson circuit with
  | .obj fields =>
    let fields := fields.toList.map fun (name, value) =>
      (name, if name == "aux_layout_data" then circuit.aux_layout_data.toNativeJson else value)
    if circuit.generic_lookup_padding.isNone then
      Json.mkObj (fields.filter fun field => field.1 != "generic_lookup_padding")
    else Json.mkObj fields
  | other => other

end Airbender
