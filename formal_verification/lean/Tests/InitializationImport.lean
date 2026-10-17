import Tests.Initialization
import Airbender.Import.Initialization

namespace Tests.InitializationImport
open Airbender Airbender.Initialization
set_option warningAsError true
set_option Elab.async false

private def check (condition : Bool) (message : String) : IO Unit :=
  if condition then IO.println s!"PASS {message}"
  else throw (IO.userError s!"FAIL {message}")

private def rejected : Except String Artifact → Bool
  | .error _ => true
  | .ok _ => false

private def mapGates (circuit : Circuit) (f : GKRRelation → GKRRelation) : Circuit :=
  { circuit with layers := circuit.layers.map fun layer => {layer with
    gates := layer.gates.map fun gate => {gate with enforced_relation := f gate.enforced_relation}
    gates_with_external_connections := layer.gates_with_external_connections.map fun gate =>
      {gate with enforced_relation := f gate.enforced_relation}} }

private def isRoot (relation : GKRRelation) (root : GKRAddress) : Bool :=
  (Import.outputs relation).contains root

def run : IO Unit := do
  for (label, path, flavor, embedded) in
      [("standalone", "../../cs/compiled_circuits/inits_and_teardowns_layout_no_caches_gkr.json",
        Import.Flavor.standalone, standalone),
       ("inline", "../../cs/compiled_circuits/unified_reduced_machine_layout_no_caches_gkr.json",
        Import.Flavor.unified, unified)] do
    let source ← IO.FS.readFile path
    let .ok circuit := parseCircuit source | throw (IO.userError s!"{label}: JSON parse failed")
    let .ok parsed := Import.extract flavor circuit source
      | throw (IO.userError s!"{label}: RAM extraction failed")
    check (parsed.layout == embedded.layout && parsed.gates == embedded.gates &&
      parsed.terminal == embedded.terminal && parsed.initial == embedded.initial &&
      source == embedded.sourceBytes) s!"initialization {label}: exact parsed/emitted metadata and wiring"
    let root := GKRAddress.InnerLayer parsed.terminal.output.layer parsed.terminal.output.offset
    let unsupported := mapGates circuit fun relation =>
      if isRoot relation root then .CopyInBaseField root root else relation
    check (rejected (Import.extract flavor unsupported)) s!"initialization {label}: unsupported producer rejected"
    let cyclic := mapGates circuit fun relation =>
      if isRoot relation root then .CopyInExtensionField root root else relation
    check (rejected (Import.extract flavor cyclic)) s!"initialization {label}: cyclic producer rejected"
    let external := mapGates circuit fun relation =>
      if isRoot relation root then .CopyInExtensionField (.BaseLayerMemory 0) root else relation
    check (rejected (Import.extract flavor external)) s!"initialization {label}: external input rejected"
    let missing := {circuit with layers := circuit.layers.map fun layer => {layer with
      gates := layer.gates.filter fun gate => !isRoot gate.enforced_relation root
      gates_with_external_connections := layer.gates_with_external_connections.filter fun gate =>
        !isRoot gate.enforced_relation root} }
    check (rejected (Import.extract flavor missing)) s!"initialization {label}: missing producer rejected"
    let duplicate := {circuit with layers := circuit.layers.map fun layer => {layer with
      gates := layer.gates ++ layer.gates.filter (fun gate => isRoot gate.enforced_relation root)
      gates_with_external_connections := layer.gates_with_external_connections ++
        layer.gates_with_external_connections.filter (fun gate => isRoot gate.enforced_relation root)} }
    check (rejected (Import.extract flavor duplicate)) s!"initialization {label}: duplicate producer rejected"
    let swapped := {circuit with global_output_map := ⟨circuit.global_output_map.entries.map fun (key, ports) =>
      (key, if ports.contains root then ports.reverse else ports)⟩ }
    check (rejected (Import.extract flavor swapped)) s!"initialization {label}: swapped output phases rejected"
    let tags := mapGates circuit fun relation => match relation with
      | .InitsOrTeardownsInitialPair mode _ output sets =>
        .InitsOrTeardownsInitialPair mode
          ⟨#[.VirtualSetup .InitsAndTeardownsHigh, .VirtualSetup .InitsAndTeardownsLow], by decide⟩ output sets
      | other => other
    check (rejected (Import.extract flavor tags)) s!"initialization {label}: wrong virtual address tags rejected"
    let columns := mapGates circuit fun relation => match relation with
      | .InitsOrTeardownsInitialPair (.Teardown lt _ rt rv) setup output sets =>
        .InitsOrTeardownsInitialPair (.Teardown lt ⟨#[999, 998], by decide⟩ rt rv) setup output sets
      | other => other
    check (rejected (Import.extract flavor columns)) s!"initialization {label}: wrong teardown columns rejected"
    check (rejected (Import.extract flavor {circuit with trace_len := 123}))
      s!"initialization {label}: wrong trace geometry rejected"
    check (rejected (Import.extract flavor {circuit with memory_layout :=
      {circuit.memory_layout with inits_and_teardowns_word_bits := none}}))
      s!"initialization {label}: missing word geometry rejected"
    check (rejected (Import.extract flavor {circuit with memory_layout :=
      {circuit.memory_layout with total_width := 0}}))
      s!"initialization {label}: out-of-bank columns rejected"

end Tests.InitializationImport
