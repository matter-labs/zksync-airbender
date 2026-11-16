module
public import Human.Compiler.Capture
public meta import Human.Import.CompilerJson
public meta import Human.Import.TranscribeCommand
public meta import Lean

public meta section

/-! Trusted transcription of pinned native compiler captures. Human imports no certificate proofs. -/
namespace Airbender
open Lean Elab Command

deriving instance ToExpr for Compiler.RemainingInputs
deriving instance ToExpr for Compiler.SourceSnapshot
deriving instance ToExpr for Compiler.NativeCapture

/-- Share literal array entries so lookup certificates can keep their payloads opaque. -/
def addTranscribedArray {α : Type} [ToExpr α] (name : Name) (entries : Array α) : CoreM Lean.Expr := do
  let type := toTypeExpr α
  let mut references : Array Lean.Expr := #[]
  for h : index in [0:entries.size] do
    let entryName := name.appendAfter s!"Entry{index}"
    addTranscribedDef entryName type (toExpr entries[index])
    references := references.push (mkConst entryName)
  let data := references.toList.foldr (mkApp3 (mkConst ``List.cons [0]) type)
    (mkApp (mkConst ``List.nil [0]) type)
  addTranscribedDef name (mkApp (mkConst ``Array [0]) type)
    (mkApp2 (mkConst ``Array.mk [0]) type data)
  return mkConst name

syntax (name := importCompilerCapture) "import_compiler_capture " ident " from " str &"family" str : command

@[command_elab importCompilerCapture]
def elabImportCompilerCapture : CommandElab := fun stx => do
  let some path := stx[3].isStrLit? | throwUnsupportedSyntax
  let some expectedFamily := stx[5].isStrLit? | throwUnsupportedSyntax
  let text ← IO.FS.readFile path
  let capture : Compiler.NativeCapture ← match Lean.Json.parse text >>= fromJson? with
    | .ok value => pure value
    | .error error => throwError "Compiler capture import failed: {error}"
  unless capture.format_version == 1 && capture.cached && capture.family == expectedFamily do
    throwError "Expected a format-1 cached compiler capture for {expectedFamily}"
  let name := (← getCurrNamespace) ++ stx[1].getId
  liftCoreM do
    addTranscribedDef (name.appendAfter "SourceBytes") (mkConst ``String) (mkStrLit text)
    let mut value := toExpr capture
    for h : index in [0:capture.circuit.layers.size] do
      let layer := capture.circuit.layers[index]
      if layer.gates.size > 253 then
        let data ← addTranscribedArray (name.appendAfter s!"Layer{index}Gates") layer.gates
        let original := toExpr layer.gates
        value := value.replace fun entry => if entry == original then some data else none
      if layer.cached_relations.size > 253 then
        let data ← addTranscribedArray (name.appendAfter s!"Layer{index}Caches") layer.cached_relations
        let original := toExpr layer.cached_relations
        value := value.replace fun entry => if entry == original then some data else none
    addSharedTranscribedDef name (mkConst ``Compiler.NativeCapture) value
      (toExpr capture.circuit.placement_data.entries)

end Airbender
