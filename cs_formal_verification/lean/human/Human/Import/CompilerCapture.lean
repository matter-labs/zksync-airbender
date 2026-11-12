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
    addTranscribedDef name (mkConst ``Compiler.NativeCapture) (toExpr capture)

end Airbender
