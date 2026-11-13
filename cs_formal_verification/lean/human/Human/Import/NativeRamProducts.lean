module
public import Human.Circuits.InitsTeardowns.Native.Extract
public meta import Human.Circuits.InitsTeardowns.Native.Extract
public meta import Human.Import.CompilerJson
public meta import Human.Import.TranscribeCommand
public meta import Lean

public meta section

namespace Airbender.InitsTeardowns.Native
open Lean Elab Command

deriving instance ToExpr for Port
deriving instance ToExpr for Columns
deriving instance ToExpr for Phase
deriving instance ToExpr for Leaf
deriving instance ToExpr for Gate
deriving instance ToExpr for Tree
deriving instance ToExpr for Layout
deriving instance ToExpr for Artifact

/-- Transcribe the two native memory-product dependency trees. The binding claim checks extraction in the kernel. -/
elab "import_ram_products " name:ident " from " path:str inline:(" unified_inline")? : command => do
  let text ← IO.FS.readFile path.getString
  let circuit : Circuit ← match Lean.Json.parse text >>= fromJson? with
    | .ok circuit => pure circuit
    | .error error => throwError "Native initialization JSON: {error}"
  let flavor := if inline.isSome then Extract.Flavor.unified else .standalone
  let artifact ← match Extract.extract flavor circuit with
    | .ok artifact => pure artifact
    | .error error => throwError "Native initialization extraction: {error}"
  liftCoreM <| addTranscribedDef ((← getCurrNamespace) ++ name.getId) (mkConst ``Artifact) (toExpr artifact)

end Airbender.InitsTeardowns.Native
