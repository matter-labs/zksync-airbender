import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
import Airbender.Proofs.GKRProtocol.NumericExpressionChecks

namespace Airbender.Compiler.NumericExpressionDataImport
open Lean Elab Command
set_option warningAsError true

private partial def expressionTerm (value : Json) : CommandElabM (TSyntax `term) := do
  let fields ← match value.getArr? with
    | .ok fields => pure fields
    | .error message => throwError "{message}"
  let tag ← match fields[0]? with
    | some value => match fromJson? (α := Nat) value with
      | .ok tag => pure tag
      | .error message => throwError "{message}"
    | none => throwError "empty numeric expression"
  if fields.size == 2 && tag < 2 then
    let value ← match fromJson? (α := Nat) fields[1]! with
      | .ok value => pure value
      | .error message => throwError "{message}"
    if tag == 0 then `(NumericExpressionChecks.Code.constant $(quote value))
    else `(NumericExpressionChecks.Code.atom $(quote value))
  else if fields.size == 3 && (tag == 2 || tag == 3) then
    let left ← expressionTerm fields[1]!
    let right ← expressionTerm fields[2]!
    if tag == 2 then `(NumericExpressionChecks.Code.add $left $right)
    else `(NumericExpressionChecks.Code.mul $left $right)
  else throwError "invalid numeric expression shape"

syntax "numeric_expressions " ident " from " str " [" str "]" : command
elab_rules : command
  | `(numeric_expressions $name:ident from $path:str [$entry:str]) => do
    let json ← match Json.parse (← IO.FS.readFile path.getString) with
      | .ok json => pure json
      | .error message => throwError "{message}"
    let payload ← match json.getObjVal? entry.getString >>= Json.getArr? with
      | .ok payload => pure payload
      | .error message => throwError "{message}"
    let terms ← payload.mapM expressionTerm
    withEnableInfoTree false <| elabCommand
      (← `(def $name : List NumericExpressionChecks.Code := [$terms,*]))

end Airbender.Compiler.NumericExpressionDataImport
