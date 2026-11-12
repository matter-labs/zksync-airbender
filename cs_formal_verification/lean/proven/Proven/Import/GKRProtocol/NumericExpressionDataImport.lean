module
public meta import Proven.Import.GKRProtocol.Export
public import Proven.Import.GKRProtocol.NumericArithmeticDataImport
public import Proven.GKRProtocol.NumericExpressionChecks
public meta import Proven.Import.GKRProtocol.NumericArithmeticDataImport
public meta import Proven.GKRProtocol.NumericExpressionChecks

public meta section
set_option warningAsError true

namespace Airbender.Compiler.NumericExpressionDataImport
open Lean Elab Command

private partial def expressionTerm (owner : Name) (counter : IO.Ref Nat) (value : Json) : CommandElabM (TSyntax `term × Nat) := do
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
    if tag == 0 then return (← `(NumericExpressionChecks.Code.constant $(quote value)), 1)
    else return (← `(NumericExpressionChecks.Code.atom $(quote value)), 1)
  else if fields.size == 3 && (tag == 2 || tag == 3) then
    let (left, leftSize) ← expressionTerm owner counter fields[1]!
    let (right, rightSize) ← expressionTerm owner counter fields[2]!
    let term ← if tag == 2 then `(NumericExpressionChecks.Code.add $left $right)
      else `(NumericExpressionChecks.Code.mul $left $right)
    let size := leftSize + rightSize + 1
    if size ≤ 48 then return (term, size)
    let index ← counter.get
    counter.set (index + 1)
    let name := mkIdent (owner ++ Name.mkSimple s!"node{index}")
    Export.emit (← `(def $name : NumericExpressionChecks.Code := $term))
    return (← `($name), 1)
  else throwError "invalid numeric expression shape"

syntax "numeric_expressions " ident " from " str " [" str "]" : command
elab_rules : command
  | `(numeric_expressions $name:ident from $path:str [$entry:str]) => do
    let json ← match Lean.Json.parse (← IO.FS.readFile path.getString) with
      | .ok json => pure json
      | .error message => throwError "{message}"
    let payload ← match json.getObjVal? entry.getString >>= Json.getArr? with
      | .ok payload => pure payload
      | .error message => throwError "{message}"
    let counter ← IO.mkRef 0
    let terms ← payload.mapM fun value => do pure (← expressionTerm name.getId counter value).1
    withEnableInfoTree false <| Export.emit
      (← `(def $name : List NumericExpressionChecks.Code := [$terms,*]))

end Airbender.Compiler.NumericExpressionDataImport
