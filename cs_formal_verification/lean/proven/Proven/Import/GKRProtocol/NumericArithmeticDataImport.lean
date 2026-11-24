module
public meta import Proven.Import.GKRProtocol.Export
public import Proven.GKRProtocol.NumericArithmeticChecks
public import Lean.AddDecl
public meta import Proven.GKRProtocol.NumericArithmeticChecks
public meta import Lean.AddDecl

public meta section
set_option warningAsError true

namespace Airbender.Compiler.NumericArithmeticDataImport
open Lean Elab Command

private def readEntry (path entry : String) : CommandElabM Json := do
  let json ← match Lean.Json.parse (← IO.FS.readFile path) with
    | .ok value => pure value
    | .error message => throwError "{message}"
  match json.getObjVal? entry with
  | .ok value => pure value
  | .error message => throwError "{message}"

private def polynomialTerm (row : Array (Nat × Array Nat)) : CommandElabM (TSyntax `term) := do
  let terms ← row.mapM fun (coefficient, monomial) => do
    let wires ← monomial.mapM fun wire => `($(quote wire))
    `((($(quote coefficient) : Nat), [$wires,*]))
  `([$terms,*])

private def closedEquality (name : Name) (statement : TSyntax `term) : CommandElabM Unit := do
  let type ← liftTermElabM do
    let value ← Term.elabType statement
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars value
  let proof ← liftTermElabM <| Meta.mkEqRefl type.getAppArgs[1]!
  liftCoreM <| addDecl (.thmDecl {name := (← getCurrNamespace) ++ name, levelParams := [], type, value := proof})
  Export.record (← `(theorem $(mkIdent name) : $statement := by rfl))

/-- Share bounded leaves between the flat payload and its materialized lookup tree. -/
private def emitRows (name : TSyntax `ident) (rowType : TSyntax `term)
    (rows : Array (TSyntax `term)) : CommandElabM Unit := withEnableInfoTree false do
  let mut leaves : Array (TSyntax `term × Nat) := #[]
  for index in [:max 1 ((rows.size + 15) / 16)] do
    let leaf := mkIdent (name.getId ++ Name.mkSimple s!"leaf{index}")
    let items := rows.extract (16 * index) (min rows.size (16 * (index + 1)))
    Export.emit (← `(def $leaf : List $rowType := [$items,*]))
    leaves := leaves.push (← `($leaf), items.size)
  let rec assemble (start count : Nat) : CommandElabM (TSyntax `term × TSyntax `term × Nat) := do
    if count ≤ 1 then
      let (leaf, size) := leaves[start]!
      return (leaf, ← `(NumericPolynomialChecks.LookupTable.leaf $leaf), size)
    else
      let middle := count / 2
      let (leftFlat, leftTree, leftSize) ← assemble start middle
      let (rightFlat, rightTree, rightSize) ← assemble (start + middle) (count - middle)
      return (← `(List.append $leftFlat $rightFlat),
        ← `(NumericPolynomialChecks.LookupTable.branch $(quote leftSize) $leftTree $rightTree), leftSize + rightSize)
  termination_by count
  let (flat, tree, _) ← assemble 0 leaves.size
  let treeName := mkIdent (name.getId ++ `tree)
  Export.emit (← `(def $name : List $rowType := $flat))
  Export.emit (← `(def $treeName : NumericPolynomialChecks.LookupTable $rowType := $tree))
  closedEquality (name.getId ++ `tree_binding) (← `(($treeName).toList = $name))
  closedEquality (name.getId ++ `tree_valid) (← `(($treeName).valid = true))

/-- Read numerical payloads. A separate kernel conversion checks their binding. -/
syntax "numeric_polynomials " ident " from " str " [" str "]" : command
elab_rules : command
  | `(numeric_polynomials $name:ident from $path:str [$entry:str]) => do
    let values ← match fromJson? (α := Array (Array (Nat × Array Nat)))
        (← readEntry path.getString entry.getString) with
      | .ok value => pure value
      | .error message => throwError "{message}"
    let rows ← values.mapM polynomialTerm
    emitRows name (← `(NumericPolynomialChecks.Data)) rows

syntax "numeric_combinations " ident " from " str " [" str "]" : command
elab_rules : command
  | `(numeric_combinations $name:ident from $path:str [$entry:str]) => do
    let values ← match fromJson? (α := Array (Array (Array (Nat × Array Nat) × Nat)))
        (← readEntry path.getString entry.getString) with
      | .ok value => pure value
      | .error message => throwError "{message}"
    let rows ← values.mapM fun row => do
      let terms ← row.mapM fun (polynomial, index) => do
        let payload ← polynomialTerm polynomial
        `(($payload, $(quote index)))
      `([$terms,*])
    emitRows name (← `(List (NumericPolynomialChecks.Data × Nat))) rows

syntax "numeric_naturals " ident " from " str " [" str "]" : command
elab_rules : command
  | `(numeric_naturals $name:ident from $path:str [$entry:str]) => do
    let values ← match fromJson? (α := Array Nat) (← readEntry path.getString entry.getString) with
      | .ok value => pure value
      | .error message => throwError "{message}"
    let terms ← values.mapM fun value => `($(quote value))
    withEnableInfoTree false <| Export.emit (← `(def $name : List Nat := [$terms,*]))

/-- The kernel checks the complete equality. No data conversion is trusted. -/
elab "numeric_data_binding " name:ident " : " statement:term : command => do
  let type ← liftTermElabM do
    let value ← Term.elabType statement
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars value
  unless type.isAppOfArity ``Eq 3 do throwError "numeric data binding requires equality"
  let proof ← liftTermElabM <| Meta.mkEqRefl type.getAppArgs[1]!
  let fullName := (← getCurrNamespace) ++ name.getId
  liftCoreM <| addDecl (.thmDecl {name := fullName, levelParams := [], type, value := proof})
  Export.record (← `(theorem $name : $statement := by rfl))

end Airbender.Compiler.NumericArithmeticDataImport
