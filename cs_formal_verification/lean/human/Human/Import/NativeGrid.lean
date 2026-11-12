module
public meta import Human.Import.SetupEmit
public meta import Lean

public meta section
namespace Airbender.Import.Setup
open Lean Meta Elab Command

/-- Compare every selected row and column. A mismatch reports its native coordinate. -/
def compareGrid (data : SetupData) (start length : Nat) (selected : List Nat)
    (formula : Fin length → Vector Nat selected.length) : Except String Unit := do
  let width := selected.length
  let mut actual : Array (Array Int) := #[]
  for column in selected do
    let some blocks := data.columns[column]? | throw "Native grid column is absent"
    let values := rowsOf (placedBlocks blocks) start (start + length)
    unless values.size = length do throw "Native grid rows are absent"
    actual := actual.push values
  for h : index in [:length] do
    let expected := formula ⟨index, h.2.1⟩
    for column in [:width] do
      unless actual[column]![index]! = (expected.toArray[column]! : Int) do
        throw s!"Native grid differs at row {index}, column {column}"

syntax "check_native_ranges " str : command
elab_rules : command
  | `(check_native_ranges $path:str) => do
    let data ← match parseSetup (← IO.FS.readFile path.getString) with
      | .ok data => pure data
      | .error reason => throwError "Native setup parse failed: {reason}"
    match compareRanges data with
    | .ok () => pure ()
    | .error reason => throwError "{reason}"

/-- Compare a named mathematical grid with every selected native row. This compiled comparison is trusted. -/
syntax "check_native_grid " str " [" num "," num "] " term:max " => " term : command

elab_rules : command
  | `(check_native_grid $path:str [$lo:num, $n:num] $cs:term => $f:term) => do
    let raw ← IO.FS.readFile path.getString
    let data ← match parseSetup raw with
      | .ok data => pure data
      | .error reason => throwError "Native setup parse failed: {reason}"
    let selected ← liftTermElabM do
      let type := mkApp (mkConst ``List [Level.zero]) (mkConst ``Nat)
      let value ← Term.elabTermEnsuringType cs type
      Term.synthesizeSyntheticMVarsNoPostponing
      unsafe evalExpr (List Nat) type (← instantiateMVars value)
    let width := selected.length
    let length := n.getNat
    let formula ← liftTermElabM do
      let type ← Term.elabType (← `(Fin $(quote length) → Vector Nat $(quote width)))
      let value ← Term.elabTermEnsuringType f type
      Term.synthesizeSyntheticMVarsNoPostponing
      unsafe evalExpr (Fin length → Vector Nat width) type (← instantiateMVars value)
    match compareGrid data lo.getNat length selected formula with
    | .ok () => pure ()
    | .error reason => throwError "{reason}"

end Airbender.Import.Setup
