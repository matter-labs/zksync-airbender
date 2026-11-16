module
public meta import Human.Import.SetupEmit
public meta import Lean

public meta section

/-! # TRUSTED: review. Native setup rows are compared with mathematical row functions
    in compiled elaborator code. DECISION B uses these comparisons as the setup binding. -/

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

/-- Validate the native ranges and table layout. -/
def validateSetupInput (data : ParsedSetup) : Except String Unit := do
  compareRanges data
  for h : column in [0:data.columns.size] do
    let _ ← structureColumn data.tables column data.columns[column]

/- The stamp records the JSON for Lake dependency tracking. This command validates
   ranges and table layout. DECISION B binds setup rows through `check_native_grid`. -/
syntax "check_native_setup_input " ident " from " str : command
elab_rules : command
  | `(check_native_setup_input $name:ident from $path:str) => do
    let raw ← IO.FS.readFile path.getString
    let data ← match parseSetup raw with
      | .ok data => pure data
      | .error reason => throwError "Native setup parse failed: {reason}"
    match validateSetupInput data with
    | .ok () => pure ()
    | .error reason => throwError "{reason}"
    elabCommand (← `(@[expose] public def $name : Nat := $(quote ((hash raw).toNat))))

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
    match compareGrid data.toSetupData lo.getNat length selected formula with
    | .ok () => pure ()
    | .error reason => throwError "{reason}"

end Airbender.Import.Setup
