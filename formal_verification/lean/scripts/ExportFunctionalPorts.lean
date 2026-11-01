import Lean
import Lean.Util.Path
open Lean

private partial def strip : Expr → Expr
  | .mdata _ value => strip value
  | value => value

private def arguments (expected : Name) (value : Expr) : Except String (Array Expr) := do
  let value := strip value
  match value.getAppFn with
  | .const name _ =>
      if name == expected then pure value.getAppArgs else throw s!"expected {expected}, got {name}"
  | _ => throw s!"expected constructor {expected}"

private partial def elements (value : Expr) : Except String (List Expr) := do
  let value := strip value
  if value.getAppFn.isConstOf ``List.nil then pure []
  else
    let args ← arguments ``List.cons value
    unless args.size == 3 do throw "invalid list constructor"
    return args[1]! :: (← elements args[2]!)

private def natural (value : Expr) : Except String Nat :=
  match strip value with
  | .lit (.natVal value) => pure value
  | _ => throw "expected natural literal"

private def pair (value : Expr) : Except String (Nat × Nat) := do
  let args ← arguments ``Prod.mk value
  unless args.size == 4 do throw "invalid pair constructor"
  return (← natural args[2]!, ← natural args[3]!)

private def row (value : Expr) : Except String Json := do
  let args ← arguments `Airbender.Compiler.NumericFunctionalStepChecks.Data.mk value
  unless args.size == 3 do throw "invalid port record"
  unless (← elements args[0]!).isEmpty do throw "expected empty known list"
  let outputs ← (← elements args[1]!).mapM pair
  let inputs ← (← elements args[2]!).mapM pair
  unless (outputs ++ inputs).all (fun value => decide (value.2 ≤ 1)) do throw "invalid base flag"
  return Json.mkObj [("outputs",toJson outputs),("inputs",toJson inputs)]

unsafe def main (args : List String) : IO UInt32 := do
  let [moduleName, owner, totalText, output] := args | throw (IO.userError "module, owner, count, output required")
  let some totalCount := totalText.toNat? | throw (IO.userError "invalid count")
  initSearchPath (← findSysroot)
  let module := moduleName.toName
  let env ← importModules #[{module}] {}
  let mut rows : Array Json := #[]
  for first in (List.range ((totalCount + 31) / 32)).map (· * 32) do
    let name := (owner ++ ".ports" ++ toString first).toName
    let some info := env.find? name | throw (IO.userError s!"missing {name}")
    let some value := info.value? | throw (IO.userError s!"missing value {name}")
    let decoded := elements value >>= fun values => values.mapM row
    match decoded with
    | .ok chunk => rows := rows ++ chunk.toArray
    | .error message => throw (IO.userError message)
  unless rows.size == totalCount do throw (IO.userError "port coverage mismatch")
  IO.FS.writeFile output ((Json.arr rows).compress ++ "\n")
  IO.println s!"exported {rows.size} untrusted numeric port rows for {owner}"
  pure 0
