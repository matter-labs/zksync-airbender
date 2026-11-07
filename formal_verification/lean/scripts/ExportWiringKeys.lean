import Airbender.Proofs.GKRCompiler.WiringChecks
import Lean

namespace WiringKeysExport
open Lean Elab Command
set_option warningAsError true

private partial def naturals (value : Expr) : CommandElabM (Array Nat) := do
  let value ← liftTermElabM <| Meta.whnf value
  if value.getAppFn.isConstOf ``List.nil then return #[]
  unless value.getAppFn.isConstOf ``List.cons do throwError "expected a closed key list"
  let args := value.getAppArgs
  let head ← liftTermElabM <| Meta.reduce args[1]!
  let .lit (.natVal number) := head | throwError "expected a closed key"
  return #[number] ++ (← naturals args[2]!)

private def originalTerm (term : TSyntax `term) : CommandElabM Expr := liftTermElabM do
  let value ← Term.elabTerm term none
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars value

/-- Export untrusted keys. Exact kernel bindings check both complete banks. -/
syntax "export_wiring_keys " term " to " str : command
elab_rules : command
  | `(export_wiring_keys $graph:term to $destination:str) => do
    let producers ← naturals (← originalTerm
      (← `(($graph).produced.map Airbender.Compiler.AddressUniqueChecks.addressCode)))
    let placements ← naturals (← originalTerm
      (← `(($graph).placement.map (fun entry => Airbender.Compiler.AddressUniqueChecks.addressCode entry.1))))
    IO.FS.writeFile destination.getString
      ((Json.mkObj [("producers", toJson producers), ("placements", toJson placements)]).compress ++ "\n")

end WiringKeysExport
