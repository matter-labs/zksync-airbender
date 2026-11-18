module
public import Human.Import.Columns
public meta import Human.Import.Columns
public import Lean
public meta import Lean

public meta section

/-! No need to review: an execution aid for `import_clean` (`Emit.lean`), whose output each artifact's
`ArtifactImportClaim` fixes (the kernel evaluates the functions of `Columns.lean` themselves).

The functions of `Columns.lean` find each logical variable through `Circuit.placements`, which builds the address
map from `placement_data` again on every call; run by Lean's interpreter at import time, that was most of an
artifact's build time. `derive_fast_columns` copies every function of `Columns.lean` that (transitively) calls
`Circuit.logicalVariable` into `Airbender.Fast`, with the map as a new first argument: the same term, with each
such function `f` replaced by `Fast.f map` and `Circuit.logicalVariable` by `Fast.logicalVariable map`. So
`Fast.f c.placements c = c.f`, by unfolding. -/

namespace Airbender.Fast
open Lean Elab Command Meta

/-- The address map of `Circuit.placements`. -/
abbrev Placements := Std.TreeMap (List Nat) (List Nat)

/-- `Circuit.logicalVariable`, the map given (`c.placements`). -/
def logicalVariable (placements : Placements) (c : Circuit) (address : GKRAddress) : Except String Nat := do
  let address ← c.lookupAddress address
  match placements.getD address.key [] with
  | [v] => pure v
  | _ => throw s!"address must have exactly one logical variable: {repr address}"

/-- Copy the functions of `Human.Import.Columns` that reach `Circuit.logicalVariable` into `Airbender.Fast`. -/
elab "derive_fast_columns" : command => liftTermElabM do
  let env ← getEnv
  let some idx := env.getModuleIdx? `Human.Import.Columns | throwError "Human.Import.Columns is not imported"
  let defs := env.constants.toList.filterMap fun (n, ci) =>
    match ci with
    | .defnInfo d => if env.getModuleIdxFor? n == some idx && (`Airbender.Circuit).isPrefixOf n
        && !n.isInternal then some d else none
    | _ => none
  -- the functions that reach `Circuit.logicalVariable`
  let mut reach : NameSet := NameSet.empty.insert ``Circuit.logicalVariable
  let mut changed := true
  while changed do
    changed := false
    for d in defs do
      if !reach.contains d.name && d.value.getUsedConstants.any reach.contains then
        reach := reach.insert d.name; changed := true
  -- callees first
  let mut done : NameSet := NameSet.empty.insert ``Circuit.logicalVariable
  let mut order : Array DefinitionVal := #[]
  changed := true
  while changed do
    changed := false
    for d in defs do
      if reach.contains d.name && !done.contains d.name &&
          d.value.getUsedConstants.all fun c => !reach.contains c || done.contains c || c == d.name then
        done := done.insert d.name; order := order.push d; changed := true
  unless order.size + 1 == reach.size do throwError "derive_fast_columns: recursive functions are unsupported"
  let fast (n : Name) : Name := `Airbender.Fast ++ n.replacePrefix `Airbender.Circuit .anonymous
  for d in order do
    let (type, value) ← withLocalDeclD `placements (mkConst ``Placements) fun pl => do
      let swap (e : Lean.Expr) : Option Lean.Expr := match e with
        | .const n _ => if reach.contains n then some (mkApp (mkConst (fast n)) pl) else none
        | _ => none
      return (← mkForallFVars #[pl] d.type, ← mkLambdaFVars #[pl] (d.value.replace swap))
    let height := getMaxHeight (← getEnv) value + 1
    let val : DefinitionVal :=
      { name := fast d.name, levelParams := d.levelParams, type := type, value := value,
        hints := .regular height, safety := .safe, all := [fast d.name] }
    let decl := Declaration.defnDecl val
    addDecl decl
    modifyEnv (markMeta · val.name)
    compileDecl decl

derive_fast_columns

end Airbender.Fast
