module
public meta import Lean

public meta section
namespace Airbender.UnifiedReduced.Standard.Instances
open Lean Meta Elab Command

/-- Apply a previously checked theorem to a layout. The remaining binders keep their order
    and implicitness, including arguments whose types depend on the layout. -/
private def applyBabyBear : Nat → Expr → Expr → MetaM Expr
  | 0, term, _ => pure term
  | fuel + 1, term, .forallE n dom rest bi => do
    if dom.isConstOf `Airbender.UnifiedReduced.Standard.Profile then
      let profile := mkConst `Airbender.UnifiedReduced.Standard.Profile.babyBear
      applyBabyBear fuel (mkApp term profile) (rest.instantiate1 profile)
    else
      withLocalDecl n bi dom fun arg => do
        let value ← applyBabyBear fuel (mkApp term arg) (rest.instantiate1 arg)
        mkLambdaFVars #[arg] value
  | _, term, _ => pure term

private def declareBabyBear (source target : Name) : MetaM Unit := do
  let info ← getConstInfo source
  let value ← applyBabyBear info.type.getForallArity (mkConst source (info.levelParams.map mkLevelParam)) info.type
  let type ← inferType value
  if info.isTheorem then
    addDecl <| .thmDecl { name := target, levelParams := info.levelParams, type, value }
  else
    let alias : Declaration := .defnDecl {
      name := target, levelParams := info.levelParams, type, value, hints := .abbrev, safety := .safe }
    addDecl alias (forceExpose := true)
    setReducibilityStatus target .reducible
    compileDecl alias

/-- Preserve BabyBear's existing row proof API by applying each shared declaration to its layout. -/
elab "babybear_instances " names:ident,+ : command => do
  let ns ← getCurrNamespace
  let baseName := `Airbender.UnifiedReduced.Standard
  unless baseName.isPrefixOf ns do throwError "expected the unified Standard namespace"
  for id in names.getElems do
    let source := ns ++ id.getId
    liftTermElabM <| declareBabyBear source (source.replacePrefix baseName `Airbender.UnifiedReduced)

end Airbender.UnifiedReduced.Standard.Instances
